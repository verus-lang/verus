use crate::ast::{
    BinaryOp, Const, Declaration, DeclarationX, Expr, ExprX, LogicalOp, Query, Stmt, StmtX, Typ,
    UnaryOp, ValidityResult,
};
use crate::context::{AssertionInfo, Context};
use std::collections::HashMap;
use z3::ast::{Bool, Dynamic, Int};
use z3::SatResult;

const PREFIX_LABEL: &str = "?lbl";
const PREFIX_USER_ID: &str = ".";

fn make_eq<'ctx, A: z3::ast::Ast<'ctx>>(lhs: &A, rhs: &A) -> Bool<'ctx> {
    lhs._eq(rhs)
}

fn expr_to_smt<'ctx>(context: &mut Context<'ctx>, expr: &Expr) -> Dynamic<'ctx> {
    match &**expr {
        ExprX::Const(Const::Bool(b)) => Bool::from_bool(&context.context, *b).into(),
        ExprX::Var(x) => match context.vars.get(x) {
            None => panic!("internal error: variable {} not found", x),
            Some(x) => x.clone(),
        },
        ExprX::Unary(op, expr) => match op {
            UnaryOp::Not => Bool::not(&expr_to_smt(context, expr).as_bool().unwrap()).into(),
        },
        ExprX::Binary(op, lhs, rhs) => {
            let lh = expr_to_smt(context, lhs);
            let rh = expr_to_smt(context, rhs);
            match op {
                BinaryOp::Implies => lh.as_bool().unwrap().implies(&rh.as_bool().unwrap()).into(),
                BinaryOp::Eq => make_eq(&lh, &rh).into(),
                BinaryOp::Ne => make_eq(&lh, &rh).not().into(),
                BinaryOp::Le => lh.as_int().unwrap().le(&rh.as_int().unwrap()).into(),
                BinaryOp::Ge => lh.as_int().unwrap().ge(&rh.as_int().unwrap()).into(),
                BinaryOp::Lt => lh.as_int().unwrap().lt(&rh.as_int().unwrap()).into(),
                BinaryOp::Gt => lh.as_int().unwrap().gt(&rh.as_int().unwrap()).into(),
                BinaryOp::Add => {
                    Int::add(context.context, &[&lh.as_int().unwrap(), &rh.as_int().unwrap()])
                        .into()
                }
                BinaryOp::Sub => {
                    Int::sub(context.context, &[&lh.as_int().unwrap(), &rh.as_int().unwrap()])
                        .into()
                }
                BinaryOp::Mul => {
                    Int::mul(context.context, &[&lh.as_int().unwrap(), &rh.as_int().unwrap()])
                        .into()
                }
                BinaryOp::EuclideanDiv => lh.as_int().unwrap().div(&rh.as_int().unwrap()).into(),
                BinaryOp::EuclideanMod => lh.as_int().unwrap().rem(&rh.as_int().unwrap()).into(),
            }
        }
        ExprX::Logical(op, exprs) => {
            let mut exprs_vec: Vec<Bool> = Vec::new();
            for expr in exprs.iter() {
                exprs_vec.push(expr_to_smt(context, expr).as_bool().unwrap());
            }
            let mut smt_exprs: Vec<&Bool> = Vec::new();
            for i in 0..exprs_vec.len() {
                smt_exprs.push(&exprs_vec[i]);
            }
            match op {
                LogicalOp::And => Bool::and(&context.context, &smt_exprs).into(),
                LogicalOp::Or => Bool::or(&context.context, &smt_exprs).into(),
            }
        }
        ExprX::LabeledAssertion(span, expr) => {
            let label = Bool::fresh_const(&context.context, PREFIX_LABEL);
            let assertion_info = AssertionInfo { span: span.clone(), label: label.clone() };
            context.assertion_infos.push(assertion_info);
            let smt_expr = expr_to_smt(context, expr).as_bool().unwrap();
            // See comments about Z3_model_eval below for why do we use => instead of or.
            // Bool::or(&context.context, &[&label, &smt_expr])
            label.implies(&smt_expr).into()
        }
    }
}

pub fn smt_add_decl<'ctx>(context: &mut Context<'ctx>, decl: &Declaration, is_global: bool) {
    match &**decl {
        DeclarationX::Const(x, typ) => {
            if is_global {
                todo!(); // push and pop groups of variables
            }
            let name = PREFIX_USER_ID.to_string() + x;
            let x_smt: Dynamic<'ctx> = match typ {
                Typ::Bool => Bool::new_const(context.context, name.clone()).into(),
                Typ::Int => Int::new_const(context.context, name.clone()).into(),
            };
            let prev = context.vars.insert(x.clone(), x_smt);
            assert_eq!(prev, None);
        }
        DeclarationX::Axiom(expr) => {
            let smt_expr = expr_to_smt(context, &expr).as_bool().unwrap();
            context.solver.assert(&smt_expr);
        }
    }
}

fn smt_check_assertion<'ctx>(context: &mut Context<'ctx>, stmt: &Stmt) -> ValidityResult {
    match &**stmt {
        StmtX::Assert(span, expr) => {
            let mut discovered_span = span.clone();
            let smt_expr = expr_to_smt(context, &expr).as_bool().unwrap();
            let not_expr = Bool::not(&smt_expr);
            context.solver.assert(&not_expr);
            //dbg!(not_expr);

            let mut params = z3::Params::new(&context.context);
            params.set_u32("rlimit", context.rlimit);
            context.solver.set_params(&params);

            let sat = context.solver.check();

            params.set_u32("rlimit", 0);
            context.solver.set_params(&params);

            //dbg!(context.solver);

            match sat {
                SatResult::Unsat => ValidityResult::Valid,
                SatResult::Sat | SatResult::Unknown => {
                    let model = context.solver.get_model();
                    match model {
                        None => {
                            panic!("SMT solver did not generate a model");
                        }
                        Some(model) => {
                            // dbg!(&context.solver);
                            // println!("model = >>{}<<", model.to_string());
                            for info in context.assertion_infos.iter() {
                                /*
                                Unfortunately, the Rust Z3 crate's eval calls Z3_model_eval
                                with model_completion = true.
                                This hides exactly what we're interested in:
                                the set of variables that are actually assigned in the model.
                                It happens, though, that Z3 completes boolean variables in
                                the model with false,
                                so we can just look for the variables that evaluate to true.
                                */
                                if let Some(b) = model.eval(&info.label) {
                                    if let Some(b) = b.as_bool() {
                                        if b {
                                            discovered_span = info.span.clone();
                                        }
                                    }
                                }
                            }
                        }
                    }
                    ValidityResult::Error(discovered_span)
                }
            }
        }
        _ => {
            panic!("internal error: expected assertion, found {:?}", stmt)
        }
    }
}

pub fn smt_check_query<'ctx>(context: &mut Context<'ctx>, query: &Query) -> ValidityResult {
    context.solver.push();
    for decl in query.local.iter() {
        smt_add_decl(context, decl, false);
    }
    context.assertion_infos = Vec::new();
    let assertion = crate::block_to_assert::block_to_assert(&query.assertion);
    let result = smt_check_assertion(context, &assertion);
    context.vars = HashMap::new(); // TODO: selectively pop variables
    context.solver.pop(1);
    result
}
