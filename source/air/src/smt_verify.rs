use crate::ast::{
    BinaryOp, Const, Declaration, DeclarationX, Expr, ExprX, Ident, LogicalOp, Query, Span,
    SpanOption, StmtX, TypX, UnaryOp, ValidityResult,
};
use crate::context::Context;
use std::collections::HashMap;
use std::rc::Rc;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{SatResult, Sort, Symbol};

pub const PREFIX_LABEL: &str = "%%location_label%%";

fn expr_to_smt<'ctx>(context: &mut Context<'ctx>, expr: &Expr) -> Dynamic<'ctx> {
    match &**expr {
        ExprX::Const(Const::Bool(b)) => Bool::from_bool(&context.context, *b).into(),
        ExprX::Const(Const::Nat(n)) => Int::from_str(&context.context, n).unwrap().into(),
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
                BinaryOp::Eq => lh._eq(&rh).into(),
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
        ExprX::LabeledAssertion(_, _) => panic!("internal error: LabeledAssertion"),
    }
}

#[derive(Debug)]
pub(crate) struct AssertionInfo {
    pub(crate) span: SpanOption,
    pub(crate) label: Ident,
    pub(crate) decl: Declaration,
}

fn label_asserts<'ctx>(
    context: &mut Context<'ctx>,
    infos: &mut Vec<AssertionInfo>,
    expr: &Expr,
) -> Expr {
    match &**expr {
        ExprX::Binary(BinaryOp::Implies, lhs, rhs) => {
            // asserts are on rhs
            Rc::new(ExprX::Binary(
                BinaryOp::Implies,
                lhs.clone(),
                label_asserts(context, infos, rhs),
            ))
        }
        ExprX::Logical(op, exprs) => {
            let mut exprs_vec: Vec<Expr> = Vec::new();
            for expr in exprs.iter() {
                exprs_vec.push(label_asserts(context, infos, expr));
            }
            Rc::new(ExprX::Logical(*op, Rc::new(exprs_vec.into_boxed_slice())))
        }
        ExprX::LabeledAssertion(span, expr) => {
            let label = Rc::new(PREFIX_LABEL.to_string() + &infos.len().to_string());
            let decl = Rc::new(DeclarationX::Const(label.clone(), Rc::new(TypX::Bool)));
            let assertion_info = AssertionInfo { span: span.clone(), label: label.clone(), decl };
            infos.push(assertion_info);
            let lhs = Rc::new(ExprX::Var(label));
            // See comments about Z3_model_eval below for why do we use => instead of or.
            Rc::new(ExprX::Binary(BinaryOp::Implies, lhs, expr.clone()))
        }
        _ => expr.clone(),
    }
}

pub fn smt_add_decl<'ctx>(context: &mut Context<'ctx>, decl: &Declaration, is_global: bool) {
    match &**decl {
        DeclarationX::Sort(x) => {
            context.smt_log.log_sort_decl(x);
            let sort = Sort::uninterpreted(context.context, Symbol::String((**x).clone()));
            let prev = context.typs.insert(x.clone(), sort);
            assert_eq!(prev, None);
        }
        DeclarationX::Const(x, typ) => {
            context.smt_log.log_function_decl(x, &[], typ);
            if is_global {
                todo!(); // push and pop groups of variables
            }
            let name = &**x;
            let x_smt: Dynamic<'ctx> = match &**typ {
                TypX::Bool => Bool::new_const(context.context, name.clone()).into(),
                TypX::Int => Int::new_const(context.context, name.clone()).into(),
                TypX::Named(x) => {
                    let sort = &context.typs[x];
                    let fdecl = z3::FuncDecl::new(context.context, name.clone(), &[], sort);
                    fdecl.apply(&[])
                }
            };
            let prev = context.vars.insert(x.clone(), x_smt);
            assert_eq!(prev, None);
        }
        DeclarationX::Axiom(expr) => {
            context.smt_log.log_assert(&expr);
            let smt_expr = expr_to_smt(context, &expr).as_bool().unwrap();
            context.solver.assert(&smt_expr);
        }
    }
}

fn smt_check_assertion<'ctx>(
    context: &mut Context<'ctx>,
    infos: &Vec<AssertionInfo>,
    expr: &Expr,
) -> ValidityResult {
    let mut discovered_span = Rc::new(None);
    let not_expr = Rc::new(ExprX::Unary(UnaryOp::Not, expr.clone()));
    context.smt_log.log_assert(&not_expr);
    context.solver.assert(&expr_to_smt(context, &not_expr).as_bool().unwrap());

    context.smt_log.log_set_option("rlimit", &context.rlimit.to_string());
    context.set_z3_param_u32("rlimit", context.rlimit, false);

    context.smt_log.log_word("check-sat");
    let sat = context.solver.check();

    context.smt_log.log_set_option("rlimit", "0");
    context.set_z3_param_u32("rlimit", 0, false);

    match sat {
        SatResult::Unsat => ValidityResult::Valid,
        SatResult::Sat | SatResult::Unknown => {
            context.smt_log.log_word("get-model");
            let model = context.solver.get_model();
            match model {
                None => {
                    panic!("SMT solver did not generate a model");
                }
                Some(model) => {
                    // dbg!(&context.solver);
                    // println!("model = >>{}<<", model.to_string());
                    for info in infos.iter() {
                        /*
                        Unfortunately, the Rust Z3 crate's eval calls Z3_model_eval
                        with model_completion = true.
                        This hides exactly what we're interested in:
                        the set of variables that are actually assigned in the model.
                        It happens, though, that Z3 completes boolean variables in
                        the model with false,
                        so we can just look for the variables that evaluate to true.
                        */
                        let x_info = context.vars[&info.label].as_bool().unwrap();
                        if let Some(b) = model.eval(&x_info) {
                            if let Some(b2) = b.as_bool() {
                                if b2 {
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

pub fn smt_check_query<'ctx>(context: &mut Context<'ctx>, query: &Query) -> ValidityResult {
    context.smt_log.log_push();
    context.solver.push();

    // add query-local declarations
    for decl in query.local.iter() {
        smt_add_decl(context, decl, false);
    }

    // after lowering, there should be just one assertion
    let assertion = match &*query.assertion {
        StmtX::Assert(_, expr) => expr,
        _ => panic!("internal error: query not lowered"),
    };

    // add labels to assertions for error reporting
    let mut infos: Vec<AssertionInfo> = Vec::new();
    let labeled_assertion = label_asserts(context, &mut infos, &assertion);
    for info in &infos {
        if let Some(Span { as_string, .. }) = &*info.span {
            context.smt_log.comment(as_string);
        }
        smt_add_decl(context, &info.decl, false);
    }

    // check assertion
    let result = smt_check_assertion(context, &infos, &labeled_assertion);

    // clean up
    context.vars = HashMap::new(); // TODO: selectively pop variables
    context.smt_log.log_pop();
    context.solver.pop(1);
    result
}
