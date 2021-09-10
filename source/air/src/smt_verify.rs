use crate::ast::{
    BinaryOp, BindX, Decl, DeclX, Expr, ExprX, Ident, MultiOp, Quant, Query, Snapshots, Span,
    StmtX, TypX, UnaryOp,
};
use crate::context::{AssertionInfo, Context, ValidityResult};
use crate::def::{GLOBAL_PREFIX_LABEL, PREFIX_LABEL};
pub use crate::model::{Model, ModelDef};
use std::collections::HashMap;
use std::sync::Arc;

fn label_asserts<'ctx>(
    context: &mut Context,
    infos: &mut Vec<AssertionInfo>,
    expr: &Expr,
    is_global: bool,
) -> Expr {
    match &**expr {
        ExprX::Binary(op @ BinaryOp::Implies, lhs, rhs)
        | ExprX::Binary(op @ BinaryOp::Eq, lhs, rhs) => {
            // asserts are on rhs of =>
            // (slight hack to also allow rhs of == for quantified function definitions)
            Arc::new(ExprX::Binary(*op, lhs.clone(), label_asserts(context, infos, rhs, is_global)))
        }
        ExprX::Multi(op @ MultiOp::And, exprs) | ExprX::Multi(op @ MultiOp::Or, exprs) => {
            let mut exprs_vec: Vec<Expr> = Vec::new();
            for expr in exprs.iter() {
                exprs_vec.push(label_asserts(context, infos, expr, is_global));
            }
            Arc::new(ExprX::Multi(*op, Arc::new(exprs_vec)))
        }
        ExprX::Bind(bind, body) => match &**bind {
            BindX::Quant(Quant::Forall, _, _) => {
                Arc::new(ExprX::Bind(bind.clone(), label_asserts(context, infos, body, is_global)))
            }
            _ => expr.clone(),
        },
        ExprX::LabeledAssertion(span, expr) => {
            let label = if is_global {
                let count = context.assert_infos_count;
                context.assert_infos_count += 1;
                Arc::new(GLOBAL_PREFIX_LABEL.to_string() + &count.to_string())
            } else {
                Arc::new(PREFIX_LABEL.to_string() + &infos.len().to_string())
            };
            let decl = Arc::new(DeclX::Const(label.clone(), Arc::new(TypX::Bool)));
            let assertion_info = AssertionInfo { span: span.clone(), label: label.clone(), decl };
            infos.push(assertion_info);
            let lhs = Arc::new(ExprX::Var(label));
            // See comments about Z3_model_eval below for why do we use => instead of or.
            Arc::new(ExprX::Binary(
                BinaryOp::Implies,
                lhs,
                label_asserts(context, infos, expr, is_global),
            ))
        }
        _ => expr.clone(),
    }
}

/// In SMT-LIB, functions applied to zero arguments are considered constants.
/// REVIEW: maybe AIR should follow this design for consistency.
fn elim_zero_args_expr(expr: &Expr) -> Expr {
    crate::visitor::map_expr_visitor(expr, &mut |expr| match &**expr {
        ExprX::Apply(x, es) if es.len() == 0 => Arc::new(ExprX::Var(x.clone())),
        _ => expr.clone(),
    })
}

pub(crate) fn smt_add_decl<'ctx>(context: &mut Context, decl: &Decl) {
    match &**decl {
        DeclX::Sort(_) | DeclX::Datatypes(_) | DeclX::Const(_, _) | DeclX::Fun(_, _, _) => {
            context.smt_log.log_decl(decl);
        }
        DeclX::Var(_, _) => {}
        DeclX::Axiom(expr) => {
            let expr = elim_zero_args_expr(expr);
            let mut infos: Vec<AssertionInfo> = Vec::new();
            let labeled_expr = label_asserts(context, &mut infos, &expr, true);
            for info in infos {
                crate::typecheck::add_decl(context, &info.decl, true).unwrap();
                context
                    .assert_infos
                    .insert(info.label.clone(), Arc::new(info.clone()))
                    .expect("internal error: duplicate assert_info");
                smt_add_decl(context, &info.decl);
            }
            context.smt_log.log_assert(&labeled_expr);
        }
    }
}

fn smt_check_assertion<'ctx>(
    context: &mut Context,
    infos: &Vec<AssertionInfo>,
    snapshots: Snapshots,
    local_vars: Vec<Decl>, // Expected to be entirely DeclX::Const
    expr: &Expr,
) -> ValidityResult {
    let mut discovered_span = Arc::new(None);
    let mut discovered_global_span = Arc::new(None);
    let not_expr = Arc::new(ExprX::Unary(UnaryOp::Not, expr.clone()));
    context.smt_log.log_assert(&not_expr);

    context.smt_log.log_set_option("rlimit", &context.rlimit.to_string());
    context.set_z3_param_u32("rlimit", context.rlimit, false);

    context.smt_log.log_word("check-sat");

    let smt_output =
        context.smt_manager.get_smt_process().send_commands(context.smt_log.take_pipe_data());
    let mut unsat = None;
    for line in smt_output {
        if line == "unsat" {
            assert!(unsat == None);
            unsat = Some(true);
        } else if line == "sat" || line == "unknown" {
            assert!(unsat == None);
            unsat = Some(false);
        } else {
            println!("warning: unexpected SMT output: {}", line);
        }
    }

    context.smt_log.log_set_option("rlimit", "0");
    context.set_z3_param_u32("rlimit", 0, false);

    match unsat {
        None => {
            panic!("expected sat/unsat/unknown from SMT solver");
        }
        Some(true) => ValidityResult::Valid,
        Some(false) => {
            context.smt_log.log_word("get-model");
            let smt_output = context
                .smt_manager
                .get_smt_process()
                .send_commands(context.smt_log.take_pipe_data());
            let model = crate::parser::lines_to_model(&smt_output);
            let mut model_defs: HashMap<Ident, ModelDef> = HashMap::new();
            for def in model.iter() {
                model_defs.insert(def.name.clone(), def.clone());
            }
            for info in infos.iter() {
                if let Some(def) = model_defs.get(&info.label) {
                    if *def.body == "true" {
                        discovered_span = info.span.clone();
                        break;
                    }
                }
            }
            for (_, info) in context.assert_infos.map().iter() {
                if let Some(def) = model_defs.get(&info.label) {
                    if *def.body == "true" {
                        discovered_global_span = info.span.clone();
                        break;
                    }
                }
            }

            if context.debug {
                println!("Z3 model: {:?}", &model);
            }
            let mut air_model = Model::new(snapshots);
            if context.debug {
                air_model.build(context, local_vars);
            }
            ValidityResult::Invalid(air_model, discovered_span, discovered_global_span)
        }
    }
}

pub(crate) fn smt_check_query<'ctx>(
    context: &mut Context,
    query: &Query,
    snapshots: Snapshots,
    local_vars: Vec<Decl>,
) -> ValidityResult {
    context.smt_log.log_push();
    context.push_name_scope();

    // add query-local declarations
    for decl in query.local.iter() {
        if let Err(err) = crate::typecheck::add_decl(context, decl, false) {
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, decl);
    }

    // after lowering, there should be just one assertion
    let assertion = match &*query.assertion {
        StmtX::Assert(_, expr) => expr,
        _ => panic!("internal error: query not lowered"),
    };
    let assertion = elim_zero_args_expr(assertion);

    // add labels to assertions for error reporting
    let mut infos: Vec<AssertionInfo> = Vec::new();
    let labeled_assertion = label_asserts(context, &mut infos, &assertion, false);
    for info in &infos {
        if let Some(Span { as_string, .. }) = &*info.span {
            context.smt_log.comment(as_string);
        }
        if let Err(err) = crate::typecheck::add_decl(context, &info.decl, false) {
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, &info.decl);
    }

    // check assertion
    let result = smt_check_assertion(context, &infos, snapshots, local_vars, &labeled_assertion);

    // clean up
    context.pop_name_scope();
    context.smt_log.log_pop();
    result
}
