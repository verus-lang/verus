use crate::ast::{
    BinaryOp, BindX, Decl, DeclX, Expr, ExprX, Ident, MultiOp, Quant, Query, StmtX, TypX, UnaryOp,
};
use crate::ast_util::{ident_var, mk_and, mk_implies, mk_not, str_ident, str_var};
use crate::context::{AssertionInfo, AxiomInfo, Context, ContextState, ValidityResult};
use crate::def::{GLOBAL_PREFIX_LABEL, PREFIX_LABEL, QUERY};
use crate::errors::{Error, ErrorLabel};
pub use crate::model::{Model, ModelDef};
use std::collections::HashMap;
use std::sync::Arc;

fn label_asserts<'ctx>(
    context: &mut Context,
    infos: &mut Vec<AssertionInfo>,
    axiom_infos: &mut Vec<AxiomInfo>,
    expr: &Expr,
) -> Expr {
    match &**expr {
        ExprX::Binary(op @ BinaryOp::Implies, lhs, rhs)
        | ExprX::Binary(op @ BinaryOp::Eq, lhs, rhs) => {
            // asserts are on rhs of =>
            // (slight hack to also allow rhs of == for quantified function definitions)
            Arc::new(ExprX::Binary(
                *op,
                lhs.clone(),
                label_asserts(context, infos, axiom_infos, rhs),
            ))
        }
        ExprX::Multi(op @ MultiOp::And, exprs) | ExprX::Multi(op @ MultiOp::Or, exprs) => {
            let mut exprs_vec: Vec<Expr> = Vec::new();
            for expr in exprs.iter() {
                exprs_vec.push(label_asserts(context, infos, axiom_infos, expr));
            }
            Arc::new(ExprX::Multi(*op, Arc::new(exprs_vec)))
        }
        ExprX::Bind(bind, body) => match &**bind {
            BindX::Quant(Quant::Forall, _, _) => Arc::new(ExprX::Bind(
                bind.clone(),
                label_asserts(context, infos, axiom_infos, body),
            )),
            _ => expr.clone(),
        },
        ExprX::LabeledAssertion(error, expr) => {
            let label = Arc::new(PREFIX_LABEL.to_string() + &infos.len().to_string());

            let decl = Arc::new(DeclX::Const(label.clone(), Arc::new(TypX::Bool)));
            let assertion_info =
                AssertionInfo { error: error.clone(), label: label.clone(), decl, disabled: false };
            infos.push(assertion_info);
            let lhs = Arc::new(ExprX::Var(label));
            Arc::new(ExprX::Binary(
                BinaryOp::Implies,
                lhs,
                label_asserts(context, infos, axiom_infos, expr),
            ))
        }
        ExprX::LabeledAxiom(labels, expr) => {
            let count = context.axiom_infos_count;
            context.axiom_infos_count += 1;
            let label = Arc::new(GLOBAL_PREFIX_LABEL.to_string() + &count.to_string());

            let decl = Arc::new(DeclX::Const(label.clone(), Arc::new(TypX::Bool)));
            let axiom_info = AxiomInfo { labels: labels.clone(), label: label.clone(), decl };
            axiom_infos.push(axiom_info);
            let lhs = Arc::new(ExprX::Var(label));
            Arc::new(ExprX::Binary(
                BinaryOp::Implies,
                lhs,
                label_asserts(context, infos, axiom_infos, expr),
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
            let mut axiom_infos: Vec<AxiomInfo> = Vec::new();
            let labeled_expr = label_asserts(context, &mut infos, &mut axiom_infos, &expr);
            for info in axiom_infos {
                crate::typecheck::add_decl(context, &info.decl, true).unwrap();
                context
                    .axiom_infos
                    .insert(info.label.clone(), Arc::new(info.clone()))
                    .expect("internal error: duplicate assert_info");
                smt_add_decl(context, &info.decl);
            }
            context.smt_log.log_assert(&labeled_expr);
        }
    }
}

pub(crate) fn smt_check_assertion<'ctx>(
    context: &mut Context,
    mut infos: Vec<AssertionInfo>,
    air_model: Model,
    only_check_earlier: bool,
) -> ValidityResult {
    if only_check_earlier {
        // disable all labels that come after the first known error
        let mut disabled: Vec<Expr> = Vec::new();
        let mut found_disabled = false;
        let mut found_enabled = false;
        for info in infos.iter_mut() {
            if found_disabled && !info.disabled {
                info.disabled = true;
                disabled.push(mk_not(&ident_var(&info.label)));
            }
            if info.disabled {
                found_disabled = true;
            } else {
                found_enabled = true;
            }
        }
        if only_check_earlier && !found_enabled {
            // no earlier assertions to check
            return ValidityResult::Valid;
        }
        context.smt_log.log_assert(&mk_and(&disabled));
    }

    let mut discovered_error: Option<Error> = None;
    let mut discovered_additional_info: Vec<ErrorLabel> = Vec::new();
    context.smt_log.log_assert(&str_var(QUERY));

    context.smt_log.log_set_option("rlimit", &context.rlimit.to_string());
    context.set_z3_param_u32("rlimit", context.rlimit, false);

    context.smt_log.log_word("check-sat");

    // Run SMT solver
    let time0 = std::time::Instant::now();
    let smt_proc = context.smt_manager.get_smt_process();
    let time1 = std::time::Instant::now();
    let smt_output = smt_proc.send_commands(context.smt_log.take_pipe_data());
    let time2 = std::time::Instant::now();
    context.time_smt_init += time1 - time0;
    context.time_smt_run += time2 - time1;

    // Process SMT results
    let mut unsat = None;
    for line in smt_output {
        if line == "unsat" {
            assert!(unsat == None);
            unsat = Some(true);
        } else if line == "sat" || line == "unknown" {
            assert!(unsat == None);
            unsat = Some(false);
        } else if context.ignore_unexpected_smt {
            println!("warning: unexpected SMT output: {}", line);
        } else {
            return ValidityResult::UnexpectedSmtOutput(line);
        }
    }

    context.smt_log.log_set_option("rlimit", "0");
    context.set_z3_param_u32("rlimit", 0, false);

    match unsat {
        None => {
            panic!("expected sat/unsat/unknown from SMT solver");
        }
        Some(true) => {
            context.state = ContextState::FoundResult;
            ValidityResult::Valid
        }
        Some(false) => {
            context.smt_log.log_word("get-model");
            let smt_output = context
                .smt_manager
                .get_smt_process()
                .send_commands(context.smt_log.take_pipe_data());
            let model = crate::parser::Parser::new().lines_to_model(&smt_output);
            let mut model_defs: HashMap<Ident, ModelDef> = HashMap::new();
            for def in model.iter() {
                model_defs.insert(def.name.clone(), def.clone());
            }
            for info in infos.iter_mut() {
                if let Some(def) = model_defs.get(&info.label) {
                    if *def.body == "true" {
                        discovered_error = Some(info.error.clone());

                        // Disable this label in subsequent check-sat calls to get additional errors
                        info.disabled = true;
                        let disable_label = mk_not(&ident_var(&info.label));
                        context.smt_log.log_assert(&disable_label);

                        break;
                    }
                }
            }
            for (_, info) in context.axiom_infos.map().iter() {
                if let Some(def) = model_defs.get(&info.label) {
                    if *def.body == "true" {
                        discovered_additional_info.append(&mut (*info.labels).clone());
                        break;
                    }
                }
            }

            if context.debug {
                println!("Z3 model: {:?}", &model);
            }

            // Attach the additional info to the error
            // For example, the error might be something like "precondition not satisfied"
            // (an error which comes from the air assert statement)
            // and the additional info might tell you _which_ precondition failed
            // (a label that comes from one of the axioms associated
            // to the function precondition)

            let error = discovered_error.expect("discovered_error");
            let e = error.append_labels(&discovered_additional_info);
            context.state = ContextState::FoundInvalid(infos, air_model.clone());
            ValidityResult::Invalid(air_model, e)
        }
    }
}

pub(crate) fn smt_check_query<'ctx>(
    context: &mut Context,
    query: &Query,
    air_model: Model,
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
    let mut axiom_infos: Vec<AxiomInfo> = Vec::new();
    let labeled_assertion = label_asserts(context, &mut infos, &mut axiom_infos, &assertion);
    for info in &infos {
        context.smt_log.comment(&info.error.msg);
        if let Err(err) = crate::typecheck::add_decl(context, &info.decl, false) {
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, &info.decl);
    }

    // check assertion
    let not_expr = Arc::new(ExprX::Unary(UnaryOp::Not, labeled_assertion));
    context.smt_log.log_decl(&Arc::new(DeclX::Const(str_ident(QUERY), Arc::new(TypX::Bool))));
    context.smt_log.log_assert(&mk_implies(&str_var(QUERY), &not_expr));
    let result = smt_check_assertion(context, infos, air_model, false);

    result
}
