use crate::ast::{
    Axiom, BinaryOp, BindX, Decl, DeclX, Expr, ExprX, Ident, MultiOp, Quant, Query, StmtX, TypX,
    UnaryOp,
};
use crate::ast_util::{ident_var, mk_and, mk_not};
use crate::context::{AssertionInfo, AxiomInfo, Context, ContextState, SmtSolver, ValidityResult};
use crate::def::{GLOBAL_PREFIX_LABEL, PREFIX_LABEL};
use crate::messages::{ArcDynMessage, Diagnostics};
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
            BindX::Quant(Quant::Forall, _, _, _) => Arc::new(ExprX::Bind(
                bind.clone(),
                label_asserts(context, infos, axiom_infos, body),
            )),
            _ => expr.clone(),
        },
        ExprX::LabeledAssertion(assert_id, error, filter, expr) => {
            let label = Arc::new(PREFIX_LABEL.to_string() + &infos.len().to_string());
            let decl = Arc::new(DeclX::Const(label.clone(), Arc::new(TypX::Bool)));
            let assertion_info = AssertionInfo {
                assert_id: assert_id.clone(),
                error: error.clone(),
                label: label.clone(),
                filter: filter.clone(),
                decl,
                disabled: false,
            };
            infos.push(assertion_info);
            let lhs = Arc::new(ExprX::Var(label));
            Arc::new(ExprX::Binary(
                BinaryOp::Implies,
                lhs,
                label_asserts(context, infos, axiom_infos, expr),
            ))
        }
        ExprX::LabeledAxiom(labels, filter, expr) => {
            let count = context.axiom_infos_count;
            context.axiom_infos_count += 1;
            let label = Arc::new(GLOBAL_PREFIX_LABEL.to_string() + &count.to_string());
            let decl = Arc::new(DeclX::Const(label.clone(), Arc::new(TypX::Bool)));
            let axiom_info = AxiomInfo {
                labels: labels.clone(),
                label: label.clone(),
                filter: filter.clone(),
                decl,
            };
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
        DeclX::Axiom(Axiom { named, expr }) => {
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
            context.smt_log.log_assert(named, &labeled_expr);
        }
    }
}

impl SmtSolver {
    pub fn reason_unknown_canceled_str(&self) -> &str {
        match self {
            SmtSolver::Z3 => "(:reason-unknown \"canceled\")",
            SmtSolver::Cvc5 => "(:reason-unknown resourceout)",
        }
    }

    pub fn reason_unknown_incomplete_str(&self) -> &str {
        match self {
            SmtSolver::Z3 => "(:reason-unknown \"(incomplete",
            SmtSolver::Cvc5 => "(:reason-unknown incomplete)",
        }
    }
}

pub type ReportLongRunning<'a> =
    (std::time::Duration, Box<dyn FnMut(std::time::Duration, bool) -> () + 'a>);

const GET_VERSION_RESPONSE_PREFIX: &str = "(:version";

pub(crate) fn smt_check_assertion<'ctx>(
    context: &mut Context,
    diagnostics: &impl Diagnostics,
    mut infos: Vec<AssertionInfo>,
    air_model: Model,
    only_check_earlier: bool,
    report_long_running: Option<&mut ReportLongRunning>,
) -> ValidityResult {
    let disabled_expr = if only_check_earlier {
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
            return ValidityResult::Valid(
                #[cfg(feature = "axiom-usage-info")]
                crate::context::UsageInfo::None,
            );
        }
        Some(mk_and(&disabled))
    } else {
        None
    };

    context.smt_log.log_get_info("version");
    let smt_init_start_time = std::time::Instant::now();
    let smt_data = context.smt_log.take_pipe_data();
    let early_smt_output = context.get_smt_process().send_commands(smt_data);
    context.time_smt_init += smt_init_start_time.elapsed();
    for line in early_smt_output {
        if line.starts_with(GET_VERSION_RESPONSE_PREFIX) {
            if let Some(expected_version) = &context.expected_solver_version {
                let value: &str = &line[GET_VERSION_RESPONSE_PREFIX.len()..line.len() - 1];
                let version = value.trim_matches(&[' ', '"'][..]);
                if version != expected_version.as_str() {
                    diagnostics.report(
                        &context
                            .message_interface
                            .unexpected_z3_version(&expected_version, version),
                    );
                    panic!(
                        "The verifier expects z3 version \"{}\", found version \"{}\"",
                        expected_version, version
                    );
                }
            }
        } else if context.ignore_unexpected_smt {
            diagnostics.report(&context.message_interface.bare(
                crate::messages::MessageLevel::Warning,
                format!("warning: unexpected SMT output: {}", line).as_str(),
            ));
        } else {
            return ValidityResult::UnexpectedOutput(line);
        }
    }

    if let Some(disabled_expr) = disabled_expr {
        context.smt_log.log_assert(&None, &disabled_expr);
    }

    if matches!(context.solver, SmtSolver::Z3) {
        context.smt_log.log_set_option("rlimit", &context.rlimit.to_string());
        context.set_z3_param_u32("rlimit", context.rlimit, false);
    }

    context.smt_log.log_word("check-sat");

    // Run SMT solver
    let smt_run_start_time = std::time::Instant::now();
    let smt_data = context.smt_log.take_pipe_data();
    let commands_handle = context.get_smt_process().send_commands_async(smt_data);
    let smt_output = if let Some((report_threshold, report_fn)) = report_long_running {
        match commands_handle.wait_timeout(*report_threshold) {
            Ok(smt_output) => smt_output,
            Err(handle) => {
                report_fn(smt_run_start_time.elapsed(), false);
                let smt_output = handle.wait();
                report_fn(smt_run_start_time.elapsed(), true);
                smt_output
            }
        }
    } else {
        commands_handle.wait()
    };
    context.time_smt_run += smt_run_start_time.elapsed();

    #[derive(PartialEq, Eq)]
    enum SmtOutput {
        Unsat,
        Sat,
        Unknown,
    }

    // Process SMT results
    let mut unsat = None;
    for line in smt_output {
        if line == "unsat" {
            assert!(unsat == None);
            unsat = Some(SmtOutput::Unsat);
        } else if line == "sat" {
            assert!(unsat == None);
            unsat = Some(SmtOutput::Sat);
        } else if line == "unknown" || line == "cvc5 interrupted by timeout." {
            assert!(unsat == None);
            unsat = Some(SmtOutput::Unknown);
        } else if context.ignore_unexpected_smt {
            diagnostics.report(&context.message_interface.bare(
                crate::messages::MessageLevel::Warning,
                format!("warning: unexpected SMT output: {}", line).as_str(),
            ));
        } else {
            return ValidityResult::UnexpectedOutput(line);
        }
    }

    if matches!(context.solver, SmtSolver::Z3) {
        context.smt_log.log_set_option("rlimit", "0");
        context.set_z3_param_u32("rlimit", 0, false);
    }

    let unsat = unsat.expect("expected sat/unsat/unknown from SMT solver");

    enum ResultDetermination<T> {
        Determined(ValidityResult),
        Undetermined(T),
    }

    let unsat_result = match unsat {
        SmtOutput::Unsat => ResultDetermination::Undetermined(true),
        SmtOutput::Sat => ResultDetermination::Undetermined(false),
        SmtOutput::Unknown => {
            context.smt_log.log_get_info("reason-unknown");
            let smt_data = context.smt_log.take_pipe_data();
            let smt_output = context.get_smt_process().send_commands(smt_data);

            #[derive(PartialEq, Eq)]
            enum SmtReasonUnknown {
                Canceled,
                Incomplete,
                Unknown,
            }

            let mut reason = None;
            for line in smt_output {
                if line == context.solver.reason_unknown_canceled_str() {
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Canceled);
                } else if line == "(:reason-unknown \"unknown\")" {
                    // it appears this sometimes happens when rlimit is exceeded
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Unknown);
                } else if line.starts_with(context.solver.reason_unknown_incomplete_str()) {
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Incomplete);
                } else if line
                    == "(:reason-unknown \"smt tactic failed to show goal to be sat/unsat (incomplete quantifiers)\")"
                {
                    // longer message shows up when there's no push/pop around the query
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Incomplete);
                } else if context.ignore_unexpected_smt {
                    diagnostics.report(&context.message_interface.bare(
                        crate::messages::MessageLevel::Warning,
                        format!("warning: unexpected SMT output: {}", line).as_str(),
                    ));
                } else {
                    return ValidityResult::UnexpectedOutput(line);
                }
            }

            match reason.expect("expected :reason-unknown") {
                SmtReasonUnknown::Canceled | SmtReasonUnknown::Unknown => {
                    context.state = ContextState::Canceled;
                    ResultDetermination::Determined(ValidityResult::Canceled)
                }
                SmtReasonUnknown::Incomplete => ResultDetermination::Undetermined(false),
            }
        }
    };

    match unsat_result {
        ResultDetermination::Determined(r) => r,
        ResultDetermination::Undetermined(true) => {
            context.state = ContextState::FoundResult;

            #[cfg(feature = "axiom-usage-info")]
            let usage_info = if context.usage_info_enabled {
                context.smt_log.log_word("get-unsat-core");

                let smt_data = context.smt_log.take_pipe_data();
                let smt_output = context.get_smt_process().send_commands(smt_data);

                let mut smt_output = smt_output.into_iter();
                let unsat_core_str =
                    smt_output.next().expect("expected one line in the unsat core output");
                assert!(smt_output.next().is_none());

                let fun_names: Vec<Ident> = unsat_core_str
                    .strip_prefix('(')
                    .expect("invalid unsat core")
                    .strip_suffix(')')
                    .expect("invalid unsat core")
                    .split_terminator(' ')
                    .map(|x| Arc::new(x.to_owned()))
                    .collect();
                crate::context::UsageInfo::UsedAxioms(fun_names)
            } else {
                crate::context::UsageInfo::None
            };

            ValidityResult::Valid(
                #[cfg(feature = "axiom-usage-info")]
                usage_info,
            )
        }
        ResultDetermination::Undetermined(false) => smt_get_model(context, infos, air_model),
    }
}

pub(crate) fn smt_update_statistics(context: &mut Context) -> Result<(), ValidityResult> {
    assert!(matches!(context.solver, SmtSolver::Z3)); // the CVC5 output format for statistics is different

    context.smt_log.log_get_info("all-statistics");
    let smt_data = context.smt_log.take_pipe_data();
    let smt_output = context.get_smt_process().send_commands(smt_data);
    let statistics = crate::parser::parse_sexpression(&smt_output);
    let stats_map = statistics
        .as_list()
        .unwrap()
        .chunks(2)
        .map(|chunk| {
            let [key, value] = chunk else {
                return Err(ValidityResult::UnexpectedOutput(format!(
                    "expected key-value pair in statistics"
                )));
            };
            let Some((key, value)) = key
                .as_atom()
                .map(|key| &key.as_str()[1..])
                .and_then(|key| value.as_atom().map(|value| (key, value.as_str())))
            else {
                return Err(ValidityResult::UnexpectedOutput(format!(
                    "expected key-value pair in statistics"
                )));
            };
            Ok((key, value))
        })
        .collect::<Result<HashMap<&str, &str>, ValidityResult>>()?;
    let Some(rlimit_count) = stats_map["rlimit-count"].parse().ok() else {
        return Err(ValidityResult::UnexpectedOutput(format!(
            "expected rlimit-count in smt statistics"
        )));
    };
    context.rlimit_count = Some(rlimit_count);

    Ok(())
}

fn smt_get_model(
    context: &mut Context,
    mut infos: Vec<AssertionInfo>,
    air_model: Model,
) -> ValidityResult {
    let mut discovered_error: Option<AssertionInfo> = None;
    let mut discovered_assert_id: Option<Option<Arc<Vec<u64>>>> = None;
    let mut discovered_additional_info: Vec<ArcDynMessage> = Vec::new();

    context.smt_log.log_word("get-model");

    let smt_data = context.smt_log.take_pipe_data();
    let smt_output = context.get_smt_process().send_commands(smt_data);

    if smt_output.iter().any(|line| line.contains("model is not available")) {
        // when we don't use incremental solving, sometime the model is not available when the z3 result is unknown
        context.state = ContextState::FoundInvalid(infos, None);
        return ValidityResult::Invalid(None, None, None);
    };

    let model =
        crate::parser::Parser::new(context.message_interface.clone()).lines_to_model(&smt_output);
    let mut model_defs: HashMap<Ident, ModelDef> = HashMap::new();
    for def in model.iter() {
        model_defs.insert(def.name.clone(), def.clone());
    }
    for info in infos.iter_mut() {
        if let Some(def) = model_defs.get(&info.label) {
            if *def.body == "true" {
                discovered_error = Some(info.clone());
                discovered_assert_id = Some(info.assert_id.clone());

                // Disable this label in subsequent check-sat calls to get additional errors
                info.disabled = true;
                let disable_label = mk_not(&ident_var(&info.label));
                context.smt_log.log_assert(&None, &disable_label);

                break;
            }
        }
    }
    let discovered_error = discovered_error.expect("discovered_error");
    let mut axiom_infos: Vec<Arc<AxiomInfo>> =
        context.axiom_infos.map().values().cloned().collect();
    axiom_infos.sort_by_key(|info| info.label.clone());
    // stabilize order
    for info in axiom_infos {
        if let Some(def) = model_defs.get(&info.label) {
            if *def.body == "true"
                && (info.filter.is_none() || info.filter == discovered_error.filter)
            {
                discovered_additional_info.append(&mut info.labels.clone());
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

    let error = discovered_error.error;
    let e = context.message_interface.append_labels(&error, &discovered_additional_info);
    context.state = ContextState::FoundInvalid(infos, Some(air_model.clone()));
    ValidityResult::Invalid(Some(air_model), Some(e), discovered_assert_id.unwrap())
}

pub(crate) fn smt_check_query<'ctx>(
    context: &mut Context,
    diagnostics: &impl Diagnostics,
    query: &Query,
    air_model: Model,
    report_long_running: Option<&mut ReportLongRunning>,
) -> ValidityResult {
    if !context.disable_incremental_solving {
        context.smt_log.log_push();
        context.push_name_scope();
    }

    // add query-local declarations
    for decl in query.local.iter() {
        if let Err(err) = crate::typecheck::add_decl(context, decl, false) {
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, decl);
    }

    // after lowering, there should be just one assertion
    let assertion = match &*query.assertion {
        StmtX::Assert(_, _, _, expr) => expr,
        _ => panic!("internal error: query not lowered"),
    };
    let assertion = elim_zero_args_expr(assertion);

    // add labels to assertions for error reporting
    let mut infos: Vec<AssertionInfo> = Vec::new();
    let mut axiom_infos: Vec<AxiomInfo> = Vec::new();
    let labeled_assertion = label_asserts(context, &mut infos, &mut axiom_infos, &assertion);
    for info in &infos {
        context.smt_log.comment(&context.message_interface.get_note(&info.error));
        if let Err(err) = crate::typecheck::add_decl(context, &info.decl, false) {
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, &info.decl);
    }

    // check assertion
    let not_expr = Arc::new(ExprX::Unary(UnaryOp::Not, labeled_assertion));
    context.smt_log.log_assert(&None, &not_expr);
    let result =
        smt_check_assertion(context, diagnostics, infos, air_model, false, report_long_running);

    result
}
