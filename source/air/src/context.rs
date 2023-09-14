use crate::ast::{Command, CommandX, Decl, Ident, Query, Typ, TypeError, Typs};
use crate::closure::ClosureTerm;
use crate::emitter::Emitter;
use crate::messages::{Diagnostics, Message, MessageLabels};
use crate::model::Model;
use crate::node;
use crate::printer::{macro_push_node, str_to_node};
use crate::profiler;
use crate::scope_map::ScopeMap;
use crate::smt_process::SmtProcess;
use crate::smt_verify::ReportLongRunning;
use crate::typecheck::Typing;
use sise::Node;
use std::collections::HashSet;
use std::sync::Arc;
use std::time::Duration;

#[derive(Clone, Debug)]
pub(crate) struct AssertionInfo {
    pub(crate) error: Message,
    pub(crate) label: Ident,
    pub(crate) decl: Decl,
    pub(crate) disabled: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct AxiomInfo {
    pub(crate) labels: MessageLabels,
    pub(crate) label: Ident,
    pub(crate) decl: Decl,
}

#[derive(Debug)]
pub enum ValidityResult {
    Valid,
    Invalid(Option<Model>, Message),
    Canceled,
    TypeError(TypeError),
    UnexpectedOutput(String),
}

#[derive(Clone, Debug)]
pub(crate) enum ContextState {
    NotStarted,
    ReadyForQuery,
    FoundResult,
    FoundInvalid(Vec<AssertionInfo>, Model),
    Canceled,
    NoMoreQueriesAllowed,
}

pub struct QueryContext<'a, 'b: 'a> {
    pub report_long_running: Option<&'a mut ReportLongRunning<'b>>,
}

impl<'a, 'b: 'a> Default for QueryContext<'a, 'b> {
    fn default() -> Self {
        QueryContext { report_long_running: None }
    }
}

pub struct Context {
    smt_process: Option<SmtProcess>,
    pub(crate) axiom_infos: ScopeMap<Ident, Arc<AxiomInfo>>,
    pub(crate) axiom_infos_count: u64,
    pub(crate) lambda_map: ScopeMap<ClosureTerm, Ident>,
    pub(crate) lambda_count: u64,
    pub(crate) choose_map: ScopeMap<ClosureTerm, Ident>,
    pub(crate) choose_count: u64,
    pub(crate) apply_map: ScopeMap<(Typs, Typ), Ident>,
    pub(crate) apply_count: u64,
    pub(crate) typing: Typing,
    pub(crate) debug: bool,
    pub(crate) profile: bool,
    pub(crate) profile_all: bool,
    pub(crate) ignore_unexpected_smt: bool,
    pub(crate) rlimit: u32,
    pub(crate) air_initial_log: Emitter,
    pub(crate) air_middle_log: Emitter,
    pub(crate) air_final_log: Emitter,
    pub(crate) smt_log: Emitter,
    pub singular_log: Option<std::fs::File>,
    pub(crate) time_smt_init: Duration,
    pub(crate) time_smt_run: Duration,
    pub(crate) state: ContextState,
    pub(crate) expected_solver_version: Option<String>,
    pub(crate) query_logfile_name: Option<String>,
    pub(crate) disable_incremental_solving: bool,
}

impl Context {
    pub fn new() -> Context {
        let mut context = Context {
            smt_process: None,
            axiom_infos: ScopeMap::new(),
            axiom_infos_count: 0,
            lambda_map: ScopeMap::new(),
            lambda_count: 0,
            choose_map: ScopeMap::new(),
            choose_count: 0,
            apply_map: ScopeMap::new(),
            apply_count: 0,
            typing: Typing { decls: crate::scope_map::ScopeMap::new(), snapshots: HashSet::new() },
            debug: false,
            profile: false,
            profile_all: false,
            ignore_unexpected_smt: false,
            rlimit: 0,
            air_initial_log: Emitter::new(false, false, None),
            air_middle_log: Emitter::new(false, false, None),
            air_final_log: Emitter::new(false, false, None),
            smt_log: Emitter::new(true, true, None),
            singular_log: None,
            time_smt_init: Duration::new(0, 0),
            time_smt_run: Duration::new(0, 0),
            state: ContextState::NotStarted,
            expected_solver_version: None,
            query_logfile_name: None,
            disable_incremental_solving: false,
        };
        context.axiom_infos.push_scope(false);
        context.lambda_map.push_scope(false);
        context.choose_map.push_scope(false);
        context.apply_map.push_scope(false);
        context.typing.decls.push_scope(false);
        context
    }

    pub fn get_smt_process(&mut self) -> &mut SmtProcess {
        // Only start the smt process if there are queries to run
        if self.smt_process.is_none() {
            self.smt_process = Some(SmtProcess::launch());
        }
        self.smt_process.as_mut().unwrap()
    }

    pub fn set_air_initial_log(&mut self, writer: Box<dyn std::io::Write>) {
        self.air_initial_log.set_log(Some(writer));
    }

    pub fn set_air_middle_log(&mut self, writer: Box<dyn std::io::Write>) {
        self.air_middle_log.set_log(Some(writer));
    }

    pub fn set_air_final_log(&mut self, writer: Box<dyn std::io::Write>) {
        self.air_final_log.set_log(Some(writer));
    }

    pub fn set_smt_log(&mut self, writer: Box<dyn std::io::Write>) {
        self.smt_log.set_log(Some(writer));
    }

    pub fn set_debug(&mut self, debug: bool) {
        self.debug = debug;
    }

    pub fn get_debug(&self) -> bool {
        self.debug
    }

    pub fn set_profile(&mut self, profile: bool) {
        self.profile = profile;
    }

    pub fn get_profile(&self) -> bool {
        self.profile
    }

    pub fn set_profile_all(&mut self, profile_all: bool) {
        self.profile_all = profile_all;
    }

    pub fn get_profile_all(&self) -> bool {
        self.profile_all
    }

    pub fn set_ignore_unexpected_smt(&mut self, ignore_unexpected_smt: bool) {
        self.ignore_unexpected_smt = ignore_unexpected_smt;
    }

    pub fn get_time(&self) -> (Duration, Duration) {
        (self.time_smt_init, self.time_smt_run)
    }

    pub fn set_expected_solver_version(&mut self, version: String) {
        self.expected_solver_version = Some(version);
    }

    pub fn set_query_logfile_name(&mut self, func_name: String) {
        self.query_logfile_name = Some(func_name);
    }

    pub fn set_rlimit(&mut self, rlimit: u32) {
        self.rlimit = rlimit;
        self.air_initial_log.log_set_option("rlimit", &rlimit.to_string());
        self.air_middle_log.log_set_option("rlimit", &rlimit.to_string());
        self.air_final_log.log_set_option("rlimit", &rlimit.to_string());
    }

    pub fn disable_incremental_solving(&mut self) {
        self.disable_incremental_solving = true;
        self.air_initial_log.log_set_option("disable_incremental_solving", "true");
        self.air_middle_log.log_set_option("disable_incremental_solving", "true");
        self.air_final_log.log_set_option("disable_incremental_solving", "true");
    }

    // emit blank line into log files
    pub fn blank_line(&mut self) {
        self.air_initial_log.blank_line();
        self.air_middle_log.blank_line();
        self.air_final_log.blank_line();
        self.smt_log.blank_line();
    }

    // Single-line comment, emitted with ";;" into log files
    pub fn comment(&mut self, s: &str) {
        self.air_initial_log.comment(s);
        self.air_middle_log.comment(s);
        self.air_final_log.comment(s);
        self.smt_log.comment(s);
    }

    fn log_set_z3_param(&mut self, option: &str, value: &str) {
        self.air_initial_log.log_set_option(option, value);
        self.air_middle_log.log_set_option(option, value);
        self.air_final_log.log_set_option(option, value);
        self.smt_log.log_set_option(option, value);
    }

    pub(crate) fn set_z3_param_bool(&mut self, option: &str, value: bool, write_to_logs: bool) {
        if option == "air_recommended_options" && value {
            self.set_z3_param_bool("auto_config", false, true);
            self.set_z3_param_bool("smt.mbqi", false, true);
            self.set_z3_param_u32("smt.case_split", 3, true);
            self.set_z3_param_f64("smt.qi.eager_threshold", 100.0, true);
            self.set_z3_param_bool("smt.delay_units", true, true);
            self.set_z3_param_u32("smt.arith.solver", 2, true);
            self.set_z3_param_bool("smt.arith.nl", false, true);
        } else if option == "disable_incremental_solving" && value {
            self.disable_incremental_solving = true;
            if write_to_logs {
                self.disable_incremental_solving();
            }
        } else {
            if write_to_logs {
                self.log_set_z3_param(option, &value.to_string());
            }
        }
    }

    pub(crate) fn set_z3_param_u32(&mut self, option: &str, value: u32, write_to_logs: bool) {
        if option == "rlimit" && write_to_logs {
            self.set_rlimit(value);
        } else {
            if write_to_logs {
                self.log_set_z3_param(option, &value.to_string());
            }
        }
    }

    pub(crate) fn set_z3_param_f64(&mut self, option: &str, value: f64, write_to_logs: bool) {
        if write_to_logs {
            let mut s = value.to_string();
            if !s.contains(".") {
                s += ".0";
            }
            self.log_set_z3_param(option, &s);
        }
    }

    pub(crate) fn set_z3_param_str(&mut self, option: &str, value: &str, write_to_logs: bool) {
        if write_to_logs {
            self.log_set_z3_param(option, &value.to_string());
        }
    }

    pub fn set_z3_param(&mut self, option: &str, value: &str) {
        if value == "true" {
            self.set_z3_param_bool(option, true, true);
        } else if value == "false" {
            self.set_z3_param_bool(option, false, true);
        } else if let Ok(v) = value.parse::<u32>() {
            self.set_z3_param_u32(option, v, true);
        } else if let Ok(v) = value.parse::<f64>() {
            self.set_z3_param_f64(option, v, true);
        } else if value.is_ascii() {
            self.set_z3_param_str(option, value, true);
        } else {
            panic!("unexpected z3 param {}", value);
        }
    }

    pub(crate) fn push_name_scope(&mut self) {
        self.axiom_infos.push_scope(false);
        self.lambda_map.push_scope(false);
        self.choose_map.push_scope(false);
        self.apply_map.push_scope(false);
        self.typing.decls.push_scope(false);
    }

    pub(crate) fn pop_name_scope(&mut self) {
        self.axiom_infos.pop_scope();
        self.lambda_map.pop_scope();
        self.choose_map.pop_scope();
        self.apply_map.pop_scope();
        self.typing.decls.pop_scope();
    }

    fn ensure_started(&mut self) {
        match self.state {
            ContextState::NotStarted => {
                if self.profile || self.profile_all {
                    self.set_z3_param("trace", "true");
                    // Very expensive.  May be needed to support more detailed log analysis.
                    //self.set_z3_param("proof", "true");
                    let file_name = match &self.query_logfile_name {
                        Some(name) => name.to_string(),
                        None => profiler::PROVER_LOG_FILE.to_string(),
                    };
                    self.log_set_z3_param("trace_file_name", &file_name);
                }
                self.blank_line();
                self.comment("AIR prelude");
                self.smt_log.log_node(&node!((declare-sort {str_to_node(crate::def::FUNCTION)} 0)));
                self.blank_line();
                self.state = ContextState::ReadyForQuery;
            }
            ContextState::ReadyForQuery => {}
            ContextState::NoMoreQueriesAllowed => {
                panic!("no more queries allowed after disabling incremental solving");
            }
            _ => {
                panic!("expected call to finish_query before next command");
            }
        }
    }

    pub fn push(&mut self) {
        self.ensure_started();
        self.air_initial_log.log_push();
        self.air_middle_log.log_push();
        self.air_final_log.log_push();
        self.smt_log.log_push();
        self.push_name_scope();
    }

    pub fn pop(&mut self) {
        self.air_initial_log.log_pop();
        self.air_middle_log.log_pop();
        self.air_final_log.log_pop();
        self.smt_log.log_pop();
        self.pop_name_scope();
    }

    pub fn global(&mut self, decl: &Decl) -> Result<(), TypeError> {
        self.ensure_started();
        self.air_initial_log.log_decl(decl);
        self.air_middle_log.log_decl(decl);
        self.air_final_log.log_decl(decl);
        let (gen_decls, decl) = crate::typecheck::check_decl(self, decl)?;
        for gen_decl in gen_decls.iter() {
            crate::smt_verify::smt_add_decl(self, gen_decl);
        }
        crate::typecheck::add_decl(self, &decl, true)?;
        crate::smt_verify::smt_add_decl(self, &decl);
        Ok(())
    }

    pub fn check_valid(
        &mut self,
        diagnostics: &impl Diagnostics,
        query: &Query,
        query_context: QueryContext<'_, '_>,
    ) -> ValidityResult {
        self.ensure_started();
        self.air_initial_log.log_query(query);
        let query = match crate::typecheck::check_query(self, query) {
            Ok(query) => query,
            Err(err) => return ValidityResult::TypeError(err),
        };
        let (query, snapshots, local_vars) = crate::var_to_const::lower_query(&query);
        self.air_middle_log.log_query(&query);
        let query = crate::block_to_assert::lower_query(&query);
        self.air_final_log.log_query(&query);

        let model = Model::new(snapshots, local_vars);
        let validity = crate::smt_verify::smt_check_query(
            self,
            diagnostics,
            &query,
            model,
            query_context.report_long_running,
        );

        validity
    }

    /// After receiving ValidityResult::Invalid, try to find another error.
    /// only_check_earlier == true means to only look for errors preceding all the previous
    /// errors, with the goal of making sure that the earliest error gets reported.
    /// Once only_check_earlier is set, it remains set until finish_query is called.
    pub fn check_valid_again(
        &mut self,
        diagnostics: &impl Diagnostics,
        only_check_earlier: bool,
        query_context: QueryContext<'_, '_>,
    ) -> ValidityResult {
        if let ContextState::FoundInvalid(infos, air_model) = self.state.clone() {
            crate::smt_verify::smt_check_assertion(
                self,
                diagnostics,
                infos,
                air_model,
                only_check_earlier,
                query_context.report_long_running,
            )
        } else {
            panic!("check_valid_again expected query to be ValidityResult::Invalid");
        }
    }

    pub fn finish_query(&mut self) {
        if self.disable_incremental_solving {
            self.state = ContextState::NoMoreQueriesAllowed;
        } else {
            self.pop_name_scope();
            self.smt_log.log_pop();
            self.state = ContextState::ReadyForQuery;
        }
    }

    pub fn eval_expr(&mut self, expr: sise::Node) -> String {
        self.smt_log.log_eval(expr);
        let smt_data = self.smt_log.take_pipe_data();
        let smt_output = self.get_smt_process().send_commands(smt_data);
        if smt_output.len() != 1 {
            panic!("unexpected output from SMT eval {:?}", &smt_output);
        }
        smt_output[0].clone()
    }

    pub fn command(
        &mut self,
        diagnostics: &impl Diagnostics,
        command: &Command,
        query_context: QueryContext<'_, '_>,
    ) -> ValidityResult {
        match &**command {
            CommandX::Push => {
                self.push();
                ValidityResult::Valid
            }
            CommandX::Pop => {
                self.pop();
                ValidityResult::Valid
            }
            CommandX::SetOption(option, value) => {
                self.set_z3_param(option, value);
                ValidityResult::Valid
            }
            CommandX::Global(decl) => {
                if let Err(err) = self.global(&decl) {
                    ValidityResult::TypeError(err)
                } else {
                    ValidityResult::Valid
                }
            }
            CommandX::CheckValid(query) => self.check_valid(diagnostics, &query, query_context),
        }
    }
}
