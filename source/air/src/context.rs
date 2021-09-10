use crate::ast::{Command, CommandX, Decl, Ident, Query, SpanOption, TypeError};
use crate::emitter::Emitter;
use crate::model::Model;
use crate::scope_map::ScopeMap;
use crate::smt_manager::SmtManager;
use crate::typecheck::Typing;
use std::collections::HashSet;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub(crate) struct AssertionInfo {
    pub(crate) span: SpanOption,
    pub(crate) label: Ident,
    pub(crate) decl: Decl,
}

#[derive(Debug)]
pub enum ValidityResult {
    Valid,
    Invalid(Model, SpanOption, SpanOption),
    TypeError(TypeError),
}

pub struct Context {
    pub(crate) smt_manager: SmtManager,
    pub(crate) assert_infos: ScopeMap<Ident, Arc<AssertionInfo>>,
    pub(crate) assert_infos_count: u64,
    pub(crate) typing: Typing,
    pub(crate) debug: bool,
    pub(crate) rlimit: u32,
    pub(crate) air_initial_log: Emitter,
    pub(crate) air_middle_log: Emitter,
    pub(crate) air_final_log: Emitter,
    pub(crate) smt_log: Emitter,
}

impl Context {
    pub fn new(smt_manager: SmtManager) -> Context {
        let mut context = Context {
            smt_manager,
            assert_infos: ScopeMap::new(),
            assert_infos_count: 0,
            typing: Typing { decls: crate::scope_map::ScopeMap::new(), snapshots: HashSet::new() },
            debug: false,
            rlimit: 0,
            air_initial_log: Emitter::new(false, None),
            air_middle_log: Emitter::new(false, None),
            air_final_log: Emitter::new(false, None),
            smt_log: Emitter::new(true, None),
        };
        context.assert_infos.push_scope(false);
        context.typing.decls.push_scope(false);
        context
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

    pub fn set_rlimit(&mut self, rlimit: u32) {
        self.rlimit = rlimit;
        self.air_initial_log.log_set_option("rlimit", &rlimit.to_string());
        self.air_middle_log.log_set_option("rlimit", &rlimit.to_string());
        self.air_final_log.log_set_option("rlimit", &rlimit.to_string());
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

    pub fn set_z3_param(&mut self, option: &str, value: &str) {
        if value == "true" {
            self.set_z3_param_bool(option, true, true);
        } else if value == "false" {
            self.set_z3_param_bool(option, false, true);
        } else if value.contains(".") {
            let v = value.parse::<f64>().expect(&format!("could not parse option value {}", value));
            self.set_z3_param_f64(option, v, true);
        } else {
            let v = value.parse::<u32>().expect(&format!("could not parse option value {}", value));
            self.set_z3_param_u32(option, v, true);
        }
    }

    pub(crate) fn push_name_scope(&mut self) {
        self.assert_infos.push_scope(false);
        self.typing.decls.push_scope(false);
    }

    pub(crate) fn pop_name_scope(&mut self) {
        self.assert_infos.pop_scope();
        self.typing.decls.pop_scope();
    }

    pub fn push(&mut self) {
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
        self.air_initial_log.log_decl(decl);
        self.air_middle_log.log_decl(decl);
        self.air_final_log.log_decl(decl);
        crate::typecheck::check_decl(&mut self.typing, decl)?;
        crate::typecheck::add_decl(self, decl, true)?;
        crate::smt_verify::smt_add_decl(self, decl);
        Ok(())
    }

    pub fn check_valid(&mut self, query: &Query) -> ValidityResult {
        self.air_initial_log.log_query(query);
        if let Err(err) = crate::typecheck::check_query(self, query) {
            return ValidityResult::TypeError(err);
        }
        let (query, snapshots, local_vars) = crate::var_to_const::lower_query(query);
        self.air_middle_log.log_query(&query);
        let query = crate::block_to_assert::lower_query(&query);
        self.air_final_log.log_query(&query);

        let validity = crate::smt_verify::smt_check_query(self, &query, snapshots, local_vars);

        validity
    }

    pub fn command(&mut self, command: &Command) -> ValidityResult {
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
            CommandX::CheckValid(query) => self.check_valid(&query),
        }
    }
}
