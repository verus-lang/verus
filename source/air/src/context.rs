use crate::ast::{Command, CommandX, Declaration, Ident, Query, SpanOption, ValidityResult};
use std::collections::HashMap;
use z3::ast::{Bool, Dynamic};

#[derive(Debug)]
pub(crate) struct AssertionInfo<'ctx> {
    pub(crate) span: SpanOption,
    pub(crate) label: Bool<'ctx>,
}

pub struct Context<'ctx> {
    pub(crate) context: &'ctx z3::Context,
    pub(crate) solver: &'ctx z3::Solver<'ctx>,
    pub(crate) vars: HashMap<Ident, Dynamic<'ctx>>,
    pub(crate) assertion_infos: Vec<AssertionInfo<'ctx>>,
    pub(crate) rlimit: u32,
}

impl<'ctx> Context<'ctx> {
    pub fn new(context: &'ctx z3::Context, solver: &'ctx z3::Solver<'ctx>) -> Context<'ctx> {
        Context { context, solver, vars: HashMap::new(), assertion_infos: Vec::new(), rlimit: 0 }
    }

    pub fn rlimit(&mut self, rlimit: u32) {
        self.rlimit = rlimit;
    }

    pub fn push(&mut self) {
        self.solver.push();
    }

    pub fn pop(&mut self) {
        self.solver.pop(1);
    }

    pub fn global(&mut self, decl: &Declaration) {
        crate::smt_verify::smt_add_decl(self, &decl, true);
    }

    pub fn check_valid(&mut self, query: &Query) -> ValidityResult {
        crate::smt_verify::smt_check_query(self, &query)
    }

    pub fn command(&mut self, command: &Command) -> ValidityResult {
        match &**command {
            CommandX::Push => {
                self.push();
                ValidityResult::Valid
            }
            CommandX::Pop => {
                self.push();
                ValidityResult::Valid
            }
            CommandX::Global(decl) => {
                self.global(&decl);
                ValidityResult::Valid
            }
            CommandX::CheckValid(query) => self.check_valid(&query),
        }
    }
}
