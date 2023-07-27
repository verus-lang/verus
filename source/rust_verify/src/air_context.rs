use air::{
    ast::{Command, CommandX},
    context::QueryContext,
};
use rand::RngCore;

pub struct AirContext {
    air_context: air::context::Context,
    stored_commands: Option<Vec<Command>>,
}

impl AirContext {
    pub(crate) fn new(air_context: air::context::Context, shufflable: bool) -> Self {
        Self { air_context, stored_commands: shufflable.then(|| Vec::with_capacity(128)) }
    }

    pub(crate) fn comment(&mut self, comment: &str) {
        self.air_context.comment(comment);
    }

    pub(crate) fn blank_line(&mut self) {
        self.air_context.blank_line();
    }

    pub(crate) fn command(
        &mut self,
        diagnostics: &impl air::messages::Diagnostics,
        command: &Command,
        query_context: air::context::QueryContext<'_, '_>,
    ) -> air::context::ValidityResult {
        if let Some(stored_commands) = &mut self.stored_commands {
            stored_commands.push(command.clone());
        }
        self.air_context.command(diagnostics, command, query_context)
    }

    pub(crate) fn take_commands(&mut self) -> Option<Vec<Command>> {
        self.stored_commands.take()
    }

    pub(crate) fn commands_expect_valid(
        &mut self,
        diagnostics: &impl air::messages::Diagnostics,
        commands: Vec<Command>,
    ) {
        assert!(self.stored_commands.is_none());
        for command in commands.into_iter() {
            assert!(matches!(
                self.air_context.command(
                    diagnostics,
                    &command,
                    QueryContext { report_long_running: None }
                ),
                air::context::ValidityResult::Valid
            ));
        }
    }

    pub(crate) fn set_expected_solver_version(&mut self, version: String) {
        self.air_context.set_expected_solver_version(version);
    }

    pub(crate) fn borrow_mut_context(&mut self) -> &mut air::context::Context {
        &mut self.air_context
    }

    pub fn check_valid_again(
        &mut self,
        diagnostics: &impl air::messages::Diagnostics,
        only_check_earlier: bool,
        query_context: air::context::QueryContext<'_, '_>,
    ) -> air::context::ValidityResult {
        self.air_context.check_valid_again(diagnostics, only_check_earlier, query_context)
    }

    pub(crate) fn finish_query(&mut self) {
        self.air_context.finish_query();
    }

    pub(crate) fn disable_incremental_solving(&mut self) {
        self.air_context.disable_incremental_solving();
    }

    pub(crate) fn get_time(&self) -> (std::time::Duration, std::time::Duration) {
        self.air_context.get_time()
    }
}

pub(crate) fn shuffle_commands(commands: &mut Vec<Command>, rng: &mut impl RngCore) {
    use rand::seq::SliceRandom;

    let mut ranges: Vec<(bool, Vec<Command>)> = Vec::new();
    let range_capacity = commands.len() / 10;
    let mut cur_range = Vec::with_capacity(range_capacity);
    let mut last_was_axiom = false;
    for command in commands.drain(..) {
        let is_axiom = matches!(&*command, CommandX::Global(decl) if matches!(&**decl, air::ast::DeclX::Axiom(_)));
        if is_axiom != last_was_axiom {
            ranges.push((
                last_was_axiom,
                std::mem::replace(&mut cur_range, Vec::with_capacity(range_capacity)),
            ));
        }
        last_was_axiom = is_axiom;
        cur_range.push(command);
    }
    ranges.push((last_was_axiom, cur_range));

    assert!(commands.is_empty());
    for (shuffle, mut range) in ranges.into_iter() {
        if shuffle {
            range.shuffle(rng);
        }
        commands.extend(range);
    }
}
