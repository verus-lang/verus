use crate::config::{Args, ShowTriggers};
use crate::context::{ArchContextX, ContextX, ErasureInfo};
use crate::debugger::Debugger;
use crate::unsupported;
use crate::util::{error, from_raw_span, signalling};
use air::ast::{Command, CommandX, Commands};
use air::context::{QueryContext, ValidityResult};
use air::errors::{Error, ErrorLabel};
use air::profiler::Profiler;
use rustc_hir::OwnerNode;
use rustc_interface::interface::Compiler;

use num_format::{Locale, ToFormattedString};
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::SourceMap;
use rustc_span::{CharPos, FileName, MultiSpan, Span};
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Write;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use vir::ast::{Fun, Function, InferMode, Krate, Mode, VirErr, Visibility};
use vir::ast_util::{fun_as_rust_dbg, fun_name_crate_relative, is_visible_to};
use vir::def::{CommandsWithContext, CommandsWithContextX, SnapPos};
use vir::func_to_air::SstMap;
use vir::prelude::PreludeConfig;
use vir::recursion::Node;

const RLIMIT_PER_SECOND: u32 = 3000000;

pub struct VerifierCallbacks {
    pub verifier: Arc<Mutex<Verifier>>,
    pub vir_ready: signalling::Signaller<bool>,
    pub now_verify: signalling::Signalled<bool>,
}

pub struct Verifier {
    pub encountered_vir_error: bool,
    pub count_verified: u64,
    pub count_errors: u64,
    pub errors: Vec<Vec<ErrorSpan>>,
    pub args: Args,
    pub test_capture_output: Option<std::sync::Arc<std::sync::Mutex<Vec<u8>>>>,
    pub erasure_hints: Option<crate::erase::ErasureHints>,
    pub time_vir: Duration,
    pub time_vir_rust_to_vir: Duration,
    pub time_vir_verify: Duration,
    pub time_air: Duration,
    pub time_smt_init: Duration,
    pub time_smt_run: Duration,

    // If we've already created the log directory, this is the path to it:
    created_log_dir: Option<String>,
    vir_crate: Option<Krate>,
    air_no_span: Option<air::ast::Span>,
    inferred_modes: Option<HashMap<InferMode, Mode>>,

    // proof debugging purposes
    expand_flag: bool,
    pub expand_targets: Vec<air::errors::Error>,
    pub expand_errors: Vec<Vec<ErrorSpan>>,
}

#[derive(Debug)]
pub struct ErrorSpan {
    pub description: Option<String>,
    pub span_data: (String, (usize, CharPos), (usize, CharPos)),
    /// The source line containing the span that caused the error.
    /// This is mainly used for testing, so that we can easily check that we got an error on the
    /// line we expected.
    pub test_span_line: String,
}

impl ErrorSpan {
    fn new_from_air_span(source_map: &SourceMap, msg: &String, air_span: &air::ast::Span) -> Self {
        let span: Span = from_raw_span(&air_span.raw_span);
        let filename: String = match source_map.span_to_filename(span) {
            FileName::Real(rfn) => rfn
                .local_path()
                .expect("internal error: not a local path")
                .to_str()
                .expect("internal error: path is not a valid string")
                .to_string(),
            _ => unsupported!("non real filenames in verifier errors", air_span),
        };
        let (start, end) = source_map.is_valid_span(span).expect("internal error: invalid Span");
        let test_span_line = {
            let span = source_map.span_extend_to_prev_char(span, '\n', false);
            let span = source_map.span_extend_to_next_char(span, '\n', false);
            source_map.span_to_snippet(span).expect("internal error: cannot extract Span line")
        };
        Self {
            description: Some(msg.clone()),
            span_data: (filename, (start.line, start.col), (end.line, end.col)),
            test_span_line: test_span_line,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ErrorAs {
    Error,
    Warning,
    Note,
}

trait Diagnostics {
    fn diagnostic(&self) -> &rustc_errors::Handler;

    fn report_error(&self, error: &Error, error_as: ErrorAs);
}

/// N.B.: The compiler performs deduplication on diagnostic messages, so reporting an error twice,
/// or emitting the same note twice will be surpressed (even if separated in time by other
/// errors/notes)
impl Diagnostics for Compiler {
    fn diagnostic(&self) -> &rustc_errors::Handler {
        self.session().diagnostic()
    }

    fn report_error(&self, error: &Error, error_as: ErrorAs) {
        let mut v = Vec::new();
        for sp in &error.spans {
            let span: Span = from_raw_span(&sp.raw_span);
            v.push(span);
        }
        while let Some(i) = v.iter().position(|a| v.iter().any(|b| a != b && a.contains(*b))) {
            // Remove i in favor of the more specific spans contained by i
            v.remove(i);
        }

        let mut multispan = MultiSpan::from_spans(v);

        for ErrorLabel { msg, span: sp } in &error.labels {
            let span: Span = from_raw_span(&sp.raw_span);
            multispan.push_span_label(span, msg.clone());
        }

        match error_as {
            ErrorAs::Note => self.diagnostic().span_note_without_error(multispan, &error.msg),
            ErrorAs::Warning => self.diagnostic().span_warn(multispan, &error.msg),
            ErrorAs::Error => self.diagnostic().span_err(multispan, &error.msg),
        }
    }
}

fn report_chosen_triggers(compiler: &Compiler, chosen: &vir::context::ChosenTriggers) {
    let span: Span = from_raw_span(&chosen.span.raw_span);
    let msg = "automatically chose triggers for this expression:";
    compiler.diagnostic().span_note_without_error(span, msg);
    for (n, trigger) in chosen.triggers.iter().enumerate() {
        let spans = MultiSpan::from_spans(
            trigger.iter().map(|(s, _)| from_raw_span(&s.raw_span)).collect(),
        );
        let msg = format!("  trigger {} of {}:", n + 1, chosen.triggers.len());
        compiler.diagnostic().span_note_without_error(spans, &msg);
    }
}

fn io_vir_err(msg: String, err: std::io::Error) -> VirErr {
    error(format!("{msg}: {err}"))
}

fn module_name(module: &vir::ast::Path) -> String {
    module.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("::")
}

impl Verifier {
    pub fn new(args: Args) -> Verifier {
        Verifier {
            encountered_vir_error: false,
            count_verified: 0,
            count_errors: 0,
            errors: Vec::new(),
            args,
            test_capture_output: None,
            erasure_hints: None,
            time_vir: Duration::new(0, 0),
            time_vir_rust_to_vir: Duration::new(0, 0),
            time_vir_verify: Duration::new(0, 0),
            time_air: Duration::new(0, 0),
            time_smt_init: Duration::new(0, 0),
            time_smt_run: Duration::new(0, 0),

            created_log_dir: None,
            vir_crate: None,
            air_no_span: None,
            inferred_modes: None,

            expand_flag: false,
            expand_targets: vec![],
            expand_errors: vec![],
        }
    }

    fn create_log_file(
        &mut self,
        module: Option<&vir::ast::Path>,
        function: Option<&vir::ast::Path>,
        suffix: &str,
    ) -> Result<File, VirErr> {
        if self.created_log_dir.is_none() {
            let dir = if let Some(dir) = &self.args.log_dir {
                dir.clone()
            } else {
                crate::config::LOG_DIR.to_string()
            };
            match std::fs::create_dir_all(dir.clone()) {
                Ok(()) => {
                    self.created_log_dir = Some(dir);
                }
                Err(err) => {
                    return Err(io_vir_err(format!("could not create directory {dir}"), err));
                }
            }
        }
        let dir_path = self.created_log_dir.clone().unwrap();
        let prefix = match module {
            None => "crate".to_string(),
            Some(module) if module.segments.len() == 0 => "root".to_string(),
            Some(module) => {
                module.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("__")
            }
        };
        let middle = match function {
            None => "".to_string(),
            Some(fcn) => format!(
                "__{}",
                fcn.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("__")
            ),
        };
        let path = std::path::Path::new(&dir_path).join(format!("{prefix}{middle}{suffix}"));
        match File::create(path.clone()) {
            Ok(file) => Ok(file),
            Err(err) => Err(io_vir_err(format!("could not open file {path:?}"), err)),
        }
    }

    /// Use when we expect our call to Z3 to always succeed
    /// If it doesn't, it's an internal error, not a failure
    /// to validate user code.
    fn check_internal_result(result: ValidityResult) {
        match result {
            ValidityResult::Valid => {}
            ValidityResult::TypeError(err) => {
                panic!("internal error: ill-typed AIR code: {}", err)
            }
            _ => panic!("internal error: decls should not generate queries ({:?})", result),
        }
    }

    fn print_profile_stats(
        &self,
        compiler: &Compiler,
        profiler: Profiler,
        qid_map: &HashMap<String, vir::sst::BndInfo>,
    ) {
        let num_quants = profiler.quant_count();
        let total = profiler.total_instantiations();
        let max = 10;
        let msg = format!(
            "Observed {} total instantiations of user-level quantifiers",
            total.to_formatted_string(&Locale::en)
        );
        compiler.diagnostic().note_without_error(&msg);

        for (index, cost) in profiler.iter().take(max).enumerate() {
            // Report the quantifier
            let bnd_info = qid_map
                .get(&cost.quant)
                .expect(format!("Failed to find quantifier {}", cost.quant).as_str());
            let span = from_raw_span(&bnd_info.span.raw_span);
            let mut spans = Vec::new();
            //spans.push(span);
            let count = cost.instantiations;
            let msg = format!(
                "Cost * Instantiations: {} (Instantiated {} times - {}% of the total, cost {}) top {} of {} user-level quantifiers.\n",
                count * cost.cost,
                count.to_formatted_string(&Locale::en),
                100 * count / total,
                cost.cost,
                index + 1,
                num_quants
            );

            // Summarize the triggers it used
            let triggers = &bnd_info.trigs;
            for trigger in triggers.iter() {
                spans.extend(trigger.iter().map(|e| from_raw_span(&e.span.raw_span)));
            }
            let mut multi = MultiSpan::from_spans(spans);
            multi.push_span_label(span, "Triggers selected for this quantifier".to_string());
            compiler.diagnostic().span_note_without_error(multi, &msg);
        }
    }

    /// Check the result of a query that was based on user input.
    /// Success/failure will (eventually) be communicated back to the user.
    /// Returns true if there was at least one Invalid resulting in an error.
    fn check_result_validity(
        &mut self,
        compiler: &Compiler,
        error_as: ErrorAs,
        air_context: &mut air::context::Context,
        assign_map: &HashMap<*const air::ast::Span, HashSet<Arc<std::string::String>>>,
        snap_map: &Vec<(air::ast::Span, SnapPos)>,
        qid_map: &HashMap<String, vir::sst::BndInfo>,
        command: &Command,
        context: &(&air::ast::Span, &str),
        is_singular: bool,
    ) -> bool {
        let report_long_running = || {
            let mut counter = 0;
            let report_fn: Box<dyn FnMut(std::time::Duration) -> ()> = Box::new(move |elapsed| {
                let msg =
                    format!("{} has been running for {} seconds", context.1, elapsed.as_secs());
                if counter % 5 == 0 {
                    let span = from_raw_span(&context.0.raw_span);
                    compiler.diagnostic().span_note_without_error(span, &msg);
                } else {
                    compiler.diagnostic().note_without_error(&msg);
                }
                counter += 1;
            });
            (std::time::Duration::from_secs(2), report_fn)
        };
        let is_check_valid = matches!(**command, CommandX::CheckValid(_));
        let time0 = Instant::now();
        #[cfg(feature = "singular")]
        let mut result = if !is_singular {
            air_context.command(
                &command,
                QueryContext { report_long_running: Some(&mut report_long_running()) },
            )
        } else {
            crate::singular::check_singular_valid(
                air_context,
                &command,
                context.0,
                QueryContext { report_long_running: Some(&mut report_long_running()) },
            )
        };

        #[cfg(not(feature = "singular"))]
        let mut result = air_context.command(
            &command,
            QueryContext { report_long_running: Some(&mut report_long_running()) },
        );

        let time1 = Instant::now();
        self.time_air += time1 - time0;
        let mut is_first_check = true;
        let mut checks_remaining = self.args.multiple_errors;
        let mut only_check_earlier = false;
        let mut invalidity = false;
        loop {
            match result {
                ValidityResult::Valid => {
                    if (is_check_valid && is_first_check && error_as == ErrorAs::Error)
                        || is_singular
                    {
                        self.count_verified += 1;
                    }
                    break;
                }
                ValidityResult::TypeError(err) => {
                    panic!("internal error: generated ill-typed AIR code: {}", err);
                }
                ValidityResult::Canceled => {
                    if is_first_check && error_as == ErrorAs::Error {
                        self.count_errors += 1;
                        invalidity = true;
                    }
                    let mut v = Vec::new();
                    v.push(from_raw_span(&context.0.raw_span));
                    let multispan = MultiSpan::from_spans(v);
                    let mut msg = format!("{}: Resource limit (rlimit) exceeded", context.1);
                    if !self.args.profile && !self.args.profile_all {
                        msg.push_str("; consider rerunning with --profile for more details");
                    }
                    match error_as {
                        ErrorAs::Error => compiler.diagnostic().span_err(multispan, &msg),
                        ErrorAs::Warning => compiler.diagnostic().span_warn(multispan, &msg),
                        ErrorAs::Note => {
                            compiler.diagnostic().span_note_without_error(multispan, &msg)
                        }
                    }

                    self.errors.push(vec![ErrorSpan::new_from_air_span(
                        compiler.session().source_map(),
                        &context.1.to_string(),
                        &context.0,
                    )]);

                    if self.args.profile {
                        let profiler = Profiler::new();
                        self.print_profile_stats(compiler, profiler, qid_map);
                    }
                    break;
                }
                ValidityResult::Invalid(air_model, error) => {
                    if air_model.is_none() {
                        // singular_invalid case
                        self.count_errors += 1;
                        compiler.report_error(&error, error_as);
                        break;
                    }
                    let air_model = air_model.unwrap();

                    if is_first_check && error_as == ErrorAs::Error {
                        self.count_errors += 1;
                        invalidity = true;
                    }
                    if !self.expand_flag || vir::split_expression::is_split_error(&error) {
                        compiler.report_error(&error, error_as);
                    }

                    if error_as == ErrorAs::Error {
                        let mut errors = vec![ErrorSpan::new_from_air_span(
                            compiler.session().source_map(),
                            &error.msg,
                            &error.spans[0],
                        )];
                        for ErrorLabel { msg, span } in &error.labels {
                            errors.push(ErrorSpan::new_from_air_span(
                                compiler.session().source_map(),
                                msg,
                                span,
                            ));
                        }

                        if !self.expand_flag {
                            self.errors.push(errors);
                            if self.args.expand_errors {
                                self.expand_targets.push(error.clone());
                            }
                        } else {
                            // For testing setup, add error for each relevant span
                            if vir::split_expression::is_split_error(&error) {
                                let mut errors: Vec<ErrorSpan> = vec![];
                                for span in &error.spans {
                                    let error = ErrorSpan::new_from_air_span(
                                        compiler.session().source_map(),
                                        &error.msg,
                                        span,
                                    );
                                    if !errors.iter().any(|x: &ErrorSpan| {
                                        x.test_span_line == error.test_span_line
                                    }) {
                                        errors.push(error);
                                    }
                                }

                                for label in &error.labels {
                                    let error = ErrorSpan::new_from_air_span(
                                        compiler.session().source_map(),
                                        &error.msg,
                                        &label.span,
                                    );
                                    if !errors.iter().any(|x: &ErrorSpan| {
                                        x.test_span_line == error.test_span_line
                                    }) {
                                        errors.push(error);
                                    }
                                }
                                self.expand_errors.push(errors);
                            }
                        }
                        if self.args.debug {
                            let mut debugger = Debugger::new(
                                air_model,
                                assign_map,
                                snap_map,
                                compiler.session().source_map(),
                            );
                            debugger.start_shell(air_context);
                        }
                    }

                    if self.args.multiple_errors == 0 {
                        break;
                    }
                    is_first_check = false;
                    if !only_check_earlier {
                        checks_remaining -= 1;
                        if checks_remaining == 0 {
                            only_check_earlier = true;
                        }
                    }

                    let time0 = Instant::now();
                    result = air_context.check_valid_again(
                        only_check_earlier,
                        QueryContext { report_long_running: Some(&mut report_long_running()) },
                    );
                    let time1 = Instant::now();
                    self.time_air += time1 - time0;
                }
                ValidityResult::UnexpectedOutput(err) => {
                    panic!("unexpected output from solver: {}", err);
                }
            }
        }
        if error_as == ErrorAs::Error && checks_remaining == 0 {
            let multispan = MultiSpan::from_spans(vec![from_raw_span(&context.0.raw_span)]);
            let msg = format!(
                "{}: not all errors may have been reported; rerun with a higher value for --multiple-errors to find other potential errors in this function",
                context.1
            );
            compiler.diagnostic().span_warn(multispan, &msg);
        }

        if is_check_valid && !is_singular {
            air_context.finish_query();
        }

        invalidity
    }

    fn run_commands(
        &mut self,
        air_context: &mut air::context::Context,
        commands: &Vec<Command>,
        comment: &str,
    ) {
        if commands.len() > 0 {
            air_context.blank_line();
            air_context.comment(comment);
        }
        for command in commands.iter() {
            let time0 = Instant::now();
            Self::check_internal_result(air_context.command(&command, Default::default()));
            let time1 = Instant::now();
            self.time_air += time1 - time0;
        }
    }

    /// Returns true if there was at least one Invalid resulting in an error.
    fn run_commands_queries(
        &mut self,
        compiler: &Compiler,
        error_as: ErrorAs,
        air_context: &mut air::context::Context,
        commands_with_context: CommandsWithContext,
        assign_map: &HashMap<*const air::ast::Span, HashSet<Arc<String>>>,
        snap_map: &Vec<(air::ast::Span, SnapPos)>,
        qid_map: &HashMap<String, vir::sst::BndInfo>,
        module: &vir::ast::Path,
        function_name: Option<&Fun>,
        comment: &str,
        desc_prefix: Option<&str>,
    ) -> bool {
        if let Some(verify_function) = &self.args.verify_function {
            if let Some(function_name) = function_name {
                let name = fun_name_crate_relative(&module, function_name);
                if &name != verify_function {
                    return false;
                }
            } else {
                return false;
            }
        }
        let mut invalidity = false;
        let CommandsWithContextX { span, desc, commands, prover_choice, skip_recommends: _ } =
            &*commands_with_context;
        if commands.len() > 0 {
            air_context.blank_line();
            air_context.comment(comment);
        }
        let desc = desc_prefix.unwrap_or("").to_string() + desc;
        for command in commands.iter() {
            let result_invalidity = self.check_result_validity(
                compiler,
                error_as,
                air_context,
                assign_map,
                snap_map,
                qid_map,
                &command,
                &(span, &desc),
                *prover_choice == vir::def::ProverChoice::Singular,
            );
            invalidity = invalidity || result_invalidity;
        }

        invalidity
    }

    fn new_air_context_with_prelude(
        &mut self,
        module_path: &vir::ast::Path,
        query_function_path_counter: Option<(&vir::ast::Path, usize)>,
        is_rerun: bool,
        prelude_config: vir::prelude::PreludeConfig,
    ) -> Result<air::context::Context, VirErr> {
        let mut air_context = air::context::Context::new();
        air_context.set_ignore_unexpected_smt(self.args.ignore_unexpected_smt);
        air_context.set_debug(self.args.debug);
        air_context.set_profile(self.args.profile);
        air_context.set_profile_all(self.args.profile_all);

        let rerun_msg = if is_rerun { "_rerun" } else { "" };
        let count_msg = query_function_path_counter
            .map(|(_, ref c)| format!("_{:02}", c))
            .unwrap_or("".to_string());
        let expand_msg = if self.expand_flag { "_expand" } else { "" };

        let function_path = query_function_path_counter.map(|(p, _)| p);
        if self.args.log_all || self.args.log_air_initial {
            let file = self.create_log_file(
                Some(module_path),
                function_path,
                format!(
                    "{}{}{}{}",
                    rerun_msg,
                    count_msg,
                    expand_msg,
                    crate::config::AIR_INITIAL_FILE_SUFFIX
                )
                .as_str(),
            )?;
            air_context.set_air_initial_log(Box::new(file));
        }
        if self.args.log_all || self.args.log_air_final {
            let file = self.create_log_file(
                Some(module_path),
                function_path,
                format!(
                    "{}{}{}{}",
                    rerun_msg,
                    count_msg,
                    expand_msg,
                    crate::config::AIR_FINAL_FILE_SUFFIX
                )
                .as_str(),
            )?;
            air_context.set_air_final_log(Box::new(file));
        }
        if self.args.log_all || self.args.log_smt {
            let file = self.create_log_file(
                Some(module_path),
                function_path,
                format!(
                    "{}{}{}{}",
                    rerun_msg,
                    count_msg,
                    expand_msg,
                    crate::config::SMT_FILE_SUFFIX
                )
                .as_str(),
            )?;
            air_context.set_smt_log(Box::new(file));
        }

        // air_recommended_options causes AIR to apply a preset collection of Z3 options
        air_context.set_z3_param("air_recommended_options", "true");
        air_context.set_rlimit(self.args.rlimit.saturating_mul(RLIMIT_PER_SECOND));
        for (option, value) in self.args.smt_options.iter() {
            air_context.set_z3_param(&option, &value);
        }

        air_context.blank_line();
        air_context.comment("Prelude");
        for command in vir::context::Ctx::prelude(prelude_config).iter() {
            Self::check_internal_result(air_context.command(&command, Default::default()));
        }

        let module_name =
            module_path.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("::");
        air_context.blank_line();
        air_context.comment(&("MODULE '".to_string() + &module_name + "'"));

        Ok(air_context)
    }

    fn new_air_context_with_module_context(
        &mut self,
        ctx: &vir::context::Ctx,
        module_path: &vir::ast::Path,
        function_path: &vir::ast::Path,
        datatype_commands: Arc<Vec<Arc<CommandX>>>,
        function_decl_commands: Arc<Vec<(Commands, String)>>,
        function_spec_commands: Arc<Vec<(Commands, String)>>,
        function_axiom_commands: Arc<Vec<(Commands, String)>>,
        is_rerun: bool,
        context_counter: usize,
        span: &air::ast::Span,
    ) -> Result<air::context::Context, VirErr> {
        let mut air_context = self.new_air_context_with_prelude(
            module_path,
            Some((function_path, context_counter)),
            is_rerun,
            PreludeConfig { arch_word_bits: self.args.arch_word_bits },
        )?;

        // Write the span of spun-off query
        air_context.comment(&span.as_string);

        air_context.blank_line();
        air_context.comment("Fuel");
        for command in ctx.fuel().iter() {
            Self::check_internal_result(air_context.command(&command, Default::default()));
        }

        // set up module context
        self.run_commands(&mut air_context, &datatype_commands, &("Datatypes".to_string()));
        for commands in &*function_decl_commands {
            self.run_commands(&mut air_context, &commands.0, &commands.1);
        }
        for commands in &*function_spec_commands {
            self.run_commands(&mut air_context, &commands.0, &commands.1);
        }
        for commands in &*function_axiom_commands {
            self.run_commands(&mut air_context, &commands.0, &commands.1);
        }
        Ok(air_context)
    }

    // Verify a single module
    fn verify_module(
        &mut self,
        compiler: &Compiler,
        krate: &Krate,
        module: &vir::ast::Path,
        ctx: &mut vir::context::Ctx,
    ) -> Result<(Duration, Duration), VirErr> {
        let mut air_context = self.new_air_context_with_prelude(
            module,
            None,
            false,
            PreludeConfig { arch_word_bits: self.args.arch_word_bits },
        )?;
        if self.args.solver_version_check {
            air_context
                .set_expected_solver_version(crate::consts::EXPECTED_SOLVER_VERSION.to_string());
        }

        let mut spunoff_time_smt_init = Duration::ZERO;
        let mut spunoff_time_smt_run = Duration::ZERO;

        let module = &ctx.module();
        air_context.blank_line();
        air_context.comment("Fuel");
        for command in ctx.fuel().iter() {
            Self::check_internal_result(air_context.command(&command, Default::default()));
        }

        let datatype_commands = vir::datatype_to_air::datatypes_to_air(
            ctx,
            &krate
                .datatypes
                .iter()
                .cloned()
                .filter(|d| is_visible_to(&d.x.visibility, module))
                .collect(),
        );
        self.run_commands(&mut air_context, &datatype_commands, &("Datatypes".to_string()));

        let mk_fun_ctx = |f: &Function, checking_recommends: bool| {
            Some(vir::context::FunctionCtx {
                checking_recommends,
                checking_recommends_for_non_spec: checking_recommends && f.x.mode != Mode::Spec,
                module_for_chosen_triggers: f.x.visibility.owning_module.clone(),
                current_fun: f.x.name.clone(),
            })
        };

        let mut function_decl_commands = vec![];
        let mut function_spec_commands = vec![];
        let mut function_axiom_commands = vec![];

        // Declare the function symbols
        for function in &krate.functions {
            ctx.fun = mk_fun_ctx(&function, false);
            if !is_visible_to(&function.x.visibility, module) || function.x.attrs.is_decrease_by {
                continue;
            }
            let commands = vir::func_to_air::func_name_to_air(ctx, &function)?;
            let comment = "Function-Decl ".to_string() + &fun_as_rust_dbg(&function.x.name);
            self.run_commands(&mut air_context, &commands, &comment);
            function_decl_commands.push((commands.clone(), comment.clone()));
        }
        ctx.fun = None;

        // Collect function definitions
        let mut funs: HashMap<Fun, (Function, Visibility)> = HashMap::new();
        for function in &krate.functions {
            assert!(!funs.contains_key(&function.x.name));
            let vis = function.x.visibility.clone();
            let vis = Visibility { is_private: vis.is_private, ..vis };
            if !is_visible_to(&vis, module) || function.x.attrs.is_decrease_by {
                continue;
            }
            let vis_abs = Visibility { is_private: function.x.publish.is_none(), ..vis };
            funs.insert(function.x.name.clone(), (function.clone(), vis_abs));
        }

        if let Some(verify_function) = &self.args.verify_function {
            let module_funs = funs
                .iter()
                .map(|(_, (f, _))| f)
                .filter(|f| Some(module.clone()) == f.x.visibility.owning_module);
            let mut module_fun_names: Vec<String> =
                module_funs.map(|f| fun_name_crate_relative(&module, &f.x.name)).collect();
            if !module_fun_names.iter().any(|f| f == verify_function) {
                module_fun_names.sort();
                let msg = vec![
                    format!(
                        "could not find function {verify_function} specified by --verify-function"
                    ),
                    format!("available functions are:"),
                ]
                .into_iter()
                .chain(module_fun_names.iter().map(|f| format!("  - {f}")))
                .collect::<Vec<String>>()
                .join("\n");
                return Err(error(msg));
            }
        }

        // For spec functions, check termination and declare consequence axioms.
        // For proof/exec functions, declare requires/ensures.
        // Declare them in SCC (strongly connected component) sorted order so that
        // termination checking precedes consequence axioms for each SCC.
        let mut fun_axioms: HashMap<Fun, Commands> = HashMap::new();
        let mut fun_ssts = SstMap::new();
        for scc in &ctx.global.func_call_sccs.clone() {
            let scc_nodes = ctx.global.func_call_graph.get_scc_nodes(scc);
            let mut scc_fun_nodes: Vec<Fun> = Vec::new();
            for node in scc_nodes.into_iter() {
                match node {
                    Node::Fun(f) => scc_fun_nodes.push(f),
                    _ => {}
                }
            }
            // Declare requires/ensures
            for f in scc_fun_nodes.iter() {
                if !funs.contains_key(f) {
                    continue;
                }
                let (function, _vis_abs) = &funs[f];

                ctx.fun = mk_fun_ctx(&function, false);
                let decl_commands = vir::func_to_air::func_decl_to_air(ctx, &fun_ssts, &function)?;
                ctx.fun = None;
                let comment = "Function-Specs ".to_string() + &fun_as_rust_dbg(f);
                self.run_commands(&mut air_context, &decl_commands, &comment);
                function_spec_commands.push((decl_commands.clone(), comment.clone()));
            }
            // Check termination
            for f in scc_fun_nodes.iter() {
                if !funs.contains_key(f) {
                    continue;
                }
                let (function, vis_abs) = &funs[f];

                ctx.fun = mk_fun_ctx(&function, false);
                let not_verifying_owning_module =
                    Some(module) != function.x.visibility.owning_module.as_ref();
                let (decl_commands, check_commands, new_fun_ssts) =
                    vir::func_to_air::func_axioms_to_air(
                        ctx,
                        fun_ssts,
                        &function,
                        is_visible_to(&vis_abs, module),
                        not_verifying_owning_module,
                    )?;
                fun_ssts = new_fun_ssts;
                fun_axioms.insert(f.clone(), decl_commands);
                ctx.fun = None;

                if not_verifying_owning_module {
                    continue;
                }
                let invalidity = self.run_commands_queries(
                    compiler,
                    ErrorAs::Error,
                    &mut air_context,
                    Arc::new(CommandsWithContextX {
                        span: function.span.clone(),
                        desc: "termination proof".to_string(),
                        commands: check_commands,
                        prover_choice: vir::def::ProverChoice::DefaultProver,
                        skip_recommends: false,
                    }),
                    &HashMap::new(),
                    &vec![],
                    &ctx.global.qid_map.borrow(),
                    module,
                    Some(&function.x.name),
                    &("Function-Termination ".to_string() + &fun_as_rust_dbg(f)),
                    Some("function termination: "),
                );
                let check_recommends = function.x.attrs.check_recommends;
                if (invalidity && !self.args.no_auto_recommends_check) || check_recommends {
                    // Rerun failed query to report possible recommends violations
                    // or (optionally) check recommends for spec function bodies
                    ctx.fun = mk_fun_ctx(&function, true);
                    let (commands, snap_map, new_fun_ssts) = vir::func_to_air::func_def_to_air(
                        ctx,
                        fun_ssts,
                        &function,
                        vir::func_to_air::FuncDefPhase::CheckingSpecs,
                        true,
                    )?;
                    ctx.fun = None;
                    fun_ssts = new_fun_ssts;
                    let error_as = if invalidity { ErrorAs::Note } else { ErrorAs::Warning };
                    let s = "Function-Decl-Check-Recommends ";
                    for command in commands.iter().map(|x| &*x) {
                        self.run_commands_queries(
                            compiler,
                            error_as,
                            &mut air_context,
                            command.clone(),
                            &HashMap::new(),
                            &snap_map,
                            &ctx.global.qid_map.borrow(),
                            module,
                            Some(&function.x.name),
                            &(s.to_string() + &fun_as_rust_dbg(&function.x.name)),
                            Some("recommends check: "),
                        );
                    }
                }
            }

            // Declare consequence axioms
            for f in scc_fun_nodes.iter() {
                if !funs.contains_key(f) {
                    continue;
                }
                let decl_commands = &fun_axioms[f];
                let comment = "Function-Axioms ".to_string() + &fun_as_rust_dbg(f);
                self.run_commands(&mut air_context, &decl_commands, &comment);
                function_axiom_commands.push((decl_commands.clone(), comment.clone()));
                funs.remove(f);
            }
        }
        assert!(funs.len() == 0);

        let function_decl_commands = Arc::new(function_decl_commands);
        let function_spec_commands = Arc::new(function_spec_commands);
        let function_axiom_commands = Arc::new(function_axiom_commands);
        // Create queries to check the validity of proof/exec function bodies
        let no_auto_recommends_check = self.args.no_auto_recommends_check;
        let expand_errors_check = self.args.expand_errors;
        self.expand_targets = vec![];
        for function in &krate.functions {
            if Some(module.clone()) != function.x.visibility.owning_module {
                continue;
            }
            let check_validity = &mut |recommends_rerun: bool,
                                       expands_rerun: bool,
                                       mut fun_ssts: SstMap|
             -> Result<(bool, SstMap), VirErr> {
                let mut spinoff_context_counter = 1;
                ctx.fun = mk_fun_ctx(&function, recommends_rerun);
                ctx.expand_flag = expands_rerun;
                self.expand_flag = expands_rerun;
                if expands_rerun {
                    ctx.debug_expand_targets = self.expand_targets.to_vec();
                }
                let (commands, snap_map, new_fun_ssts) = vir::func_to_air::func_def_to_air(
                    ctx,
                    fun_ssts,
                    &function,
                    vir::func_to_air::FuncDefPhase::CheckingProofExec,
                    recommends_rerun,
                )?;
                fun_ssts = new_fun_ssts;
                let error_as = if recommends_rerun { ErrorAs::Note } else { ErrorAs::Error };
                let s =
                    if recommends_rerun { "Function-Check-Recommends " } else { "Function-Def " };

                let mut function_invalidity = false;
                for command in commands.iter().map(|x| &*x) {
                    let CommandsWithContextX {
                        span,
                        desc: _,
                        commands: _,
                        prover_choice,
                        skip_recommends,
                    } = &**command;
                    if recommends_rerun && *skip_recommends {
                        continue;
                    }
                    if *prover_choice == vir::def::ProverChoice::Singular {
                        #[cfg(not(feature = "singular"))]
                        panic!(
                            "Found singular command when Verus is compiled without Singular feature"
                        );

                        #[cfg(feature = "singular")]
                        if air_context.singular_log.is_none() {
                            let file = self.create_log_file(
                                Some(module),
                                None,
                                crate::config::SINGULAR_FILE_SUFFIX,
                            )?;
                            air_context.singular_log = Some(file);
                        }
                    }
                    let mut spinoff_z3_context;
                    let query_air_context = if *prover_choice == vir::def::ProverChoice::Spinoff {
                        spinoff_z3_context = self.new_air_context_with_module_context(
                            ctx,
                            module,
                            &(function.x.name).path,
                            datatype_commands.clone(),
                            function_decl_commands.clone(),
                            function_spec_commands.clone(),
                            function_axiom_commands.clone(),
                            recommends_rerun,
                            spinoff_context_counter,
                            &span,
                        )?;
                        spinoff_context_counter += 1;
                        &mut spinoff_z3_context
                    } else {
                        &mut air_context
                    };
                    let desc_prefix = recommends_rerun.then(|| "recommends check: ");
                    let command_invalidity = self.run_commands_queries(
                        compiler,
                        error_as,
                        query_air_context,
                        command.clone(),
                        &HashMap::new(),
                        &snap_map,
                        &ctx.global.qid_map.borrow(),
                        module,
                        Some(&function.x.name),
                        &(s.to_string() + &fun_as_rust_dbg(&function.x.name)),
                        desc_prefix,
                    );
                    if *prover_choice == vir::def::ProverChoice::Spinoff {
                        let (time_smt_init, time_smt_run) = query_air_context.get_time();
                        spunoff_time_smt_init += time_smt_init;
                        spunoff_time_smt_run += time_smt_run;
                    }

                    function_invalidity = function_invalidity || command_invalidity;
                }
                Ok((function_invalidity, fun_ssts))
            };
            let (function_invalidity, new_fun_ssts) = check_validity(false, false, fun_ssts)?;
            fun_ssts = new_fun_ssts;
            if function_invalidity && expand_errors_check {
                fun_ssts = check_validity(false, true, fun_ssts)?.1;
            }
            if function_invalidity && !no_auto_recommends_check {
                fun_ssts = check_validity(true, false, fun_ssts)?.1;
            }
        }
        ctx.fun = None;

        let (time_smt_init, time_smt_run) = air_context.get_time();

        Ok((time_smt_init + spunoff_time_smt_init, time_smt_run + spunoff_time_smt_run))
    }

    fn verify_module_outer(
        &mut self,
        compiler: &Compiler,
        krate: &Krate,
        module: &vir::ast::Path,
        mut global_ctx: vir::context::GlobalCtx,
    ) -> Result<vir::context::GlobalCtx, VirErr> {
        let module_name = module_name(module);
        if module.segments.len() == 0 {
            compiler.diagnostic().note_without_error("verifying root module");
        } else {
            compiler.diagnostic().note_without_error(&format!("verifying module {}", &module_name));
        }

        let (pruned_krate, mono_abstract_datatypes, lambda_types) =
            vir::prune::prune_krate_for_module(&krate, &module);
        let mut ctx = vir::context::Ctx::new(
            &pruned_krate,
            global_ctx,
            module.clone(),
            mono_abstract_datatypes,
            lambda_types,
            self.args.debug,
        )?;
        let poly_krate = vir::poly::poly_krate_for_module(&mut ctx, &pruned_krate);
        if self.args.log_all || self.args.log_vir_poly {
            let mut file =
                self.create_log_file(Some(&module), None, crate::config::VIR_POLY_FILE_SUFFIX)?;
            vir::printer::write_krate(&mut file, &poly_krate);
        }

        let (time_smt_init, time_smt_run) =
            self.verify_module(compiler, &poly_krate, module, &mut ctx)?;

        global_ctx = ctx.free();

        self.time_smt_init += time_smt_init;
        self.time_smt_run += time_smt_run;

        Ok(global_ctx)
    }

    // Verify one or more modules in a crate
    fn verify_crate_inner(&mut self, compiler: &Compiler) -> Result<(), VirErr> {
        let krate = self.vir_crate.clone().expect("vir_crate should be initialized");
        let air_no_span = self.air_no_span.clone().expect("air_no_span should be initialized");
        let inferred_modes =
            self.inferred_modes.take().expect("inferred_modes should be initialized");

        #[cfg(debug_assertions)]
        vir::check_ast_flavor::check_krate(&krate);

        let mut global_ctx =
            vir::context::GlobalCtx::new(&krate, air_no_span.clone(), inferred_modes)?;
        vir::recursive_types::check_traits(&krate, &global_ctx)?;
        let krate = vir::ast_simplify::simplify_krate(&mut global_ctx, &krate)?;

        if self.args.log_all || self.args.log_vir_simple {
            let mut file =
                self.create_log_file(None, None, crate::config::VIR_SIMPLE_FILE_SUFFIX)?;
            vir::printer::write_krate(&mut file, &krate);
        }

        #[cfg(debug_assertions)]
        vir::check_ast_flavor::check_krate_simplified(&krate);

        if self.args.verify_pervasive
            && (!self.args.verify_module.is_empty() || self.args.verify_root)
        {
            return Err(error(
                "--verify-pervasive not allowed when --verify-root or --verify-module are present",
            ));
        }

        if self.args.verify_function.is_some() {
            if self.args.verify_module.is_empty() && !self.args.verify_root {
                return Err(error(
                    "--verify-function option requires --verify-module or --verify-root",
                ));
            }

            if self.args.verify_module.len() > 1 {
                return Err(error(
                    "--verify-function only allowed with a single --verify-module (or --verify-root)",
                ));
            }
        }

        let module_ids_to_verify: Vec<vir::ast::Path> = {
            let mut remaining_verify_module: HashSet<_> = self.args.verify_module.iter().collect();
            let module_ids_to_verify = krate
                .module_ids
                .iter()
                .filter(|m| {
                    let name = module_name(m);
                    let is_pervasive = name.starts_with("pervasive::") || name == "pervasive";
                    (!self.args.verify_root
                        && self.args.verify_module.is_empty()
                        && (!is_pervasive ^ self.args.verify_pervasive))
                        || (self.args.verify_root && m.segments.len() == 0)
                        || remaining_verify_module.take(&name).is_some()
                })
                .cloned()
                .collect();

            if let Some(mod_name) = remaining_verify_module.into_iter().next() {
                let msg = vec![
                    format!("could not find module {mod_name} specified by --verify-module"),
                    format!("available modules are:"),
                ]
                .into_iter()
                .chain(krate.module_ids.iter().filter_map(|m| {
                    let name = module_name(m);
                    (!(name.starts_with("pervasive::") || name == "pervasive")
                        && m.segments.len() > 0)
                        .then(|| format!("- {name}"))
                }))
                .chain(Some(format!("or use --verify-root, --verify-pervasive")).into_iter())
                .collect::<Vec<_>>()
                .join("\n");

                return Err(error(msg));
            }

            module_ids_to_verify
        };

        for module in &module_ids_to_verify {
            global_ctx = self.verify_module_outer(compiler, &krate, module, global_ctx)?;
        }

        let verified_modules: HashSet<_> = module_ids_to_verify.iter().collect();

        if self.args.profile_all {
            let profiler = Profiler::new();
            self.print_profile_stats(compiler, profiler, &global_ctx.qid_map.borrow());
        }
        // Log/display triggers
        if self.args.log_all || self.args.log_triggers {
            let mut file = self.create_log_file(None, None, crate::config::TRIGGERS_FILE_SUFFIX)?;
            let chosen_triggers = global_ctx.get_chosen_triggers();
            for triggers in chosen_triggers {
                writeln!(file, "{:#?}", triggers).expect("error writing to trigger log file");
            }
        }
        let chosen_triggers = global_ctx.get_chosen_triggers();
        let mut low_confidence_triggers = None;
        for chosen in chosen_triggers {
            match (self.args.show_triggers, verified_modules.contains(&chosen.module)) {
                (ShowTriggers::Selective, true) if chosen.low_confidence => {
                    report_chosen_triggers(compiler, &chosen);
                    low_confidence_triggers = Some(chosen.span);
                }
                (ShowTriggers::Module, true) => {
                    report_chosen_triggers(compiler, &chosen);
                }
                (ShowTriggers::Verbose, _) => {
                    report_chosen_triggers(compiler, &chosen);
                }
                _ => {}
            }
        }
        if let Some(span) = low_confidence_triggers {
            let span = from_raw_span(&span.raw_span);
            let msg = "Verus printed one or more automatically chosen quantifier triggers\n\
                because it had low confidence in the chosen triggers.\n\
                To suppress these messages, do one of the following:\n  \
                (1) manually annotate a single desired trigger using #[trigger]\n      \
                (example: forall(|i: int, j: int| f(i) && #[trigger] g(i) && #[trigger] h(j))),\n  \
                (2) manually annotate multiple desired triggers using with_triggers\n      \
                (example: forall(|i: int| with_triggers!([f(i)], [g(i)] => f(i) && g(i)))),\n  \
                (3) accept the automatically chosen trigger using #[auto_trigger]\n      \
                (example: forall(|i: int, j: int| #[auto_trigger] f(i) && g(i) && h(j)))\n  \
                (4) use the --triggers-silent command-line option to suppress all printing of triggers.\n\
                (Note: triggers are used by the underlying SMT theorem prover to instantiate quantifiers;\n\
                the theorem prover instantiates a quantifier whenever some expression matches the\n\
                pattern specified by one of the quantifier's triggers.)\
                ";
            compiler.diagnostic().span_note_without_error(span, &msg);
        }

        Ok(())
    }

    pub fn verify_crate<'tcx>(&mut self, compiler: &Compiler) -> Result<bool, VirErr> {
        // Verify crate
        let time3 = Instant::now();
        if !self.args.no_verify {
            self.verify_crate_inner(&compiler)?;
        }
        let time4 = Instant::now();

        self.time_vir_verify = time4 - time3;
        self.time_vir += self.time_vir_verify;
        Ok(true)
    }

    fn construct_vir_crate<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        diagnostics: &impl Diagnostics,
    ) -> Result<bool, VirErr> {
        let autoviewed_call_typs = Arc::new(std::sync::Mutex::new(HashMap::new()));
        if !self.args.no_enhanced_typecheck {
            let _ =
                tcx.formal_verifier_callback.replace(Some(Box::new(crate::typecheck::Typecheck {
                    int_ty_id: None,
                    nat_ty_id: None,
                    enhanced_typecheck: !self.args.no_enhanced_typecheck,
                    exprs_in_spec: Arc::new(std::sync::Mutex::new(HashSet::new())),
                    autoviewed_calls: HashSet::new(),
                    autoviewed_call_typs: autoviewed_call_typs.clone(),
                })));
        }
        match rustc_typeck::check_crate(tcx) {
            Ok(()) => {}
            Err(rustc_errors::ErrorReported {}) => {
                return Ok(false);
            }
        }

        tcx.hir().par_body_owners(|def_id| tcx.ensure().check_match(def_id.to_def_id()));
        tcx.ensure().check_private_in_public(());
        tcx.hir().par_for_each_module(|module| {
            tcx.ensure().check_mod_privacy(module);
        });

        let autoviewed_call_typs =
            autoviewed_call_typs.lock().expect("get autoviewed_call_typs").clone();

        let time0 = Instant::now();

        let hir = tcx.hir();
        let erasure_info = ErasureInfo {
            resolved_calls: vec![],
            resolved_exprs: vec![],
            resolved_pats: vec![],
            external_functions: vec![],
            ignored_functions: vec![],
        };
        let erasure_info = std::rc::Rc::new(std::cell::RefCell::new(erasure_info));
        let ctxt = Arc::new(ContextX {
            tcx,
            krate: hir.krate(),
            erasure_info,
            autoviewed_call_typs,
            unique_id: std::cell::Cell::new(0),
            arch: Arc::new(ArchContextX { word_bits: self.args.arch_word_bits }),
        });

        // Convert HIR -> VIR
        let time1 = Instant::now();
        let vir_crate = crate::rust_to_vir::crate_to_vir(&ctxt)?;
        let time2 = Instant::now();
        let vir_crate = vir::ast_sort::sort_krate(&vir_crate);

        if self.args.log_all || self.args.log_vir {
            let mut file = self.create_log_file(None, None, crate::config::VIR_FILE_SUFFIX)?;
            vir::printer::write_krate(&mut file, &vir_crate);
        }
        let mut check_crate_diags = vec![];
        let check_crate_result = vir::well_formed::check_crate(&vir_crate, &mut check_crate_diags);
        for diag in check_crate_diags {
            match diag {
                vir::ast::VirErrAs::Warning(err) => {
                    diagnostics.report_error(&err, ErrorAs::Warning)
                }
                vir::ast::VirErrAs::Note(err) => diagnostics.report_error(&err, ErrorAs::Note),
            }
        }
        check_crate_result?;
        let (erasure_modes, inferred_modes) = vir::modes::check_crate(&vir_crate)?;
        let vir_crate = vir::traits::demote_foreign_traits(&vir_crate)?;

        self.vir_crate = Some(vir_crate.clone());
        self.air_no_span = (!self.args.no_verify).then(|| {
            let no_span = hir
                .krate()
                .owners
                .iter()
                .filter_map(|oi| {
                    oi.as_ref().and_then(|o| {
                        if let OwnerNode::Crate(c) = o.node() { Some(c.inner) } else { None }
                    })
                })
                .next()
                .expect("OwnerNode::Crate missing");
            air::ast::Span {
                raw_span: crate::util::to_raw_span(no_span),
                as_string: "no location".to_string(),
            }
        });
        self.inferred_modes = Some(inferred_modes);

        let erasure_info = ctxt.erasure_info.borrow();
        let resolved_calls = erasure_info.resolved_calls.clone();
        let resolved_exprs = erasure_info.resolved_exprs.clone();
        let resolved_pats = erasure_info.resolved_pats.clone();
        let external_functions = erasure_info.external_functions.clone();
        let ignored_functions = erasure_info.ignored_functions.clone();
        let erasure_hints = crate::erase::ErasureHints {
            vir_crate,
            resolved_calls,
            resolved_exprs,
            resolved_pats,
            erasure_modes,
            external_functions,
            ignored_functions,
        };
        self.erasure_hints = Some(erasure_hints);

        let time4 = Instant::now();
        self.time_vir = time4 - time0;
        self.time_vir_rust_to_vir = time2 - time1;

        Ok(true)
    }
}

struct DiagnosticOutputBuffer {
    output: std::sync::Arc<std::sync::Mutex<Vec<u8>>>,
}

impl std::io::Write for DiagnosticOutputBuffer {
    fn write(&mut self, buf: &[u8]) -> Result<usize, std::io::Error> {
        self.output.lock().expect("internal error: cannot lock captured output").write(buf)
    }
    fn flush(&mut self) -> Result<(), std::io::Error> {
        self.output.lock().expect("internal error: cannot lock captured output").flush()
    }
}

struct Rewrite {}

impl rustc_lint::FormalVerifierRewrite for Rewrite {
    fn rewrite_crate(
        &mut self,
        krate: &rustc_ast::ast::Crate,
        _next_node_id: &mut dyn FnMut() -> rustc_ast::ast::NodeId,
    ) -> rustc_ast::ast::Crate {
        use crate::rustc_ast::mut_visit::MutVisitor;
        let mut krate = krate.clone();
        let mut visitor = crate::erase_rewrite::Visitor::new();
        visitor.visit_crate(&mut krate);
        krate
    }
}

impl rustc_driver::Callbacks for VerifierCallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        if let Some(target) = &self.verifier.lock().unwrap().test_capture_output {
            config.diagnostic_output =
                rustc_session::DiagnosticOutput::Raw(Box::new(DiagnosticOutputBuffer {
                    output: target.clone(),
                }));
        }
    }

    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        let _ = {
            // Install the rewrite_crate callback so that Rust will later call us back on the AST
            let registration = queries.register_plugins().expect("register_plugins");
            let peeked = registration.peek();
            let lint_store = &peeked.1;
            lint_store.formal_verifier_callback.replace(Some(Box::new(Rewrite {})));
        };
        rustc_driver::Compilation::Continue
    }

    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        let _result = queries.global_ctxt().expect("global_ctxt").peek_mut().enter(|tcx| {
            {
                let mut verifier = self.verifier.lock().expect("verifier mutex");
                if let Err(err) = verifier.construct_vir_crate(tcx, compiler) {
                    compiler.report_error(&err, ErrorAs::Error);
                    verifier.encountered_vir_error = true;
                    return;
                }
            }

            if !compiler.session().compile_status().is_ok() {
                return;
            }

            self.vir_ready.signal(false);

            if self.now_verify.wait() {
                // there was an error in typeck or borrowck
                return;
            }

            {
                let mut verifier = self.verifier.lock().expect("verifier mutex");
                match verifier.verify_crate(compiler) {
                    Ok(_) => {}
                    Err(err) => {
                        compiler.report_error(&err, ErrorAs::Error);
                        verifier.encountered_vir_error = true;
                    }
                }
            }
        });
        rustc_driver::Compilation::Stop
    }
}
