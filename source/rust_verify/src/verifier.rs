use crate::commands::{Op, OpGenerator, OpKind, QueryOp, Style};
use crate::config::{Args, ShowTriggers};
use crate::context::{ContextX, ErasureInfo};
use crate::debugger::Debugger;
use crate::spans::{from_raw_span, SpanContext, SpanContextX};
use crate::user_filter::UserFilter;
use crate::util::error;
use crate::verus_items::VerusItems;
use air::ast::AssertId;
use air::ast::{Command, CommandX, Commands};
use air::context::{QueryContext, SmtSolver, ValidityResult};
use air::messages::{ArcDynMessage, Diagnostics as _};
use air::profiler::Profiler;
use rustc_errors::{DiagnosticBuilder, EmissionGuarantee};
use rustc_hir::OwnerNode;
use rustc_interface::interface::Compiler;
use rustc_session::config::ErrorOutputType;

use vir::messages::{
    message, note, note_bare, warning_bare, Message, MessageLabel, MessageLevel, MessageX, ToAny,
};

use num_format::{Locale, ToFormattedString};
use rustc_error_messages::MultiSpan;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LOCAL_CRATE;
use rustc_span::source_map::SourceMap;
use rustc_span::Span;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::File;
use std::io::Write;
use std::sync::Arc;
use std::time::{Duration, Instant};
use vir::context::{FuncCallGraphLogFiles, GlobalCtx};

use crate::buckets::{Bucket, BucketId};
use crate::expand_errors_driver::ExpandErrorsResult;
use vir::ast::{Fun, Krate, VirErr};
use vir::ast_util::{fun_as_friendly_rust_name, is_visible_to};
use vir::def::{
    path_to_string, CommandContext, CommandsWithContext, CommandsWithContextX, SnapPos,
};
use vir::prelude::PreludeConfig;

const RLIMIT_PER_SECOND: f32 = 3000000f32;

#[derive(Clone, Hash, PartialEq, Eq)]
pub(crate) struct ProgressBarId(String);

trait Diagnostics: air::messages::Diagnostics {
    fn use_progress_bars(&self) -> bool;
    fn add_progress_bar(&self, ctx: CommandContext);
    fn complete_progress_bar(&self, ctx: CommandContext);
}

pub(crate) struct Reporter<'tcx> {
    spans: SpanContext,
    compiler_diagnostics: &'tcx rustc_errors::DiagCtxt,
    source_map: &'tcx rustc_span::source_map::SourceMap,
}

impl<'tcx> Reporter<'tcx> {
    pub(crate) fn new(spans: &SpanContext, compiler: &'tcx Compiler) -> Self {
        Reporter {
            spans: spans.clone(),
            compiler_diagnostics: compiler.sess.dcx(),
            source_map: compiler.sess.source_map(),
        }
    }
}

/// N.B.: The compiler performs deduplication on diagnostic messages, so reporting an error twice,
/// or emitting the same note twice will be surpressed (even if separated in time by other
/// errors/notes)
impl air::messages::Diagnostics for Reporter<'_> {
    fn report_as(&self, msg: &ArcDynMessage, level: MessageLevel) {
        let msg: &MessageX =
            msg.downcast_ref().expect("unexpected value in Any -> Message conversion");

        let mut v: Vec<Span> = Vec::new();
        for sp in &msg.spans {
            if let Some(span) = self.spans.from_air_span(&sp, Some(self.source_map)) {
                v.push(span);
            }
        }
        while let Some(i) = v.iter().position(|a| v.iter().any(|b| a != b && a.contains(*b))) {
            // Remove i in favor of the more specific spans contained by i
            v.remove(i);
        }

        let mut multispan = MultiSpan::from_spans(v);

        for MessageLabel { note, span: sp } in &msg.labels {
            if let Some(span) = self.spans.from_air_span(&sp, Some(self.source_map)) {
                multispan.push_span_label(span, note.clone());
            } else {
                dbg!(&note, &sp.as_string);
            }
        }

        fn emit_with_diagnostic_details<'a, G: EmissionGuarantee>(
            mut diag: DiagnosticBuilder<'a, G>,
            multispan: MultiSpan,
            help: &Option<String>,
        ) {
            diag.span = multispan;
            if let Some(help) = help {
                diag.help(help.clone());
            }
            diag.emit();
        }

        match level {
            MessageLevel::Note => emit_with_diagnostic_details(
                self.compiler_diagnostics.struct_note(msg.note.clone()),
                multispan,
                &msg.help,
            ),
            MessageLevel::Warning => emit_with_diagnostic_details(
                self.compiler_diagnostics.struct_warn(msg.note.clone()),
                multispan,
                &msg.help,
            ),
            MessageLevel::Error => emit_with_diagnostic_details(
                self.compiler_diagnostics.struct_err(msg.note.clone()),
                multispan,
                &msg.help,
            ),
        }
    }

    fn report(&self, msg: &ArcDynMessage) {
        let vir_msg: &MessageX =
            msg.downcast_ref().expect("unexpected value in Any -> Message conversion");
        self.report_as(msg, vir_msg.level)
    }

    fn report_now(&self, msg: &ArcDynMessage) {
        let vir_msg: &MessageX =
            msg.downcast_ref().expect("unexpected value in Any -> Message conversion");
        self.report_as(msg, vir_msg.level)
    }

    fn report_as_now(&self, msg: &ArcDynMessage, msg_as: MessageLevel) {
        self.report_as(msg, msg_as)
    }
}

impl Diagnostics for Reporter<'_> {
    fn use_progress_bars(&self) -> bool {
        false
    }
    fn add_progress_bar(&self, _: CommandContext) {
        panic!("progress bars not supported in single-threaded Reporter");
    }
    fn complete_progress_bar(&self, _: CommandContext) {
        panic!("progress bars not supported in single-threaded Reporter");
    }
}

/// A reporter message that is being collected by the main thread
pub(crate) enum ReporterMessage {
    ReportLongRunning(CommandContext),
    FinishLongRunning(CommandContext),
    Message(usize, Message, MessageLevel, bool),
    WorkerPanicked(Box<dyn std::any::Any + Send>),
    Done(usize),
}

/// A reporter that forwards messages on an mpsc channel
pub(crate) struct QueuedReporter {
    bucket_id: usize,
    queue: std::sync::mpsc::Sender<ReporterMessage>,
}

impl QueuedReporter {
    pub(crate) fn new(bucket_id: usize, queue: std::sync::mpsc::Sender<ReporterMessage>) -> Self {
        Self { bucket_id, queue }
    }

    pub(crate) fn done(&self) {
        self.queue.send(ReporterMessage::Done(self.bucket_id)).expect("could not send!");
    }
}

impl air::messages::Diagnostics for QueuedReporter {
    fn report_as(&self, msg: &ArcDynMessage, level: MessageLevel) {
        let msg: Message =
            msg.clone().downcast().expect("unexpected value in Any -> Message conversion");
        self.queue
            .send(ReporterMessage::Message(self.bucket_id, msg, level, false))
            .expect("could not send the message!");
    }

    fn report_as_now(&self, msg: &ArcDynMessage, level: MessageLevel) {
        let msg: Message =
            msg.clone().downcast().expect("unexpected value in Any -> Message conversion");
        self.queue
            .send(ReporterMessage::Message(self.bucket_id, msg, level, true))
            .expect("could not send the message!");
    }

    fn report(&self, msg: &ArcDynMessage) {
        let air_msg: &MessageX =
            msg.downcast_ref().expect("unexpected value in Any -> Message conversion");
        self.report_as(msg, air_msg.level)
    }

    fn report_now(&self, msg: &ArcDynMessage) {
        let air_msg: &MessageX =
            msg.downcast_ref().expect("unexpected value in Any -> Message conversion");
        self.report_as_now(msg, air_msg.level)
    }
}

impl Diagnostics for QueuedReporter {
    fn use_progress_bars(&self) -> bool {
        true
    }

    fn add_progress_bar(&self, pb: CommandContext) {
        self.queue
            .send(ReporterMessage::ReportLongRunning(pb))
            .expect("could not send the message!");
    }

    fn complete_progress_bar(&self, f: CommandContext) {
        self.queue
            .send(ReporterMessage::FinishLongRunning(f))
            .expect("could not send the message!");
    }
}

#[derive(Default)]
pub struct BucketStats {
    /// cummulative time in AIR to verify the bucket (this includes SMT solver time)
    pub time_air: Duration,
    /// time to initialize the SMT solver
    pub time_smt_init: Duration,
    /// cummulative time of all SMT queries
    pub time_smt_run: Duration,
    /// total time to verify the bucket
    pub time_verify: Duration,
    /// total rlimit count for the bucket
    pub rlimit_count: Option<u64>,
}

pub struct FunctionSmtStats {
    pub smt_time: Duration,
    pub rlimit_count: Option<u64>,
}

pub struct Verifier {
    /// this is the actual number of threads used for verification. This will be set to the
    /// minimum of the requested threads and the number of buckets to verify
    pub num_threads: usize,
    pub encountered_vir_error: bool,
    pub count_verified: u64,
    pub count_errors: u64,
    /// Functions that failed to verify
    pub func_fails: HashSet<Fun>,
    pub args: Args,
    pub user_filter: Option<UserFilter>,
    pub erasure_hints: Option<crate::erase::ErasureHints>,

    /// total real time to verify all activated buckets of the crate, including real time for
    /// the parallel bucket verification
    pub time_verify_crate: Duration,
    /// sequential part of the crate verification before parallel verification
    pub time_verify_crate_sequential: Duration,
    /// total sequantial time spent constructing teh VIR
    pub time_vir: Duration,
    /// the time it took convert the VIR from rust AST
    pub time_vir_rust_to_vir: Duration,
    /// time spent in hir when creating the VIR for the crate
    pub time_hir: Duration,
    /// time spent importing VIR from other crates
    pub time_import: Duration,
    /// execution times for each bucket run in parallel
    pub bucket_stats: HashMap<BucketId, BucketStats>,
    /// smt runtimes for each function per bucket
    pub func_times: HashMap<BucketId, HashMap<Fun, FunctionSmtStats>>,

    // If we've already created the log directory, this is the path to it:
    created_log_dir: Arc<std::sync::Mutex<Option<std::path::PathBuf>>>,
    created_solver_log_dir: Arc<std::sync::Mutex<Option<std::path::PathBuf>>>,
    vir_crate: Option<Krate>,
    crate_name: Option<String>,
    crate_names: Option<Vec<String>>,
    air_no_span: Option<vir::messages::Span>,
    current_crate_modules: Option<Vec<vir::ast::Module>>,
    item_to_module_map: Option<Arc<crate::rust_to_vir::ItemToModuleMap>>,
    buckets: HashMap<BucketId, Bucket>,

    // proof debugging purposes
    expand_flag: bool,

    error_format: Option<ErrorOutputType>,
}

fn report_chosen_triggers(
    diagnostics: &impl air::messages::Diagnostics,
    chosen: &vir::context::ChosenTriggers,
) {
    diagnostics
        .report(&note(&chosen.span, "automatically chose triggers for this expression:").to_any());

    for (n, trigger) in chosen.triggers.iter().enumerate() {
        let note = format!("  trigger {} of {}:", n + 1, chosen.triggers.len());
        let msg = note_bare(note);
        let msg: ArcDynMessage = trigger.iter().fold(msg, |m, (s, _)| {
            let m: &vir::messages::MessageX =
                m.downcast_ref().expect("unexpected value in Any -> Message conversion");
            m.primary_span(s)
        });
        diagnostics.report(&msg);
    }
}

pub(crate) fn io_vir_err(msg: String, err: std::io::Error) -> VirErr {
    error(format!("{msg}: {err}"))
}

pub fn module_name(module: &vir::ast::Path) -> String {
    module.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("::")
}

mod util {
    pub(crate) struct PanicOnDropVec<T>(Option<Vec<T>>);

    // For https://github.com/verus-lang/verus/issues/1044 :
    pub(crate) static PANIC_ON_DROP_VEC: std::sync::atomic::AtomicBool =
        std::sync::atomic::AtomicBool::new(true);

    impl<T> PanicOnDropVec<T> {
        pub fn new(v: Vec<T>) -> Self {
            PanicOnDropVec(Some(v))
        }

        pub fn into_inner(mut self) -> Vec<T> {
            self.0.take().unwrap()
        }

        pub fn as_mut(&mut self) -> &mut Vec<T> {
            self.0.as_mut().unwrap()
        }
    }

    impl<T> Drop for PanicOnDropVec<T> {
        fn drop(&mut self) {
            if self.0.is_some() && PANIC_ON_DROP_VEC.load(std::sync::atomic::Ordering::SeqCst) {
                panic!("dropped, expected call to `into_inner` instead");
            }
        }
    }
}

use util::PanicOnDropVec;

struct RunCommandQueriesResult {
    invalidity: bool,
    timed_out: bool,
    not_skipped: bool,
    #[cfg(feature = "axiom-usage-info")]
    used_axioms: Option<Vec<air::ast::Ident>>,
}

impl std::ops::Add for RunCommandQueriesResult {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        RunCommandQueriesResult {
            invalidity: self.invalidity || rhs.invalidity,
            timed_out: self.timed_out || rhs.timed_out,
            not_skipped: self.not_skipped || rhs.not_skipped,
            #[cfg(feature = "axiom-usage-info")]
            used_axioms: match (self.used_axioms, rhs.used_axioms) {
                (Some(u), None) => Some(u),
                (None, Some(u)) => Some(u),
                (None, None) => None,
                (Some(_), Some(_)) => panic!("only the primary query should contain used_axioms"),
            },
        }
    }
}

struct VerifyBucketOut {
    time_smt_init: Duration,
    time_smt_run: Duration,
    rlimit_count: Option<u64>,
}

impl Verifier {
    pub fn new(args: Args) -> Verifier {
        Verifier {
            num_threads: 1,
            encountered_vir_error: false,
            count_verified: 0,
            count_errors: 0,
            func_fails: HashSet::new(),
            args,
            user_filter: None,
            erasure_hints: None,
            time_verify_crate: Duration::new(0, 0),
            time_verify_crate_sequential: Duration::new(0, 0),
            time_hir: Duration::new(0, 0),
            time_import: Duration::new(0, 0),
            time_vir: Duration::new(0, 0),
            time_vir_rust_to_vir: Duration::new(0, 0),

            bucket_stats: HashMap::new(),
            func_times: HashMap::new(),

            created_log_dir: Arc::new(std::sync::Mutex::new(None)),
            created_solver_log_dir: Arc::new(std::sync::Mutex::new(None)),
            vir_crate: None,
            crate_name: None,
            crate_names: None,
            air_no_span: None,
            current_crate_modules: None,
            item_to_module_map: None,
            buckets: HashMap::new(),

            expand_flag: false,
            error_format: None,
        }
    }

    pub fn from_self(&self) -> Verifier {
        Verifier {
            num_threads: 1,
            encountered_vir_error: false,
            count_verified: 0,
            count_errors: 0,
            func_fails: HashSet::new(),
            args: self.args.clone(),
            user_filter: self.user_filter.clone(),
            erasure_hints: self.erasure_hints.clone(),

            time_verify_crate: Duration::new(0, 0),
            time_verify_crate_sequential: Duration::new(0, 0),
            time_hir: Duration::new(0, 0),
            time_import: Duration::new(0, 0),
            time_vir: Duration::new(0, 0),
            time_vir_rust_to_vir: Duration::new(0, 0),
            bucket_stats: HashMap::new(),
            func_times: HashMap::new(),
            created_log_dir: self.created_log_dir.clone(),
            created_solver_log_dir: self.created_solver_log_dir.clone(),
            vir_crate: self.vir_crate.clone(),
            crate_name: self.crate_name.clone(),
            crate_names: self.crate_names.clone(),
            air_no_span: self.air_no_span.clone(),
            current_crate_modules: self.current_crate_modules.clone(),
            item_to_module_map: self.item_to_module_map.clone(),
            buckets: self.buckets.clone(),
            expand_flag: self.expand_flag,
            error_format: self.error_format,
        }
    }

    /// merges two verifiers by summing up times and verified stats from other into self.
    pub fn merge(&mut self, other: Self) {
        self.count_verified += other.count_verified;
        self.count_errors += other.count_errors;
        self.func_fails.extend(other.func_fails);
        self.time_vir += other.time_vir;
        self.time_vir_rust_to_vir += other.time_vir_rust_to_vir;
        self.bucket_stats.extend(other.bucket_stats);
        self.func_times.extend(other.func_times);
    }

    fn get_bucket<'a>(&'a self, bucket_id: &BucketId) -> &'a Bucket {
        self.buckets.get(bucket_id).expect("expected valid BucketId")
    }

    fn ensure_solver_log_dir(&mut self) -> Result<std::path::PathBuf, VirErr> {
        Ok({
            let mut created_solver_log_dir =
                self.created_solver_log_dir.lock().expect("failed to lock created_solver_log_dir");
            if let Some(dir_path) = &*created_solver_log_dir {
                dir_path.clone()
            } else {
                let dir = std::path::PathBuf::from(crate::config::SOLVER_LOG_DIR.to_string());
                delete_dir_if_exists_and_is_dir(&dir)?;
                std::fs::create_dir_all(&dir).map_err(|err| {
                    io_vir_err(format!("could not create directory {}", dir.display()), err)
                })?;
                *created_solver_log_dir = Some(dir.clone());
                dir
            }
        })
    }

    fn create_log_file(
        &mut self,
        bucket_id_opt: Option<&BucketId>,
        suffix: &str,
    ) -> Result<File, VirErr> {
        let dir_path = {
            let mut created_log_dir =
                self.created_log_dir.lock().expect("failed to lock created_log_dir");
            if let Some(dir_path) = &*created_log_dir {
                dir_path.clone()
            } else {
                let dir = std::path::PathBuf::from(if let Some(dir) = &self.args.log_dir {
                    dir.clone()
                } else {
                    crate::config::LOG_DIR.to_string()
                });
                delete_dir_if_exists_and_is_dir(&dir)?;
                std::fs::create_dir_all(&dir).map_err(|err| {
                    io_vir_err(format!("could not create directory {}", dir.display()), err)
                })?;
                *created_log_dir = Some(dir.clone());
                dir
            }
        };
        let log_file_name = self.log_file_name(&dir_path, bucket_id_opt, suffix);
        match File::create(&log_file_name) {
            Ok(file) => Ok(file),
            Err(err) => {
                Err(io_vir_err(format!("could not open file {}", log_file_name.display()), err))
            }
        }
    }

    fn log_file_name(
        &self,
        dir_path: &std::path::Path,
        bucket_id_opt: Option<&BucketId>,
        suffix: &str,
    ) -> std::path::PathBuf {
        let prefix = match bucket_id_opt {
            None => "crate".to_string(),
            Some(bucket_id) => bucket_id.to_log_string(),
        };
        std::path::PathBuf::from(&dir_path).join(format!("{prefix}{suffix}"))
    }

    /// Use when we expect our call to Z3 to always succeed
    /// If it doesn't, it's an internal error, not a failure
    /// to validate user code.
    fn check_internal_result(result: ValidityResult) {
        match result {
            #[cfg(feature = "axiom-usage-info")]
            ValidityResult::Valid(air::context::UsageInfo::None) => {}
            #[cfg(not(feature = "axiom-usage-info"))]
            ValidityResult::Valid() => {}
            ValidityResult::TypeError(err) => {
                util::PANIC_ON_DROP_VEC.store(false, std::sync::atomic::Ordering::SeqCst);
                panic!("internal error: ill-typed AIR code: {}", err)
            }
            _ => panic!("internal error: decls should not generate queries ({:?})", result),
        }
    }

    fn print_profile_stats(
        &self,
        diagnostics: &impl air::messages::Diagnostics,
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
        diagnostics.report(&note_bare(&msg).to_any());

        for (index, cost) in profiler.iter().take(max).enumerate() {
            // Report the quantifier
            let count = cost.instantiations;
            let note = format!(
                "Cost * Instantiations: {} (Instantiated {} times - {}% of the total, cost {}) top {} of {} user-level quantifiers.\n",
                count * cost.cost,
                count.to_formatted_string(&Locale::en),
                100 * count / total,
                cost.cost,
                index + 1,
                num_quants
            );
            let bnd_info = qid_map
                .get(&cost.quant)
                .expect(format!("Failed to find quantifier {}", cost.quant).as_str());
            let mut msg = note_bare(note);

            // Summarize the triggers it used
            let triggers = &bnd_info.user.as_ref().unwrap().trigs;
            for trigger in triggers.iter() {
                // HACK: we do not have span info for the builtin crate
                if !trigger.iter().any(|t| t.span.as_string.contains("builtin")) {
                    msg = trigger.iter().fold(msg, |m, e| m.primary_span(&e.span));
                }
            }
            msg = msg.secondary_label(
                &bnd_info.user.as_ref().unwrap().span,
                "Triggers selected for this quantifier".to_string(),
            );

            diagnostics.report(&msg.to_any());
        }
    }

    fn print_internal_profile_stats(
        &self,
        diagnostics: &impl air::messages::Diagnostics,
        profile: Vec<(String, u64, Vec<(String, u64)>)>,
        qid_map: &HashMap<String, vir::sst::BndInfo>,
    ) {
        let max = 50;
        for (index, (name, count, identcounts)) in profile.iter().take(max).enumerate() {
            let index = index + 1;
            // Report the quantifier
            if let Some(bnd_info) = qid_map.get(name) {
                let mut msg =
                    format!("{:2}. Quantifier {}, instantiations: {}\n", index, name, count);
                for (ident, count) in identcounts {
                    msg += format!("    at: {}, instantiations: {}\n", ident, count).as_str();
                }

                let mut msg = note_bare(msg);
                if let Some(span) = bnd_info.user.as_ref().map(|u| &u.span) {
                    msg = msg.primary_span(span);
                }
                diagnostics.report(&msg.to_any());
            } else {
                let mut msg =
                    format!("{:2}. Quantifier {}, instantiations: {}\n", index, name, count);
                for (ident, count) in identcounts {
                    msg += format!("    at: {}, instantiations: {}\n", ident, count).as_str();
                }

                let msg = note_bare(msg);
                diagnostics.report(&msg.to_any());
            }
        }
    }

    /// Check the result of a query that was based on user input.
    /// Success/failure will (eventually) be communicated back to the user.
    /// invalidity is true if there was at least one Invalid resulting in an error.
    /// timed_out is true if there was at least one time out
    /// not_skipped is true if the performed command was a CheckValid() request
    ///
    /// If `level` is None, do not report errors.
    fn check_result_validity(
        &mut self,
        bucket_id: &BucketId,
        reporter: &impl Diagnostics,
        source_map: Option<&SourceMap>,
        diagnostics_to_report: &std::cell::RefCell<Option<PanicOnDropVec<(Message, MessageLevel)>>>,
        level: Option<MessageLevel>,
        air_context: &mut air::context::Context,
        assign_map: &HashMap<*const vir::messages::Span, HashSet<Arc<std::string::String>>>,
        snap_map: &Vec<(vir::messages::Span, SnapPos)>,
        command: &Command,
        context: &CommandContext,
        hint_upon_failure: &std::cell::RefCell<Option<Message>>,
        is_singular: bool,
        failed_assert_ids: &mut Vec<AssertId>,
    ) -> RunCommandQueriesResult {
        let message_interface = Arc::new(vir::messages::VirMessageInterface {});

        let do_report_long_running = self.args.report_long_running;
        let report_long_running = || {
            let report_fn: Box<dyn FnMut(std::time::Duration, bool) -> ()> = Box::new(
                move |elapsed, completed| {
                    if !completed {
                        if let Some(in_line_order) = diagnostics_to_report.take() {
                            let mut in_line_order = in_line_order.into_inner();
                            in_line_order.sort_by_key(|(m, _)| {
                                m.spans
                                    .get(0)
                                    .and_then(|s| crate::spans::from_raw_span(&s.raw_span))
                            });
                            for (error, error_level) in in_line_order.into_iter() {
                                reporter.report_as(&error.clone().to_any(), error_level);
                            }
                        }
                    }

                    if do_report_long_running {
                        if !completed {
                            if reporter.use_progress_bars() {
                                reporter.add_progress_bar(context.clone());
                            } else {
                                let msg = format!(
                                    "{} has been running for {} seconds\nreporting errors as they are discovered (they may not be in source order)",
                                    context.desc,
                                    elapsed.as_secs()
                                );
                                let msg = note(&context.span, msg);
                                reporter.report_now(&msg.to_any());
                            }
                        } else {
                            if reporter.use_progress_bars() {
                                reporter.complete_progress_bar(context.clone());
                            } else {
                                let msg = format!(
                                    "{} finished in {} seconds",
                                    context.desc,
                                    elapsed.as_secs()
                                );
                                let msg = note(&context.span, msg);
                                reporter.report_now(&msg.to_any());
                            }
                        }
                    }
                },
            );
            (std::time::Duration::from_secs(2), report_fn)
        };
        let is_check_valid = matches!(**command, CommandX::CheckValid(_));
        let time0 = Instant::now();
        #[cfg(feature = "singular")]
        let mut result = if !is_singular {
            air_context.command(
                &*message_interface,
                reporter,
                &command,
                QueryContext { report_long_running: Some(&mut report_long_running()) },
            )
        } else {
            crate::singular::check_singular_valid(
                air_context,
                &command,
                &context.span,
                QueryContext { report_long_running: Some(&mut report_long_running()) },
            )
        };

        #[cfg(not(feature = "singular"))]
        let mut result = air_context.command(
            &*message_interface,
            reporter,
            &command,
            QueryContext { report_long_running: Some(&mut report_long_running()) },
        );

        let time1 = Instant::now();
        let bucket_time = self.bucket_stats.get_mut(bucket_id).expect("bucket time not found");
        bucket_time.time_air += time1 - time0;

        let mut is_first_check = true;
        let mut checks_remaining = self.args.multiple_errors;
        let mut only_check_earlier = false;
        let mut invalidity = false;
        let mut timed_out = false;
        #[cfg(feature = "axiom-usage-info")]
        let mut used_axioms = None;
        loop {
            match result {
                #[cfg(not(feature = "axiom-usage-info"))]
                ValidityResult::Valid() => {
                    if (is_check_valid && is_first_check && level == Some(MessageLevel::Error))
                        || is_singular
                    {
                        self.count_verified += 1;
                    }
                    break;
                }
                #[cfg(feature = "axiom-usage-info")]
                ValidityResult::Valid(usage_info) => {
                    if (is_check_valid && is_first_check && level == Some(MessageLevel::Error))
                        || is_singular
                    {
                        self.count_verified += 1;

                        if let air::context::UsageInfo::UsedAxioms(axioms) = usage_info {
                            assert!(used_axioms.replace(axioms).is_none());
                        }
                    }
                    break;
                }
                ValidityResult::TypeError(err) => {
                    util::PANIC_ON_DROP_VEC.store(false, std::sync::atomic::Ordering::SeqCst);
                    panic!("internal error: generated ill-typed AIR code: {}", err);
                }
                ValidityResult::Canceled => {
                    if is_first_check && level == Some(MessageLevel::Error) {
                        self.count_errors += 1;
                        self.func_fails.insert(context.fun.clone());
                        invalidity = true;
                    }
                    if self.expand_flag {
                        invalidity = true;
                    }
                    let mut msg = format!("{}: Resource limit (rlimit) exceeded", context.desc);
                    if !self.args.profile && !self.args.profile_all && !self.args.capture_profiles {
                        msg.push_str("; consider rerunning with --profile for more details");
                    }
                    if let Some(level) = level {
                        reporter.report(&message(level, msg, &context.span).to_any());
                    }
                    // need to report that we need to rerun from this function (into spinoff)
                    // so that we can run the profiler on an isolated file on the second pass
                    timed_out = true;
                    break;
                }
                ValidityResult::Invalid(None, error, _)
                | ValidityResult::Invalid(_, error @ None, _) => {
                    if is_first_check && level == Some(MessageLevel::Error) {
                        self.count_errors += 1;
                        invalidity = true;
                    }
                    if self.expand_flag {
                        invalidity = true;
                    }
                    if let Some(level) = level {
                        if let Some(error) = error {
                            // singular_invalid case
                            reporter.report_as(&error, level);
                        } else {
                            // bitvector case
                            reporter.report(&message(level, &context.desc, &context.span).to_any());
                        }
                    }
                    break;
                }
                ValidityResult::Invalid(Some(air_model), Some(error), assert_id_opt) => {
                    if let Some(assert_id) = assert_id_opt {
                        failed_assert_ids.push(assert_id.clone());
                    }

                    if is_first_check && level == Some(MessageLevel::Error) {
                        self.count_errors += 1;
                        self.func_fails.insert(context.fun.clone());
                        invalidity = true;
                        if let Some(hint) = hint_upon_failure.take() {
                            reporter.report_as(&hint.to_any(), MessageLevel::Note);
                        }
                    }
                    if self.expand_flag {
                        invalidity = true;
                    }
                    let error: Message = error.downcast().unwrap();
                    if let Some(level) = level {
                        if !self.expand_flag {
                            if let Some(collected) = &mut *diagnostics_to_report.borrow_mut() {
                                collected.as_mut().push((error.clone(), level));
                            } else {
                                reporter.report_as(&error.clone().to_any(), level);
                            }
                        }
                    }

                    if level == Some(MessageLevel::Error) {
                        if self.args.expand_errors {
                            assert!(!self.expand_flag);
                        }

                        if self.args.debugger {
                            if let Some(source_map) = source_map {
                                let mut debugger =
                                    Debugger::new(air_model, assign_map, snap_map, source_map);
                                debugger.start_shell(air_context);
                            } else {
                                reporter.report(&message(
                                    MessageLevel::Warning,
                                    "no source map available for debugger. Try running single threaded.",
                                    &context.span,
                                ).to_any());
                            }
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
                        reporter,
                        only_check_earlier,
                        QueryContext { report_long_running: Some(&mut report_long_running()) },
                    );
                    let time1 = Instant::now();

                    let bucket_time =
                        self.bucket_stats.get_mut(bucket_id).expect("bucket time not found");
                    bucket_time.time_air += time1 - time0;
                }
                ValidityResult::UnexpectedOutput(err) => {
                    util::PANIC_ON_DROP_VEC.store(false, std::sync::atomic::Ordering::SeqCst);
                    panic!("unexpected output from solver: {}", err);
                }
            }
        }

        if level == Some(MessageLevel::Error) && checks_remaining == 0 {
            let msg = format!(
                "{}: not all errors may have been reported; rerun with a higher value for --multiple-errors to find other potential errors in this function",
                context.desc
            );
            reporter.report(&note(&context.span, msg).to_any());
        }

        if is_check_valid && !is_singular {
            air_context.finish_query();
        }

        RunCommandQueriesResult {
            #[cfg(feature = "axiom-usage-info")]
            used_axioms,
            invalidity,
            timed_out,
            not_skipped: matches!(**command, CommandX::CheckValid(_)),
        }
    }

    fn run_commands(
        &mut self,
        bucket_id: &BucketId,
        diagnostics: &impl air::messages::Diagnostics,
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
            Self::check_internal_result(air_context.command(
                &vir::messages::VirMessageInterface {},
                diagnostics,
                &command,
                Default::default(),
            ));
            let time1 = Instant::now();

            let bucket_time = self.bucket_stats.get_mut(bucket_id).expect("bucket time not found");
            bucket_time.time_air += time1 - time0;
        }
    }

    /// Returns the status of running the provided queries
    /// invalidity: whether the command returned invalid or not
    /// timed_out: whether the command timed out or not
    /// not_skipped : whether a nontrivial validity check was performed or not
    fn run_commands_queries(
        &mut self,
        reporter: &impl Diagnostics,
        source_map: Option<&SourceMap>,
        level: Option<MessageLevel>,
        diagnostics_to_report: &std::cell::RefCell<Option<PanicOnDropVec<(Message, MessageLevel)>>>,
        air_context: &mut air::context::Context,
        commands_with_context: CommandsWithContext,
        assign_map: &HashMap<*const vir::messages::Span, HashSet<Arc<String>>>,
        snap_map: &Vec<(vir::messages::Span, SnapPos)>,
        bucket_id: &BucketId,
        function_name: &Fun,
        comment: &str,
        desc_prefix: Option<&str>,
        failed_assert_ids: &mut Vec<AssertId>,
    ) -> RunCommandQueriesResult {
        let user_filter = self.user_filter.as_ref().unwrap();
        let includes_function = user_filter.includes_function(function_name);
        if !includes_function {
            return RunCommandQueriesResult {
                invalidity: false,
                timed_out: false,
                not_skipped: false,
                #[cfg(feature = "axiom-usage-info")]
                used_axioms: None,
            };
        }

        let mut result = RunCommandQueriesResult {
            invalidity: false,
            timed_out: false,
            not_skipped: false,
            #[cfg(feature = "axiom-usage-info")]
            used_axioms: None,
        };
        let CommandsWithContextX {
            context,
            commands,
            prover_choice,
            skip_recommends: _,
            hint_upon_failure,
        } = &*commands_with_context;
        let context = context.with_desc_prefix(desc_prefix);
        if commands.len() > 0 {
            air_context.blank_line();
            air_context.comment(comment);
            air_context.comment(&context.span.as_string);
        }
        for command in commands.iter() {
            result = result
                + self.check_result_validity(
                    bucket_id,
                    reporter,
                    source_map,
                    diagnostics_to_report,
                    level,
                    air_context,
                    assign_map,
                    snap_map,
                    &command,
                    &context,
                    hint_upon_failure,
                    *prover_choice == vir::def::ProverChoice::Singular,
                    failed_assert_ids,
                );
        }

        result
    }

    fn log_fine_name_suffix(
        is_rerun: bool,
        query_function_path_counter: Option<(&vir::ast::Path, usize)>,
        expand_flag: bool,
        suffix: &str,
    ) -> String {
        let rerun_msg = if is_rerun { "_rerun" } else { "" };
        let count_msg = query_function_path_counter
            .map(|(n, ref c)| format!("{}_{:02}", path_to_string(n), c))
            .unwrap_or("".to_string());
        let expand_msg = if expand_flag { "_expand" } else { "" };

        format!("{}{}{}{}", rerun_msg, count_msg, expand_msg, suffix,)
    }

    fn set_rlimit(air_context: &mut air::context::Context, rlimit: f32) {
        air_context.set_rlimit(if rlimit == f32::INFINITY {
            0 // z3 interprets a zero rlimit as infinity
        } else {
            (rlimit * RLIMIT_PER_SECOND).min(u32::MAX as f32) as u32
        });
    }

    fn set_default_rlimit(&self, air_context: &mut air::context::Context) {
        Self::set_rlimit(air_context, self.args.rlimit);
    }

    fn new_air_context_with_prelude<'m>(
        &mut self,
        message_interface: Arc<dyn air::messages::MessageInterface>,
        diagnostics: &impl air::messages::Diagnostics,
        bucket_id: &BucketId,
        query_function_path_counter: Option<(&vir::ast::Path, usize)>,
        is_rerun: bool,
        prelude_config: vir::prelude::PreludeConfig,
        profile_file_name: Option<&std::path::PathBuf>,
    ) -> Result<air::context::Context, VirErr> {
        let mut air_context =
            air::context::Context::new(message_interface.clone(), self.args.solver);
        air_context.set_ignore_unexpected_smt(self.args.ignore_unexpected_smt);
        air_context.set_debug(self.args.debugger);
        if let Some(profile_file_name) = profile_file_name {
            air_context.set_profile_with_logfile_name(
                profile_file_name.to_str().expect("invalid prover log path").to_owned(),
            );
        }

        if self.args.log_all || self.args.log_args.log_air_initial {
            let file = self.create_log_file(
                Some(bucket_id),
                Self::log_fine_name_suffix(
                    is_rerun,
                    query_function_path_counter,
                    self.expand_flag,
                    crate::config::AIR_INITIAL_FILE_SUFFIX,
                )
                .as_str(),
            )?;
            air_context.set_air_initial_log(Box::new(file));
        }
        if self.args.log_all || self.args.log_args.log_air_final {
            let file = self.create_log_file(
                Some(bucket_id),
                Self::log_fine_name_suffix(
                    is_rerun,
                    query_function_path_counter,
                    self.expand_flag,
                    crate::config::AIR_FINAL_FILE_SUFFIX,
                )
                .as_str(),
            )?;
            air_context.set_air_final_log(Box::new(file));
        }
        if self.args.log_all || self.args.log_args.log_smt {
            let file = self.create_log_file(
                Some(bucket_id),
                Self::log_fine_name_suffix(
                    is_rerun,
                    query_function_path_counter,
                    self.expand_flag,
                    crate::config::SMT_FILE_SUFFIX,
                )
                .as_str(),
            )?;
            air_context.set_smt_log(Box::new(file));
        }

        // air_recommended_options causes AIR to apply a preset collection of Z3 options
        air_context.set_z3_param("air_recommended_options", "true");
        self.set_default_rlimit(&mut air_context);
        for (option, value) in self.args.smt_options.iter() {
            air_context.set_z3_param(&option, &value);
        }
        #[cfg(feature = "axiom-usage-info")]
        if self.args.broadcast_usage_info {
            air_context.enable_usage_info();
        }

        air_context.blank_line();
        air_context.comment("Prelude");
        for command in vir::context::Ctx::prelude(prelude_config).iter() {
            Self::check_internal_result(air_context.command(
                &*message_interface,
                diagnostics,
                &command,
                Default::default(),
            ));
        }

        air_context.blank_line();
        air_context.comment(&("MODULE '".to_string() + &bucket_id.friendly_name() + "'"));

        Ok(air_context)
    }

    fn new_air_context_with_bucket_context<'m>(
        &mut self,
        message_interface: Arc<dyn air::messages::MessageInterface>,
        ctx: &vir::context::Ctx,
        diagnostics: &impl air::messages::Diagnostics,
        bucket_id: &BucketId,
        function_path: &vir::ast::Path,
        datatype_commands: Commands,
        assoc_type_decl_commands: Commands,
        trait_commands: Commands,
        assoc_type_impl_commands: Commands,
        function_decl_commands: Arc<Vec<(Commands, String)>>,
        ops: &Vec<Op>,
        is_rerun: bool,
        context_counter: usize,
        span: &vir::messages::Span,
        profile_file_name: Option<&std::path::PathBuf>,
        spinoff_reason: &str,
    ) -> Result<air::context::Context, VirErr> {
        let mut air_context = self.new_air_context_with_prelude(
            message_interface.clone(),
            diagnostics,
            bucket_id,
            Some((function_path, context_counter)),
            is_rerun,
            PreludeConfig { arch_word_bits: ctx.arch_word_bits, solver: self.args.solver },
            profile_file_name,
        )?;

        // Write the span of spun-off query
        air_context.comment(&span.as_string);
        air_context.blank_line();
        air_context.comment(&format!("query spun off because: {}", spinoff_reason));
        air_context.blank_line();
        air_context.comment("Fuel");
        for command in ctx.fuel().iter() {
            Self::check_internal_result(air_context.command(
                &*message_interface,
                diagnostics,
                &command,
                Default::default(),
            ));
        }

        // set up bucket context
        self.run_commands(
            bucket_id,
            diagnostics,
            &mut air_context,
            &assoc_type_decl_commands,
            &("Associated-Type-Decls".to_string()),
        );
        self.run_commands(
            bucket_id,
            diagnostics,
            &mut air_context,
            &datatype_commands,
            &("Datatypes".to_string()),
        );
        self.run_commands(
            bucket_id,
            diagnostics,
            &mut air_context,
            &trait_commands,
            &("Traits".to_string()),
        );
        self.run_commands(
            bucket_id,
            diagnostics,
            &mut air_context,
            &assoc_type_impl_commands,
            &("Associated-Type-Impls".to_string()),
        );
        for commands in &*function_decl_commands {
            self.run_commands(bucket_id, diagnostics, &mut air_context, &commands.0, &commands.1);
        }
        for op in ops.iter() {
            match &op.kind {
                OpKind::Context(_context_op, commands) => {
                    self.run_commands(
                        bucket_id,
                        diagnostics,
                        &mut air_context,
                        commands,
                        &op.to_air_comment(),
                    );
                }
                OpKind::Query { .. } => {
                    panic!("should have only got Context ops");
                }
            }
        }

        Ok(air_context)
    }

    // Verify a single bucket
    fn verify_bucket(
        &mut self,
        reporter: &impl Diagnostics,
        krate: &vir::sst::KrateSst,
        source_map: Option<&SourceMap>,
        bucket_id: &BucketId,
        ctx: &mut vir::context::Ctx,
    ) -> Result<VerifyBucketOut, VirErr> {
        let message_interface = Arc::new(vir::messages::VirMessageInterface {});

        assert!(!(self.args.profile && self.args.profile_all));
        assert!(!(self.args.profile && self.args.capture_profiles));
        let profile_all_file_name = if self.args.profile_all || self.args.capture_profiles {
            let solver_log_dir = self.ensure_solver_log_dir()?;
            let profile_file_name = self.log_file_name(
                &solver_log_dir,
                Some(bucket_id),
                Self::log_fine_name_suffix(false, None, false, crate::config::PROFILE_FILE_SUFFIX)
                    .as_str(),
            );
            assert!(!profile_file_name.exists());
            Some(profile_file_name)
        } else {
            None
        };
        let mut air_context = self.new_air_context_with_prelude(
            message_interface.clone(),
            reporter,
            bucket_id,
            None,
            false,
            PreludeConfig { arch_word_bits: ctx.arch_word_bits, solver: self.args.solver },
            profile_all_file_name.as_ref(),
        )?;
        if self.args.solver_version_check {
            air_context.set_expected_solver_version(match self.args.solver {
                air::context::SmtSolver::Z3 => crate::consts::EXPECTED_Z3_VERSION.to_string(),
                air::context::SmtSolver::Cvc5 => crate::consts::EXPECTED_CVC5_VERSION.to_string(),
            });
        }

        let mut spunoff_time_smt_init = Duration::ZERO;
        let mut spunoff_time_smt_run = Duration::ZERO;
        let mut spunoff_rlimit_count: Option<u64> = match self.args.solver {
            SmtSolver::Z3 => Some(0),
            SmtSolver::Cvc5 => None,
        };

        let module = &ctx.module_path();
        air_context.blank_line();
        air_context.comment("Fuel");
        for command in ctx.fuel().iter() {
            Self::check_internal_result(air_context.command(
                &*message_interface,
                reporter,
                &command,
                Default::default(),
            ));
        }

        let assoc_type_decl_commands =
            vir::assoc_types_to_air::assoc_type_decls_to_air(ctx, &krate.traits);
        self.run_commands(
            bucket_id,
            reporter,
            &mut air_context,
            &assoc_type_decl_commands,
            &("Associated-Type-Decls".to_string()),
        );

        let datatype_commands = vir::datatype_to_air::datatypes_and_primitives_to_air(
            ctx,
            &krate
                .datatypes
                .iter()
                .cloned()
                .filter(|d| is_visible_to(&d.x.visibility, module))
                .collect(),
        );
        self.run_commands(
            bucket_id,
            reporter,
            &mut air_context,
            &datatype_commands,
            &("Datatypes".to_string()),
        );

        let trait_commands = vir::traits::traits_to_air(ctx, &krate);
        let trait_type_bounds_commands = vir::traits::trait_bound_axioms(ctx, &krate.traits);
        let trait_commands = Arc::new(
            trait_commands.iter().chain(trait_type_bounds_commands.iter()).cloned().collect(),
        );
        self.run_commands(
            bucket_id,
            reporter,
            &mut air_context,
            &trait_commands,
            &("Traits".to_string()),
        );

        let assoc_type_impl_commands =
            vir::assoc_types_to_air::assoc_type_impls_to_air(ctx, &krate.assoc_type_impls);
        self.run_commands(
            bucket_id,
            reporter,
            &mut air_context,
            &assoc_type_impl_commands,
            &("Associated-Type-Impls".to_string()),
        );

        let mut function_decl_commands = vec![];

        // Declare the function symbols
        for function in &krate.functions {
            ctx.fun = vir::ast_to_sst_func::mk_fun_ctx(function, false);
            let commands = vir::sst_to_air_func::func_name_to_air(ctx, reporter, function)?;
            let comment =
                "Function-Decl ".to_string() + &fun_as_friendly_rust_name(&function.x.name);
            self.run_commands(bucket_id, reporter, &mut air_context, &commands, &comment);
            function_decl_commands.push((commands.clone(), comment.clone()));
        }
        ctx.fun = None;

        let function_decl_commands = Arc::new(function_decl_commands);

        let bucket = self.get_bucket(bucket_id);
        let mut opgen = OpGenerator::new(ctx, krate, bucket.clone());
        let mut all_context_ops = vec![];
        while let Some(mut function_opgen) = opgen.next()? {
            let diagnostics_to_report: std::cell::RefCell<
                Option<PanicOnDropVec<(Message, MessageLevel)>>,
            > = std::cell::RefCell::new(Some(PanicOnDropVec::new(Vec::new())));
            let mut flush_diagnostics_to_report = false;
            loop {
                let mut next_op = None;
                let mut expand_errors_diagnostic = None;
                if let Some(r) = function_opgen.expand_errors_next(self.error_format) {
                    match r {
                        Ok(op) => {
                            next_op = Some(op);
                        }
                        Err(diagnostic) => {
                            expand_errors_diagnostic = Some(diagnostic);
                            flush_diagnostics_to_report = true;
                        }
                    }
                }

                if next_op.is_none() {
                    next_op = function_opgen.next();
                }

                if next_op.is_none() {
                    flush_diagnostics_to_report = true;
                }
                if flush_diagnostics_to_report {
                    if let Some(container) = diagnostics_to_report.take() {
                        let mut in_line_order = container.into_inner();
                        in_line_order.sort_by_key(|(m, _)| {
                            m.spans.get(0).and_then(|s| crate::spans::from_raw_span(&s.raw_span))
                        });
                        for (message, level) in in_line_order {
                            reporter.report_as(&message.clone().to_any(), level);
                        }
                    }
                    if let Some(diag) = expand_errors_diagnostic {
                        reporter.report(&diag);
                    }
                }
                let Some(op) = next_op else {
                    break;
                };
                match &op.kind {
                    OpKind::Context(_context_op, commands) => {
                        self.run_commands(
                            bucket_id,
                            reporter,
                            &mut air_context,
                            commands,
                            &op.to_air_comment(),
                        );
                        all_context_ops.push(op);
                    }
                    OpKind::Query {
                        query_op,
                        commands_with_context_list,
                        snap_map,
                        profile_rerun,
                        func_check_sst,
                    } => {
                        let level = match query_op {
                            QueryOp::SpecTermination => MessageLevel::Error,
                            QueryOp::Body(Style::Normal) => MessageLevel::Error,
                            QueryOp::Body(Style::RecommendsFollowupFromError) => MessageLevel::Note,
                            QueryOp::Body(Style::RecommendsChecked) => MessageLevel::Warning,
                            QueryOp::Body(Style::Expanded) => MessageLevel::Note,
                        };
                        let function = &op.get_function();
                        let is_recommend = query_op.is_recommend();
                        self.expand_flag = query_op.is_expanded();

                        let mut spinoff_context_counter = 1;

                        let mut any_invalid = false;
                        let mut any_timed_out = false;
                        let mut failed_assert_ids = vec![];
                        let mut func_curr_smt_time = Duration::ZERO;

                        let mut func_curr_smt_rlimit_count = match self.args.solver {
                            air::context::SmtSolver::Z3 => Some(0),
                            air::context::SmtSolver::Cvc5 => None,
                        };
                        for cmds in commands_with_context_list.iter() {
                            if is_recommend && cmds.skip_recommends {
                                continue;
                            }
                            if cmds.prover_choice == vir::def::ProverChoice::Singular {
                                #[cfg(not(feature = "singular"))]
                                panic!(
                                    "Found singular command when Verus is compiled without Singular feature"
                                );
                            }
                            let mut spinoff_z3_context;
                            let do_spinoff = (cmds.prover_choice
                                == vir::def::ProverChoice::Nonlinear)
                                || (cmds.prover_choice == vir::def::ProverChoice::BitVector)
                                || *profile_rerun
                                || self.args.spinoff_all;

                            let profile_file_name = if *profile_rerun
                                || ((self.args.profile_all || self.args.capture_profiles)
                                    && do_spinoff)
                            {
                                let solver_log_dir = self.ensure_solver_log_dir()?;
                                let profile_file_name = self.log_file_name(
                                    &solver_log_dir,
                                    Some(bucket_id),
                                    Self::log_fine_name_suffix(
                                        is_recommend,
                                        Some((&(function.x.name).path, spinoff_context_counter)),
                                        self.expand_flag,
                                        crate::config::PROFILE_FILE_SUFFIX,
                                    )
                                    .as_str(),
                                );
                                assert!(!profile_file_name.exists());
                                Some(profile_file_name)
                            } else {
                                None
                            };

                            let mut query_air_context = if do_spinoff {
                                let spinoff_reason = if cmds.prover_choice
                                    == vir::def::ProverChoice::Nonlinear
                                {
                                    "nonlinear"
                                } else if cmds.prover_choice == vir::def::ProverChoice::BitVector {
                                    "bitvector"
                                } else if *profile_rerun {
                                    "profile_rerun"
                                } else {
                                    "spinoff_all"
                                };
                                spinoff_z3_context = self.new_air_context_with_bucket_context(
                                    message_interface.clone(),
                                    function_opgen.ctx(),
                                    reporter,
                                    bucket_id,
                                    &(function.x.name).path,
                                    datatype_commands.clone(),
                                    assoc_type_decl_commands.clone(),
                                    trait_commands.clone(),
                                    assoc_type_impl_commands.clone(),
                                    function_decl_commands.clone(),
                                    &all_context_ops,
                                    is_recommend,
                                    spinoff_context_counter,
                                    &cmds.context.span,
                                    profile_file_name.as_ref(),
                                    spinoff_reason,
                                )?;
                                // for bitvector, only one query, no push/pop
                                if cmds.prover_choice == vir::def::ProverChoice::BitVector {
                                    spinoff_z3_context.disable_incremental_solving();
                                }
                                spinoff_context_counter += 1;
                                &mut spinoff_z3_context
                            } else {
                                &mut air_context
                            };
                            let iter_curr_smt_time = query_air_context.get_time().1;
                            let iter_curr_smt_rlimit_count = query_air_context.get_rlimit_count();
                            if let Some(rlimit) = function.x.attrs.rlimit {
                                Self::set_rlimit(&mut query_air_context, rlimit);
                            }
                            let RunCommandQueriesResult {
                                invalidity: command_invalidity,
                                timed_out: command_timed_out,
                                not_skipped: command_not_skipped,
                                #[cfg(feature = "axiom-usage-info")]
                                    used_axioms: command_used_axioms,
                            } = self.run_commands_queries(
                                reporter,
                                source_map,
                                (!profile_rerun).then(|| level),
                                &diagnostics_to_report,
                                query_air_context,
                                cmds.clone(),
                                &HashMap::new(),
                                &snap_map,
                                bucket_id,
                                &function.x.name,
                                &op.to_air_comment(),
                                None,
                                &mut failed_assert_ids,
                            );
                            func_curr_smt_time +=
                                query_air_context.get_time().1 - iter_curr_smt_time;
                            if let Some(func_curr_smt_rlimit_count) =
                                &mut func_curr_smt_rlimit_count
                            {
                                *func_curr_smt_rlimit_count += query_air_context
                                    .get_rlimit_count()
                                    .expect("rlimit count in query context")
                                    - iter_curr_smt_rlimit_count
                                        .expect("rlimit count in query context");
                            }
                            if do_spinoff {
                                let (time_smt_init, time_smt_run) = query_air_context.get_time();
                                spunoff_time_smt_init += time_smt_init;
                                spunoff_time_smt_run += time_smt_run;
                                if let Some(spunoff_rlimit_count) = &mut spunoff_rlimit_count {
                                    *spunoff_rlimit_count += query_air_context
                                        .get_rlimit_count()
                                        .expect("rlimit count in query context");
                                }
                            }
                            if function.x.attrs.rlimit.is_some() {
                                self.set_default_rlimit(&mut query_air_context);
                            }

                            any_invalid |= command_invalidity;
                            any_timed_out |= command_timed_out;

                            #[cfg(feature = "axiom-usage-info")]
                            if let Some(used_axioms) = command_used_axioms {
                                if used_axioms.len() > 0 {
                                    let axioms_list = used_axioms
                                        .iter()
                                        .map(|x| {
                                            let funx = &function_opgen.ctx().fun_ident_map[x];
                                            let is_reveal_group = krate
                                                .reveal_groups
                                                .iter()
                                                .find(|g| &g.x.name == funx)
                                                .is_some();
                                            format!(
                                                "  -{} {}",
                                                if is_reveal_group { " (group)" } else { "" },
                                                fun_as_friendly_rust_name(&funx,),
                                            )
                                        })
                                        .collect::<Vec<String>>()
                                        .join(",\n");
                                    let msg = format!(
                                        "{} used these broadcasted lemmas and broadcast groups:\n{}",
                                        op.to_friendly_desc()
                                            .unwrap_or("checking this function".to_owned()),
                                        axioms_list,
                                    );
                                    reporter
                                        .report(&vir::messages::note(&function.span, msg).to_any());
                                }
                            }

                            if let Some(profile_file_name) = profile_file_name {
                                if command_not_skipped && query_air_context.check_valid_used() {
                                    assert!(profile_file_name.exists());

                                    let current_profile_description =
                                        op.to_friendly_desc().map(|x| x + " ").unwrap_or("".into())
                                            + &fun_as_friendly_rust_name(&function.x.name);

                                    if !self.args.use_internal_profiler {
                                        match Profiler::parse(
                                            message_interface.clone(),
                                            &profile_file_name,
                                            Some(&current_profile_description),
                                            self.args.profile || self.args.profile_all,
                                            reporter,
                                            self.args.capture_profiles,
                                        ) {
                                            Ok(profiler) => {
                                                if self.args.capture_profiles {
                                                    // if capture profiles was passed, silence the report
                                                    // as we are only interested in the graph/profile data
                                                    crate::profiler::write_instantiation_graph(
                                                        &bucket_id,
                                                        Some(&op),
                                                        &function_opgen.ctx().func_map,
                                                        profiler.instantiation_graph().unwrap(),
                                                        &function_opgen
                                                            .ctx()
                                                            .global
                                                            .qid_map
                                                            .borrow(),
                                                        profile_file_name,
                                                    );
                                                } else {
                                                    reporter.report(
                                                        &note_bare(format!(
                                                            "Profile statistics for {}",
                                                            fun_as_friendly_rust_name(
                                                                &function.x.name
                                                            )
                                                        ))
                                                        .to_any(),
                                                    );
                                                    self.print_profile_stats(
                                                        reporter,
                                                        profiler,
                                                        &function_opgen
                                                            .ctx()
                                                            .global
                                                            .qid_map
                                                            .borrow(),
                                                    );
                                                }
                                            }
                                            Err(err) => {
                                                reporter.report_now(
                                                    &warning_bare(format!(
                                                        "Failed parsing profile file for {}: {}",
                                                        current_profile_description, err
                                                    ))
                                                    .to_any(),
                                                );
                                            }
                                        }
                                    } else {
                                        reporter.report(
                                            &note_bare(format!(
                                                "Internal profile statistics for {}",
                                                fun_as_friendly_rust_name(&function.x.name)
                                            ))
                                            .to_any(),
                                        );
                                        let profiler =
                                            air::profiler::internal::profile(&profile_file_name);
                                        self.print_internal_profile_stats(
                                            reporter,
                                            profiler,
                                            &function_opgen.ctx().global.qid_map.borrow(),
                                        );
                                    }
                                }
                            } else {
                                if command_timed_out && self.args.profile {
                                    function_opgen.retry_with_profile(
                                        query_op.clone(),
                                        commands_with_context_list.clone(),
                                        snap_map.clone(),
                                        function,
                                        func_check_sst.clone(),
                                    );
                                    flush_diagnostics_to_report = true;
                                }
                            }
                        }

                        // collect the smt run time from this command into the function duration
                        if commands_with_context_list.len() != 0 {
                            let func_time =
                                self.func_times.entry(bucket_id.clone()).or_insert(HashMap::new());
                            let func_stats = func_time.entry(function.x.name.clone()).or_insert(
                                FunctionSmtStats {
                                    smt_time: Duration::ZERO,
                                    rlimit_count: matches!(self.args.solver, SmtSolver::Z3)
                                        .then(|| 0),
                                },
                            );
                            func_stats.smt_time += func_curr_smt_time;
                            if let Some(rlimit_count) = &mut func_stats.rlimit_count {
                                *rlimit_count += func_curr_smt_rlimit_count
                                    .expect("current rlimit count should be present");
                            }
                        }

                        if matches!(query_op, QueryOp::Body(Style::Normal)) {
                            if (any_invalid && !self.args.no_auto_recommends_check)
                                || function.x.attrs.check_recommends
                            {
                                function_opgen.retry_with_recommends(&op, any_invalid)?;
                            }

                            if any_invalid && self.args.expand_errors && failed_assert_ids.len() > 0
                            {
                                function_opgen.start_expand_errors_if_possible(
                                    &op,
                                    failed_assert_ids[0].clone(),
                                );
                                flush_diagnostics_to_report = true;
                            }
                        }

                        if matches!(query_op, QueryOp::Body(Style::Expanded)) {
                            let res = if any_timed_out {
                                ExpandErrorsResult::Timeout
                            } else if any_invalid {
                                ExpandErrorsResult::Fail
                            } else {
                                ExpandErrorsResult::Pass
                            };
                            function_opgen.report_expand_error_result(res);
                        }

                        if matches!(query_op, QueryOp::SpecTermination) {
                            if (any_invalid && !self.args.no_auto_recommends_check)
                                || function.x.attrs.check_recommends
                            {
                                // Do recommends-checking for the body of the function.
                                // This should always happen for spec(checked).
                                //
                                // Note: this is done as a response to the 'termination check'
                                // because a failed termination check will trigger the
                                // spec body check even if spec(checked) is not marked.
                                // TODO the user probably expects us to also do a recommends-retry
                                // or an expand-errors retry of the decreases-by lemma if
                                // it exists.

                                function_opgen.retry_with_recommends(&op, any_invalid)?;
                            }
                        }
                    }
                }
            }
        }
        // if spinning off all, the regular profile loop inside has already profiled everything
        if let (Some(profile_all_file_name), false) = (profile_all_file_name, self.args.spinoff_all)
        {
            if air_context.check_valid_used() {
                if !self.args.use_internal_profiler {
                    match Profiler::parse(
                        message_interface.clone(),
                        &profile_all_file_name,
                        Some(&bucket_id.friendly_name()),
                        self.args.profile || self.args.profile_all,
                        reporter,
                        self.args.capture_profiles,
                    ) {
                        Ok(profiler) => {
                            if self.args.capture_profiles {
                                // if capture profiles was passed, silence the report
                                // as we are only interested in the graph/profile data
                                crate::profiler::write_instantiation_graph(
                                    &bucket_id,
                                    None,
                                    &opgen.ctx.func_map,
                                    profiler.instantiation_graph().unwrap(),
                                    &opgen.ctx.global.qid_map.borrow(),
                                    profile_all_file_name,
                                );
                            } else {
                                reporter.report(
                                    &note_bare(format!(
                                        "Profile statistics for {}",
                                        bucket_id.friendly_name()
                                    ))
                                    .to_any(),
                                );
                                self.print_profile_stats(
                                    reporter,
                                    profiler,
                                    &opgen.ctx.global.qid_map.borrow(),
                                );
                            }
                        }
                        Err(err) => {
                            reporter.report_now(
                                &warning_bare(format!(
                                    "Failed parsing profile file for {}: {}",
                                    bucket_id.friendly_name(),
                                    err
                                ))
                                .to_any(),
                            );
                        }
                    }
                } else {
                    reporter.report(
                        &note_bare(format!(
                            "Internal profile statistics for {}",
                            bucket_id.friendly_name()
                        ))
                        .to_any(),
                    );
                    let profiler = air::profiler::internal::profile(&profile_all_file_name);
                    self.print_internal_profile_stats(
                        reporter,
                        profiler,
                        &opgen.ctx.global.qid_map.borrow(),
                    );
                }
            }
        }

        ctx.fun = None;

        let (time_smt_init, time_smt_run) = air_context.get_time();
        let rlimit_count = air_context.get_rlimit_count();

        Ok(VerifyBucketOut {
            time_smt_init: time_smt_init + spunoff_time_smt_init,
            time_smt_run: time_smt_run + spunoff_time_smt_run,
            rlimit_count: rlimit_count.map(|rlimit_count| {
                rlimit_count + spunoff_rlimit_count.expect("spunoff rlimit count should be present")
            }),
        })
    }

    fn verify_bucket_outer(
        &mut self,
        reporter: &impl Diagnostics,
        krate: &Krate,
        source_map: Option<&SourceMap>,
        bucket_id: &BucketId,
        mut global_ctx: vir::context::GlobalCtx,
    ) -> Result<vir::context::GlobalCtx, VirErr> {
        let time_verify_start = Instant::now();

        self.bucket_stats.insert(bucket_id.clone(), Default::default());

        let bucket_name = bucket_id.friendly_name();
        let user_filter = self.user_filter.as_ref().unwrap();
        if self.args.trace || !user_filter.is_everything() {
            let functions_msg =
                if user_filter.is_function_filter() { " (selected functions)" } else { "" };
            reporter
                .report_now(&note_bare(format!("verifying {bucket_name}{functions_msg}")).to_any());
        }
        let (pruned_krate, mono_abstract_datatypes, spec_fn_types, uses_array, fndef_types) =
            vir::prune::prune_krate_for_module_or_krate(
                &krate,
                &Arc::new(self.crate_name.clone().expect("crate_name")),
                None,
                Some(bucket_id.module().clone()),
                bucket_id.function(),
                true,
            );
        let mono_abstract_datatypes = mono_abstract_datatypes.unwrap();
        let module = pruned_krate
            .modules
            .iter()
            .find(|m| &m.x.path == bucket_id.module())
            .expect("module in krate")
            .clone();
        let mut ctx = vir::context::Ctx::new(
            &pruned_krate,
            global_ctx,
            module,
            mono_abstract_datatypes,
            spec_fn_types,
            uses_array,
            fndef_types,
            self.args.debugger,
        )?;
        let poly_krate = vir::poly::poly_krate_for_module(&mut ctx, &pruned_krate);
        if self.args.log_all || self.args.log_args.log_vir_poly {
            let mut file =
                self.create_log_file(Some(&bucket_id), crate::config::VIR_POLY_FILE_SUFFIX)?;
            vir::printer::write_krate(&mut file, &poly_krate, &self.args.log_args.vir_log_option);
        }

        let krate_sst = vir::ast_to_sst_crate::ast_to_sst_krate(
            &mut ctx,
            reporter,
            &self.get_bucket(bucket_id).funs,
            &poly_krate,
        )?;

        let VerifyBucketOut { time_smt_init, time_smt_run, rlimit_count } =
            self.verify_bucket(reporter, &krate_sst, source_map, bucket_id, &mut ctx)?;

        global_ctx = ctx.free();

        let time_verify_end = Instant::now();

        let stats_bucket = self.bucket_stats.get_mut(bucket_id).expect("bucket should exist");
        stats_bucket.time_smt_init = time_smt_init;
        stats_bucket.time_smt_run = time_smt_run;
        stats_bucket.time_verify = time_verify_end - time_verify_start;
        stats_bucket.rlimit_count = rlimit_count;

        if self.args.trace {
            reporter.report_now(
                &note_bare(format!("done with {:}", bucket_id.friendly_name())).to_any(),
            );
        }

        Ok(global_ctx)
    }

    // Verify one or more modules in a crate
    fn verify_crate_inner(
        &mut self,
        compiler: &Compiler,
        spans: &SpanContext,
    ) -> Result<(), VirErr> {
        let time_verify_sequential_start = Instant::now();

        let reporter = Reporter::new(spans, compiler);
        let krate = self.vir_crate.clone().expect("vir_crate should be initialized");
        let air_no_span = self.air_no_span.clone().expect("air_no_span should be initialized");

        #[cfg(debug_assertions)]
        vir::check_ast_flavor::check_krate(&krate);

        let call_graph_log = if self.args.log_all || self.args.log_args.log_call_graph {
            #[rustfmt::skip] // r to work around attributes being experimental on expressions
            let r = Some(FuncCallGraphLogFiles {
                all_initial:      self.create_log_file(None, crate::config::CALL_GRAPH_FILE_SUFFIX_FULL_INITIAL)?,
                all_simplified:   self.create_log_file(None, crate::config::CALL_GRAPH_FILE_SUFFIX_FULL_SIMPLIFIED)?,
                nostd_initial:    self.create_log_file(None, crate::config::CALL_GRAPH_FILE_SUFFIX_NOSTD_INITIAL)?,
                nostd_simplified: self.create_log_file(None, crate::config::CALL_GRAPH_FILE_SUFFIX_NOSTD_SIMPLIFIED)?,
            });
            r
        } else {
            None
        };

        let mut global_ctx = vir::context::GlobalCtx::new(
            &krate,
            Arc::new(self.crate_name.clone().expect("crate_name")),
            air_no_span.clone(),
            self.args.rlimit,
            Arc::new(std::sync::Mutex::new(None)),
            Arc::new(std::sync::Mutex::new(call_graph_log)),
            self.args.solver,
            false,
        )?;
        vir::recursive_types::check_traits(&krate, &global_ctx)?;
        let krate = vir::ast_simplify::simplify_krate(&mut global_ctx, &krate)?;

        if self.args.log_all || self.args.log_args.log_vir_simple {
            let mut file = self.create_log_file(None, crate::config::VIR_SIMPLE_FILE_SUFFIX)?;
            vir::printer::write_krate(&mut file, &krate, &self.args.log_args.vir_log_option);
        }

        #[cfg(debug_assertions)]
        vir::check_ast_flavor::check_krate_simplified(&krate);

        // The 'user_filter' handles the filter provided on the command line
        // (--verify-module, --verify-function, etc.)
        // Whereas the 'buckets' are the way we group obligations for parallelizing
        // and context pruning.
        // Buckets usually fall along module boundaries, but the user can create
        // more buckets using #[spinoff_prover].
        //
        // For example, suppose module M has functions a, b, c, d.
        // with a and b both marked spinoff_prover.
        // Then we would create buckets {a}, {b}, and {c, d}.
        //
        // We don't need to create any buckets for stuff that we don't intend
        // to verify. However, we can't shrink any existing bucket based on the
        // the user_filter.
        // For example, suppose the user includes a filter `--verify-function c`.
        // Then, we can drop the {a} and {b} buckets.
        // HOWEVER, we still create the entire {c, d} bucket.
        // We skip the d-related queries when we get to them; however, we still
        // include d in the bucket because d influences the context.
        // Our objective is to generate the same queries for c that we'd otherwise
        // get if we were running verification on the whole module.
        // If the user wants to reduce the context used for d, then they can use
        // the spinoff_prover attribute.

        let user_filter = self.user_filter.as_ref().unwrap();
        let modules_to_verify: Vec<vir::ast::Module> = {
            let current_crate_module_ids = self
                .current_crate_modules
                .as_ref()
                .expect("current_crate_module_ids should be initialized");
            user_filter.filter_modules(current_crate_module_ids)?
        };
        let buckets = crate::buckets::get_buckets(&krate, &modules_to_verify);
        let buckets = user_filter.filter_buckets(buckets);
        let bucket_ids: Vec<BucketId> = buckets.iter().map(|p| p.0.clone()).collect();
        self.buckets = buckets.into_iter().collect();

        let time_verify_sequential_end = Instant::now();
        self.time_verify_crate_sequential =
            time_verify_sequential_end - time_verify_sequential_start;

        let source_map = compiler.sess.source_map();

        self.num_threads = std::cmp::min(self.args.num_threads, bucket_ids.len());
        if self.args.num_threads != 1 && self.num_threads >= 1 {
            // create the multiple producers, single consumer queue
            let (sender, receiver) = std::sync::mpsc::channel();

            // collect the buckets and create the task queueu
            let mut tasks = VecDeque::with_capacity(bucket_ids.len());
            let mut messages: Vec<(bool, Vec<(Message, MessageLevel)>)> = Vec::new();
            for (i, bucket_id) in bucket_ids.iter().enumerate() {
                // give each bucket its own log file
                let interpreter_log_file = Arc::new(std::sync::Mutex::new(
                    if self.args.log_all || self.args.log_args.log_interpreter {
                        Some(self.create_log_file(
                            Some(bucket_id),
                            crate::config::INTERPRETER_FILE_SUFFIX,
                        )?)
                    } else {
                        None
                    },
                ));

                // give each task a queued reporter to identify the bucket that is sending messages
                let reporter = QueuedReporter::new(i, sender.clone());

                tasks.push_back((
                    i,
                    bucket_id.clone(),
                    global_ctx.from_self_with_log(interpreter_log_file),
                    reporter,
                ));
                messages.push((false, Vec::new()));
            }

            // protect the taskq with a mutex
            let taskq = std::sync::Arc::new(std::sync::Mutex::new(tasks));

            // create the worker threads
            let mut workers = Vec::new();
            let mut workers_finished = Vec::new();
            for _tid in 0..self.num_threads {
                // we create a clone of the verifier here to pass each thread its own local
                // copy as we modify fields in the verifier struct. later, we merge the results
                let mut thread_verifier = self.from_self();
                let thread_taskq = taskq.clone();
                let thread_krate = krate.clone(); // is an Arc<T>

                let worker_sender = sender.clone();
                let worker = std::thread::spawn(move || {
                    let r = std::panic::catch_unwind(|| {
                        let mut completed_tasks: Vec<GlobalCtx> = Vec::new();
                        loop {
                            let mut tq = thread_taskq.lock().unwrap();
                            let elm = tq.pop_front();
                            drop(tq);
                            if let Some((_i, bucket_id, task, reporter)) = elm {
                                let res = thread_verifier.verify_bucket_outer(
                                    &reporter,
                                    &thread_krate,
                                    None,
                                    &bucket_id,
                                    task,
                                );
                                reporter.done(); // we've verified the bucket, send the done message
                                match res {
                                    Ok(res) => {
                                        completed_tasks.push(res);
                                    }
                                    Err(e) => return Err(e),
                                }
                            } else {
                                break;
                            }
                        }
                        Ok::<(Verifier, Vec<GlobalCtx>), VirErr>((thread_verifier, completed_tasks))
                    });

                    match r {
                        Ok(x) => x,
                        Err(e) => {
                            worker_sender
                                .send(ReporterMessage::WorkerPanicked(e))
                                .expect("mpsc open");
                            panic!("worker thread panicked");
                        }
                    }
                });
                workers.push(worker);
            }

            let multi_progress = indicatif::MultiProgress::with_draw_target(
                indicatif::ProgressDrawTarget::stderr_with_hz(1),
            );
            let mut multi_progress_header = None;
            let mut progress_bars = HashMap::new();

            // start handling messages, we keep track of the current active bucket for which we
            // print messages immediately, while buffering other messages from the other buckets
            let mut active_bucket = None;
            let mut num_done = 0;
            let reporter = Reporter::new(spans, compiler);
            loop {
                let msg = receiver.recv().expect("receiving message failed");
                match msg {
                    ReporterMessage::Message(id, msg, level, now) => {
                        if now {
                            // if the message should be reported immediately, do so
                            // this is used for printing notices for long running queries
                            multi_progress.suspend(|| reporter.report_as(&msg.to_any(), level));
                            continue;
                        }

                        if let Some(m) = active_bucket {
                            // if it's the active bucket, print the message
                            if id == m {
                                multi_progress.suspend(|| reporter.report_as(&msg.to_any(), level));
                            } else {
                                let msgs = messages.get_mut(id).expect("message id out of range");
                                msgs.1.push((msg, level));
                            }
                        } else {
                            // no active bucket, print this message and set the bucket as the
                            // active one
                            active_bucket = Some(id);
                            multi_progress.suspend(|| reporter.report_as(&msg.to_any(), level));
                        }
                    }
                    ReporterMessage::Done(id) => {
                        // the done message is sent by the thread whenever it is done with verifying
                        // a bucket, we mark the bucket as done here.
                        {
                            // record that the bucket is done
                            let msgs = messages.get_mut(id).expect("message id out of range");
                            msgs.0 = true;
                        }

                        // if it is the active bucket, mark it as done, and reset the active bucket
                        if let Some(m) = active_bucket {
                            if m == id {
                                assert!(
                                    messages
                                        .get_mut(id)
                                        .expect("message id out of range")
                                        .1
                                        .is_empty()
                                );
                                active_bucket = None;
                            }
                        }

                        // try to pick a new active bucket here, the first one that has any messages
                        if active_bucket.is_none() {
                            for (i, msgs) in messages.iter_mut().enumerate() {
                                if msgs.1.is_empty() {
                                    continue;
                                }
                                // drain and print all messages of the bucket
                                for (msg, level) in msgs.1.drain(..) {
                                    multi_progress
                                        .suspend(|| reporter.report_as(&msg.to_any(), level));
                                }
                                // if the bucket wasn't done, make it active and handle next message
                                if !msgs.0 {
                                    active_bucket = Some(i);
                                    break;
                                }
                            }
                        }

                        num_done = num_done + 1;
                    }
                    ReporterMessage::ReportLongRunning(context) => {
                        let CommandContext { fun, span, desc } = &context;
                        let span = from_raw_span(&span.raw_span).expect("valid span");
                        let span_str = source_map.span_to_diagnostic_string(span);
                        let pid = ProgressBarId(span_str.clone());
                        if progress_bars.contains_key(&pid) {
                            // we already have a primary progress bar, so this query is either for
                            // error localization or recommends checking
                            let (pb, pb_aux) = progress_bars.remove(&pid).unwrap();
                            match pb_aux {
                                None => {
                                    let pb_aux = multi_progress.insert_from_back(
                                        0,
                                        indicatif::ProgressBar::new_spinner()
                                            .with_elapsed(Duration::from_millis(2000)),
                                    );
                                    pb_aux
                                        .enable_steady_tick(std::time::Duration::from_millis(120));
                                    let progress_style = indicatif::ProgressStyle::with_template(
                                        "{prefix} {elapsed}\n{msg}",
                                    )
                                    .expect("invalid progress style");
                                    pb_aux.set_style(progress_style);
                                    pb_aux.set_prefix(format!(
                                        "{} {} {} {} {}",
                                        console::style("•").red(),
                                        span_str,
                                        console::style("has been").bold(),
                                        console::style("running").bold().red(),
                                        console::style("for").bold()
                                    ));
                                    pb_aux.set_message(format!(
                                        "  ⌝ {} {} {} {}",
                                        desc,
                                        console::style("for").bold(),
                                        fun_as_friendly_rust_name(&fun),
                                        console::style("(auxiliary checks)").bold()
                                    ));
                                    progress_bars.insert(pid, (pb, Some(pb_aux)));
                                }
                                Some(pb_aux) => {
                                    let new_pb_aux = multi_progress.insert_after(
                                        &pb_aux,
                                        indicatif::ProgressBar::new_spinner()
                                            .with_elapsed(pb_aux.elapsed()),
                                    );
                                    pb_aux.finish_and_clear();
                                    new_pb_aux
                                        .enable_steady_tick(std::time::Duration::from_millis(120));
                                    let progress_style = indicatif::ProgressStyle::with_template(
                                        "{prefix} {elapsed}\n{msg}",
                                    )
                                    .expect("invalid progress style");
                                    new_pb_aux.set_style(progress_style);
                                    new_pb_aux.set_prefix(format!(
                                        "{} {} {} {} {}",
                                        console::style("•").red(),
                                        span_str,
                                        console::style("has been").bold(),
                                        console::style("running").bold().red(),
                                        console::style("for").bold()
                                    ));
                                    new_pb_aux.set_message(format!(
                                        "  ⌝ {} {} {} {}",
                                        desc,
                                        console::style("for").bold(),
                                        fun_as_friendly_rust_name(&fun),
                                        console::style("(auxiliary checks)").bold()
                                    ));
                                    progress_bars.insert(pid, (pb, Some(new_pb_aux)));
                                }
                            }
                        } else {
                            if let None = multi_progress_header {
                                let header_pb = multi_progress
                                    .insert_from_back(0, indicatif::ProgressBar::new_spinner());
                                let progress_style =
                                    indicatif::ProgressStyle::with_template("{msg}")
                                        .expect("invalid progress style");
                                header_pb.set_style(progress_style);
                                header_pb.set_message(format!(
                                    "{}",
                                    console::style("Some checks are taking longer than 2s (diagnostics for these may be reported out of order)").bold(),
                                ));
                                header_pb.finish();
                                multi_progress_header = Some(header_pb);
                            }
                            let pb = multi_progress.insert_from_back(
                                0,
                                indicatif::ProgressBar::new_spinner()
                                    .with_elapsed(Duration::from_millis(2000)),
                            );
                            pb.enable_steady_tick(std::time::Duration::from_millis(120));
                            let progress_style = indicatif::ProgressStyle::with_template(
                                "{prefix} {elapsed}\n{msg}",
                            )
                            .expect("invalid progress style");
                            pb.set_style(progress_style);
                            let CommandContext { fun, span, desc } = &context;
                            let span = from_raw_span(&span.raw_span).expect("valid span");
                            let span_str = source_map.span_to_diagnostic_string(span);
                            pb.set_prefix(format!(
                                "{} {} {} {} {}",
                                console::style("•").red(),
                                span_str,
                                console::style("has been").bold(),
                                console::style("running").bold().red(),
                                console::style("for").bold()
                            ));
                            pb.set_message(format!(
                                "  ⌝ {} {} {}",
                                desc,
                                console::style("for").bold(),
                                fun_as_friendly_rust_name(&fun)
                            ));
                            progress_bars.insert(pid, (pb, None));
                        }
                    }
                    ReporterMessage::FinishLongRunning(context) => {
                        let CommandContext { fun, span, desc } = &context;
                        let span = from_raw_span(&span.raw_span).expect("valid span");
                        let span_str = source_map.span_to_diagnostic_string(span);
                        let pid = ProgressBarId(span_str.clone());
                        let (pb, pb_aux) = progress_bars.get_mut(&pid).unwrap();
                        if !pb.is_finished() {
                            pb.set_prefix(format!(
                                "{} {} {} {} {}",
                                console::style("•").blue(),
                                span_str,
                                console::style("has").bold(),
                                console::style("finished").bold().blue(),
                                console::style("in").bold()
                            ));
                            pb.finish_with_message(format!(
                                "  ⌝ {} {} {}",
                                desc,
                                console::style("for").bold(),
                                fun_as_friendly_rust_name(&fun)
                            ));
                        } else {
                            let pb_aux = pb_aux.as_ref().unwrap();
                            pb_aux.set_prefix(format!(
                                "{} {} {} {} {}",
                                console::style("•").blue(),
                                span_str,
                                console::style("has").bold(),
                                console::style("finished").bold().blue(),
                                console::style("in").bold()
                            ));
                            pb_aux.finish_with_message(format!(
                                "  ⌝ {} {} {} {}",
                                desc,
                                console::style("for").bold(),
                                fun_as_friendly_rust_name(&fun),
                                console::style("(auxiliary checks)").bold()
                            ));
                        }
                    }
                    ReporterMessage::WorkerPanicked(err) => {
                        std::panic::resume_unwind(err);
                    }
                }

                let mut workers_running = Vec::with_capacity(workers.len());
                for worker in workers.into_iter() {
                    if worker.is_finished() {
                        match worker.join() {
                            Ok(finished) => workers_finished.push(finished),
                            Err(_) => panic!("worker thread panicked"),
                        }
                    } else {
                        workers_running.push(worker);
                    }
                }
                workers = workers_running;

                if num_done == bucket_ids.len() {
                    break;
                }
            }

            // join with all worker threads, theys should all have exited by now.
            // merge the verifier and global contexts
            for worker in workers {
                let res = worker.join().unwrap();
                workers_finished.push(res);
            }

            for res in workers_finished {
                match res {
                    Ok((verifier, res)) => {
                        for r in res {
                            global_ctx.merge(r);
                        }
                        self.merge(verifier);
                    }
                    Err(e) => return Err(e),
                }
            }

            // print remaining messages
            for msgs in messages.drain(..) {
                for (msg, level) in msgs.1 {
                    reporter.report_as(&msg.to_any(), level);
                }
            }
        } else {
            global_ctx.set_interpreter_log_file(Arc::new(std::sync::Mutex::new(
                if self.args.log_all || self.args.log_args.log_interpreter {
                    Some(self.create_log_file(None, crate::config::INTERPRETER_FILE_SUFFIX)?)
                } else {
                    None
                },
            )));

            for bucket_id in &bucket_ids {
                global_ctx = self.verify_bucket_outer(
                    &reporter,
                    &krate,
                    Some(source_map),
                    bucket_id,
                    global_ctx,
                )?;
            }
        }

        if self.args.profile && self.count_errors == 0 {
            let msg = note_bare(
                "--profile reports prover performance data only when rlimts are exceeded, use --profile-all to always report profiler results",
            );
            reporter.report(&msg.to_any());
        }

        // Log/display triggers
        if self.args.log_all || self.args.log_args.log_triggers {
            let mut file = self.create_log_file(None, crate::config::TRIGGERS_FILE_SUFFIX)?;
            let chosen_triggers = global_ctx.get_chosen_triggers();
            for triggers in chosen_triggers {
                writeln!(file, "{:#?}", triggers).expect("error writing to trigger log file");
            }
        }
        let chosen_triggers = global_ctx.get_chosen_triggers();
        let mut low_confidence_triggers = None;
        for chosen in chosen_triggers {
            match (
                self.args.show_triggers,
                modules_to_verify.iter().find(|m| &m.x.path == &chosen.module).is_some(),
            ) {
                (ShowTriggers::Selective, true) if chosen.low_confidence => {
                    report_chosen_triggers(&reporter, &chosen);
                    low_confidence_triggers = Some(chosen.span);
                }
                (ShowTriggers::Module, true) => {
                    report_chosen_triggers(&reporter, &chosen);
                }
                (ShowTriggers::Verbose, _) => {
                    report_chosen_triggers(&reporter, &chosen);
                }
                _ => {}
            }
        }
        if let Some(span) = low_confidence_triggers {
            let msg = "Verus printed one or more automatically chosen quantifier triggers\n\
                because it had low confidence in the chosen triggers.\n\
                To suppress these messages, do one of the following:\n  \
                (1) manually annotate a single desired trigger using #[trigger]\n      \
                (example: forall|i: int, j: int| f(i) && #[trigger] g(i) && #[trigger] h(j)),\n  \
                (2) manually annotate multiple desired triggers using #![trigger ...]\n      \
                (example: forall|i: int| #![trigger f(i)] #![trigger g(i)] f(i) && g(i)),\n  \
                (3) accept the automatically chosen trigger using #![auto]\n      \
                (example: forall|i: int, j: int| #![auto] f(i) && g(i) && h(j))\n  \
                (4) use the --triggers-silent command-line option to suppress all printing of triggers.\n\
                (Note: triggers are used by the underlying SMT theorem prover to instantiate quantifiers;\n\
                the theorem prover instantiates a quantifier whenever some expression matches the\n\
                pattern specified by one of the quantifier's triggers.)\
                ";
            reporter.report(&note(&span, msg).to_any());
        }

        Ok(())
    }

    pub(crate) fn verify_crate<'tcx>(
        &mut self,
        compiler: &Compiler,
        spans: &SpanContext,
    ) -> Result<(), VirErr> {
        // Verify crate
        let time_verify_crate_start = Instant::now();

        let result =
            if !self.args.no_verify { self.verify_crate_inner(&compiler, spans) } else { Ok(()) };

        let time_verify_crate_end = Instant::now();
        self.time_verify_crate = time_verify_crate_end - time_verify_crate_start;

        result
    }

    fn construct_vir_crate<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        verus_items: Arc<VerusItems>,
        spans: &SpanContext,
        other_crate_names: Vec<String>,
        other_vir_crates: Vec<Krate>,
        diagnostics: &impl air::messages::Diagnostics,
        crate_name: String,
    ) -> Result<bool, (VirErr, Vec<vir::ast::VirErrAs>)> {
        let time_hir0 = Instant::now();

        match rustc_hir_analysis::check_crate(tcx) {
            Ok(()) => {}
            Err(_) => {
                return Ok(false);
            }
        }

        let hir = tcx.hir();
        hir.par_body_owners(|def_id| tcx.ensure().check_match(def_id));
        tcx.ensure().check_private_in_public(());
        hir.par_for_each_module(|module| {
            tcx.ensure().check_mod_privacy(module);
        });

        self.air_no_span = {
            let no_span = hir
                .krate()
                .owners
                .iter()
                .filter_map(|oi| {
                    oi.as_owner().as_ref().and_then(|o| {
                        if let OwnerNode::Crate(c) = o.node() {
                            Some(c.spans.inner_span)
                        } else {
                            None
                        }
                    })
                })
                .next()
                .expect("OwnerNode::Crate missing");
            Some(vir::messages::Span {
                raw_span: crate::spans::to_raw_span(no_span),
                id: 0,
                data: vec![],
                as_string: "no location".to_string(),
            })
        };

        let time_hir1 = Instant::now();
        self.time_hir = time_hir1 - time_hir0;

        let time0 = Instant::now();

        let mut crate_names: Vec<String> = vec![crate_name.clone()];
        crate_names.extend(other_crate_names.into_iter());
        // TODO vec![vir::builtins::builtin_krate(&self.air_no_span.clone().unwrap())];

        let erasure_info = ErasureInfo {
            hir_vir_ids: vec![],
            resolved_calls: vec![],
            resolved_exprs: vec![],
            resolved_pats: vec![],
            direct_var_modes: vec![],
            external_functions: vec![],
            ignored_functions: vec![],
        };
        let erasure_info = std::rc::Rc::new(std::cell::RefCell::new(erasure_info));
        let import_len = self.args.import.len();
        let vstd_crate_name = Arc::new(vir::def::VERUSLIB.to_string());
        let mut ctxt = Arc::new(ContextX {
            cmd_line_args: self.args.clone(),
            tcx,
            krate: hir.krate(),
            erasure_info,
            spans: spans.clone(),
            verus_items,
            diagnostics: std::rc::Rc::new(std::cell::RefCell::new(Vec::new())),
            no_vstd: self.args.vstd == crate::config::Vstd::NoVstd,
            arch_word_bits: None,
            crate_name: Arc::new(crate_name.clone()),
            vstd_crate_name,
        });
        let multi_crate = self.args.export.is_some() || import_len > 0 || self.args.use_crate_name;
        crate::rust_to_vir_base::MULTI_CRATE
            .with(|m| m.store(multi_crate, std::sync::atomic::Ordering::Relaxed));

        let ctxt_diagnostics = ctxt.diagnostics.clone();
        let map_err_diagnostics =
            |err: VirErr| (err, ctxt_diagnostics.borrow_mut().drain(..).collect());

        // Convert HIR -> VIR
        let time1 = Instant::now();
        let (vir_crate, item_to_module_map) =
            crate::rust_to_vir::crate_to_vir(&mut ctxt, &other_vir_crates)
                .map_err(map_err_diagnostics)?;

        let time2 = Instant::now();
        let vir_crate = vir::ast_sort::sort_krate(&vir_crate);
        self.current_crate_modules = Some(vir_crate.modules.clone());
        self.item_to_module_map = Some(Arc::new(item_to_module_map));

        // Export crate if requested.
        let crate_metadata = crate::import_export::CrateMetadata {
            crate_id: spans.local_crate.as_u64(),
            original_files: spans.local_files.clone(),
        };

        let user_filter =
            UserFilter::from_args(&self.args, &vir_crate).map_err(map_err_diagnostics)?;
        self.user_filter = Some(user_filter);

        let mut current_vir_crate = vir_crate.clone();

        // Gather all crates and merge them into one crate.
        // REVIEW: by merging all the crates into one here, we end up rechecking well_formed/modes
        // of the library crates, which were already checked when they were exported.
        // If this turns out to be slow, we could keep the library crates separate from
        // the new crate.  (We do need to have all the crate definitions available in some form,
        // because well_formed and modes checking look up definitions from libraries.)
        // Currently, the most expensive merged-crate operations are (most expensive first):
        // - ast_simplify::simplify_krate
        // - modes::check_crate
        // - traits::demote_foreign_traits
        // - GlobalCtx::new
        // - well_formed::check_crate
        let mut vir_crates: Vec<Krate> = other_vir_crates;
        vir_crates.push(vir_crate);
        let unpruned_crate =
            vir::ast_simplify::merge_krates(vir_crates).map_err(map_err_diagnostics)?;
        let (vir_crate, _, _, _, _) = vir::prune::prune_krate_for_module_or_krate(
            &unpruned_crate,
            &Arc::new(crate_name.clone()),
            Some(&current_vir_crate),
            None,
            None,
            false,
        );
        let vir_crate =
            vir::traits::merge_external_traits(vir_crate).map_err(map_err_diagnostics)?;

        Arc::make_mut(&mut current_vir_crate).arch.word_bits = vir_crate.arch.word_bits;

        crate::import_export::export_crate(&self.args, crate_metadata, current_vir_crate.clone())
            .map_err(map_err_diagnostics)?;

        if self.args.log_all || self.args.log_args.log_vir {
            let mut file = self
                .create_log_file(None, crate::config::VIR_FILE_SUFFIX)
                .map_err(map_err_diagnostics)?;
            vir::printer::write_krate(&mut file, &vir_crate, &self.args.log_args.vir_log_option);
        }
        let path_to_well_known_item = crate::def::path_to_well_known_item(&ctxt);

        let vir_crate =
            vir::traits::demote_external_traits(diagnostics, &path_to_well_known_item, &vir_crate)
                .map_err(map_err_diagnostics)?;
        let vir_crate =
            vir::traits::inherit_default_bodies(&vir_crate).map_err(|e| (e, Vec::new()))?;

        let check_crate_result1 = vir::well_formed::check_one_crate(&current_vir_crate);
        let check_crate_result = vir::well_formed::check_crate(
            &vir_crate,
            unpruned_crate,
            &mut ctxt.diagnostics.borrow_mut(),
            self.args.no_verify,
        );
        for diag in ctxt.diagnostics.borrow_mut().drain(..) {
            match diag {
                vir::ast::VirErrAs::Warning(err) => {
                    diagnostics.report_as(&err.to_any(), MessageLevel::Warning)
                }
                vir::ast::VirErrAs::Note(err) => {
                    diagnostics.report_as(&err.to_any(), MessageLevel::Note)
                }
            }
        }
        check_crate_result1.map_err(|e| (e, Vec::new()))?;
        check_crate_result.map_err(|e| (e, Vec::new()))?;
        let vir_crate = vir::autospec::resolve_autospec(&vir_crate).map_err(|e| (e, Vec::new()))?;
        let (vir_crate, erasure_modes) =
            vir::modes::check_crate(&vir_crate).map_err(|e| (e, Vec::new()))?;

        self.vir_crate = Some(vir_crate.clone());
        self.crate_name = Some(crate_name);
        self.crate_names = Some(crate_names);

        let erasure_info = ctxt.erasure_info.borrow();
        let hir_vir_ids = erasure_info.hir_vir_ids.clone();
        let resolved_calls = erasure_info.resolved_calls.clone();
        let resolved_exprs = erasure_info.resolved_exprs.clone();
        let resolved_pats = erasure_info.resolved_pats.clone();
        let direct_var_modes = erasure_info.direct_var_modes.clone();
        let external_functions = erasure_info.external_functions.clone();
        let ignored_functions = erasure_info.ignored_functions.clone();
        let erasure_hints = crate::erase::ErasureHints {
            vir_crate,
            hir_vir_ids,
            resolved_calls,
            resolved_exprs,
            resolved_pats,
            erasure_modes,
            direct_var_modes,
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

fn delete_dir_if_exists_and_is_dir(dir: &std::path::PathBuf) -> Result<(), VirErr> {
    Ok(if dir.exists() {
        if dir.is_dir() {
            let entries = std::fs::read_dir(dir).map_err(|err| {
                io_vir_err(format!("could not read directory {}", dir.display()), err)
            })?;
            for entry in entries {
                if let Ok(entry) = entry {
                    if entry.path().is_file() {
                        std::fs::remove_file(entry.path()).map_err(|err| {
                            io_vir_err(
                                format!("could not remove file {}", entry.path().display()),
                                err,
                            )
                        })?;
                    }
                }
            }
        } else {
            return Err(error(format!("{} exists and is not a directory", dir.display())));
        }
    })
}

// TODO: move the callbacks into a different file, like driver.rs
pub(crate) struct VerifierCallbacksEraseMacro {
    pub(crate) verifier: Verifier,
    /// start time of the rustc compilation
    pub(crate) rust_start_time: Instant,
    /// time when entered the `after_expansion` callback
    pub(crate) rust_end_time: Option<Instant>,
    /// start time of lifetime analysys
    pub(crate) lifetime_start_time: Option<Instant>,
    /// end time of lifetime analysys
    pub(crate) lifetime_end_time: Option<Instant>,
    pub(crate) rustc_args: Vec<String>,
    pub(crate) file_loader:
        Option<Box<dyn 'static + rustc_span::source_map::FileLoader + Send + Sync>>,
}

pub(crate) static BODY_HIR_ID_TO_REVEAL_PATH_RES: std::sync::RwLock<
    Option<
        HashMap<
            rustc_span::def_id::DefId,
            (Option<rustc_hir::def::Res>, crate::hir_hide_reveal_rewrite::ResOrSymbol),
        >,
    >,
> = std::sync::RwLock::new(None);

fn hir_crate<'tcx>(tcx: TyCtxt<'tcx>, _: ()) -> rustc_hir::Crate<'tcx> {
    let mut crate_ = (rustc_interface::DEFAULT_QUERY_PROVIDERS.hir_crate)(tcx, ());
    crate::hir_hide_reveal_rewrite::hir_hide_reveal_rewrite(&mut crate_, tcx);
    crate_
}

impl rustc_driver::Callbacks for VerifierCallbacksEraseMacro {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.override_queries = Some(|_session, providers| {
            providers.hir_crate = hir_crate;
        });
    }

    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        self.rust_end_time = Some(Instant::now());

        if !compiler.sess.compile_status().is_ok() {
            return rustc_driver::Compilation::Stop;
        }

        self.verifier.error_format = Some(compiler.sess.opts.error_format);

        // write_dep_info will internally check whether the `--emit=dep-info` flag is set
        if let Err(_) = queries.write_dep_info() {
            // ErrorGuaranteed indicates than an error has already been reported to the user, so we can just exit
            std::process::exit(-1);
        }

        let _result = queries.global_ctxt().expect("global_ctxt").enter(|tcx| {
            let crate_name = tcx.crate_name(LOCAL_CRATE).as_str().to_owned();

            let time_import0 = Instant::now();
            let imported = match crate::import_export::import_crates(&self.verifier.args) {
                Ok(imported) => imported,
                Err(err) => {
                    assert!(err.spans.len() == 0);
                    assert!(err.level == MessageLevel::Error);
                    compiler.sess.dcx().err(err.note.clone());
                    self.verifier.encountered_vir_error = true;
                    return;
                }
            };
            let time_import1 = Instant::now();
            self.verifier.time_import = time_import1 - time_import0;
            let verus_items =
                Arc::new(crate::verus_items::from_diagnostic_items(&tcx.all_diagnostic_items(())));
            let spans = SpanContextX::new(
                tcx,
                tcx.stable_crate_id(LOCAL_CRATE),
                compiler.sess.source_map(),
                imported.metadatas.into_iter().map(|c| (c.crate_id, c.original_files)).collect(),
            );
            {
                let reporter = Reporter::new(&spans, compiler);
                if self.verifier.args.trace {
                    reporter.report_now(&note_bare("preparing crate for verification").to_any());
                }
                if let Err((err, mut diagnostics)) = self.verifier.construct_vir_crate(
                    tcx,
                    verus_items.clone(),
                    &spans,
                    imported.crate_names,
                    imported.vir_crates,
                    &reporter,
                    crate_name.clone(),
                ) {
                    reporter.report_as(&err.to_any(), MessageLevel::Error);
                    self.verifier.encountered_vir_error = true;

                    for diag in diagnostics.drain(..) {
                        match diag {
                            vir::ast::VirErrAs::Warning(err) => {
                                reporter.report_as(&err.to_any(), MessageLevel::Warning)
                            }
                            vir::ast::VirErrAs::Note(err) => {
                                reporter.report_as(&err.to_any(), MessageLevel::Note)
                            }
                        }
                    }
                    return;
                }
                if !compiler.sess.compile_status().is_ok() {
                    return;
                }
                self.lifetime_start_time = Some(Instant::now());
                let status = if self.verifier.args.no_lifetime {
                    Ok(vec![])
                } else {
                    let log_lifetime =
                        self.verifier.args.log_all || self.verifier.args.log_args.log_lifetime;
                    let lifetime_log_file = if log_lifetime {
                        let file = self
                            .verifier
                            .create_log_file(None, crate::config::LIFETIME_FILE_SUFFIX);
                        match file {
                            Err(err) => {
                                reporter.report_as(&err.to_any(), MessageLevel::Error);
                                self.verifier.encountered_vir_error = true;
                                return;
                            }
                            Ok(file) => Some(file),
                        }
                    } else {
                        None
                    };
                    crate::lifetime::check_tracked_lifetimes(
                        self.verifier.args.clone(),
                        tcx,
                        verus_items,
                        &spans,
                        self.verifier.erasure_hints.as_ref().expect("erasure_hints"),
                        self.verifier.item_to_module_map.as_ref().expect("item_to_module_map"),
                        self.verifier.vir_crate.as_ref().expect("vir_crate should be initialized"),
                        lifetime_log_file,
                    )
                };
                self.lifetime_end_time = Some(Instant::now());
                match status {
                    Ok(msgs) => {
                        if msgs.len() > 0 {
                            self.verifier.encountered_vir_error = true;
                            // We found lifetime errors.
                            // We could print them immediately, but instead,
                            // let's first run rustc's standard lifetime checking
                            // because the error messages are likely to be better.
                            let file_loader =
                                std::mem::take(&mut self.file_loader).expect("file_loader");
                            let compile_status = crate::driver::run_with_erase_macro_compile(
                                self.rustc_args.clone(),
                                file_loader,
                                false,
                                self.verifier.args.vstd,
                            );
                            if compile_status.is_err() {
                                return;
                            }
                            for msg in &msgs {
                                reporter.report(&msg.clone().to_any());
                            }
                            reporter.report(&note_bare("This error was found in Verus pass: ownership checking of tracked code").to_any());
                            return;
                        }
                    }
                    Err(err) => {
                        reporter.report_as(&err.to_any(), MessageLevel::Error);
                        self.verifier.encountered_vir_error = true;
                        return;
                    }
                }
            }

            if !compiler.sess.compile_status().is_ok() {
                return;
            }

            match self.verifier.verify_crate(compiler, &spans) {
                Ok(()) => {}
                Err(err) => {
                    let reporter = Reporter::new(&spans, compiler);
                    reporter.report_as(&err.to_any(), MessageLevel::Error);
                    self.verifier.encountered_vir_error = true;
                }
            }
        });
        rustc_driver::Compilation::Stop
    }
}
