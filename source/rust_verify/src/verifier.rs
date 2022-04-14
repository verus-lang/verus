use crate::config::{Args, ShowTriggers};
use crate::context::{ContextX, ErasureInfo};
use crate::debugger::Debugger;
use crate::unsupported;
use crate::util::{from_raw_span, signalling};
use air::ast::{Command, CommandX, Commands};
use air::context::ValidityResult;
use air::errors::{Error, ErrorLabel};
use rustc_hir::OwnerNode;
use rustc_interface::interface::Compiler;

use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::SourceMap;
use rustc_span::{CharPos, FileName, MultiSpan, Span};
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Write;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use vir::ast::{Fun, Function, InferMode, Krate, Mode, VirErr, Visibility};
use vir::ast_util::{fun_as_rust_dbg, is_visible_to};
use vir::def::SnapPos;
use vir::recursion::Node;

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

    vir_crate: Option<Krate>,
    air_no_span: Option<air::ast::Span>,
    inferred_modes: Option<HashMap<InferMode, Mode>>,
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

fn report_error(compiler: &Compiler, error: &Error) {
    if error.spans.len() == 0 {
        panic!("internal error: found Error with no span")
    }

    let mut v = Vec::new();
    for sp in &error.spans {
        let span: Span = from_raw_span(&sp.raw_span);
        v.push(span);
    }

    let mut multispan = MultiSpan::from_spans(v);

    for ErrorLabel { msg, span: sp } in &error.labels {
        let span: Span = from_raw_span(&sp.raw_span);
        multispan.push_span_label(span, msg.clone());
    }

    compiler.session().parse_sess.span_diagnostic.span_err(multispan, &error.msg);
}

fn report_chosen_triggers(compiler: &Compiler, chosen: &vir::context::ChosenTriggers) {
    let span: Span = from_raw_span(&chosen.span.raw_span);
    let msg = "automatically chose triggers for this expression:";
    compiler.session().parse_sess.span_diagnostic.span_note_without_error(span, msg);
    for (n, trigger) in chosen.triggers.iter().enumerate() {
        let spans = MultiSpan::from_spans(
            trigger.iter().map(|(s, _)| from_raw_span(&s.raw_span)).collect(),
        );
        let msg = format!("  trigger {} of {}:", n + 1, chosen.triggers.len());
        compiler.session().parse_sess.span_diagnostic.span_note_without_error(spans, &msg);
    }
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

            vir_crate: None,
            air_no_span: None,
            inferred_modes: None,
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

    /// Check the result of a query that was based on user input.
    /// Success/failure will (eventually) be communicated back to the user.
    fn check_result_validity(
        &mut self,
        compiler: &Compiler,
        air_context: &mut air::context::Context,
        assign_map: &HashMap<*const air::ast::Span, HashSet<Arc<std::string::String>>>,
        snap_map: &Vec<(air::ast::Span, SnapPos)>,
        command: &Command,
    ) {
        let is_check_valid = matches!(**command, CommandX::CheckValid(_));
        let mut result = air_context.command(&command);
        let mut is_first_check = true;
        let mut checks_remaining = self.args.multiple_errors;
        let mut only_check_earlier = false;
        loop {
            match result {
                ValidityResult::Valid => {
                    if is_check_valid && is_first_check {
                        self.count_verified += 1;
                    }
                    break;
                }
                ValidityResult::TypeError(err) => {
                    panic!("internal error: generated ill-typed AIR code: {}", err);
                }
                ValidityResult::Invalid(air_model, error) => {
                    if is_first_check {
                        self.count_errors += 1;
                    }
                    report_error(compiler, &error);

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

                    self.errors.push(errors);
                    if self.args.debug {
                        let mut debugger = Debugger::new(
                            air_model,
                            assign_map,
                            snap_map,
                            compiler.session().source_map(),
                        );
                        debugger.start_shell(air_context);
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

                    result = air_context.check_valid_again(only_check_earlier);
                }
                ValidityResult::UnexpectedSmtOutput(err) => {
                    panic!("unexpected SMT output: {}", err);
                }
            }
        }

        if is_check_valid {
            air_context.finish_query();
        }
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
            Self::check_internal_result(air_context.command(&command));
            let time1 = Instant::now();
            self.time_air += time1 - time0;
        }
    }

    fn run_commands_queries(
        &mut self,
        compiler: &Compiler,
        air_context: &mut air::context::Context,
        commands: &Vec<Command>,
        assign_map: &HashMap<*const air::ast::Span, HashSet<Arc<String>>>,
        snap_map: &Vec<(air::ast::Span, SnapPos)>,
        comment: &str,
    ) {
        if commands.len() > 0 {
            air_context.blank_line();
            air_context.comment(comment);
        }
        for command in commands.iter() {
            let time0 = Instant::now();
            self.check_result_validity(compiler, air_context, assign_map, snap_map, &command);
            let time1 = Instant::now();
            self.time_air += time1 - time0;
        }
    }

    // Verify a single module
    fn verify_module(
        &mut self,
        compiler: &Compiler,
        krate: &Krate,
        air_context: &mut air::context::Context,
        ctx: &mut vir::context::Ctx,
    ) -> Result<(), VirErr> {
        let module = &ctx.module();
        air_context.blank_line();
        air_context.comment("Fuel");
        for command in ctx.fuel().iter() {
            Self::check_internal_result(air_context.command(&command));
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
        self.run_commands(air_context, &datatype_commands, &("Datatypes".to_string()));

        // Declare the function symbols
        for function in &krate.functions {
            ctx.module_for_chosen_triggers = function.x.visibility.owning_module.clone();
            if !is_visible_to(&function.x.visibility, module) || function.x.attrs.is_decrease_by {
                continue;
            }
            let commands = vir::func_to_air::func_name_to_air(ctx, &function)?;
            self.run_commands(
                air_context,
                &commands,
                &("Function-Decl ".to_string() + &fun_as_rust_dbg(&function.x.name)),
            );
        }
        ctx.module_for_chosen_triggers = None;

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

        // For spec functions, check termination and declare consequence axioms.
        // For proof/exec functions, declare requires/ensures.
        // Declare them in SCC (strongly connected component) sorted order so that
        // termination checking precedes consequence axioms for each SCC.
        let mut fun_decls: HashMap<Fun, Commands> = HashMap::new();
        for scc in &ctx.global.func_call_sccs.clone() {
            let scc_nodes = ctx.global.func_call_graph.get_scc_nodes(scc);
            let mut scc_fun_nodes: Vec<Fun> = Vec::new();
            for node in scc_nodes.into_iter() {
                match node {
                    Node::Fun(f) => scc_fun_nodes.push(f),
                    _ => {}
                }
            }
            // Check termination
            for f in scc_fun_nodes.iter() {
                if !funs.contains_key(f) {
                    continue;
                }
                let (function, vis_abs) = &funs[f];

                ctx.module_for_chosen_triggers = function.x.visibility.owning_module.clone();
                let (decl_commands, check_commands) = vir::func_to_air::func_decl_to_air(
                    ctx,
                    &function,
                    is_visible_to(&vis_abs, module),
                )?;
                fun_decls.insert(f.clone(), decl_commands);
                ctx.module_for_chosen_triggers = None;

                if Some(module.clone()) != function.x.visibility.owning_module {
                    continue;
                }
                self.run_commands_queries(
                    compiler,
                    air_context,
                    &check_commands,
                    &HashMap::new(),
                    &vec![],
                    &("Function-Termination ".to_string() + &fun_as_rust_dbg(f)),
                );
            }

            // Declare consequence axioms
            for f in scc_fun_nodes.iter() {
                if !funs.contains_key(f) {
                    continue;
                }
                let decl_commands = &fun_decls[f];
                self.run_commands(
                    air_context,
                    &decl_commands,
                    &("Function-Axioms ".to_string() + &fun_as_rust_dbg(f)),
                );
                funs.remove(f);
            }
        }
        assert!(funs.len() == 0);

        // Create queries to check the validity of proof/exec function bodies
        for function in &krate.functions {
            ctx.module_for_chosen_triggers = function.x.visibility.owning_module.clone();
            if Some(module.clone()) != function.x.visibility.owning_module {
                continue;
            }
            let (commands, snap_map) = vir::func_to_air::func_def_to_air(ctx, &function)?;
            self.run_commands_queries(
                compiler,
                air_context,
                &commands,
                &HashMap::new(),
                &snap_map,
                &("Function-Def ".to_string() + &fun_as_rust_dbg(&function.x.name)),
            );
        }
        ctx.module_for_chosen_triggers = None;

        Ok(())
    }

    // Verify one or more modules in a crate
    fn verify_crate_inner(&mut self, compiler: &Compiler) -> Result<(), VirErr> {
        let krate = self.vir_crate.as_ref().expect("vir_crate should be initialized");
        let air_no_span = self.air_no_span.as_ref().expect("air_no_span should be initialized");
        let inferred_modes =
            self.inferred_modes.take().expect("inferred_modes should be initialized");

        #[cfg(debug_assertions)]
        vir::check_ast_flavor::check_krate(&krate);

        let mut air_context = air::context::Context::new(air::smt_manager::SmtManager::new());
        air_context.set_ignore_unexpected_smt(self.args.ignore_unexpected_smt);
        air_context.set_debug(self.args.debug);

        if let Some(filename) = &self.args.log_air_initial {
            let file = File::create(filename).expect(&format!("could not open file {}", filename));
            air_context.set_air_initial_log(Box::new(file));
        }
        if let Some(filename) = &self.args.log_air_final {
            let file = File::create(filename).expect(&format!("could not open file {}", filename));
            air_context.set_air_final_log(Box::new(file));
        }
        if let Some(filename) = &self.args.log_smt {
            let file = File::create(filename).expect(&format!("could not open file {}", filename));
            air_context.set_smt_log(Box::new(file));
        }

        // air_recommended_options causes AIR to apply a preset collection of Z3 options
        air_context.set_z3_param("air_recommended_options", "true");
        air_context.set_rlimit(self.args.rlimit * 1000000);
        for (option, value) in self.args.smt_options.iter() {
            air_context.set_z3_param(&option, &value);
        }

        let mut global_ctx =
            vir::context::GlobalCtx::new(&krate, air_no_span.clone(), inferred_modes)?;
        vir::recursive_types::check_traits(&krate, &global_ctx)?;
        let krate = vir::ast_simplify::simplify_krate(&mut global_ctx, &krate)?;

        if let Some(filename) = &self.args.log_vir_simple {
            let mut file =
                File::create(filename).expect(&format!("could not open file {}", filename));
            vir::printer::write_krate(&mut file, &krate);
        }

        #[cfg(debug_assertions)]
        vir::check_ast_flavor::check_krate_simplified(&krate);

        air_context.blank_line();
        air_context.comment("Prelude");
        for command in vir::context::Ctx::prelude().iter() {
            Self::check_internal_result(air_context.command(&command));
        }

        let verify_entire_crate = !self.args.verify_root && self.args.verify_module.is_none();
        let mut verified_modules = HashSet::new();
        for module in &krate.module_ids {
            let module_name =
                module.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("::");
            if module.segments.len() == 0 {
                if !verify_entire_crate && !self.args.verify_root {
                    continue;
                }
                println!("Verifying root module");
            } else {
                if !verify_entire_crate && self.args.verify_module != Some(module_name.clone()) {
                    continue;
                }
                let is_pervasive =
                    module_name.starts_with("pervasive::") || module_name == "pervasive";
                if !self.args.verify_pervasive && is_pervasive {
                    continue;
                }
                println!("Verifying module {}", &module_name);
            }
            air_context.blank_line();
            air_context.comment(&("MODULE '".to_string() + &module_name + "'"));
            air_context.push();
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
            if let Some(filename) = &self.args.log_vir_poly {
                let module_name_os = if module.segments.len() > 0 {
                    module.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("__")
                } else {
                    "root".to_string()
                };
                let mut file = File::create(filename.to_string() + "-" + &module_name_os)
                    .expect(&format!("could not open file {}", filename));
                vir::printer::write_krate(&mut file, &poly_krate);
            }
            self.verify_module(compiler, &poly_krate, &mut air_context, &mut ctx)?;
            verified_modules.insert(module.clone());
            global_ctx = ctx.free();
            air_context.pop();
        }

        // Log/display triggers
        if let Some(filename) = &self.args.log_triggers {
            let mut file =
                File::create(filename).expect(&format!("could not open file {}", filename));
            let chosen_triggers = global_ctx.get_chosen_triggers();
            for triggers in chosen_triggers {
                writeln!(file, "{:#?}", triggers)
                    .expect(&format!("error writing to file {}", filename));
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
            compiler.session().parse_sess.span_diagnostic.span_note_without_error(span, &msg);
        }

        let (time_smt_init, time_smt_run) = air_context.get_time();
        self.time_smt_init = time_smt_init;
        self.time_smt_run = time_smt_run;
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

    fn construct_vir_crate<'tcx>(&mut self, tcx: TyCtxt<'tcx>) -> Result<bool, VirErr> {
        let autoviewed_call_typs = Arc::new(std::sync::Mutex::new(HashMap::new()));
        let _ = tcx.formal_verifier_callback.replace(Some(Box::new(crate::typecheck::Typecheck {
            int_ty_id: None,
            nat_ty_id: None,
            exprs_in_spec: Arc::new(std::sync::Mutex::new(HashSet::new())),
            autoviewed_calls: HashSet::new(),
            autoviewed_call_typs: autoviewed_call_typs.clone(),
        })));
        match rustc_typeck::check_crate(tcx) {
            Ok(()) => {}
            Err(rustc_errors::ErrorReported {}) => {
                return Ok(false);
            }
        }
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
        });

        // Convert HIR -> VIR
        let time1 = Instant::now();
        let vir_crate = crate::rust_to_vir::crate_to_vir(&ctxt)?;
        let time2 = Instant::now();

        if let Some(filename) = &self.args.log_vir {
            let mut file =
                File::create(filename).expect(&format!("could not open file {}", filename));
            vir::printer::write_krate(&mut file, &vir_crate);
        }
        vir::well_formed::check_crate(&vir_crate)?;
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
                if let Err(err) = verifier.construct_vir_crate(tcx) {
                    report_error(compiler, &err);
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
                        report_error(compiler, &err);
                        verifier.encountered_vir_error = true;
                    }
                }
            }
        });
        rustc_driver::Compilation::Stop
    }
}
