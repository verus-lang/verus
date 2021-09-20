use crate::config::Args;
use crate::context::{Context, ErasureInfo};
use crate::model::Model;
use crate::unsupported;
use crate::util::from_raw_span;
use air::ast::{Command, CommandX, SpanOption};
use air::context::ValidityResult;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::SourceMap;
use rustc_span::{CharPos, FileName, MultiSpan, Span};
use std::fs::File;
use std::io::Write;
use vir::ast::{Krate, Path, VirErr, VirErrX, Visibility};
use vir::ast_util::path_to_string;
use vir::def::SnapPos;
use vir::model::Model as VModel;

pub struct Verifier {
    pub encountered_vir_error: bool,
    pub count_verified: u64,
    // Two error slots that can be filled in if needed.  TODO: Convert to list/vec
    pub errors: Vec<(Option<ErrorSpan>, Option<ErrorSpan>)>,
    args: Args,
    pub test_capture_output: Option<std::sync::Arc<std::sync::Mutex<Vec<u8>>>>,
    pub erasure_hints: Option<crate::erase::ErasureHints>,
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
    fn new_from_air_span(source_map: &SourceMap, air_span: &air::ast::Span) -> Self {
        let span: Span = from_raw_span(&air_span.raw_span);
        let filename: String = match source_map.span_to_filename(span) {
            FileName::Real(rfn) => rfn
                .local_path()
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
            description: air_span.description.clone(),
            span_data: (filename, (start.line, start.col), (end.line, end.col)),
            test_span_line: test_span_line,
        }
    }
}

fn report_vir_error(compiler: &Compiler, vir_err: VirErr) {
    let span: Span = from_raw_span(&vir_err.span.raw_span);
    let multispan = MultiSpan::from_span(span);
    match &vir_err.x {
        VirErrX::Str(msg) => {
            compiler.session().parse_sess.span_diagnostic.span_err(multispan, &msg);
        }
    }
}

fn report_verify_error(compiler: &Compiler, span1: &SpanOption, span2: &SpanOption) {
    match &**span1 {
        None => {
            panic!("internal error: found Error with no span")
        }
        Some(air::ast::Span { description, raw_span, .. }) => {
            let msg = description.as_ref().unwrap_or(&"assertion failed".to_string()).clone();
            let span: Span = from_raw_span(raw_span);
            let mut multispan = MultiSpan::from_span(span);
            match &**span2 {
                None => {}
                Some(air::ast::Span { description, raw_span, .. }) => {
                    let msg =
                        description.as_ref().unwrap_or(&"related location".to_string()).clone();
                    let span: Span = from_raw_span(raw_span);
                    multispan.push_span_label(span, msg);
                }
            }
            compiler.session().parse_sess.span_diagnostic.span_err(multispan, &msg);
        }
    }
}

fn report_chosen_triggers(
    compiler: &Compiler,
    air_span: &air::ast::Span,
    triggers: &Vec<Vec<String>>,
) {
    let span: Span = from_raw_span(&air_span.raw_span);
    let msg = format!("chosen triggers: {:#?}", triggers);
    compiler.session().parse_sess.span_diagnostic.span_note_without_error(span, &msg);
}

impl Verifier {
    pub fn new(args: Args) -> Verifier {
        Verifier {
            encountered_vir_error: false,
            count_verified: 0,
            errors: Vec::new(),
            args: args,
            test_capture_output: None,
            erasure_hints: None,
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
        snap_map: &Vec<(air::ast::Span, SnapPos)>,
        command: &Command,
        result: ValidityResult,
    ) {
        match result {
            ValidityResult::Valid => {
                if let CommandX::CheckValid(_) = **command {
                    self.count_verified += 1;
                }
            }
            ValidityResult::TypeError(err) => {
                panic!("internal error: generated ill-typed AIR code: {}", err);
            }
            ValidityResult::Invalid(air_model, span1, span2) => {
                report_verify_error(compiler, &span1, &span2);
                self.errors.push((
                    span1
                        .as_ref()
                        .as_ref()
                        .map(|x| ErrorSpan::new_from_air_span(compiler.session().source_map(), x)),
                    span2
                        .as_ref()
                        .as_ref()
                        .map(|x| ErrorSpan::new_from_air_span(compiler.session().source_map(), x)),
                ));
                if self.args.debug {
                    println!("Received AIR model: {}", air_model);
                    let vir_model = VModel::new(air_model);
                    let model = Model::new(vir_model, snap_map, compiler.session().source_map());
                    println!("Build Rust model: {}", model);
                }
            }
        }
    }

    // Can source_module see an item with target_visibility?
    fn is_visible_to(target_visibility: &Visibility, source_module: &Path) -> bool {
        let Visibility { owning_module, is_private } = target_visibility;
        match owning_module {
            _ if !is_private => true,
            None => true,
            Some(target) if target.len() > source_module.len() => false,
            // Child can access private item in parent, so check if target is parent:
            Some(target) => target[..] == source_module[..target.len()],
        }
    }

    fn run_commands(
        air_context: &mut air::context::Context,
        commands: &Vec<Command>,
        comment: &str,
    ) {
        if commands.len() > 0 {
            air_context.blank_line();
            air_context.comment(comment);
        }
        for command in commands.iter() {
            Self::check_internal_result(air_context.command(&command));
        }
    }

    fn run_commands_queries(
        &mut self,
        compiler: &Compiler,
        air_context: &mut air::context::Context,
        commands: &Vec<Command>,
        snap_map: &Vec<(air::ast::Span, SnapPos)>,
        comment: &str,
    ) {
        if commands.len() > 0 {
            air_context.blank_line();
            air_context.comment(comment);
        }
        for command in commands.iter() {
            self.check_result_validity(compiler, snap_map, &command, air_context.command(&command));
        }
    }

    // Verify a single module
    fn verify_module(
        &mut self,
        compiler: &Compiler,
        krate: &Krate,
        air_context: &mut air::context::Context,
        ctx: &vir::context::Ctx,
        module: &Path,
    ) -> Result<(), VirErr> {
        air_context.blank_line();
        air_context.comment("Fuel");
        for command in ctx.fuel().iter() {
            Self::check_internal_result(air_context.command(&command));
        }

        let datatype_commands = vir::datatype_to_air::datatypes_to_air(
            ctx,
            module,
            &krate
                .datatypes
                .iter()
                .cloned()
                .filter(|d| Verifier::is_visible_to(&d.x.visibility, module))
                .collect(),
        );
        Self::run_commands(air_context, &datatype_commands, &("Datatypes".to_string()));

        // Declare the function symbols
        for function in &krate.functions {
            if !Verifier::is_visible_to(&function.x.visibility, module) {
                continue;
            }
            let commands = vir::func_to_air::func_name_to_air(&ctx, &function)?;
            Self::run_commands(
                air_context,
                &commands,
                &("Function-Decl ".to_string() + &path_to_string(&function.x.path)),
            );
        }

        // Declare consequence axioms for spec functions, and function signatures for proof/exec functions
        // Also check termination
        for function in &krate.functions {
            let vis = function.x.visibility.clone();
            let vis = Visibility { is_private: vis.is_private || function.x.is_abstract, ..vis };
            if !Verifier::is_visible_to(&vis, module) {
                continue;
            }
            let (decl_commands, check_commands) =
                vir::func_to_air::func_decl_to_air(&ctx, &function)?;
            Self::run_commands(
                air_context,
                &decl_commands,
                &("Function-Axioms ".to_string() + &path_to_string(&function.x.path)),
            );

            // Check termination
            if Some(module.clone()) != function.x.visibility.owning_module {
                continue;
            }
            self.run_commands_queries(
                compiler,
                air_context,
                &check_commands,
                &vec![],
                &("Function-Termination ".to_string() + &path_to_string(&function.x.path)),
            );
        }

        // Create queries to check the validity of proof/exec function bodies
        for function in &krate.functions {
            if Some(module.clone()) != function.x.visibility.owning_module {
                continue;
            }
            let (commands, snap_map) = vir::func_to_air::func_def_to_air(&ctx, &function)?;
            self.run_commands_queries(
                compiler,
                air_context,
                &commands,
                &snap_map,
                &("Function-Def ".to_string() + &path_to_string(&function.x.path)),
            );
        }

        Ok(())
    }

    // Verify one or more modules in a crate
    fn verify_crate(&mut self, compiler: &Compiler, krate: &Krate) -> Result<(), VirErr> {
        let mut air_context = air::context::Context::new(air::smt_manager::SmtManager::new());
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

        let ctx = vir::context::Ctx::new(&krate, self.args.debug)?;

        air_context.blank_line();
        air_context.comment("Prelude");
        for command in ctx.prelude().iter() {
            Self::check_internal_result(air_context.command(&command));
        }

        let verify_entire_crate = !self.args.verify_root && self.args.verify_module.is_none();
        for module in &krate.module_ids {
            let module_name = module.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("::");
            if module.len() == 0 {
                if !verify_entire_crate && !self.args.verify_root {
                    continue;
                }
                println!("Verifying root module");
            } else {
                if !verify_entire_crate && self.args.verify_module != Some(module_name.clone()) {
                    continue;
                }
                println!("Verifying module {}", &module_name);
            }
            air_context.blank_line();
            air_context.comment(&("MODULE '".to_string() + &module_name + "'"));
            air_context.push();
            self.verify_module(compiler, krate, &mut air_context, &ctx, module)?;
            air_context.pop();
        }

        if let Some(filename) = &self.args.log_triggers {
            let mut file =
                File::create(filename).expect(&format!("could not open file {}", filename));
            let chosen_triggers = ctx.get_chosen_triggers();
            for triggers in chosen_triggers {
                writeln!(file, "{:#?}", triggers)
                    .expect(&format!("error writing to file {}", filename));
            }
        }
        if self.args.show_triggers {
            let chosen_triggers = ctx.get_chosen_triggers();
            for (span, triggers) in chosen_triggers {
                report_chosen_triggers(compiler, &span, &triggers);
            }
        }

        Ok(())
    }

    fn run<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Result<bool, VirErr> {
        let _ = tcx.formal_verifier_callback.replace(Some(Box::new(crate::typecheck::Typecheck {
            int_ty_id: None,
            nat_ty_id: None,
        })));
        match rustc_typeck::check_crate(tcx) {
            Ok(()) => {}
            Err(rustc_errors::ErrorReported {}) => {
                return Ok(false);
            }
        }

        let hir = tcx.hir();
        let erasure_info = ErasureInfo {
            resolved_calls: vec![],
            condition_modes: vec![],
            external_functions: vec![],
        };
        let erasure_info = std::rc::Rc::new(std::cell::RefCell::new(erasure_info));
        let ctxt = Context { tcx, krate: hir.krate(), erasure_info };
        let vir_crate = crate::rust_to_vir::crate_to_vir(&ctxt)?;
        if let Some(filename) = &self.args.log_vir {
            let mut file =
                File::create(filename).expect(&format!("could not open file {}", filename));
            for datatype in vir_crate.datatypes.iter() {
                writeln!(&mut file, "datatype {:?} @ {:?}", datatype.x.path, datatype.span)
                    .expect("cannot write to vir file");
                writeln!(&mut file, "{:?}", datatype.x.variants).expect("cannot write to vir file");
                writeln!(&mut file).expect("cannot write to vir file");
            }
            for func in vir_crate.functions.iter() {
                writeln!(&mut file, "fn {} @ {:?}", path_to_string(&func.x.path), func.span)
                    .expect("cannot write to vir file");
                for param in func.x.params.iter() {
                    writeln!(
                        &mut file,
                        "parameter {}: {:?} @ {:?}",
                        param.x.name, param.x.typ, param.span
                    )
                    .expect("cannot write to vir file");
                }
                writeln!(&mut file, "body {:#?}", func.x.body).expect("cannot write to vir file");
                writeln!(&mut file).expect("cannot write to vir file");
            }
        }
        vir::well_formed::check_crate(&vir_crate)?;
        let erasure_modes = vir::modes::check_crate(&vir_crate)?;
        if !self.args.no_verify {
            self.verify_crate(&compiler, &vir_crate)?;
        }
        let erasure_info = ctxt.erasure_info.borrow();
        let resolved_calls = erasure_info.resolved_calls.clone();
        let external_functions = erasure_info.external_functions.clone();
        let erasure_hints = crate::erase::ErasureHints {
            vir_crate,
            resolved_calls,
            erasure_modes,
            external_functions,
        };
        self.erasure_hints = Some(erasure_hints);
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

impl rustc_driver::Callbacks for Verifier {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        if let Some(target) = &self.test_capture_output {
            config.diagnostic_output =
                rustc_session::DiagnosticOutput::Raw(Box::new(DiagnosticOutputBuffer {
                    output: target.clone(),
                }));
        }
    }

    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        let _result = queries.global_ctxt().expect("global_ctxt").peek_mut().enter(|tcx| {
            queries.expansion().expect("expansion");
            match self.run(compiler, tcx) {
                Ok(true) => {}
                Ok(false) => {}
                Err(err) => {
                    report_vir_error(compiler, err);
                    self.encountered_vir_error = true;
                }
            }
        });
        rustc_driver::Compilation::Stop
    }
}
