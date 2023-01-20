use crate::erase::ErasureHints;
use crate::lifetime_emit::*;
use crate::lifetime_generate::*;
use crate::util::{error, to_air_span};
use crate::verifier::DiagnosticOutputBuffer;
use air::messages::{message_bare, Message, MessageLevel};
use rustc_hir::{AssocItemKind, Crate, ItemKind, OwnerNode};
use rustc_middle::ty::TyCtxt;
use serde::Deserialize;
use std::fs::File;
use std::io::Write;
use vir::ast::VirErr;

// Call Rust's mir_borrowck to check lifetimes of #[spec] and #[proof] code and variables
pub(crate) fn check<'tcx>(queries: &'tcx rustc_interface::Queries<'tcx>) {
    queries.global_ctxt().expect("global_ctxt").peek_mut().enter(|tcx| {
        let hir = tcx.hir();
        let krate = hir.krate();
        for owner in &krate.owners {
            if let Some(owner) = owner {
                match owner.node() {
                    OwnerNode::Item(item) => match &item.kind {
                        rustc_hir::ItemKind::Fn(..) => {
                            tcx.ensure().mir_borrowck(item.def_id);
                        }
                        ItemKind::Impl(impll) => {
                            for item in impll.items {
                                match item.kind {
                                    AssocItemKind::Fn { .. } => {
                                        tcx.ensure().mir_borrowck(item.id.def_id);
                                    }
                                    _ => {}
                                }
                            }
                        }
                        _ => {}
                    },
                    _ => (),
                }
            }
        }
    });
}

fn emit_check_tracked_lifetimes<'tcx>(
    tcx: TyCtxt<'tcx>,
    krate: &'tcx Crate<'tcx>,
    emit_state: &mut EmitState,
    erasure_hints: &ErasureHints,
) -> State {
    let gen_state =
        crate::lifetime_generate::gen_check_tracked_lifetimes(tcx, krate, erasure_hints);
    emit_state.writeln("#![allow(non_camel_case_types)]");
    emit_state.writeln("#![allow(unused_imports)]");
    emit_state.writeln("#![allow(unused_variables)]");
    emit_state.writeln("#![allow(unreachable_patterns)]");
    emit_state.writeln("#![allow(unused_parens)]");
    emit_state.writeln("#![allow(unused_braces)]");
    emit_state.writeln("#![allow(dead_code)]");
    emit_state.writeln("#![allow(unused_mut)]");
    emit_state.writeln("#[derive(Copy)] struct PhantomData<A> { a: A }");
    emit_state.writeln("impl<A> Clone for PhantomData<A> { fn clone(&self) -> Self { panic!() } }");
    emit_state.writeln("#[derive(Clone, Copy)] struct Ghost<A> { a: PhantomData<A> }");
    emit_state.writeln("struct Tracked<A> { a: PhantomData<A> }");
    emit_state.writeln("#[derive(Clone, Copy)] struct int;");
    emit_state.writeln("#[derive(Clone, Copy)] struct nat;");
    emit_state.writeln("fn op<A, B>(a: A) -> B { unimplemented!() }");
    for d in gen_state.datatype_decls.iter() {
        emit_datatype_decl(emit_state, d);
    }
    for f in gen_state.const_decls.iter() {
        emit_const_decl(emit_state, f);
    }
    for f in gen_state.fun_decls.iter() {
        emit_fun_decl(emit_state, f);
    }
    gen_state
}

struct LifetimeCallbacks {
    capture_output: std::sync::Arc<std::sync::Mutex<Vec<u8>>>,
}

impl rustc_driver::Callbacks for LifetimeCallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.diagnostic_output =
            rustc_session::DiagnosticOutput::Raw(Box::new(DiagnosticOutputBuffer {
                output: self.capture_output.clone(),
            }));
    }

    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        check(queries);
        rustc_driver::Compilation::Stop
    }
}

struct LifetimeFileLoader {
    rust_code: String,
}

impl LifetimeFileLoader {
    const FILENAME: &'static str = "dummyrs.rs";
}

impl rustc_span::source_map::FileLoader for LifetimeFileLoader {
    fn file_exists(&self, _path: &std::path::Path) -> bool {
        panic!("unexpected call to file_exists")
    }

    fn read_file(&self, path: &std::path::Path) -> Result<String, std::io::Error> {
        assert!(path.display().to_string() == Self::FILENAME.to_string());
        Ok(self.rust_code.clone())
    }
}

#[derive(Debug, Deserialize)]
struct DiagnosticSpan {
    line_start: usize,
    line_end: usize,
    column_start: usize,
    column_end: usize,
}

#[derive(Debug, Deserialize)]
struct Diagnostic {
    message: String,
    level: String,
    spans: Vec<DiagnosticSpan>,
}

pub(crate) fn check_tracked_lifetimes<'tcx>(
    tcx: TyCtxt<'tcx>,
    erasure_hints: &ErasureHints,
    lifetime_log_file: Option<File>,
) -> Result<Vec<Message>, VirErr> {
    let krate = tcx.hir().krate();
    let mut emit_state = EmitState::new();
    let gen_state = emit_check_tracked_lifetimes(tcx, krate, &mut emit_state, erasure_hints);
    let mut rust_code: String = String::new();
    for line in &emit_state.lines {
        rust_code.push_str(&line.text);
        rust_code.push('\n');
    }
    if let Some(mut file) = lifetime_log_file {
        write!(file, "{}", &rust_code).expect("error writing to lifetime log file");
    }
    let rustc_args = vec![
        "dummyexe".to_string(),
        LifetimeFileLoader::FILENAME.to_string(),
        "--error-format=json".to_string(),
    ];
    let capture_output = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let mut callbacks = LifetimeCallbacks { capture_output };
    let mut compiler = rustc_driver::RunCompiler::new(&rustc_args, &mut callbacks);
    compiler.set_file_loader(Some(Box::new(LifetimeFileLoader { rust_code })));
    let run = compiler.run();
    let bytes: &Vec<u8> = &*callbacks.capture_output.lock().expect("lock capture_output");
    let rust_output = std::str::from_utf8(bytes).unwrap().trim();
    let mut msgs: Vec<Message> = Vec::new();
    if rust_output.len() > 0 {
        for ss in rust_output.split("\n") {
            let diag: Diagnostic = serde_json::from_str(ss).expect("serde_json from_str");
            if diag.level == "failure-note" {
                continue;
            }
            if diag.level == "warning" {
                dbg!("internal error: unexpected warning");
                dbg!(diag);
                continue;
            }
            assert!(diag.level == "error");
            let msg_text = gen_state.unmangle_names(&diag.message);
            let mut msg = message_bare(MessageLevel::Error, &msg_text);
            for dspan in &diag.spans {
                let span = emit_state.get_span(
                    dspan.line_start - 1,
                    dspan.column_start - 1,
                    dspan.line_end - 1,
                    dspan.column_end - 1,
                );
                msg = msg.primary_span(&to_air_span(span));
            }
            msgs.push(msg);
        }
    }
    if msgs.len() == 0 && run.is_err() { Err(error("lifetime checking failed")) } else { Ok(msgs) }
}
