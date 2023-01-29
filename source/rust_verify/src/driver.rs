use crate::erase::CompilerCallbacksEraseAst;
use crate::util::signalling;
use crate::verifier::{Verifier, VerifierCallbacksEraseAst, VerifierCallbacksEraseMacro};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

fn mk_compiler<'a, 'b>(
    rustc_args: &'a [String],
    verifier: &'b mut (dyn rustc_driver::Callbacks + Send),
    file_loader: Box<dyn 'static + rustc_span::source_map::FileLoader + Send + Sync>,
) -> rustc_driver::RunCompiler<'a, 'b> {
    let mut compiler = rustc_driver::RunCompiler::new(rustc_args, verifier);
    compiler.set_file_loader(Some(file_loader));
    compiler
}

fn run_compiler<'a, 'b>(
    mut rustc_args: Vec<String>,
    syntax_macro: bool,
    erase_ghost: bool,
    verifier: &'b mut (dyn rustc_driver::Callbacks + Send),
    file_loader: Box<dyn 'static + rustc_span::source_map::FileLoader + Send + Sync>,
) -> Result<(), rustc_errors::ErrorReported> {
    crate::config::enable_default_features(&mut rustc_args, syntax_macro, erase_ghost);
    mk_compiler(&rustc_args, verifier, file_loader).run()
}

fn print_verification_results(verifier: &Verifier) {
    if !verifier.encountered_vir_error {
        println!(
            "verification results:: verified: {} errors: {}",
            verifier.count_verified, verifier.count_errors
        );
    }
}

pub struct CompilerCallbacksEraseMacro {
    pub lifetimes_only: bool,
    pub test_capture_output: Option<std::sync::Arc<std::sync::Mutex<Vec<u8>>>>,
}

impl rustc_driver::Callbacks for CompilerCallbacksEraseMacro {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        if let Some(target) = &self.test_capture_output {
            config.diagnostic_output = rustc_session::DiagnosticOutput::Raw(Box::new(
                crate::verifier::DiagnosticOutputBuffer { output: target.clone() },
            ));
        }
    }

    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        if self.lifetimes_only {
            crate::lifetime::check(queries);
            rustc_driver::Compilation::Stop
        } else {
            rustc_driver::Compilation::Continue
        }
    }
}

pub struct Stats {
    pub time_verify: Duration,
    pub time_lifetime: Duration,
    pub time_compile: Duration,
    pub time_erasure: Duration,
}

pub(crate) fn run_with_erase_macro_compile(
    mut rustc_args: Vec<String>,
    file_loader: Box<dyn 'static + rustc_span::source_map::FileLoader + Send + Sync>,
    compile: bool,
    test_capture_output: Option<std::sync::Arc<std::sync::Mutex<Vec<u8>>>>,
) -> Result<(), rustc_errors::ErrorReported> {
    let mut callbacks =
        CompilerCallbacksEraseMacro { lifetimes_only: !compile, test_capture_output };
    rustc_args.extend(["--cfg", "verus_macro_erase_ghost"].map(|s| s.to_string()));
    run_compiler(rustc_args, true, true, &mut callbacks, file_loader)
}

fn run_with_erase_macro<F>(
    verifier: Verifier,
    rustc_args: Vec<String>,
    file_loader: F,
) -> (Verifier, Result<Stats, ()>)
where
    F: 'static + rustc_span::source_map::FileLoader + Send + Sync + Clone,
{
    let time0 = Instant::now();

    // Build VIR and run verification
    let mut verifier_callbacks = VerifierCallbacksEraseMacro {
        verifier,
        lifetime_start_time: None,
        rustc_args: rustc_args.clone(),
        file_loader: Some(Box::new(file_loader.clone())),
    };
    let status = run_compiler(
        rustc_args.clone(),
        true,
        false,
        &mut verifier_callbacks,
        Box::new(file_loader.clone()),
    );
    if !verifier_callbacks.verifier.encountered_vir_error {
        print_verification_results(&verifier_callbacks.verifier);
    }
    if status.is_err() || verifier_callbacks.verifier.encountered_vir_error {
        return (verifier_callbacks.verifier, Err(()));
    }
    let VerifierCallbacksEraseMacro { verifier, lifetime_start_time, .. } = verifier_callbacks;
    let time1 = lifetime_start_time.expect("lifetime_start_time");
    let time2 = Instant::now();

    // Run borrow checker and compiler with #[exec] (not #[proof])
    if let Err(_) = run_with_erase_macro_compile(
        rustc_args,
        Box::new(file_loader),
        verifier.args.compile,
        verifier.test_capture_output.clone(),
    ) {
        return (verifier, Err(()));
    }

    let time3 = Instant::now();
    (
        verifier,
        Ok(Stats {
            time_verify: time1 - time0,
            time_lifetime: time2 - time1,
            time_compile: time3 - time2,
            time_erasure: Duration::new(0, 0),
        }),
    )
}

fn run_with_erase_ast<F>(
    verifier: Verifier,
    rustc_args: Vec<String>,
    file_loader: F,
) -> (Verifier, Result<Stats, ()>)
where
    F: 'static + rustc_span::source_map::FileLoader + Send + Sync + Clone,
{
    let time0 = Instant::now();
    let mut time_erasure1 = Duration::new(0, 0);
    let mut time_erasure2 = Duration::new(0, 0);

    // In order to run borrowck on proof and exec code _before_ lowering to AIR and running Z3,
    // we start the first instance of rustc, pause it after expansion to generate VIR, then keep
    // the rustc thread waiting to maintain its state for VIR->AIR and to report errors from Z3.

    // Signal from the rustc thread to this thread that expansion and HIR->VIR are complete
    let (vir_ready_s, vir_ready_d) = signalling::signal();
    // Signal from this thread to the rustc thread that we've run borrowck (on a separate instance
    // of rustc) and it's now time to lower to AIR and run Z3
    let (now_verify_s, now_verify_d) = signalling::signal();

    let verifier = Arc::new(Mutex::new(verifier));
    let compiler_thread = {
        let mut verifier_callbacks = VerifierCallbacksEraseAst {
            verifier: verifier.clone(),
            vir_ready: vir_ready_s.clone(),
            now_verify: now_verify_d,
        };
        let rustc_args = rustc_args.clone();
        let file_loader = file_loader.clone();
        // Start rustc in a separate thread: run verifier callback to build VIR tree and run verifier
        std::thread::spawn(move || {
            let status = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                run_compiler(
                    rustc_args,
                    false,
                    false,
                    &mut verifier_callbacks,
                    Box::new(file_loader),
                )
            }));
            match status {
                Ok(Ok(_)) => Ok(()),
                _ => {
                    vir_ready_s.signal(true);
                    Err(())
                }
            }
        })
    };

    let compiler_err = vir_ready_d.wait();

    let time1 = Instant::now();

    if let Err(()) = {
        if compiler_err {
            Err(())
        } else {
            verifier.lock().map_err(|_| ()).and_then(|verifier| {
                if !verifier.args.no_lifetime {
                    // Run borrow checker with both #[exec] and #[proof]
                    let erasure_hints = verifier.erasure_hints.clone().expect("erasure_hints");
                    let mut callbacks = CompilerCallbacksEraseAst {
                        erasure_hints,
                        lifetimes_only: true,
                        print: verifier.args.print_erased_spec,
                        test_capture_output: verifier.test_capture_output.clone(),
                        time_erasure: Arc::new(Mutex::new(Duration::new(0, 0))),
                    };
                    let status = run_compiler(
                        rustc_args.clone(),
                        false,
                        false,
                        &mut callbacks,
                        Box::new(file_loader.clone()),
                    );
                    time_erasure1 = *callbacks.time_erasure.lock().unwrap();
                    status.map_err(|_| ())
                } else {
                    Ok(())
                }
            })
        }
    } {
        now_verify_s.signal(true);
        let _status = compiler_thread.join().expect("join compiler thread");
        let verifier = Arc::try_unwrap(verifier)
            .map_err(|_| ())
            .expect("only one Arc reference to the verifier")
            .into_inner()
            .unwrap_or_else(|e| e.into_inner());
        return (verifier, Err(()));
    }

    let time2 = Instant::now();

    now_verify_s.signal(false);
    let status = compiler_thread.join().expect("join compiler thread");

    let time3 = Instant::now();

    let verifier = Arc::try_unwrap(verifier)
        .map_err(|_| ())
        .expect("only one Arc reference to the verifier")
        .into_inner()
        .unwrap_or_else(|e| e.into_inner());
    print_verification_results(&verifier);

    if let Err(()) = status {
        return (verifier, Err(()));
    }

    // Run borrow checker and compiler on #[exec] (if enabled)
    if verifier.args.compile {
        let erasure_hints =
            verifier.erasure_hints.clone().expect("erasure_hints should be initialized").clone();
        let mut callbacks = CompilerCallbacksEraseAst {
            erasure_hints,
            lifetimes_only: false,
            print: verifier.args.print_erased,
            test_capture_output: verifier.test_capture_output.clone(),
            time_erasure: Arc::new(Mutex::new(Duration::new(0, 0))),
        };
        run_compiler(rustc_args, false, false, &mut callbacks, Box::new(file_loader))
            .expect("RunCompiler.run() failed");
        time_erasure2 = *callbacks.time_erasure.lock().unwrap();
    }

    let time4 = Instant::now();
    (
        verifier,
        Ok(Stats {
            time_verify: (time1 - time0) + (time3 - time2),
            time_lifetime: time2 - time1 - time_erasure1,
            time_compile: time4 - time3 - time_erasure2,
            time_erasure: time_erasure1 + time_erasure2,
        }),
    )
}

pub fn run<F>(
    verifier: Verifier,
    rustc_args: Vec<String>,
    file_loader: F,
) -> (Verifier, Result<Stats, ()>)
where
    F: 'static + rustc_span::source_map::FileLoader + Send + Sync + Clone,
{
    match verifier.args.erasure {
        crate::config::Erasure::Ast => run_with_erase_ast(verifier, rustc_args, file_loader),
        crate::config::Erasure::Macro => run_with_erase_macro(verifier, rustc_args, file_loader),
    }
}
