use crate::erase::CompilerCallbacks;
use crate::util::signalling;
use crate::verifier::{Verifier, VerifierCallbacks};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

fn mk_compiler<'a, 'b, F>(
    rustc_args: &'a [String],
    verifier: &'b mut (dyn verus_rustc_driver::Callbacks + Send),
    file_loader: &F,
) -> verus_rustc_driver::RunCompiler<'a, 'b>
where
    F: 'static + rustc_span::source_map::FileLoader + Send + Sync + Clone,
{
    let mut compiler = verus_rustc_driver::RunCompiler::new(rustc_args, verifier);
    compiler.set_file_loader(Some(Box::new(file_loader.clone())));
    compiler
}

pub struct Stats {
    pub time_verify: Duration,
    pub time_lifetime: Duration,
    pub time_compile: Duration,
    pub time_erasure: Duration,
}

pub fn run<F>(
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
        let mut verifier_callbacks = VerifierCallbacks {
            verifier: verifier.clone(),
            vir_ready: vir_ready_s.clone(),
            now_verify: now_verify_d,
        };
        let rustc_args = rustc_args.clone();
        let file_loader = file_loader.clone();
        // Start rustc in a separate thread: run verifier callback to build VIR tree and run verifier
        std::thread::spawn(move || {
            let status = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let verifier_compiler =
                    mk_compiler(&rustc_args, &mut verifier_callbacks, &file_loader);
                verifier_compiler.run()
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
                    let mut callbacks = CompilerCallbacks {
                        erasure_hints,
                        lifetimes_only: true,
                        print: verifier.args.print_erased_spec,
                        time_erasure: Arc::new(Mutex::new(Duration::new(0, 0))),
                    };
                    let status = mk_compiler(&rustc_args, &mut callbacks, &file_loader).run();
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

    if let Err(()) = status {
        return (verifier, Err(()));
    }

    // Run borrow checker and compiler on #[exec] (if enabled)
    if verifier.args.compile {
        let erasure_hints =
            verifier.erasure_hints.clone().expect("erasure_hints should be initialized").clone();
        let mut callbacks = CompilerCallbacks {
            erasure_hints,
            lifetimes_only: false,
            print: verifier.args.print_erased,
            time_erasure: Arc::new(Mutex::new(Duration::new(0, 0))),
        };
        mk_compiler(&rustc_args, &mut callbacks, &file_loader)
            .run()
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
