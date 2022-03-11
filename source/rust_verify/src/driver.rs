use crate::erase::CompilerCallbacks;
use crate::verifier::{Verifier, VerifierCallbacks};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

fn mk_compiler<'a, 'b, F>(
    rustc_args: &'a [String],
    verifier: &'b mut (dyn rustc_driver::Callbacks + Send),
    file_loader: &F,
) -> rustc_driver::RunCompiler<'a, 'b>
where
    F: 'static + rustc_span::source_map::FileLoader + Send + Sync + Clone,
{
    let mut compiler = rustc_driver::RunCompiler::new(rustc_args, verifier);
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

    let vir_ready = Arc::new((Mutex::new(None), Condvar::new()));
    let now_verify = Arc::new((Mutex::new(None), Condvar::new()));
    let verifier = Arc::new(Mutex::new(verifier));
    let compiler_thread = {
        let mut verifier_callbacks = VerifierCallbacks {
            verifier: verifier.clone(),
            vir_ready: vir_ready.clone(),
            now_verify: now_verify.clone(),
        };
        let vir_ready = vir_ready.clone();
        let rustc_args = rustc_args.clone();
        let file_loader = file_loader.clone();
        // Run verifier callback to build VIR tree and run verifier
        std::thread::spawn(move || {
            let verifier_compiler = mk_compiler(&rustc_args, &mut verifier_callbacks, &file_loader);
            let status = verifier_compiler.run();
            match status {
                Ok(_) => Ok(()),
                Err(_) => {
                    let (vir_ready, cvar) = &*vir_ready;
                    *vir_ready.lock().expect("vir_ready mutex") = Some(true);
                    cvar.notify_one();
                    Err(())
                }
            }
        })
    };

    let compiler_err = {
        let (lock, cvar) = &*vir_ready;
        let mut vir_ready = lock.lock().expect("vir_ready mutex");
        while vir_ready.is_none() {
            vir_ready = cvar.wait(vir_ready).expect("cvar wait");
        }
        vir_ready.unwrap()
    };

    let time1 = Instant::now();

    if let Err(()) = {
        let verifier = verifier.lock().unwrap();
        if compiler_err {
            Err(())
        } else if !verifier.args.no_lifetime {
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
    } {
        {
            let (now_verify, cvar) = &*now_verify;
            *now_verify.lock().expect("now_verify mutex") = Some(true);
            cvar.notify_one();
        }
        let _status = compiler_thread.join().expect("join compiler thread");
        let verifier = Arc::try_unwrap(verifier)
            .map_err(|_| ())
            .expect("only one reference to the verifier expected")
            .into_inner()
            .expect("valid Mutex for verifier");
        return (verifier, Err(()));
    }

    let time2 = Instant::now();

    {
        let (now_verify, cvar) = &*now_verify;
        *now_verify.lock().expect("now_verify mutex") = Some(false);
        cvar.notify_one();
    }
    let status = compiler_thread.join().expect("join compiler thread");

    let time3 = Instant::now();

    let verifier = Arc::try_unwrap(verifier)
        .map_err(|_| ())
        .expect("only one Arc reference to the verifier")
        .into_inner()
        .expect("valid Mutex for verifier");

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
