use crate::erase::CompilerCallbacks;
use crate::verifier::Verifier;
use std::sync::{Arc, Mutex};
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
    verifier: &mut Verifier,
    rustc_args: &Vec<String>,
    file_loader: &F,
) -> Result<Stats, ()>
where
    F: 'static + rustc_span::source_map::FileLoader + Send + Sync + Clone,
{
    let time0 = Instant::now();
    let mut time_erasure1 = Duration::new(0, 0);
    let mut time_erasure2 = Duration::new(0, 0);

    // Run verifier callback to build VIR tree and run verifier
    let status = mk_compiler(rustc_args, verifier, file_loader).run();
    match status {
        Ok(_) => {}
        Err(_) => {
            return Err(());
        }
    }

    let time1 = Instant::now();

    // Run borrow checker with both #[exec] and #[proof]
    if !verifier.args.no_lifetime {
        let erasure_hints = verifier.erasure_hints.clone().expect("erasure_hints");
        let mut callbacks = CompilerCallbacks {
            erasure_hints,
            lifetimes_only: true,
            print: verifier.args.print_erased_spec,
            time_erasure: Arc::new(Mutex::new(Duration::new(0, 0))),
        };
        let status = mk_compiler(&rustc_args, &mut callbacks, file_loader).run();
        time_erasure1 = *callbacks.time_erasure.lock().unwrap();
        match status {
            Ok(_) => {}
            Err(_) => {
                return Err(());
            }
        }
    }

    let time2 = Instant::now();

    // Run borrow checker and compiler on #[exec] (if enabled)
    if verifier.args.compile {
        let erasure_hints = verifier.erasure_hints.clone().expect("erasure_hints").clone();
        let mut callbacks = CompilerCallbacks {
            erasure_hints,
            lifetimes_only: false,
            print: verifier.args.print_erased,
            time_erasure: Arc::new(Mutex::new(Duration::new(0, 0))),
        };
        mk_compiler(&rustc_args, &mut callbacks, file_loader)
            .run()
            .expect("RunCompiler.run() failed");
        time_erasure2 = *callbacks.time_erasure.lock().unwrap();
    }

    let time3 = Instant::now();
    Ok(Stats {
        time_verify: time1 - time0,
        time_lifetime: time2 - time1 - time_erasure1,
        time_compile: time3 - time2 - time_erasure2,
        time_erasure: time_erasure1 + time_erasure2,
    })
}
