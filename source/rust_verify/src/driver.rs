use crate::erase::CompilerCallbacks;
use crate::verifier::Verifier;

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

pub fn run<F>(verifier: &mut Verifier, rustc_args: &Vec<String>, file_loader: &F) -> Result<(), ()>
where
    F: 'static + rustc_span::source_map::FileLoader + Send + Sync + Clone,
{
    // Run verifier callback to build VIR tree and run verifier
    let status = mk_compiler(rustc_args, verifier, file_loader).run();
    match status {
        Ok(_) => {}
        Err(_) => {
            return Err(());
        }
    }

    // Run borrow checker with both #[code] and #[proof]
    if verifier.args.lifetime {
        let erasure_hints = verifier.erasure_hints.clone().expect("erasure_hints");
        let mut callbacks = CompilerCallbacks {
            erasure_hints,
            lifetimes_only: true,
            print: verifier.args.print_erased_spec,
        };
        let status = mk_compiler(&rustc_args, &mut callbacks, file_loader).run();
        match status {
            Ok(_) => {}
            Err(_) => {
                return Err(());
            }
        }
    }

    // Run borrow checker and compiler on #[code] (if enabled)
    if verifier.args.compile {
        let erasure_hints = verifier.erasure_hints.clone().expect("erasure_hints").clone();
        let mut callbacks = CompilerCallbacks {
            erasure_hints,
            lifetimes_only: false,
            print: verifier.args.print_erased,
        };
        mk_compiler(&rustc_args, &mut callbacks, file_loader)
            .run()
            .expect("RunCompiler.run() failed");
    }
    Ok(())
}
