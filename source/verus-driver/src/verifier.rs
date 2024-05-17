use std::time::Instant;

use rustc_driver::Callbacks;
use rustc_span::source_map::FileLoader;
use rustc_span::ErrorGuaranteed;

use rust_verify::driver::{is_verifying_entire_crate, CompilerCallbacksEraseMacro};
use rust_verify::verifier::{Verifier, VerifierCallbacksEraseMacro};

pub(crate) use rust_verify::lifetime::{lifetime_rustc_driver, LIFETIME_DRIVER_ARG};

pub(crate) trait CompilerRunner {
    fn run_compiler<C: Callbacks + Send>(
        &mut self,
        args: &[String],
        callbacks: &mut C,
    ) -> Result<(), ErrorGuaranteed>;
}

impl<F> CompilerRunner for F
where
    F: FnMut(&[String], &mut (dyn Callbacks + Send)) -> Result<(), ErrorGuaranteed>,
{
    fn run_compiler<C: Callbacks + Send>(
        &mut self,
        args: &[String],
        callbacks: &mut C,
    ) -> Result<(), ErrorGuaranteed> {
        self(args, callbacks)
    }
}

pub(crate) fn run<'a, T, U, V>(
    verus_inner_args: impl Iterator<Item = String>,
    rustc_args: &[String],
    mk_file_loader: U,
    mut compiler_runner: V,
) -> Result<(), ErrorGuaranteed>
where
    T: FileLoader + Send + Sync + 'static,
    U: Fn() -> T,
    V: CompilerRunner,
{
    let program_name_for_config = "TODO";

    let (parsed_verus_inner_args, unparsed) = rust_verify::config::parse_args_with_imports(
        &program_name_for_config.to_owned(),
        verus_inner_args,
        None,
    );

    assert!(
        unparsed.len() == 1 && unparsed[0] == program_name_for_config,
        "leftovers after parsing --verus-arg=<..> args: {:?}",
        unparsed
    );

    // TODO
    assert!(!parsed_verus_inner_args.version);

    let is_core = parsed_verus_inner_args.vstd == rust_verify::config::Vstd::IsCore;

    let verifier = Verifier::new(parsed_verus_inner_args);

    let mut rustc_args_for_verify = rustc_args.to_vec();
    extend_rustc_args_for_verify(&mut rustc_args_for_verify, is_core);

    let mut verifier_callbacks = VerifierCallbacksEraseMacro {
        verifier,
        rust_start_time: Instant::now(),
        rust_end_time: None,
        lifetime_start_time: None,
        lifetime_end_time: None,
        rustc_args: rustc_args_for_verify.clone(),
        file_loader: Some(Box::new(mk_file_loader())),
    };

    let status = compiler_runner.run_compiler(&rustc_args_for_verify, &mut verifier_callbacks);

    let VerifierCallbacksEraseMacro { verifier, .. } = verifier_callbacks;

    if !verifier.args.output_json && !verifier.encountered_vir_error {
        eprint!(
            "verification results:: {} verified, {} errors",
            verifier.count_verified, verifier.count_errors,
        );
        if !is_verifying_entire_crate(&verifier) {
            eprint!(" (partial verification with `--verify-*`)");
        }
        eprintln!();
    }

    if status.is_err() || verifier.encountered_vir_error {
        panic!("verification failed");
    }

    if !verifier.args.compile && verifier.args.no_lifetime {
        Ok(())
    } else {
        let mut rustc_args_for_compile = rustc_args.to_vec();
        extend_rustc_args_for_compile(&mut rustc_args_for_compile, is_core);
        compiler_runner.run_compiler(
            &rustc_args_for_compile,
            &mut CompilerCallbacksEraseMacro { do_compile: verifier.args.compile },
        )
    }
}

fn extend_rustc_args_for_verify(args: &mut Vec<String>, is_core: bool) {
    rust_verify::config::enable_default_features_and_verus_attr(args, true, false);
    args.extend(["--cfg", "verus_keep_ghost"].map(ToOwned::to_owned));
    args.extend(["--cfg", "verus_keep_ghost_body"].map(ToOwned::to_owned));
    if is_core {
        args.extend(["--cfg", "verus_verify_core"].map(|s| s.to_string()));
    }
}

fn extend_rustc_args_for_compile(args: &mut Vec<String>, is_core: bool) {
    rust_verify::config::enable_default_features_and_verus_attr(args, true, true);
    args.extend(["--cfg", "verus_keep_ghost"].map(ToOwned::to_owned));
    if is_core {
        args.extend(["--cfg", "verus_verify_core"].map(|s| s.to_string()));
    }
    let allow = &[
        "unused_imports",
        "unused_variables",
        "unused_assignments",
        "unreachable_patterns",
        "unused_parens",
        "unused_braces",
        "dead_code",
        "unreachable_code",
        "unused_mut",
        "unused_labels",
        "unused_attributes",
    ];
    for a in allow {
        args.extend(["-A", a].map(ToOwned::to_owned));
    }
}
