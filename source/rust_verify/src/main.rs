#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_span;
extern crate rustc_typeck;

use rust_verify::config;
use rust_verify::erase::CompilerCallbacks;
use rust_verify::verifier::Verifier;

#[cfg(target_family = "windows")]
fn os_setup() -> Result<(), Box<dyn std::error::Error>> {
    // Configure Windows to kill the child SMT process if the parent is killed
    let job = win32job::Job::create()?;
    let mut info = job.query_extended_limit_info()?;
    info.limit_kill_on_job_close();
    job.set_extended_limit_info(&mut info)?;
    job.assign_current_process()?;
    // dropping the job object would kill us immediately, so just let it live forever instead:
    std::mem::forget(job);
    Ok(())
}

#[cfg(target_family = "unix")]
fn os_setup() -> Result<(), Box<dyn std::error::Error>> {
    Ok(())
}

pub fn main() {
    let _ = os_setup();

    let mut args = std::env::args();
    let program = args.next().unwrap();
    let (our_args, rustc_args) = config::parse_args(&program, args);
    let compile = our_args.compile;

    // Run verifier callback to build VIR tree and run verifier
    let mut verifier = Verifier::new(our_args);
    let status = rustc_driver::RunCompiler::new(&rustc_args, &mut verifier).run();
    if !verifier.encountered_vir_error {
        println!(
            "Verification results:: verified: {} errors: {}",
            verifier.count_verified,
            verifier.errors.len()
        );
    }
    match status {
        Ok(_) => {}
        Err(_) => {
            std::process::exit(1);
        }
    }

    // Run borrow checker and compiler (if enabled)
    if compile {
        let erasure_hints = verifier.erasure_hints.expect("erasure_hints").clone();
        let mut callbacks = CompilerCallbacks { erasure_hints };
        rustc_driver::RunCompiler::new(&rustc_args, &mut callbacks)
            .run()
            .expect("RunCompiler.run() failed");
    }
}
