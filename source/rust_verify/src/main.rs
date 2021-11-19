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
    let (our_args, rustc_args) = rust_verify::config::parse_args(&program, args);
    let pervasive_path = our_args.pervasive_path.clone();

    let file_loader = rust_verify::file_loader::PervasiveFileLoader::new(pervasive_path);
    let mut verifier = rust_verify::verifier::Verifier::new(our_args);

    let status = rust_verify::driver::run(&mut verifier, &rustc_args, &file_loader);
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
}
