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
    let total_time_0 = std::time::Instant::now();

    let _ = os_setup();
    rustc_driver::init_env_logger("RUSTVERIFY_LOG");

    let mut args = std::env::args();
    let program = args.next().unwrap();
    let (our_args, mut rustc_args) = rust_verify::config::parse_args(&program, args);
    rust_verify::config::enable_default_features(&mut rustc_args);
    let pervasive_path = our_args.pervasive_path.clone();

    let file_loader = rust_verify::file_loader::PervasiveFileLoader::new(pervasive_path);
    let verifier = rust_verify::verifier::Verifier::new(our_args);

    let (verifier, status) = rust_verify::driver::run(verifier, rustc_args, file_loader);

    if !verifier.encountered_vir_error {
        println!(
            "verification results:: verified: {} errors: {}",
            verifier.count_verified, verifier.count_errors
        );
    }

    let total_time_1 = std::time::Instant::now();
    let total_time = total_time_1 - total_time_0;

    match status {
        Ok(stats) => {
            if verifier.args.time {
                let verify = stats.time_verify;
                let mut vir = verifier.time_vir;
                let vir_rust_to_vir = verifier.time_vir_rust_to_vir;
                let mut vir_verify = verifier.time_vir_verify;
                let mut air = verifier.time_air;
                let smt_init = verifier.time_smt_init;
                let smt_run = verifier.time_smt_run;
                let lifetime = stats.time_lifetime;
                let compile = stats.time_compile;
                let erasure = stats.time_erasure;
                let rust_init = verify - vir;
                let rust = rust_init + lifetime + compile;
                vir_verify -= air;
                vir -= air;
                air -= smt_init + smt_run;
                println!("total-time:      {:>10} ms", total_time.as_millis());
                println!("    rust-time:       {:>10} ms", rust.as_millis());
                println!("        init-and-types:  {:>10} ms", rust_init.as_millis());
                println!("        lifetime-time:   {:>10} ms", lifetime.as_millis());
                println!("        compile-time:    {:>10} ms", compile.as_millis());
                println!("    vir-time:        {:>10} ms", vir.as_millis());
                println!("        rust-to-vir:     {:>10} ms", vir_rust_to_vir.as_millis());
                println!("        verify:          {:>10} ms", vir_verify.as_millis());
                println!("        erase:           {:>10} ms", erasure.as_millis());
                println!("    air-time:        {:>10} ms", air.as_millis());
                println!("    smt-time:        {:>10} ms", (smt_init + smt_run).as_millis());
                println!("        smt-init:        {:>10} ms", smt_init.as_millis());
                println!("        smt-run:         {:>10} ms", smt_run.as_millis());
            }
        }
        Err(_) => {
            std::process::exit(1);
        }
    }
}
