#![feature(rustc_private)]

extern crate rustc_driver; // TODO(main_new) can we remove this?

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
    let mut internal_args = std::env::args();
    let internal_program = internal_args.next().unwrap();
    let build_test_mode = if let Some(first_arg) = internal_args.next() {
        match first_arg.as_str() {
            rust_verify::lifetime::LIFETIME_DRIVER_ARG => {
                let mut internal_args: Vec<_> = internal_args.collect();
                internal_args.insert(0, internal_program);
                let mut buffer = String::new();
                use std::io::Read;
                std::io::stdin().read_to_string(&mut buffer).expect("cannot read stdin");
                rust_verify::lifetime::lifetime_rustc_driver(&internal_args[..], buffer);
                return;
            }
            "--internal-build-vstd-driver" => {
                let pervasive_path = internal_args.next().unwrap();
                let vstd_vir = internal_args.next().unwrap();
                let target_path = internal_args.next().unwrap();
                let z3_path = internal_args.next().unwrap();

                let mut internal_args: Vec<_> = internal_args.collect();
                internal_args.insert(0, internal_program);

                use rust_verify::config::Args;
                use rust_verify::file_loader::PervasiveFileLoader;
                use rust_verify::verifier::Verifier;

                let mut our_args: Args = Default::default();
                our_args.pervasive_path = Some(pervasive_path.to_string());
                our_args.verify_pervasive = true;
                our_args.multiple_errors = 2;
                our_args.export = Some(target_path.to_string() + vstd_vir.as_str());
                our_args.compile = true;

                std::env::set_var("VERUS_Z3_PATH", z3_path);

                let file_loader = PervasiveFileLoader::new(Some(pervasive_path.to_string()));
                let verifier = Verifier::new(our_args);
                dbg!(&internal_args);
                let (_verifier, _stats, status) =
                    rust_verify::driver::run(verifier, internal_args, file_loader, true);
                status.expect("failed to build vstd library");
                return;
            }
            "--internal-test-mode" => true,
            _ => false,
        }
    } else {
        false
    };

    if cfg!(debug_assertions) {
        if !build_test_mode {
            eprintln!(
                "warning: verus was compiled in debug mode, which will result in worse performance"
            );
            // TODO(main_new) eprintln!("to compile in release mode use ./tools/cargo.sh build --release");
        }
    }

    let total_time_0 = std::time::Instant::now();

    let _ = os_setup();
    verus_rustc_driver::init_env_logger("RUSTVERIFY_LOG");

    let mut args = if build_test_mode { internal_args } else { std::env::args() };
    let program = if build_test_mode { internal_program } else { args.next().unwrap() };
    let (our_args, rustc_args) = rust_verify::config::parse_args(&program, args);
    let pervasive_path = our_args.pervasive_path.clone();

    std::env::set_var("RUSTC_BOOTSTRAP", "1");

    let file_loader = rust_verify::file_loader::PervasiveFileLoader::new(pervasive_path);
    let verifier = rust_verify::verifier::Verifier::new(our_args);

    let (verifier, stats, status) =
        rust_verify::driver::run(verifier, rustc_args, file_loader, build_test_mode);

    let total_time_1 = std::time::Instant::now();
    let total_time = total_time_1 - total_time_0;

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
    match status {
        Ok(()) => (),
        Err(_) => {
            std::process::exit(1);
        }
    }
}
