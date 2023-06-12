#![feature(rustc_private)]

use rust_verify::util::{verus_build_profile, VerusBuildProfile, print_commit_info};
use std::process::Command;

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
            "--version" => {
                println!("Verus");
                println!("platform: {}_{}", std::env::consts::OS, std::env::consts::ARCH);
                print_commit_info();
                return;
            }
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
                let target_path = std::path::PathBuf::from(internal_args.next().unwrap());
                let verify = match internal_args.next().unwrap().as_str() {
                    "verify" => true,
                    "no-verify" => false,
                    _ => panic!("invalid verify argument"),
                };

                let mut internal_args: Vec<_> = internal_args.collect();
                internal_args.insert(0, internal_program);

                use rust_verify::config::Args;
                use rust_verify::file_loader::PervasiveFileLoader;
                use rust_verify::verifier::Verifier;

                let mut our_args: Args = Default::default();
                our_args.pervasive_path = Some(pervasive_path.to_string());
                our_args.verify_pervasive = true;
                our_args.no_verify = !verify;
                our_args.no_lifetime = !verify;
                our_args.multiple_errors = 2;
                our_args.export = Some(target_path.join(vstd_vir).to_str().unwrap().to_string());
                our_args.compile = true;

                let file_loader = PervasiveFileLoader::new(Some(pervasive_path.to_string()));
                let verifier = Verifier::new(our_args);
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

    let profile = verus_build_profile();

    if !build_test_mode {
        match profile {
            VerusBuildProfile::Debug => eprintln!(
                "warning: verus was compiled in debug mode, which will result in worse performance"
            ),
            VerusBuildProfile::Unknown => eprintln!(
                "warning: verus was compiled outside vargo, and we cannot determine whether it was built in debug mode, which will result in worse performance"
            ),
            VerusBuildProfile::Release => (),
        }
    }

    let total_time_0 = std::time::Instant::now();

    let _ = os_setup();
    verus_rustc_driver::init_env_logger("RUSTVERIFY_LOG");

    let mut args = if build_test_mode { internal_args } else { std::env::args() };
    let program = if build_test_mode { internal_program } else { args.next().unwrap() };
    let (our_args, rustc_args) = rust_verify::config::parse_args(&program, args);
    let pervasive_path = our_args.pervasive_path.clone();

    if our_args.error_report {
        // it is printing some wierd things
        
        let mut args = std::env::args();
        args.next();
        
        // let hi = "main.rs";
        let hi = args.filter(|x| x != "--error-report");
        // println!("hi: {:?}", args.filter(|x| x != "--error-report"));

        // why i need a child process here
        let mut res = Command::new("error_report")
            .args( hi )
            .spawn()
            .expect("error_report failed to start");

        res.wait().expect("error_report failed to run");

        return;
    }

    std::env::set_var("RUSTC_BOOTSTRAP", "1");

    let file_loader = rust_verify::file_loader::PervasiveFileLoader::new(pervasive_path);
    let verifier = rust_verify::verifier::Verifier::new(our_args);

    let (verifier, stats, status) =
        rust_verify::driver::run(verifier, rustc_args, file_loader, build_test_mode);

    let total_time_1 = std::time::Instant::now();
    let total_time = total_time_1 - total_time_0;

    let times_ms_json_data = if verifier.args.time {
        let verify = stats.time_verify;
        let mut vir = verifier.time_vir;
        let vir_rust_to_vir = verifier.time_vir_rust_to_vir;
        let mut vir_verify = verifier.time_vir_verify;
        let mut air = verifier.time_air;
        let smt_init = verifier.time_smt_init;
        let smt_run = verifier.time_smt_run;
        let lifetime = stats.time_lifetime;
        let compile = stats.time_compile;
        let rust_init = verify - vir;
        let rust = rust_init + lifetime + compile;
        vir_verify -= air;
        vir -= air;
        air -= smt_init + smt_run;
        if verifier.args.output_json {
            let mut times = serde_json::json!({
                "total": total_time.as_millis(),
                "rust": {
                    "total": rust.as_millis(),
                    "init-and-types": rust_init.as_millis(),
                    "lifetime": lifetime.as_millis(),
                    "compile": compile.as_millis(),
                },
                "vir": {
                    "total": vir.as_millis(),
                    "rust-to-vir": vir_rust_to_vir.as_millis(),
                    "verify": vir_verify.as_millis(),
                },
                "air": {
                    "total": air.as_millis(),
                },
            });
            if !verifier.encountered_vir_error {
                times.as_object_mut().unwrap().insert(
                    "smt".to_string(),
                    serde_json::json!({
                        "total": (smt_init + smt_run).as_millis(),
                        "smt-init": smt_init.as_millis(),
                        "smt-run": smt_run.as_millis(),
                    }),
                );
            }
            Some(times)
        } else {
            println!("verus-build-profile: {}", profile.to_string());
            println!("total-time:      {:>10} ms", total_time.as_millis());
            println!("    rust-time:       {:>10} ms", rust.as_millis());
            println!("        init-and-types:  {:>10} ms", rust_init.as_millis());
            println!("        lifetime-time:   {:>10} ms", lifetime.as_millis());
            println!("        compile-time:    {:>10} ms", compile.as_millis());
            println!("    vir-time:        {:>10} ms", vir.as_millis());
            println!("        rust-to-vir:     {:>10} ms", vir_rust_to_vir.as_millis());
            println!("        verify:          {:>10} ms", vir_verify.as_millis());
            println!("    air-time:        {:>10} ms", air.as_millis());
            if !verifier.encountered_vir_error {
                println!("    smt-time:        {:>10} ms", (smt_init + smt_run).as_millis());
                println!("        smt-init:        {:>10} ms", smt_init.as_millis());
                println!("        smt-run:         {:>10} ms", smt_run.as_millis());
            }
            None
        }
    } else {
        None
    };

    if verifier.args.output_json {
        let mut res = serde_json::json!({
            "encountered-vir-error": verifier.encountered_vir_error,
        });
        if rust_verify::driver::is_verifying_entire_crate(&verifier) {
            res["success"] =
                serde_json::json!(!verifier.encountered_vir_error && verifier.count_errors == 0);
        }
        if !verifier.encountered_vir_error {
            res.as_object_mut().unwrap().append(
                serde_json::json!({
                    "verified": verifier.count_verified,
                    "errors": verifier.count_errors,
                })
                .as_object_mut()
                .unwrap(),
            );
        }
        let mut out: serde_json::Map<String, serde_json::Value> = serde_json::Map::new();
        out.insert("verification-results".to_string(), res);
        if let Some(times_ms) = times_ms_json_data {
            out.insert("times-ms".to_string(), times_ms);
        }
        out.insert(
            "verus-build-profile".to_string(),
            serde_json::Value::String(profile.to_string()),
        );
        println!("{}", serde_json::ser::to_string_pretty(&out).expect("invalid json"));
    }

    match status {
        Ok(()) => (),
        Err(_) => {
            std::process::exit(1);
        }
    }
}
