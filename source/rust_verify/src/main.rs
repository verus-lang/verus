#![feature(rustc_private)]

use rust_verify::util::{VerusBuildProfile, verus_build_info};

extern crate rustc_driver;
extern crate rustc_log;
extern crate rustc_session;

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
    let mut dep_tracker = rust_verify::cargo_verus_dep_tracker::DepTracker::init();
    let via_cargo = dep_tracker.compare_env(rust_verify::cargo_verus::VERUS_DRIVER_VIA_CARGO, "1");
    // For now, verus_builtin, vstd, etc. must be rebuilt for each via_cargo crate:
    let via_cargo_rebuild_verus_libs = via_cargo;

    let mut internal_args = std::env::args();
    let internal_program = internal_args.next().unwrap();
    let (build_test_mode, has_rustc) = if let Some(first_arg) = internal_args.next() {
        match first_arg.as_str() {
            rust_verify::trait_check::TC_DRIVER_ARG => {
                let mut internal_args: Vec<_> = internal_args.collect();
                internal_args.insert(0, internal_program);
                let mut buffer = String::new();
                use std::io::Read;
                std::io::stdin().read_to_string(&mut buffer).expect("cannot read stdin");
                rust_verify::trait_check::trait_check_rustc_driver(&internal_args[..], buffer);
                return;
            }
            arg if arg.contains("rustc") => {
                // Setting RUSTC_WRAPPER causes Cargo to pass rustc path as the first argument.
                (false, true)
            }
            "--internal-test-mode" => (true, false),
            _ => (false, false),
        }
    } else {
        (false, false)
    };

    let build_info = verus_build_info();

    let total_time_0 = std::time::Instant::now();

    let _ = os_setup();
    vir::util::set_verus_github_bug_report_url(
        ::rust_verify::consts::VERUS_GITHUB_BUG_REPORT_URL.to_owned(),
    );
    let logger_handler =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
    rustc_driver::init_logger(&logger_handler, rustc_log::LoggerConfig::from_env("RUSTVERIFY_LOG"));

    if via_cargo != has_rustc {
        let _ = logger_handler.early_err("Error: VERUS_DRIVER_VIA_CARGO must be 1 if and only if 'rustc' is the first argument to verus");
        std::process::exit(1);
    }

    let mut args = if build_test_mode || via_cargo { internal_args } else { std::env::args() };
    let program =
        if build_test_mode || via_cargo { internal_program } else { args.next().unwrap() };

    let mut vstd = None;
    let verus_root = if !(build_test_mode || via_cargo_rebuild_verus_libs) {
        let verus_root = rust_verify::driver::find_verusroot();
        if let Some(rust_verify::driver::VerusRoot { path: verusroot, .. }) = &verus_root {
            let vstd_path = verusroot.join("vstd.vir").to_str().unwrap().to_string();
            vstd = Some((format!("vstd"), vstd_path));
        }
        verus_root
    } else {
        None
    };

    let mut args: Vec<String> = args.collect();
    let is_direct_rustc_call = via_cargo
        && rust_verify::cargo_verus::extend_args_and_check_is_direct_rustc_call(
            &mut args,
            &mut dep_tracker,
        );

    if is_direct_rustc_call {
        args.insert(0, program.clone());
        rust_verify::driver::run_rustc_compiler_directly(&args);
        return;
    }

    let via_cargo = via_cargo.then(|| rust_verify::config::parse_cargo_args(&program, &mut args));

    let (our_args, rustc_args) =
        rust_verify::config::parse_args_with_imports(&program, args.into_iter(), vstd);

    if our_args.version {
        if our_args.output_json {
            println!(
                "{}",
                serde_json::ser::to_string_pretty(&build_info.to_json()).expect("invalid json")
            );
        } else {
            println!("{}", build_info);
        }
        return;
    }

    let via_cargo_compile = via_cargo
        .as_ref()
        .map(|args| rust_verify::cargo_verus::is_compile(args, &mut dep_tracker))
        .unwrap_or(false);

    if !build_test_mode {
        match build_info.profile {
            VerusBuildProfile::Debug => eprintln!(
                "warning: verus was compiled in debug mode, which will result in worse performance"
            ),
            VerusBuildProfile::Unknown => eprintln!(
                "warning: verus was compiled outside vargo, and we cannot determine whether it was built in debug mode, which will result in worse performance"
            ),
            VerusBuildProfile::Release => (),
        }
    }

    // TODO: Audit that the environment access only happens in single-threaded code.
    unsafe { std::env::set_var("RUSTC_BOOTSTRAP", "1") };

    let verifier =
        rust_verify::verifier::Verifier::new(our_args, via_cargo, via_cargo_compile, dep_tracker);

    let (verifier, stats, status) = rust_verify::driver::run(
        verifier,
        rustc_args,
        verus_root,
        build_test_mode || via_cargo_rebuild_verus_libs,
    );

    let total_time_1 = std::time::Instant::now();
    let total_time = total_time_1 - total_time_0;

    let times_ms_json_data = if verifier.args.time {
        fn compute_total(
            verifier: &rust_verify::verifier::Verifier,
            f: impl Fn(&rust_verify::verifier::BucketStats) -> std::time::Duration,
        ) -> u128 {
            verifier.bucket_stats.values().map(|v| f(v)).sum::<std::time::Duration>().as_millis()
        }

        #[derive(Debug, Clone)]
        struct SmtStat {
            time_millis: u128,
            time_micros: u128,
            rlimit_count: Option<u64>, // at the moment, only available for Z3
        }

        impl Default for SmtStat {
            fn default() -> Self {
                Self { time_millis: 0, time_micros: 0, rlimit_count: None }
            }
        }

        impl SmtStat {
            fn add(&mut self, other: SmtStat) {
                self.time_millis += other.time_millis;
                self.time_micros += other.time_micros;
                self.rlimit_count = match (self.rlimit_count, other.rlimit_count) {
                    (Some(a), Some(b)) => Some(a + b),
                    (Some(a), None) => Some(a),
                    (None, Some(b)) => Some(b),
                    (None, None) => None,
                };
            }
        }

        #[derive(Clone, Debug, Default)]
        struct SmtStats {
            init: SmtStat,
            run: SmtStat,
        }

        impl SmtStats {
            fn add(&mut self, other: SmtStats) {
                self.init.add(other.init);
                self.run.add(other.run);
            }
        }

        let smt_module_stats = {
            let mut smt_module_stats: std::collections::HashMap<
                std::sync::Arc<vir::ast::PathX>,
                SmtStats,
            > = std::collections::HashMap::new();

            for (k, v) in verifier.bucket_stats.iter() {
                smt_module_stats.entry(k.module().clone()).or_default().add(SmtStats {
                    init: SmtStat {
                        time_millis: v.time_smt_init.as_millis(),
                        time_micros: v.time_smt_init.as_micros(),
                        rlimit_count: v.rlimit_count.map(|x| x.0),
                    },
                    run: SmtStat {
                        time_millis: v.time_smt_run.as_millis(),
                        time_micros: v.time_smt_run.as_micros(),
                        rlimit_count: v.rlimit_count.map(|x| x.1),
                    },
                });
            }

            smt_module_stats
        };

        fn sorted_smt_stats(
            smt_module_stats: &std::collections::HashMap<std::sync::Arc<vir::ast::PathX>, SmtStats>,
            selector: impl Fn(&SmtStats) -> &SmtStat,
        ) -> Vec<(&std::sync::Arc<vir::ast::PathX>, SmtStat)> {
            let mut stats: Vec<(&std::sync::Arc<vir::ast::PathX>, SmtStat)> =
                smt_module_stats.iter().map(|(k, v)| (k, selector(v).clone())).collect();
            stats.sort_by(|(_, a), (_, b)| b.time_micros.cmp(&a.time_micros));
            stats
        }

        let smt_init_stats = sorted_smt_stats(&smt_module_stats, |v| &v.init);
        let total_smt_init: u128 = compute_total(&verifier, |v| v.time_smt_init);

        let smt_run_stats = sorted_smt_stats(&smt_module_stats, |v| &v.run);
        let total_smt_run: u128 = compute_total(&verifier, |v| v.time_smt_run);

        let smt_init_rlimit_counts: Option<Vec<u64>> =
            smt_init_stats.iter().map(|(_, v)| v.rlimit_count).collect();
        let total_rlimit_init: Option<u64> = smt_init_rlimit_counts.map(|rs| rs.iter().sum());

        let smt_run_rlimit_counts: Option<Vec<u64>> =
            smt_run_stats.iter().map(|(_, v)| v.rlimit_count).collect();
        let total_rlimit_run: Option<u64> = smt_run_rlimit_counts.map(|rs| rs.iter().sum());

        let mut smt_function_breakdown = {
            let mod_fun_times: Vec<_> = verifier
                .func_times
                .iter()
                .flat_map(|(k, v)| {
                    v.iter()
                        .map(|(f, t)| {
                            (
                                k.module().clone(),
                                (
                                    f.clone(),
                                    SmtStat {
                                        time_millis: t.smt_time.as_millis(),
                                        time_micros: t.smt_time.as_micros(),
                                        rlimit_count: t.rlimit_count,
                                    },
                                ),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .collect();
            let mut per_module: std::collections::HashMap<
                vir::ast::Path,
                Vec<(vir::ast::Fun, SmtStat)>,
            > = std::collections::HashMap::new();
            for (m, f_t) in mod_fun_times {
                per_module.entry(m).or_insert(Vec::new()).push(f_t);
            }
            per_module
        };

        let mut air_times = verifier
            .bucket_stats
            .iter()
            .map(|(k, v)| {
                (k.module(), (v.time_air - (v.time_smt_init + v.time_smt_run)).as_millis())
            })
            .collect::<Vec<_>>();
        air_times.sort_by(|(_, a), (_, b)| b.cmp(a));
        let total_air: u128 =
            compute_total(&verifier, |v| v.time_air - (v.time_smt_init + v.time_smt_run));

        let mut verify_times = verifier
            .bucket_stats
            .iter()
            .map(|(k, v)| (k.module(), (v.time_verify).as_millis()))
            .collect::<Vec<_>>();
        verify_times.sort_by(|(_, a), (_, b)| b.cmp(a));
        let total_verify: u128 = compute_total(&verifier, |v| v.time_verify);

        // Rust time:
        let rust_init = stats.time_rustc;
        let trait_conflicts = stats.time_trait_conflicts;
        let compile = stats.time_compile;
        let rust = rust_init + trait_conflicts + compile;

        // total verification time
        let vir_rust_to_vir = verifier.time_vir_rust_to_vir; // included in verifier.time_vir
        let vir_vir_time = verifier.time_vir;
        let hir_time = verifier.time_hir;
        let import_time = verifier.time_import;
        let vir_time = hir_time + import_time + vir_vir_time;
        let verify_crate_time = verifier.time_verify_crate;

        // total verify time is now the time to verify the crate plus the vir time
        let verify = verifier.time_verify_crate + vir_time;

        // Unaccounted time is now total time minus all the other times
        let unaccounted = total_time - (rust + verify);

        let total_cpu_time = if verifier.num_threads > 1 {
            (total_time.as_millis()
                + total_verify
                + verifier.time_verify_crate_sequential.as_millis())
                - verifier.time_verify_crate.as_millis()
        } else {
            total_time.as_millis()
        };

        if verifier.args.output_json {
            {
                let _smt_function_breakdown_set =
                    smt_function_breakdown.keys().collect::<std::collections::HashSet<_>>();
                let _smt_run_times_set =
                    smt_run_stats.iter().map(|(x, _)| *x).collect::<std::collections::HashSet<_>>();
                // REVIEW check these are consistent
            }

            let mut times = serde_json::json!({
                "verus-build": {
                    "profile": build_info.profile.to_string(),
                    "version": build_info.version.to_string(),
                },
                "num-threads": verifier.num_threads,
                "total": total_time.as_millis(),
                "estimated-cpu-time": if verifier.num_threads > 1 {total_cpu_time} else {total_time.as_millis()},
                "rust": {
                    "total": rust.as_millis(),
                    "init-and-types": rust_init.as_millis(),
                    "trait-conflicts": trait_conflicts.as_millis(),
                    "compile": compile.as_millis(),
                },
                "verification": {
                    "total": verify.as_millis(),
                    "vir" : {
                        "total": vir_time.as_millis(),
                        "hir": hir_time.as_millis(),
                        "import": import_time.as_millis(),
                        "rust-to-vir": vir_rust_to_vir.as_millis()
                    }
                },
                "total-verify": total_verify,
                "total-verify-module-times" : verify_times.iter().map(|(m, t)| {
                    serde_json::json!({
                        "module" : rust_verify::verifier::module_name(m),
                        "time" : t
                    })
                }).collect::<Vec<serde_json::Value>>(),
                "air": {
                    "total": total_air,
                    "module-times" : air_times.iter().map(|(m, t)| {
                        serde_json::json!({
                            "module" : rust_verify::verifier::module_name(m),
                            "time" : t
                        })
                    }).collect::<Vec<serde_json::Value>>(),
                },
            });
            if !verifier.encountered_vir_error {
                times.as_object_mut().unwrap().insert(
                    "smt".to_string(),
                    serde_json::json!({
                        "total": (total_smt_init + total_smt_run),
                        "smt-init": total_smt_init,
                        "rlimit-init": total_rlimit_init,
                        "smt-init-module-times" : smt_init_stats.iter().map(|(m, t)| {
                            serde_json::json!({
                                "module" : rust_verify::verifier::module_name(m),
                                "time" : t.time_millis,
                                "time-micros" : t.time_micros,
                                "rlimit" : t.rlimit_count,
                            })
                        }).collect::<Vec<serde_json::Value>>(),
                        "smt-run": total_smt_run,
                        "rlimit-run": total_rlimit_run,
                        "smt-run-module-times" : smt_run_stats.iter().map(|(m, t)| {
                            serde_json::json!({
                                "module" : rust_verify::verifier::module_name(m),
                                "time" : t.time_millis,
                                "time-micros" : t.time_micros,
                                "rlimit" : t.rlimit_count,
                                "function-breakdown" : smt_function_breakdown.get_mut(*m).map(|b| b.iter().map(|(f, t)| {
                                    serde_json::json!({
                                        "function" : vir::ast_util::fun_as_friendly_rust_name(f),
                                        "mode:" : verifier.get_function_mode(f).map(|m| m.to_string()),
                                        "time" : t.time_millis,
                                        "time-micros" : t.time_micros,
                                        "rlimit" : t.rlimit_count,
                                        "success" : !verifier.func_fails.contains(f),
                                    })
                                 }).collect::<Vec<serde_json::Value>>()).unwrap_or_default(),
                            })
                        }).collect::<Vec<serde_json::Value>>(),
                    }),
                );
            }

            Some(times)
        } else {
            println!("(use --output-json for machine-readable output)");
            println!("verus-build-info\n{}", build_info);
            print!("total-time:      {:>10} ms", total_time.as_millis());
            if verifier.num_threads > 1 {
                println!("    (estimated total cpu time {} ms)", total_cpu_time);
            } else {
                println!();
            }
            println!("    rust-time:          {:>10} ms", rust.as_millis());
            println!("        init-and-types:     {:>10} ms", rust_init.as_millis());
            println!("        trait-conflicts:    {:>10} ms", trait_conflicts.as_millis());
            println!("        compile-time:       {:>10} ms", compile.as_millis());

            println!("    verification-time:  {:>10} ms", verify.as_millis());
            println!("        vir-time:           {:>10} ms", vir_time.as_millis());
            println!("            hir-time:           {:>10} ms", hir_time.as_millis());
            println!("            import-time:        {:>10} ms", import_time.as_millis());
            println!("            rust-to-vir:        {:>10} ms", vir_rust_to_vir.as_millis());
            println!("        verify-crate-time:  {:>10} ms", verify_crate_time.as_millis());
            println!("    unaccounted-time:   {:>10} ms", unaccounted.as_millis());

            println!("\nverify-crate-time-breakdown");
            println!(
                "    total verify-time:     {:>10} ms   ({} threads)",
                total_verify, verifier.num_threads
            );
            if verifier.args.time_expanded {
                for (i, (m, t)) in verify_times.iter().take(3).enumerate() {
                    println!(
                        "      {}. {:<40} {:>10} ms",
                        i + 1,
                        rust_verify::verifier::module_name(m),
                        t
                    );
                }
            }
            println!(
                "        total air-time:        {:>10} ms   ({} threads)",
                total_air, verifier.num_threads
            );
            if verifier.args.time_expanded {
                for (i, (m, t)) in air_times.iter().take(3).enumerate() {
                    println!(
                        "      {}. {:<40} {:>10} ms",
                        i + 1,
                        rust_verify::verifier::module_name(m),
                        t
                    );
                }
            }
            if !verifier.encountered_vir_error {
                println!(
                    "        total smt-time:        {:>10} ms   ({} threads)",
                    (total_smt_init + total_smt_run),
                    verifier.num_threads
                );
                println!(
                    "            total smt-init:        {:>10} ms{} ({} threads)",
                    total_smt_init,
                    total_rlimit_init
                        .map(|rc| format!(", {:>8} rlimit", rc))
                        .unwrap_or(format!("")),
                    verifier.num_threads
                );
                if verifier.args.time_expanded {
                    for (i, (m, t)) in smt_init_stats.iter().take(3).enumerate() {
                        println!(
                            "                {}. {:<40} {:>10} ms",
                            i + 1,
                            rust_verify::verifier::module_name(m),
                            t.time_millis
                        );
                    }
                }
                println!(
                    "            total smt-run:         {:>10} ms{} ({} threads)",
                    total_smt_run,
                    total_rlimit_run.map(|rc| format!(", {:>8} rlimit", rc)).unwrap_or(format!("")),
                    verifier.num_threads,
                );
                if verifier.args.time_expanded {
                    for (i, (m, t)) in smt_run_stats.iter().take(3).enumerate() {
                        println!(
                            "                {}. {:<40} {:>10} ms{}",
                            i + 1,
                            rust_verify::verifier::module_name(m),
                            t.time_millis,
                            t.rlimit_count
                                .map(|rc| format!(", {:>8} rlimit", rc))
                                .unwrap_or(format!("")),
                        );
                    }
                }
            }

            None
        }
    } else {
        None
    };

    if verifier.args.output_json {
        let mut res = serde_json::json!({
            "encountered-error": status.is_err(),
            "encountered-vir-error": verifier.encountered_vir_error,
        });
        if rust_verify::driver::is_verifying_entire_crate(&verifier) {
            res["success"] = serde_json::json!(
                !status.is_err() && !verifier.encountered_vir_error && verifier.count_errors == 0
            );
        }
        if !verifier.encountered_vir_error {
            res.as_object_mut().unwrap().append(
                serde_json::json!({
                    "verified": verifier.count_verified,
                    "errors": verifier.count_errors,
                    "is-verifying-entire-crate": rust_verify::driver::is_verifying_entire_crate(&verifier),
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
        out.append(&mut build_info.to_json().as_object_mut().unwrap());
        println!("{}", serde_json::ser::to_string_pretty(&out).expect("invalid json"));
    }

    match status {
        Ok(()) => (),
        Err(_) => {
            std::process::exit(1);
        }
    }
}
