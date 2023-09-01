use std::process::Command;

mod record;

mod platform {
    pub struct ExitCode(pub i32);

    use std::process::Command;

    #[cfg(unix)]
    pub fn exec(cmd: &mut Command) -> std::io::Result<ExitCode> {
        use std::os::unix::prelude::*;
        Err(
            // This call never returns, if successful, because the current process
            // is replaced with `cmd` by `exec`
            cmd.exec(),
        )
    }

    #[cfg(windows)]
    pub fn exec(cmd: &mut Command) -> std::io::Result<ExitCode> {
        // Configure Windows to kill the child SMT process if the parent is killed
        let job = win32job::Job::create().map_err(|_| std::io::Error::last_os_error())?;
        let mut info =
            job.query_extended_limit_info().map_err(|_| std::io::Error::last_os_error())?;
        info.limit_kill_on_job_close();
        job.set_extended_limit_info(&mut info).map_err(|_| std::io::Error::last_os_error())?;
        job.assign_current_process().map_err(|_| std::io::Error::last_os_error())?;
        std::mem::forget(job);
        let status = cmd.status()?;
        Ok(ExitCode(status.code().unwrap()))
    }
}

const TOOLCHAIN: &str = env!("VERUS_TOOLCHAIN");

const RUST_VERIFY_FILE_NAME: &str =
    if cfg!(target_os = "windows") { "rust_verify.exe" } else { "rust_verify" };

const Z3_FILE_NAME: &str = if cfg!(target_os = "windows") { ".\\z3.exe" } else { "./z3" };

fn main() {
    match run() {
        Ok(()) => (),
        Err(err) => {
            eprintln!("{}", yansi::Paint::red(format!("error: {}", err)));
            std::process::exit(1);
        }
    }
}

fn warning(msg: &str) {
    eprintln!("{}", yansi::Paint::yellow(format!("warning: {}", msg)));
}

fn run() -> Result<(), String> {
    let (mut args, record) = {
        let mut args = std::env::args().into_iter();
        let _bin = args.next().expect("executable in args");
        let mut all_args: Vec<_> = args.collect();
        let mut record = false;
        all_args.retain(|arg| match arg.as_str() {
            "--record" => {
                record = true;
                false
            }
            _ => true,
        });

        (all_args, record)
    };

    let current_exe = std::env::current_exe().ok().and_then(|c| {
        if c.symlink_metadata().ok()?.is_symlink() { std::fs::read_link(c).ok() } else { Some(c) }
    });

    let parent = current_exe.and_then(|current| current.parent().map(std::path::PathBuf::from));

    let Some(verusroot_path) = parent.clone().and_then(|mut path| {
            if path.join("verus-root").is_file() {
                if !path.is_absolute() {
                    path =
                        std::env::current_dir().expect("working directory invalid").join(path);
                }
                Some(path)
            } else {
                None
            }
    }) else {
        eprintln!("error: did not find a valid verusroot");
        std::process::exit(128);
    };

    let parent = parent.expect("parent must be Some if we found a verusroot");

    let mut cmd = Command::new("rustup");

    #[allow(unused_variables)]
    let z3_path = if let Some(z3_path) = std::env::var("VERUS_Z3_PATH").ok() {
        Some(std::path::PathBuf::from(z3_path))
    } else {
        let mut maybe_z3_path = parent.join(Z3_FILE_NAME);
        if maybe_z3_path.exists() {
            if !maybe_z3_path.is_absolute() {
                maybe_z3_path =
                    std::env::current_dir().expect("working directory invalid").join(maybe_z3_path);
            }
            cmd.env("VERUS_Z3_PATH", &maybe_z3_path);
            Some(maybe_z3_path)
        } else {
            None
        }
    };

    let z3_version_output = record
        .then_some(())
        .and_then(|()| z3_path)
        .and_then(|ref z3_path| record::get_z3_version(z3_path));

    let original_args = args.clone();

    if record {
        fn ensure_arg(args: &mut Vec<String>, arg: String) {
            if !args.contains(&arg) {
                args.push(arg.into());
            }
        }
        ensure_arg(&mut args, "--output-json".into());
        ensure_arg(&mut args, "--time".into());
        ensure_arg(&mut args, "--emit=dep-info".into());
    }

    cmd.arg("run")
        .arg(TOOLCHAIN)
        .arg("--")
        .arg(verusroot_path.join(RUST_VERIFY_FILE_NAME))
        .args(&args)
        .stdin(std::process::Stdio::inherit());

    if !record {
        match platform::exec(&mut cmd) {
            Err(e) => {
                eprintln!("error: failed to execute rust_verify {e:?}");
                std::process::exit(128);
            }
            Ok(code) => {
                std::process::exit(code.0);
            }
        }
    } else {
        let source_file = record::find_source_file(&args)?;
        let temp_dep_file = record::temp_dep_file_from_source_file(&source_file)?;

        eprintln!(
            "{}",
            yansi::Paint::blue("Rerunning verus to create zip archive (verus outputs are blocked)")
        );

        let start_time = std::time::Instant::now();

        cmd.stdin(std::process::Stdio::piped()).stderr(std::process::Stdio::piped());

        let verus_output = match cmd.output() {
            Ok(output) => output,
            Err(err) => {
                // remove temp file if created
                if let Err(err) = std::fs::remove_file(&temp_dep_file) {
                    warning(&format!(
                        "failed to delete `.d` file with this error message: {}",
                        err
                    ));
                }
                Err(format!("failed to execute verus with error message {}", err,))?
            }
        };

        let verus_duration = start_time.elapsed();

        let toml_string = match record::error_report_toml_string(
            original_args,
            z3_version_output,
            verus_output,
            verus_duration,
        ) {
            Ok(toml_string) => toml_string,
            Err(err) => {
                // remove temp file if created
                if let Err(err) = std::fs::remove_file(&temp_dep_file) {
                    warning(&format!(
                        "failed to delete `.d` file with this error message: {}",
                        err
                    ));
                }
                return Err(err);
            }
        };

        let zip_path = record::write_zip_for(&temp_dep_file, toml_string);

        if let Err(err) = std::fs::remove_file(&temp_dep_file) {
            warning(&format!(
                "failed to delete dependencies file with this error message: {}, path to dependency file is {}",
                err,
                temp_dep_file.to_string_lossy()
            ));
        }

        println!(
            "Collected dependencies and stored your reproducible crate to zip file: {}\n",
            zip_path?
        );

        Ok(())
    }
}
