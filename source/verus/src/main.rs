use std::{
    io::{Read, Write},
    process::Command,
};

mod record;
#[cfg(feature = "record-history")]
mod record_history;

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
        Ok(exit_status) => {
            if !exit_status.success() {
                std::process::exit(exit_status.code().unwrap_or(-1));
            }
        }
        Err(err) => {
            eprintln!("{}", yansi::Paint::red(format!("error: {}", err)));
            std::process::exit(1);
        }
    }
}

fn warning(msg: &str) {
    eprintln!("{}", yansi::Paint::yellow(format!("warning: {}", msg)));
}

fn run() -> Result<std::process::ExitStatus, String> {
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

    let source_file = record::find_source_file(&args);

    #[cfg(feature = "record-history")]
    let record_history_dirs = {
        let source_file = source_file.as_ref()?;
        let project_dir = source_file
            .exists()
            .then(|| ())
            .and_then(|()| source_file.canonicalize().ok())
            .and_then(|d| d.parent().map(|x| x.to_owned()));
        let Some(project_dir) = project_dir else {
            return Err(format!("cannot find directory for source file {}", source_file.display()));
        };
        let history_dir = project_dir.join(".record-history");
        if history_dir.exists() {
            if !history_dir.is_dir() {
                return Err(format!(
                    ".record-history ({}) is not a directory",
                    history_dir.display()
                ));
            }
            let git_dir = history_dir.join("git");
            Some((project_dir, git_dir))
        } else {
            None
        }
    };

    #[cfg(not(feature = "record-history"))]
    let record_history_dirs: Option<std::path::PathBuf> = None;

    if record || record_history_dirs.is_some() {
        fn ensure_arg(args: &mut Vec<String>, arg: String) {
            if !args.contains(&arg) {
                args.push(arg.into());
            }
        }
        ensure_arg(&mut args, "--output-json".into());
        ensure_arg(&mut args, "--time".into());
        ensure_arg(&mut args, "--time-expanded".into());
        ensure_arg(&mut args, "--emit=dep-info".into());
    }

    #[cfg(feature = "record-history")]
    if record_history_dirs.is_some() && is_terminal::is_terminal(&std::io::stderr()) {
        if !args.iter().find(|x| x.starts_with("--color")).is_some() {
            args.push("--color=always".to_owned());
        }
    }

    cmd.arg("run")
        .arg(TOOLCHAIN)
        .arg("--")
        .arg(verusroot_path.join(RUST_VERIFY_FILE_NAME))
        .args(&args)
        .stdin(std::process::Stdio::inherit());

    if !record && record_history_dirs.is_none() {
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
        let source_file = source_file?;

        let temp_dep_file = record::temp_dep_file_from_source_file(&source_file)?;

        #[cfg(feature = "record-history")]
        let record_history_repo = record_history::find_record_history_repo(record_history_dirs)?;

        if record {
            eprintln!(
                "{}",
                yansi::Paint::blue(
                    "Rerunning verus to create zip archive (verus outputs are blocked)"
                )
            );
        }

        let start_time = std::time::Instant::now();

        cmd.stdout(std::process::Stdio::piped()).stderr(std::process::Stdio::piped());

        let mut verus_child = match cmd.spawn() {
            Ok(child) => child,
            Err(err) => {
                // remove temp file if created
                if let Err(err) = std::fs::remove_file(&temp_dep_file) {
                    warning(&format!(
                        "failed to delete `.d` file with this error message: {}",
                        err
                    ));
                }
                return Err(format!("failed to execute verus with error message {}", err,));
            }
        };

        let (mut verus_stdout, mut verus_stderr) = (
            verus_child.stdout.take().expect("no stdout on verus child process"),
            verus_child.stderr.take().expect("no stderr on verus child process"),
        );

        let mut verus_full_stdout = Vec::with_capacity(1024);
        let mut verus_full_stderr = Vec::with_capacity(1024);

        let mut verus_stdout_buf = Vec::with_capacity(1024);
        let mut verus_stderr_buf = Vec::with_capacity(1024);

        let write_stdio_streams = &mut |to_end: bool| {
            if to_end {
                verus_stdout
                    .read_to_end(&mut verus_stdout_buf)
                    .expect("failed to write to stdout buffer");
                verus_stderr
                    .read_to_end(&mut verus_stderr_buf)
                    .expect("failed to write to stderr buffer");
            } else {
                verus_stdout.read(&mut verus_stdout_buf).expect("failed to write to stdout buffer");
                verus_stderr.read(&mut verus_stderr_buf).expect("failed to write to stderr buffer");
            }

            #[cfg(feature = "record-history")]
            if !record {
                std::io::stderr()
                    .lock()
                    .write_all(&verus_stderr_buf)
                    .expect("failed to write to stderr");
            }

            verus_full_stdout
                .write_all(&verus_stdout_buf)
                .expect("failed to write to stdout buffer");
            verus_full_stderr
                .write_all(&verus_stderr_buf)
                .expect("failed to write to stderr buffer");

            verus_stdout_buf.clear();
            verus_stderr_buf.clear();
        };

        let exit_status: std::process::ExitStatus = loop {
            write_stdio_streams(false);

            match verus_child.try_wait() {
                Ok(Some(exit_status)) => break exit_status,
                Ok(None) => (),
                Err(err) => {
                    // remove temp file if created
                    if let Err(err) = std::fs::remove_file(&temp_dep_file) {
                        warning(&format!(
                            "failed to delete `.d` file with this error message: {}",
                            err
                        ));
                    }
                    return Err(format!("failed to execute verus with error message {}", err,));
                }
            }
        };

        let verus_duration = start_time.elapsed();

        write_stdio_streams(true);

        #[cfg(feature = "record-history")]
        record_history::print_verification_results(record, &verus_full_stdout);

        let toml_value = match record::error_report_toml_string(
            original_args,
            z3_version_output,
            verus_full_stdout,
            verus_full_stderr,
            verus_duration,
            exit_status.code(),
        ) {
            Ok(toml_value) => toml_value,
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

        let (deps_prefix, deps) = record::get_dependencies(&temp_dep_file)?;

        #[cfg(feature = "record-history")]
        record_history::record_history_commit(
            record_history_repo,
            &deps,
            &deps_prefix,
            &toml_value,
        )?;

        let zip_path = if record {
            let toml_string = toml::to_string(&toml_value)
                .map_err(|x| format!("Could not encode TOML value with error message: {}", x))?;
            Some(record::write_zip_archive(deps_prefix, deps, toml_string))
        } else {
            None
        };

        if let Err(err) = std::fs::remove_file(&temp_dep_file) {
            warning(&format!(
                "failed to delete dependencies file with this error message: {}, path to dependency file is {}",
                err,
                temp_dep_file.to_string_lossy()
            ));
        }

        if let Some(zip_path) = zip_path {
            println!(
                "Collected dependencies and stored your reproducible crate to zip file: {}\n",
                zip_path?
            );
        }

        Ok(exit_status)
    }
}
