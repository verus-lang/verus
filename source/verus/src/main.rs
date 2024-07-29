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
const CVC5_FILE_NAME: &str = if cfg!(target_os = "windows") { ".\\cvc5.exe" } else { "./cvc5" };

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
    #[allow(unused_variables)] // unpretty_arg is unused if --features record-history is disabled
    let (mut args, record, unpretty_arg) = {
        let mut args = std::env::args().into_iter();
        let _bin = args.next().expect("executable in args");
        let mut all_args: Vec<_> = args.collect();
        let mut record = false;
        let mut unpretty_arg = false;
        for i in 0..all_args.len() {
            if all_args[i] == "-Z"
                && all_args.get(i + 1).map(|x| x.starts_with("unpretty")).unwrap_or(false)
            {
                unpretty_arg = true;
            } else if all_args[i].starts_with("-Zunpretty") {
                unpretty_arg = true;
            }
        }
        all_args.retain(|arg| match arg.as_str() {
            "--record" => {
                record = true;
                false
            }
            _ => true,
        });
        (all_args, record, unpretty_arg)
    };

    let current_exe = std::env::current_exe().ok().and_then(|c| {
        if c.symlink_metadata().ok()?.is_symlink() { std::fs::read_link(c).ok() } else { Some(c) }
    });

    let parent = current_exe.and_then(|current| current.parent().map(std::path::PathBuf::from));

    let Some(verusroot_path) = parent.clone().and_then(|mut path| {
        if path.join("verus-root").is_file() {
            if !path.is_absolute() {
                path = std::env::current_dir().expect("working directory invalid").join(path);
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

    match Command::new("rustup")
        .arg("toolchain")
        .arg("list")
        .output()
        .ok()
        .and_then(|output| output.status.success().then(|| output))
    {
        Some(output) => {
            use std::io::BufRead;
            if output
                .stdout
                .lines()
                .find(|l| l.as_ref().map(|l| l.contains(TOOLCHAIN)).unwrap_or(false))
                .is_none()
            {
                eprintln!(
                    "{}",
                    yansi::Paint::red(format!(
                        "verus: required rust toolchain {} not found",
                        TOOLCHAIN
                    ))
                );
                eprintln!(
                    "{}",
                    yansi::Paint::blue(
                        "run the following command (in a bash-compatible shell) to install the necessary toolchain:"
                    )
                );
                eprintln!("  {}", yansi::Paint::white(format!("rustup install {}", TOOLCHAIN)));
            }
        }
        None => {
            eprintln!(
                "{}",
                yansi::Paint::red(format!("verus: rustup not found, or not executable"))
            );
            eprintln!("{}", yansi::Paint::yellow(format!("verus needs a rustup installation")));
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            {
                eprintln!(
                    "{}",
                    yansi::Paint::blue(
                        "run the following command (in a bash-compatible shell) to install rustup:"
                    )
                );
                eprintln!(
                    "  {}",
                    yansi::Paint::white(format!(
                        "curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- --default-toolchain {}",
                        TOOLCHAIN
                    ))
                );
                eprintln!(
                    "{}",
                    yansi::Paint::blue("or visit https://rustup.rs/ for more information")
                );
            }
            #[cfg(any(target_os = "windows"))]
            {
                eprintln!(
                    "{}",
                    yansi::Paint::blue(
                        "visit https://rustup.rs/ for installation instructions for Windows"
                    )
                );
            }
        }
    }

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

    if std::env::var("VERUS_CVC5_PATH").ok().is_none() {
        let mut maybe_cvc5_path = parent.join(CVC5_FILE_NAME);
        if maybe_cvc5_path.exists() {
            if !maybe_cvc5_path.is_absolute() {
                maybe_cvc5_path = std::env::current_dir()
                    .expect("working directory invalid")
                    .join(maybe_cvc5_path);
            }
            cmd.env("VERUS_CVC5_PATH", &maybe_cvc5_path);
        }
    };

    let original_args = args.clone();

    let source_file = record::find_source_file(&args);

    let record_history_project_dirs: Option<(std::path::PathBuf, std::path::PathBuf)> = if let Ok(
        source_file,
    ) =
        source_file.as_ref()
    {
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
            #[cfg(feature = "record-history")]
            {
                if unpretty_arg {
                    warning(
                        "a `-Z unpretty` argument was specified, which is incompatible with history recording; disabling hisotry recording for this session",
                    );
                    None
                } else {
                    if !history_dir.is_dir() {
                        return Err(format!(
                            ".record-history ({}) is not a directory",
                            history_dir.display()
                        ));
                    }
                    Some((project_dir, history_dir))
                }
            }
            #[cfg(not(feature = "record-history"))]
            {
                warning(&format!(
                    "this project {} opted in to history recording via {}, but Verus was compiled without --features record-history and thus will not be recording history",
                    project_dir.display(),
                    history_dir.display(),
                ));
                None
            }
        } else {
            None
        }
    } else {
        None
    };

    if record || record_history_project_dirs.is_some() {
        fn ensure_arg(args: &mut Vec<String>, arg: String) {
            if !args.contains(&arg) {
                args.push(arg.into());
            }
        }
        ensure_arg(&mut args, "--output-json".into());
        ensure_arg(&mut args, "--time".into());
        ensure_arg(&mut args, "--time-expanded".into());
        if args.iter().find(|x| x.starts_with("--emit")).is_some() {
            return Err(format!(
                "an explicit --emit argument is not allowed when recording a report or when history recording is enabled",
            ));
        } else {
            if args.contains(&"--compile".to_owned()) {
                ensure_arg(&mut args, "--emit=dep-info,link".into());
            } else {
                ensure_arg(&mut args, "--emit=dep-info".into());
            }
        }
    }

    #[cfg(feature = "record-history")]
    if record_history_project_dirs.is_some() && is_terminal::is_terminal(&std::io::stderr()) {
        if !args.iter().any(|x| x.starts_with("--color")) {
            args.push("--color=always".to_owned());
        } else if let Some(pos) = args.iter().position(|x| x == "--color=auto") {
            args.remove(pos);
            args.insert(pos, "--color=always".into());
        }
    }

    cmd.arg("run")
        .arg(TOOLCHAIN)
        .arg("--")
        .arg(verusroot_path.join(RUST_VERIFY_FILE_NAME))
        .args(&args)
        .stdin(std::process::Stdio::inherit());

    // HOTFIX: On Windows, libraries are in the bin directory, not in the lib directory,
    // so we currently need the old behavior of rustup of adding the bin directory to the PATH.
    #[cfg(windows)]
    cmd.env("RUSTUP_WINDOWS_PATH_ADD_BIN", "1");

    if !record && record_history_project_dirs.is_none() {
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
        let z3_version_output = record
            .then_some(())
            .and_then(|()| z3_path)
            .and_then(|ref z3_path| record::get_z3_version(z3_path));

        let source_file = source_file?;

        let temp_dep_file = record::temp_dep_file_from_source_file(&source_file)?;

        #[cfg(feature = "record-history")]
        let record_history_repo =
            record_history::find_record_history_repo(record_history_project_dirs)?;

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
                return Err(format!("failed to execute rust_verify {}", err,));
            }
        };

        let (verus_stdout, verus_stderr) = (
            verus_child.stdout.take().expect("no stdout on verus child process"),
            verus_child.stderr.take().expect("no stderr on verus child process"),
        );

        fn start_reader_thread(
            child_stdio: impl Read + Send + 'static,
            print_to: Option<impl Write + Send + 'static>,
        ) -> std::thread::JoinHandle<Vec<u8>> {
            std::thread::spawn(move || {
                let mut child_stdio = child_stdio;
                let mut print_to = print_to;
                let mut buffer = vec![0; 512];
                let mut full_output = Vec::with_capacity(1024);
                loop {
                    let bytes = child_stdio.read(&mut buffer[..]).expect("read from stdio failed");
                    if bytes == 0 {
                        break;
                    }
                    if let Some(print_to) = &mut print_to {
                        print_to.write(&buffer[..bytes]).expect("failed to write to stdio");
                    }
                    full_output
                        .write_all(&buffer[..bytes])
                        .expect("failed to write to internal buffer");
                }
                let bytes = child_stdio.read_to_end(&mut buffer).expect("read from stdio failed");
                if let Some(print_to) = &mut print_to {
                    print_to.write(&buffer[..bytes]).expect("failed to write to stdio");
                }
                full_output
                    .write_all(&buffer[..bytes])
                    .expect("failed to write to internal buffer");
                full_output
            })
        }

        let verus_full_stdout_handle = start_reader_thread(verus_stdout, None::<std::io::Stdout>);
        let verus_full_stderr_handle =
            start_reader_thread(verus_stderr, (!record).then(|| std::io::stderr()));

        let exit_status: std::process::ExitStatus = match verus_child.wait() {
            Ok(exit_status) => exit_status,
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

        let verus_full_stdout =
            verus_full_stdout_handle.join().expect("stdout reader thread failed");
        let verus_full_stderr =
            verus_full_stderr_handle.join().expect("stderr reader thread failed");

        let verus_duration = start_time.elapsed();

        #[cfg(feature = "record-history")]
        record_history::print_verification_results(record, &verus_full_stdout);

        let toml_value = match record::error_report_toml_value(
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
