use std::process::Command;
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
    let mut args = std::env::args().into_iter();
    let _bin = args.next().expect("executable in args");

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

    // Step 1: check if there's a verus/reports/.git file in the XDG cache,
    // if not so, create verus/ directory
    // https://docs.rs/dirs/latest/dirs/
    let cache_dir = dirs::data_local_dir().expect("cache dir invalid");
    let repo_dir = cache_dir.join("verus").join("reports");
    if !repo_dir.clone().join(".git").is_file() {
        // create verus/reports/ directory
        std::fs::create_dir_all(repo_dir.clone()).expect("failed to create verus/ directory");

        // create verus/reports/.git file
        std::process::Command::new("git")
            .current_dir(&repo_dir)
            .arg("init")
            .output()
            .expect("failed to init git in user's cache directory.");
    }

    // Step 2: check if file verus/reports/userid exists, if not so, create it
    // https://docs.rs/uuid/latest/uuid/

    // at this point, there must be a .git file in cache_dir/verus/reports
    // we check if there's a uuid file
    if !repo_dir.clone().join("uuid").is_file() {
        // create uuid file
        let uuid = uuid::Uuid::new_v4();
        std::fs::write(repo_dir.join("uuid"), uuid.to_string()).expect("failed to write uuid file");
    }

    // Step 3: project dir check/create (project = SHA256((normalized/absolute)path to foo.rs)
    // note that we need the convention that verus should be run like
    // verus INPUT [options]

    // clone is not implemented for Args, so i grabbed the arguments here again
    let new_args = std::env::args().into_iter();

    // this step assumes the input_file is the first file that has .rs extension
    let input_file = match new_args.filter(|arg| arg.ends_with(".rs")).next() {
        Some(file) => file,
        None => {
            eprintln!(
                "{}: No input file, Usage: <verus_path> INPUT [options]\n",
                nu_ansi_term::Color::Red.bold().paint("error")
            );
            // std::process::exit(2);
            // if I still want it to use rust_verify, I want some default value
            "a".to_string()
        }
    };

    // I probably want rustc like error message of this rather than a panic
    let input_file_path = match std::fs::canonicalize(input_file.clone()) {
        Ok(path) => path,
        Err(_) => {
            eprintln!(
                "{}: could't canonicalize input file {}, No such file or directory\n",
                nu_ansi_term::Color::Red.bold().paint("error"),
                input_file
            );
            // std::process::exit(2);
            std::path::Path::new("a").to_path_buf()
        }
    };

    // in the prototype, the assumption is that the project file will be the
    // normalzed path to whatever the .rs file is
    let project_name =
        sha256::digest(input_file_path.into_os_string().into_string().unwrap().as_bytes());
    // println!("project_name: {:?}", project_name);

    let project_dir = repo_dir.join(project_name);
    if !project_dir.is_dir() {
        // create project dir
        std::fs::create_dir_all(project_dir.clone()).expect("failed to create project directory");
    }

    let mut cmd = Command::new("rustup");
    if std::env::var("VERUS_Z3_PATH").ok().is_none() {
        if let Some(mut maybe_z3_path) = parent.map(|p| p.join(Z3_FILE_NAME)) {
            if maybe_z3_path.exists() {
                if !maybe_z3_path.is_absolute() {
                    maybe_z3_path = std::env::current_dir()
                        .expect("working directory invalid")
                        .join(maybe_z3_path);
                }
                cmd.env("VERUS_Z3_PATH", maybe_z3_path);
            }
        }
    }
    cmd.arg("run")
        .arg(TOOLCHAIN)
        .arg("--")
        .arg(verusroot_path.join(RUST_VERIFY_FILE_NAME))
        .args(args)
        .stdin(std::process::Stdio::inherit());
    match platform::exec(&mut cmd) {
        Err(e) => {
            eprintln!("error: failed to execute rust_verify {e:?}");
            std::process::exit(128);
        }
        Ok(code) => {
            std::process::exit(code.0);
        }
    }
}
