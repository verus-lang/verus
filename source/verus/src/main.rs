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

const RUST_VERIFY: &str =
    if cfg!(target_os = "windows") { "rust_verify.exe" } else { "rust_verify" };

fn main() {
    let mut args = std::env::args().into_iter();
    let _bin = args.next().expect("executable in args");

    let Some(verusroot_path) = std::env::current_exe().ok().and_then(|current| {
        current.parent().and_then(|p| {
            let mut path = std::path::PathBuf::from(&p);
            if path.join("verus-root").is_file() {
                if !path.is_absolute() {
                    path =
                        std::env::current_dir().expect("working directory invalid").join(path);
                }
                Some(path)
            } else {
                None
            }
        })
    }) else {
        eprintln!("error: did not find a valid verusroot");
        std::process::exit(128);
    };

    let mut cmd = Command::new("rustup");
    cmd.arg("run")
        .arg(TOOLCHAIN)
        .arg("--")
        .arg(verusroot_path.join(RUST_VERIFY))
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
