use std::fs::create_dir_all;
use std::io::BufRead;
use std::path::PathBuf;
use std::process::Command;
mod platform {
    pub struct ExitCode(pub i32);

    use std::process::Command;

    #[cfg(unix)]
    pub fn exec(cmd: &mut Command) -> std::io::Result<ExitCode> {
        // is it okay to execute this as child process?
        let status = cmd.status()?;
        Ok(ExitCode(status.code().unwrap()))
    }

    // thew windows version seems to use cmd.status() to execute the command
    // which also forks the process to create a child process (unlike exec)

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

    let parent = current_exe.and_then(|current| current.parent().map(PathBuf::from));

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

    let report_path = repo_path();

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

    match report_path.clone() {
        Some(reports) => {
            std::env::set_var("VERUS_REPORT_PATH", reports.path);
            std::env::set_var("VERUS_CRATE_ROOT", reports.crate_root);
            // std::fs::remove_file(std::env::current_dir().unwrap().join(reports.crate_root.with_extension(".d"))).ok();
        }
        None => {}
    }

    // let color_arg = if is_tty() { "--color=always" } else { "--color=never" };

    cmd.arg("run")
        .arg(TOOLCHAIN)
        .arg("--")
        .arg(verusroot_path.join(RUST_VERIFY_FILE_NAME))
        .arg("--emit=dep-info")
        // .arg(color_arg)
        .args(args)
        .stdin(std::process::Stdio::inherit());
    // piped stdout/stderr
    // .stdout(std::process::Stdio::piped())
    // .stderr(std::process::Stdio::piped());
    // pseudo-tty see the color_arg function defined before this run

    match platform::exec(&mut cmd) {
        Err(e) => {
            eprintln!("error: failed to execute rust_verify {e:?}");
            std::process::exit(128);
        }
        Ok(code) => {
            if let Some(reports) = report_path {
                let repo_path = reports.path.clone();

                let dep_file_rel_path = reports
                    .crate_root
                    .with_extension("d")
                    .file_name()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_string();

                let dep_file_path = std::env::current_dir().unwrap().join(dep_file_rel_path);

                let deps = get_dependencies(dep_file_path.clone());

                // copy files to repo_path
                for dep in deps.iter() {
                    println!("copying {} into {}", dep.display(), repo_path.join(dep).display());
                    // copy cnannt create non-existing directories
                    create_dir_all(repo_path.join(dep.parent().unwrap())).unwrap();
                    std::fs::copy(dep, repo_path.join(dep)).unwrap();
                }

                clean_up(dep_file_path);
            }
            std::process::exit(code.0);
        }
    }
}

type ReportsPath = Option<Reports>;
#[derive(Debug)]
struct Reports {
    path: PathBuf,
    crate_root: PathBuf,
}

// is it easier to impl the copy trait? I'm not sure about the paradigm here
impl Clone for Reports {
    fn clone(&self) -> Self {
        Self { path: self.path.clone(), crate_root: self.crate_root.clone() }
    }
}

fn repo_path() -> ReportsPath {
    // Step 1: check if there's a verus/reports/.git file in the XDG cache,
    // if not so, create verus/ directory
    let cache_dir = dirs::data_local_dir().expect("cache dir invalid");
    let repo_dir = cache_dir.join("verus").join("reports");
    if !repo_dir.clone().join(".git").is_file() {
        std::fs::create_dir_all(repo_dir.clone())
            .expect("Creating verus/ directory in local data cache");

        std::process::Command::new("git")
            .current_dir(&repo_dir)
            .arg("init")
            .output()
            .expect("Initializing git in local data cache");
    }

    let uuid_file = repo_dir.join("userid");
    if !uuid_file.is_file() {
        let uuid = uuid::Uuid::new_v4();
        std::fs::write(uuid_file, uuid.to_string()).expect("Writing user id file");
    }

    // Step 3: project dir check/create (project = SHA256((normalized/absolute)path to root.rs)

    // clone is not implemented for Args, so i grabbed the arguments here again
    let new_args = std::env::args().into_iter();

    let rs_files = new_args.filter(|arg| arg.ends_with(".rs")).collect::<Vec<_>>();

    let input_file: Option<String> = match rs_files.len() {
        1 => Some(rs_files[0].clone()),
        _ => {
            eprintln!("{}: cannot find input file", yansi::Paint::red("error"));
            None // passed down to rust_verify for error message
        }
    };

    let input_file_path = match input_file.clone() {
        Some(input_file_name) => std::fs::canonicalize(input_file_name).ok(),
        None => None,
    };

    let project_name = match input_file_path.clone() {
        Some(path) => Some(sha256::digest(path.into_os_string().into_string().unwrap().as_bytes())),
        None => None,
    };

    let proj_dir = match project_name {
        Some(name) => {
            let project_dir = repo_dir.join(name);
            if !project_dir.is_dir() {
                std::fs::create_dir_all(project_dir.clone())
                    .expect("failed to create project directory");
            }
            Some(project_dir)
        }
        None => None,
    };

    match (input_file_path, proj_dir) {
        (Some(crate_root_path), Some(proj_dir)) => {
            Some(Reports { path: proj_dir, crate_root: crate_root_path })
        }
        _ => None,
    }
}

fn clean_up(file: PathBuf) {
    println!("removing {}", std::env::current_dir().unwrap().join(file.clone()).display());
    std::fs::remove_file(file).expect("remove crate root dependency file");
}

fn get_dependencies(file_name: PathBuf) -> Vec<PathBuf> {
    let file = std::fs::File::open(file_name).expect("Couldn't open file!");
    let mut reader = std::io::BufReader::new(file);
    let mut dependencies = String::new();
    reader.read_line(&mut dependencies).expect("Could not read the first line");
    let dep: Vec<String> = dependencies.split_whitespace().skip(1).map(|x| x.to_string()).collect();
    println!("dependencies: {:?}", dep);
    return dep.into_iter().map(|x| PathBuf::from(x)).collect();
}
