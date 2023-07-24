use sha2::Digest;
use std::fs::{create_dir_all, read_to_string, remove_dir_all, write, File};
use std::io::Write;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::Command;

const TOOLCHAIN: &str = env!("VERUS_TOOLCHAIN");

const RUST_VERIFY_FILE_NAME: &str =
    if cfg!(target_os = "windows") { "rust_verify.exe" } else { "rust_verify" };

const Z3_FILE_NAME: &str = if cfg!(target_os = "windows") { ".\\z3.exe" } else { "./z3" };

fn main() {
    if cfg!(windows) && !yansi::Paint::enable_windows_ascii() {
        yansi::Paint::disable();
    }
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

    let mut args_bucket = args.collect::<Vec<_>>();

    let local_store = args_bucket
        .iter()
        .position(|x| x.as_str() == "--local-store")
        .map(|p| args_bucket.remove(p))
        .is_some();

    let report_path = repo_path(local_store);

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
        .args(args_bucket)
        .stdin(std::process::Stdio::inherit());

    if !std::env::args().any(|arg| arg.starts_with("--color")) {
        if is_terminal::is_terminal(&std::io::stderr())
            || is_terminal::is_terminal(&std::io::stdout())
        {
            cmd.arg("--color=always");
        } else {
            cmd.arg("--color=never");
        }
    }

    match exec(&mut cmd, report_path) {
        Err(e) => {
            eprintln!("{}: failed to execute rust_verify: {}", yansi::Paint::red("error"), e);
            std::process::exit(128);
        }
        Ok(_) => {
            std::process::exit(0);
        }
    }
}

pub fn exec(cmd: &mut Command, reports: Option<Reports>) -> Result<(), String> {
    #[cfg(windows)]
    if cfg!(windows) {
        // Configure Windows to kill the child SMT process if the parent is killed
        let job = win32job::Job::create()
            .map_err(|_| format!("last os error: {}", std::io::Error::last_os_error()))?;
        let mut info = job
            .query_extended_limit_info()
            .map_err(|_| format!("last os error: {}", std::io::Error::last_os_error()))?;
        info.limit_kill_on_job_close();
        job.set_extended_limit_info(&mut info)
            .map_err(|_| format!("last os error: {}", std::io::Error::last_os_error()))?;
        job.assign_current_process()
            .map_err(|_| format!("last os error: {}", std::io::Error::last_os_error()))?;
        std::mem::forget(job);
    }

    let reports = match reports {
        Some(reports) => {
            // proj path is only created after the project has --local-store flag
            if !reports.proj_path.is_dir() {
                cmd.status().map_err(|x| format!("verus failed to run with error: {}", x))?;
                return Ok(());
            }
            reports
        },
        None => {
            cmd.status().map_err(|x| format!("verus failed to run with error: {}", x))?;
            return Ok(());
        }
    };

    let proj_path = reports.proj_path;

    cmd.arg(format!("--emit=dep-info={}", reports.dep_path.display()));

    // clean all files in proj_path
    remove_dir_all(&proj_path).expect("failed to remove repo_path");

    let toml_path = proj_path.join("reports.toml");

    create_dir_all(&proj_path).expect("creating reports.toml");
    let mut file = File::create(toml_path).expect("creating reports.toml");

    let mut child = cmd
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|x| format!("verus failed to run with error: {}", x))?;

    let out = BufReader::new(child.stdout.take().expect("create BufReader for stdout"));
    let err = BufReader::new(child.stderr.take().expect("create BufReader for stderr"));

    let thread_err = std::thread::spawn(move || {
        let mut stderr_output = String::new();
        err.lines().for_each(|line| {
            let line = line.unwrap();
            eprintln!("{}", line);
            let x = anstream::adapter::strip_str(&line).to_string() + "\n";
            stderr_output.push_str(&x);
        });
        return stderr_output;
    });

    let thread_out = std::thread::spawn(move || {
        let mut stdout_output = String::new();
        out.lines().for_each(|line| {
            let line = line.unwrap();
            println!("{}", line);
            let x = anstream::adapter::strip_str(&line).to_string() + "\n";
            stdout_output.push_str(&x);
        });
        return stdout_output;
    });

    let err_string = thread_err.join().unwrap();
    let out_string = thread_out.join().unwrap();

    child.wait().map_err(|x| format!("verus failed to run with error: {}", x))?;

    writeln!(file, "{}", err_string)
        .map_err(|x| format!("failed to write to reports.toml: {}", x))?;
    writeln!(file, "{}", out_string)
        .map_err(|x| format!("failed to write to reports.toml: {}", x))?;

    let dep_file_path = reports.dep_path;

    let deps = get_dependencies(&dep_file_path)?;

    let deps_path = deps.iter().map(|x| Path::new(x)).collect::<Vec<_>>();

    // compute common ancester
    let common = match common_path::common_path_all(deps_path) {
        Some(common) => common,
        None => PathBuf::from(""),
    };

    if deps.clone().into_iter().any(|dep| dep.is_absolute()) {
        // copy files to repo_path
        for dep in deps.iter() {
            let rel_dest = dep.clone().strip_prefix(&common).unwrap().to_path_buf();
            create_dir_all(proj_path.join(&rel_dest.parent().unwrap())).unwrap();
            std::fs::copy(dep, proj_path.join(&rel_dest)).map_err(|err| {
                format!(
                    "failed to copy file {} to repo_path with error message: {}",
                    dep.display(),
                    err
                )
            })?;
        }
    } else {
        // copy files to repo_path, none of dep should be absolute path at thsi point
        for dep in deps.iter() {
            create_dir_all(proj_path.join(dep.parent().unwrap())).unwrap();
            std::fs::copy(dep, proj_path.join(dep)).map_err(|err| {
                format!(
                    "failed to copy file {} to repo_path with error message: {}",
                    dep.display(),
                    err
                )
            })?;
        }
    }

    std::fs::remove_file(&dep_file_path).map_err(|err| {
        format!(
            "failed to remove dependency file {} in local data cache with error message: {}",
            dep_file_path.display(),
            err
        )
    })?;

    Command::new("git").current_dir(&proj_path).arg("add").arg(".").output().map_err(|x| {
        format!("localstorage: failed to stage current project with error message: {}", x)
    })?;

    std::process::Command::new("git")
        .current_dir(&proj_path)
        .arg("commit")
        .arg("-m")
        .arg("\"verus\"")
        .env("GIT_AUTHOR_NAME", "nobody")
        .env("GIT_AUTHOR_EMAIL", "nobody@nobody.nobody")
        .env("GIT_COMMITTER_NAME", "nobody")
        .env("GIT_COMMITTER_EMAIL", "nobody@nobody.nobody")
        .output()
        .map_err(|x| format!("localstorage: failed to git commit with error message: {}", x))?;

    Ok(())
}

#[derive(Debug)]
pub struct Reports {
    proj_path: PathBuf,
    dep_path: PathBuf,
}

fn repo_path(store: bool) -> Option<Reports> {
    // check if user has git as executable
    if Command::new("git").arg("--version").output().is_err() {
        return None;
    }

    // check if user has local storage enabled during vargo build
    if option_env!("VERUS_LOCAL_STORE").is_none() {
        return None;
    }
    
    // Check if there's a verus/reports/.git file in the user's local data lib
    // if not so, create verus/ directory
    let reports_dir = dirs::data_local_dir()?.join("verus").join("reports");

    if !reports_dir.join(".git").is_file() {
        create_dir_all(&reports_dir).expect("Creating verus/ directory in local data dir");

        Command::new("git")
            .current_dir(&reports_dir)
            .arg("init")
            .output()
            .expect("Initializing git in local data dir");
    }

    let uuid_file = reports_dir.join("userid");
    if !uuid_file.is_file() {
        let uuid = uuid::Uuid::new_v4();
        write(&uuid_file, uuid.to_string()).expect("Writing user id file");
    }

    let uuid = read_to_string(&uuid_file).expect("Reading user id file");

    // Project dir check/create (project = SHA256((normalized/absolute)path to root.rs)
    let new_args = std::env::args().into_iter();

    let rs_files = new_args.filter(|arg| arg.ends_with(".rs")).collect::<Vec<_>>();

    let input_file: Option<String> = match rs_files.len() {
        1 => Some(rs_files[0].clone()),
        _ => {
            None // passed down to rust_verify for error message
        }
    };

    let input_file_path = input_file.and_then(|f| std::fs::canonicalize(f).ok());

    let project_name = input_file_path
        .as_ref()
        .map(|path| format!("{:x}", sha2::Sha256::digest(path.to_str().unwrap().as_bytes())));
    // not sure how to write a ? to replace unwrap

    let proj_dir = project_name.map(|name| {
        let project_dir = reports_dir.join(uuid).join(name);        
        if !project_dir.is_dir() && store {
            create_dir_all(&project_dir).expect("failed to create project directory");
        }
        project_dir
    });

    let dir = std::env::temp_dir();
    let temp_file = dir.join("verus-dep-info");

    match (input_file_path, proj_dir) {
        (Some(_), Some(proj_dir)) => Some(Reports { proj_path: proj_dir, dep_path: temp_file }),
        _ => None,
    }
}

fn get_dependencies(dep_file_path: &std::path::Path) -> Result<Vec<PathBuf>, String> {
    let file = File::open(dep_file_path)
        .map_err(|x| format!("{}, dependency file name: {:?}", x, dep_file_path))?;
    let mut reader = std::io::BufReader::new(file);
    let mut dependencies = String::new();
    reader.read_line(&mut dependencies).map_err(|x| {
        format!("Could not read the first line of the dependency file with message: {}", x)
    })?;
    let dep: Vec<String> = dependencies.split_whitespace().skip(1).map(|x| x.to_string()).collect();
    let result = dep.into_iter().map(|x| PathBuf::from(x)).collect();
    Ok(result)
}
