use sha2::Digest;
use std::fs::{create_dir_all, read_to_string, remove_dir_all, write, File};
use std::io::Write;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
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

    // This unfortunately isn't a sufficient check; if the user specifies it as --color=never, but they are on a terminal, then it will still give color.

    // Also it doesn't account for users passing the always/never argument as the next parameter, rather than using = (eg: verus --color always foo.rs).

    let color_arg = if std::env::args().any(|arg| arg == "--color=always") {
        "--color=always"
    } else if is_terminal::is_terminal(&std::io::stderr())
        && is_terminal::is_terminal(&std::io::stdout())
    {
        "--color=always"
    } else {
        "--color=never"
    };

    cmd.arg("run")
        .arg(TOOLCHAIN)
        .arg("--")
        .arg(verusroot_path.join(RUST_VERIFY_FILE_NAME))
        .arg("--emit=dep-info")
        .arg(color_arg)
        .args(args)
        .stdin(std::process::Stdio::inherit());

    match exec(&mut cmd, report_path) {
        Err(e) => {
            eprintln!(
                "{}",
                yansi::Paint::red(format!("error: failed to execute rust_verify: {}", e))
            );
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
        Some(reports) => reports,
        None => {
            // need to keep running rust_verify to get the rustc error message
            cmd.status().map_err(|x| format!("verus failed to run with error: {}", x))?;
            return Ok(());
        }
    };

    let proj_path = reports.proj_path;

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
            let to_push = anstream::adapter::strip_str(&line).to_string() + "\n";
            stderr_output.push_str(&to_push);
        });
        return stderr_output;
    });

    let thread_out = std::thread::spawn(move || {
        let mut stdout_output = String::new();
        out.lines().for_each(|line| {
            let line = line.unwrap();
            println!("{}", line);
            let to_push = anstream::adapter::strip_str(&line).to_string() + "\n";
            stdout_output.push_str(&to_push);
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

    // TODO: going to change after using --emit-dep-info=PATH
    let dep_file_rel_path =
        reports.crate_root.with_extension("d").file_name().unwrap().to_str().unwrap().to_string();

    let dep_file_path = std::env::current_dir().unwrap().join(dep_file_rel_path);

    let deps = get_dependencies(&dep_file_path)?;

    // copy files to repo_path
    for dep in deps.iter() {
        // change path to relative path, since adjoining a relative path will overwrite the caller path
        let rel_path = if dep.is_absolute() {
            if cfg!(windows) {
                dep.strip_prefix(r"C:\")
                    .map_err(|err| format!("failed to strip absolute path {}", err))?
            } else {
                dep.strip_prefix("/")
                    .map_err(|err| format!("failed to strip absolute path {}", err))?
            }
        } else {
            &dep
        };
        create_dir_all(proj_path.join(rel_path.parent().unwrap())).unwrap();

        std::fs::copy(dep, proj_path.join(rel_path))
            .map_err(|err| format!("failed to copy file {} to repo_path {}", dep.display(), err))?;
    }

    std::fs::remove_file(&dep_file_path).map_err(|err| {
        format!(
            "failed to remove dependency file {} in local data cache with error message: {}",
            dep_file_path.display(),
            err
        )
    })?;

    Command::new("git")
        .current_dir(&proj_path)
        .arg("add")
        .args(deps)
        .arg("reports.toml")
        .output()
        .map_err(|x| {
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
    crate_root: PathBuf,
}

fn repo_path() -> Option<Reports> {
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
            eprintln!("{}: cannot find input file", yansi::Paint::red("error"));
            None // passed down to rust_verify for error message
        }
    };

    let input_file_path = input_file.and_then(|f| std::fs::canonicalize(f).ok());

    let project_name = input_file_path
        .as_ref()
        .map(|path| format!("{:x}", sha2::Sha256::digest(path.to_str().unwrap().as_bytes())));

    let proj_dir = project_name.map(|name| {
        let project_dir = reports_dir.join(uuid).join(name);
        if !project_dir.is_dir() {
            create_dir_all(&project_dir).expect("failed to create project directory");
        }
        project_dir
    });

    match (input_file_path, proj_dir) {
        (Some(crate_root_path), Some(proj_dir)) => {
            Some(Reports { proj_path: proj_dir, crate_root: crate_root_path })
        }
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
