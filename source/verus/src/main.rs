use sha2::Digest;
use std::fs::{create_dir_all, read_to_string, remove_dir_all, write, File};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::Command;
use toml::{map::Map, value::Value};

const TOOLCHAIN: &str = env!("VERUS_TOOLCHAIN");

const RUST_VERIFY_FILE_NAME: &str =
    if cfg!(target_os = "windows") { "rust_verify.exe" } else { "rust_verify" };

const Z3_FILE_NAME: &str = if cfg!(target_os = "windows") { ".\\z3.exe" } else { "./z3" };

const OPT_IN_FILE_NAME: &str = ".verus_opt_in";

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

    // check for --color=auto
    if let Some(x) = args_bucket.iter().position(|x| x.as_str() == "--color=auto") {
        if is_terminal::is_terminal(&std::io::stderr())
            || is_terminal::is_terminal(&std::io::stdout())
        {
            args_bucket[x] = "--color=always".into();
        } else {
            args_bucket[x] = "--color=never".into();
        }
    }

    // check if --color auto is in args
    if let Some(x) = args_bucket.iter().position(|x| x.as_str() == "--color") {
        if x + 1 < args_bucket.len() && args_bucket[x + 1] == "auto" {
            args_bucket.remove(x + 1);
            if is_terminal::is_terminal(&std::io::stderr())
                || is_terminal::is_terminal(&std::io::stdout())
            {
                args_bucket[x] = "--color=always".into();
            } else {
                args_bucket[x] = "--color=never".into();
            }
        }
    }

    // if not supplied, same as --color auto
    if !std::env::args().any(|arg| arg.starts_with("--color")) {
        if is_terminal::is_terminal(&std::io::stderr())
            || is_terminal::is_terminal(&std::io::stdout())
        {
            args_bucket.push("--color=always".into());
        } else {
            args_bucket.push("--color=never".into());
        }
    }

    cmd.arg("run")
        .arg(TOOLCHAIN)
        .arg("--")
        .arg(verusroot_path.join(RUST_VERIFY_FILE_NAME))
        .args(args_bucket)
        .stdin(std::process::Stdio::inherit());

    match exec(&mut cmd, report_path) {
        Err(e) => {
            eprintln!("{}: failed to execute rust_verify: {}", yansi::Paint::red("error"), e);
            std::process::exit(128);
        }
        Ok(code) => {
            std::process::exit(code);
        }
    }
}

pub fn exec(cmd: &mut Command, reports: Option<Reports>) -> Result<i32, String> {
    #[cfg(windows)]
    {
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
            if !reports.project_directory.is_dir() {
                cmd.status().map_err(|x| format!("verus failed to run with error: {}", x))?;
                return Ok(0);
            }
            reports
        }
        None => {
            cmd.status().map_err(|x| format!("verus failed to run with error: {}", x))?;
            return Ok(0);
        }
    };

    let project_directory = reports.project_directory;

    cmd.arg(format!("--emit=dep-info={}", reports.dependencies_listing_file.display()));

    // clean all files in project_directory
    remove_dir_all(&project_directory).expect("failed to remove repo_path");

    let toml_path = project_directory.join("reports.toml");

    create_dir_all(&project_directory).expect("creating reports.toml");

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

    let ecode = child.wait().map_err(|x| format!("verus failed to run with error: {}", x))?;

    let mut map = Map::new();
    map.insert("title".to_string(), Value::String("Verus Snapshot".to_string()));
    map.insert("verus-stdout".into(), Value::String(out_string));
    map.insert("verus-stderr".into(), Value::String(err_string));
    let toml_content = Value::Table(map);

    write(toml_path, toml::to_string_pretty(&toml_content).unwrap())
        .map_err(|x| format!("failed to write to reports.toml: {}", x))?;

    let dependencies_listing_file = reports.dependencies_listing_file;

    let deps = get_dependencies(&dependencies_listing_file)?;

    let curr_dir = std::env::current_dir().unwrap();
    // append current working dir to all deps
    let deps = deps.iter().map(|x| curr_dir.join(x)).collect::<Vec<_>>();
    let deps_path = deps.iter().map(|x| Path::new(x)).collect::<Vec<_>>();

    // compute common ancester
    let common = common_path::common_path_all(deps_path).expect(&format!(
        "{} Getting common ancestor for dependencies",
        yansi::Paint::red("error").bold()
    ));

    // strip common ancesters
    let deps =
        deps.iter().map(|x| x.strip_prefix(&common).unwrap().to_path_buf()).collect::<Vec<_>>();

    // copy files to repo_path, none of dep should be absolute path at thsi point
    for dep in deps.iter() {
        create_dir_all(project_directory.join(dep.parent().unwrap())).unwrap();
        std::fs::copy(dep, project_directory.join(dep)).map_err(|err| {
            format!(
                "failed to copy file {} to repo_path with error message: {}",
                dep.display(),
                err
            )
        })?;
    }

    Command::new("git").current_dir(&project_directory).arg("add").arg(".").output().map_err(
        |x| format!("localstorage: failed to stage current project with error message: {}", x),
    )?;

    Command::new("git")
        .current_dir(&project_directory)
        .arg("commit")
        .arg("--message")
        .arg("verus command invocation")
        .env("GIT_AUTHOR_NAME", "nobody")
        .env("GIT_AUTHOR_EMAIL", "nobody@nobody.nobody")
        .env("GIT_COMMITTER_NAME", "nobody")
        .env("GIT_COMMITTER_EMAIL", "nobody@nobody.nobody")
        .output()
        .map_err(|x| format!("localstorage: failed to git commit with error message: {}", x))?;

    match ecode.code() {
        Some(code) => Ok(code),
        None => Err(format!("verus failed to generate exit code"))?,
    }
}

#[derive(Debug)]
pub struct Reports {
    project_directory: PathBuf,
    dependencies_listing_file: PathBuf,
}

fn repo_path() -> Option<Reports> {
    // check if user has git as executable
    if Command::new("git").arg("--version").output().is_err() {
        eprintln!(
            "{} Opted into Verus analytics, but git unavailable on system. Please make sure git is installed to be able to use analytics",
            yansi::Paint::yellow("NOTE:").bold()
        );
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

    let userid_file = reports_dir.join("userid");
    if !userid_file.is_file() {
        let userid = uuid::Uuid::new_v4();
        write(&userid_file, userid.to_string()).expect("Writing user id file");
    }

    let userid = read_to_string(&userid_file).expect("Reading user id file");

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

    // take snapshot when there's a .verus_opt_in file in the current directory
    // or any ancestor directory
    if let Some(path) = input_file_path.as_ref() {
        if !path.ancestors().any(|p| p.join(OPT_IN_FILE_NAME).is_file()) {
            return None;
        }
    }

    let project_name = input_file_path
        .as_ref()
        .map(|path| format!("{:x}", sha2::Sha256::digest(path.to_string_lossy().as_bytes())));
    // not sure how to write a ? to replace unwrap

    let proj_dir = project_name.map(|name| {
        let project_dir = reports_dir.join(userid).join(name);
        if !project_dir.is_dir() {
            create_dir_all(&project_dir).expect("failed to create project directory");
        }
        project_dir
    });

    let dir = std::env::temp_dir();
    let temp_file = dir.join("verus-dep-info");

    Some(Reports { project_directory: proj_dir?, dependencies_listing_file: temp_file })
}

fn get_dependencies(dependencies_listing_file: &std::path::Path) -> Result<Vec<PathBuf>, String> {
    let file = File::open(dependencies_listing_file)
        .map_err(|x| format!("{}, dependency file name: {:?}", x, dependencies_listing_file))?;
    let mut reader = std::io::BufReader::new(file);
    let mut dependencies = String::new();
    reader.read_line(&mut dependencies).map_err(|x| {
        format!("Could not read the first line of the dependency file with message: {}", x)
    })?;
    let dep: Vec<String> = dependencies.split_whitespace().skip(1).map(|x| x.to_string()).collect();
    let result = dep.into_iter().map(|x| PathBuf::from(x)).collect();
    Ok(result)
}
