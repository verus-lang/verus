use std::fs::create_dir_all;
use std::io::BufRead;
use std::path::PathBuf;
use std::process::Command;

mod platform {
    pub struct ExitCode(pub i32);
    use crate::ReportsPath;
    use std::process::Command;

    pub fn exec(cmd: &mut Command, reports: ReportsPath) -> std::io::Result<ExitCode> {
        use std::io::Write;
        use std::io::{BufRead, BufReader};
        use std::process::Stdio;
        use std::thread;

        #[cfg(windows)]
        {
            // Configure Windows to kill the child SMT process if the parent is killed
            let job = win32job::Job::create().map_err(|_| std::io::Error::last_os_error())?;
            let mut info =
                job.query_extended_limit_info().map_err(|_| std::io::Error::last_os_error())?;
            info.limit_kill_on_job_close();
            job.set_extended_limit_info(&mut info).map_err(|_| std::io::Error::last_os_error())?;
            job.assign_current_process().map_err(|_| std::io::Error::last_os_error())?;
            std::mem::forget(job);
        }

        if let None = reports {
            // need to keep running rust_verify to get the rustc error message
            let status = cmd.status()?;
            return Ok(ExitCode(status.code().unwrap()));
        }

        let toml_path = reports.unwrap().proj_path.join("reports.toml");
        eprintln!("toml_path: {:?}", toml_path);

        let mut file = std::fs::File::create(toml_path).expect("creating reports.toml");

        let mut child = cmd.stdout(Stdio::piped()).stderr(Stdio::piped()).spawn()?;

        let out = BufReader::new(child.stdout.take().unwrap());
        let err = BufReader::new(child.stderr.take().unwrap());

        let thread_err = thread::spawn(move || {
            let mut tmpstr = String::new();
            err.lines().for_each(|line| {
                let line = line.unwrap();
                eprintln!("{}", line);
                let to_push = anstream::adapter::strip_str(&line).to_string() + "\n";
                tmpstr.push_str(&to_push);
            });
            return tmpstr;
        });

        let thread_out = thread::spawn(move || {
            let mut tmpstr = String::new();
            out.lines().for_each(|line| {
                let line = line.unwrap();
                println!("{}", line);
                let to_push = anstream::adapter::strip_str(&line).to_string() + "\n";
                tmpstr.push_str(&to_push);
            });
            return tmpstr;
        });

        let err_string = thread_err.join().unwrap();
        let out_string = thread_out.join().unwrap();

        writeln!(file, "{}", err_string).unwrap();
        writeln!(file, "{}", out_string).unwrap();

        let status = child.wait()?;

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

    // change it to return Child process and do all the operations here
    match platform::exec(&mut cmd, report_path.clone()) {
        Err(e) => {
            eprintln!("error: failed to execute rust_verify {e:?}");
            std::process::exit(128);
        }
        Ok(code) => {
            if let Some(reports) = report_path {
                let repo_path = reports.proj_path.clone();

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

                // clean all files in repo_path
                std::fs::remove_dir_all(&repo_path).expect("failed to remove repo_path");

                // copy files to repo_path
                for dep in deps.iter() {
                    println!(
                        "\n{} {} {} {}",
                        yansi::Paint::blue("copying"),
                        dep.display(),
                        yansi::Paint::blue("into"),
                        repo_path.join(dep).display()
                    );
                    // copy cnannt create non-existing directories
                    create_dir_all(repo_path.join(dep.parent().unwrap())).unwrap();
                    std::fs::copy(dep, repo_path.join(dep)).unwrap();
                }

                clean_up(dep_file_path);

                // step 5, git commiting
                // git add
                std::process::Command::new("git")
                .current_dir(&repo_path)
                .arg("add")
                .args(deps)
                .output()
                .expect("commiting");
    
                // git commit
                println!(
                    "\n{} {}",
                    yansi::Paint::blue("commiting"),
                    repo_path.display()
                );
                std::process::Command::new("git")
                    .current_dir(&repo_path)
                    .arg("commit")
                    .arg("-m")
                    .arg("\"verus telemtry\"")
                    .output()
                    .expect("commiting");
                

            }
            std::process::exit(code.0);
        }
    }
}

pub type ReportsPath = Option<Reports>;
#[derive(Debug)]
pub struct Reports {
    proj_path: PathBuf,
    crate_root: PathBuf,
}

// is it easier to impl the copy trait? I'm not sure about the paradigm here
impl Clone for Reports {
    fn clone(&self) -> Self {
        Self { proj_path: self.proj_path.clone(), crate_root: self.crate_root.clone() }
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
            Some(Reports { proj_path: proj_dir, crate_root: crate_root_path })
        }
        _ => None,
    }
}

fn clean_up(file: PathBuf) {
    println!(
        "\n{} {}",
        yansi::Paint::blue("removing:"),
        std::env::current_dir().unwrap().join(file.clone()).display()
    );
    std::fs::remove_file(file).expect("remove crate root dependency file");
}

fn get_dependencies(file_name: PathBuf) -> Vec<PathBuf> {
    let file = std::fs::File::open(file_name).expect("Couldn't open file!");
    let mut reader = std::io::BufReader::new(file);
    let mut dependencies = String::new();
    reader.read_line(&mut dependencies).expect("Could not read the first line");
    let dep: Vec<String> = dependencies.split_whitespace().skip(1).map(|x| x.to_string()).collect();
    println!("\n{} {:?}", yansi::Paint::blue("dependencies:"), dep);
    return dep.into_iter().map(|x| PathBuf::from(x)).collect();
}
