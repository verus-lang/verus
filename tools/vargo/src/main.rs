// Vargo is a wrapper around cargo that sets up the environment for building
// Verus and collects build artifacts for libraries used by vstd and client
// code so that later compilation stages (building, verifying vstd and running tests)
// can use them. This is necessary because cargo only builds libraries in
// `target/debug` or `target/release` when they are the main build target, and
// not when they're a dependency of another target.

mod util;

use filetime::FileTime as FFileTime;
use regex::Regex;
use serde::{Deserialize, Serialize};

static VARGO_NEST: std::sync::RwLock<u64> = std::sync::RwLock::new(0);

#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Hash, Debug, Deserialize, Serialize)]
struct FileTime {
    seconds: i64,
    nanos: u32,
}

impl From<FFileTime> for FileTime {
    fn from(value: FFileTime) -> Self {
        FileTime {
            seconds: value.seconds(),
            nanos: value.nanoseconds(),
        }
    }
}

#[derive(Debug, Deserialize, Serialize, Eq, PartialEq, Ord, PartialOrd)]
struct Fingerprint {
    dependencies_mtime: FileTime,
    vstd_mtime: FileTime,
}

fn main() {
    match run() {
        Ok(()) => (),
        Err(err) => {
            eprintln!("{}", yansi::Paint::red(format!("error: {}", err)));
            std::process::exit(1);
        }
    }
}

fn info(msg: &str) {
    let vargo_nest = *VARGO_NEST.read().unwrap();
    eprintln!(
        "{}",
        yansi::Paint::blue(format!("vargo info [{}]: {}", vargo_nest, msg))
    );
}

fn warn(msg: &str) {
    let vargo_nest = *VARGO_NEST.read().unwrap();
    eprintln!(
        "{}",
        yansi::Paint::yellow(format!("vargo warn [{}]: {}", vargo_nest, msg))
    );
}

fn log_command(cmd: &std::process::Command, verbose: bool) {
    if verbose {
        let vargo_nest = *VARGO_NEST.read().unwrap();
        eprintln!(
            "{}",
            yansi::Paint::magenta(format!("vargo running [{}]: {:?}", vargo_nest, cmd))
        );
    }
}

const SUPPORTED_COMMANDS: &[&str] = &[
    "build", "test", "nextest", "run", "clean", "fmt", "metadata",
];

const CARGO_FORWARD_ARGS: &[&str] = &["-v", "-vv", "--verbose", "--offline"];
const CARGO_FORWARD_ARG_KEYS: &[&str] = &["--color="];
const CARGO_FORWARD_ARGS_NEXT: &[&str] = &[];

#[derive(Clone, Copy, Debug)]
enum Task {
    Build,
    Test { nextest: bool },
    Run,
    Clean,
    Metadata,
    Fmt,
}

#[cfg(target_os = "macos")]
mod lib_exe_names {
    pub const LIB_PRE: &str = "lib";
    pub const LIB_DL: &str = "dylib";
    pub const EXE: &str = "";
}

#[cfg(target_os = "linux")]
mod lib_exe_names {
    pub const LIB_PRE: &str = "lib";
    pub const LIB_DL: &str = "so";
    pub const EXE: &str = "";
}

#[cfg(target_os = "windows")]
mod lib_exe_names {
    pub const LIB_PRE: &str = "";
    pub const LIB_DL: &str = "dll";
    pub const EXE: &str = ".exe";
}

use lib_exe_names::*;

fn clean_vstd(target_verus_dir: &std::path::PathBuf) -> Result<(), String> {
    for f in vec![
        format!("vstd.vir"),
        format!("{LIB_PRE}vstd.rlib"),
        format!(".vstd-fingerprint"),
    ]
    .into_iter()
    {
        let f = target_verus_dir.join(f);
        if f.is_file() {
            info(format!("removing {}", f.display()).as_str());
            std::fs::remove_file(&f)
                .map_err(|x| format!("could not delete file {} ({x})", f.display()))?;
        }
    }
    Ok(())
}

fn run() -> Result<(), String> {
    let _vargo_nest = {
        let vargo_nest = std::env::var("VARGO_NEST")
            .ok()
            .and_then(|x| x.parse().ok().map(|x: u64| x + 1))
            .unwrap_or(0);
        *VARGO_NEST.write().unwrap() = vargo_nest;
        std::env::set_var("VARGO_NEST", format!("{}", vargo_nest));
        vargo_nest
    };

    let mut args = std::env::args().skip(1).collect::<Vec<_>>();
    let mut args_bucket = args.clone();
    let in_nextest = std::env::var("VARGO_IN_NEXTEST").is_ok();

    let rust_toolchain_toml = toml::from_str::<toml::Value>(
        &std::fs::read_to_string(std::path::Path::new("..").join("rust-toolchain.toml")).map_err(
            |x| {
                format!(
                    "could not read rust-toolchain.toml ({})\nrun vargo in `source`",
                    x
                )
            },
        )?,
    )
    .map_err(|x| format!("could not parse Cargo.toml ({})\nrun vargo in `source`", x))?;
    let rust_toolchain_toml_channel = rust_toolchain_toml.get("toolchain").and_then(|t| t.get("channel"))
        .and_then(|t| if let toml::Value::String(s) = t { Some(s) } else { None })
        .ok_or(
            format!("rust-toolchain.toml does not contain the toolchain.channel key, or it isn't a string\nrun vargo in `source`"))?;

    if !in_nextest {
        let output = std::process::Command::new("rustup")
            .arg("show")
            .arg("active-toolchain")
            .stderr(std::process::Stdio::inherit())
            .output()
            .map_err(|x| format!("could not execute rustup ({})", x))?;
        if !output.status.success() {
            return Err(format!("rustup failed"));
        }
        let active_toolchain_re = Regex::new(
            r"^(([A-Za-z0-9.]+)-[A-Za-z0-9_]+-[A-Za-z0-9]+-[A-Za-z0-9-]+) \(overridden by '(.*)'\)",
        )
        .unwrap();
        let stdout = std::str::from_utf8(&output.stdout)
            .map_err(|_| format!("rustup output is invalid utf8"))?;
        let mut captures = active_toolchain_re.captures_iter(&stdout);
        if let Some(cap) = captures.next() {
            let channel = &cap[2];
            let _toolchain = &cap[1];
            if rust_toolchain_toml_channel != channel {
                return Err(format!("rustup is using a toolchain with channel {channel}, we expect {rust_toolchain_toml_channel}\ndo you have a rustup override set?"));
            }
        } else {
            return Err(format!("unexpected output from `rustup show active-toolchain`\nexpected a toolchain override\ngot: {stdout}"));
        }
    }

    if !std::path::Path::new(if cfg!(target_os = "windows") {
        ".\\z3.exe"
    } else {
        "./z3"
    })
    .is_file()
        && std::env::var("VERUS_Z3_PATH").is_err()
    {
        warn("z3 not found -- this is likely to cause errors; run `tools/get-z3.sh`, or set VERUS_Z3_PATH");
    }

    let cargo_toml = toml::from_str::<toml::Value>(
        &std::fs::read_to_string("Cargo.toml")
            .map_err(|x| format!("could not read Cargo.toml ({})\nrun vargo in `source`", x))?,
    )
    .map_err(|x| format!("could not parse Cargo.toml ({})\nrun vargo in `source`", x))?;
    let vargo_meta = &cargo_toml
        .get("workspace")
        .and_then(|t| t.get("metadata"))
        .and_then(|t| t.get("vargo"))
        .ok_or(
            "Cargo.toml does not contain the workspace.metadata.vargo table\nrun vargo in `source`"
                .to_string(),
        )?;
    if Some("workspace") != vargo_meta.get("tag").and_then(|t| t.as_str()) {
        return Err("Cargo.toml does not have the vargo tag\nrun vargo in `source`".to_string());
    }

    let cmd_position = args_bucket
        .iter()
        .position(|x| SUPPORTED_COMMANDS.contains(&x.as_str()))
        .ok_or(format!(
            "vargo supports the following cargo commands: {}",
            SUPPORTED_COMMANDS.join(", ")
        ))?;
    let cmd = args_bucket.remove(cmd_position);
    let task = match cmd.as_str() {
        "build" => Task::Build,
        "test" => Task::Test { nextest: false },
        "nextest" => Task::Test { nextest: true },
        "run" => Task::Run,
        "clean" => Task::Clean,
        "metadata" => Task::Metadata,
        "fmt" => Task::Fmt,
        _ => panic!("unexpected command"),
    };
    let release = args_bucket
        .iter()
        .position(|x| x.as_str() == "--release" || x.as_str() == "-r")
        .map(|p| args_bucket.remove(p))
        .is_some();

    // This argument is --vargo-verbose to distinguish it from --verbose
    // which is forwarded to cargo
    let verbose = args_bucket
        .iter()
        .position(|x| x.as_str() == "--vargo-verbose")
        .map(|p| args_bucket.remove(p))
        .is_some();

    let vstd_no_verify = args_bucket
        .iter()
        .position(|x| x.as_str() == "--vstd-no-verify")
        .map(|p| args_bucket.remove(p))
        .is_some();

    let package = args_bucket
        .iter()
        .position(|x| x == "--package" || x == "-p")
        .map(|pos| {
            args_bucket.remove(pos);
            args_bucket.remove(pos)
        });

    let cargo_forward_args: Vec<_> = {
        let mut forward_args: Vec<_> = {
            let (forward_args, new_args_bucket): (Vec<_>, Vec<_>) =
                args_bucket.into_iter().partition(|x| {
                    let x = x.as_str();
                    CARGO_FORWARD_ARGS.contains(&x)
                        || CARGO_FORWARD_ARG_KEYS
                            .iter()
                            .any(|prefix| x.starts_with(prefix))
                });
            args_bucket = new_args_bucket;
            forward_args
        };
        forward_args.extend({
            let (forward_args, new_args_bucket): (Vec<_>, Vec<_>) =
                args_bucket.iter().cloned().enumerate().partition(|(i, y)| {
                    args_bucket
                        .get(i - 1)
                        .map(|x| CARGO_FORWARD_ARGS_NEXT.contains(&x.as_str()))
                        .unwrap_or(false)
                        || CARGO_FORWARD_ARGS_NEXT.contains(&y.as_str())
                });
            args_bucket = new_args_bucket.into_iter().map(|(_, x)| x).collect();
            forward_args.into_iter().map(|(_, x)| x)
        });
        forward_args
    };

    let exclude: Vec<_> = {
        let mut i = 0;
        while i < args.len() {
            if args[i] == "--exclude" {
                args.remove(i);
                args.remove(i);
            } else {
                i += 1;
            }
        }
        let mut exclude = Vec::new();
        let mut i = 0;
        while i < args_bucket.len() {
            if args_bucket[i] == "--exclude" {
                args_bucket.remove(i);
                exclude.push(args_bucket.remove(i));
            } else {
                i += 1;
            }
        }
        exclude
    };

    let feature_args: Vec<_> = {
        let (feature_args, new_args_bucket): (Vec<_>, Vec<_>) =
            args_bucket.iter().cloned().enumerate().partition(|(i, y)| {
                args_bucket
                    .get(i - 1)
                    .map(|x| x.as_str() == "-F" || x.as_str() == "--features")
                    .unwrap_or(false)
                    || y.as_str() == "-F"
                    || y.as_str() == "--features"
            });
        args_bucket = new_args_bucket.into_iter().map(|(_, x)| x).collect();
        feature_args.into_iter().map(|(_, x)| x).collect()
    };

    if !in_nextest {
        match (task, package.as_ref().map(|x| x.as_str())) {
            (Task::Run | Task::Test { .. }, Some("air")) => (),
            (Task::Run, Some("rust_verify")) | (Task::Test { .. }, Some("rust_verify_test")) => {
                let current_exe =
                    std::env::current_exe().expect("no path for the current executable");
                let mut vargo = std::process::Command::new(current_exe);
                let mut vargo = vargo.arg("build");
                if release {
                    vargo = vargo.arg("--release");
                }
                vargo = vargo.args(&cargo_forward_args);
                for e in exclude.iter() {
                    vargo = vargo.arg("--exclude").arg(e);
                }
                log_command(&vargo, verbose);
                vargo
                    .status()
                    .map_err(|x| format!("vargo could not execute vargo ({})", x))
                    .and_then(|x| {
                        if x.success() {
                            Ok(())
                        } else {
                            Err(format!("vargo returned status code {:?}", x.code()))
                        }
                    })?;
                info(&format!(
                    "rebuilding: done{}",
                    if release { " (release)" } else { "" }
                ));
            }
            (Task::Run | Task::Test { .. }, _) => {
                return Err(format!(
                    "unexpected package for `vargo run` or `vargo test`"
                ));
            }
            (_, _) => (),
        }
    }

    let target_verus_dir = {
        let parent_dir = std::path::PathBuf::from("target-verus");
        if !parent_dir.exists() {
            std::fs::create_dir(&parent_dir)
                .map_err(|x| format!("could not create target-verus directory ({})", x))?;
        }
        let target_verus_dir = parent_dir.join(if release { "release" } else { "debug" });

        if !target_verus_dir.exists() {
            std::fs::create_dir(&target_verus_dir)
                .map_err(|x| format!("could not create target-verus directory ({})", x))?;
        }
        target_verus_dir
    };

    let target_dir =
        std::path::PathBuf::from("target").join(if release { "release" } else { "debug" });

    let dashdash_pos =
        (!in_nextest && (cmd == "test" || cmd == "nextest" || cmd == "fmt")).then(|| {
            args.iter().position(|x| x == "--").unwrap_or_else(|| {
                args.push("--".to_string());
                args.len() - 1
            })
        });

    if let Some(pos) = dashdash_pos {
        args.insert(
            if cmd == "nextest" { pos } else { pos + 1 },
            "--color=always".to_string(),
        );
    }

    match (task, package.as_ref().map(|x| x.as_str()), in_nextest) {
        (Task::Clean | Task::Fmt | Task::Run | Task::Metadata, package, false) => {
            if let Task::Fmt = task {
                let pos = dashdash_pos.unwrap();

                args.insert(pos + 1, "--config".to_string());
                args.insert(pos + 2, "unstable_features=true,version=Two".to_string());
            }

            let target_verus_dir_absolute = std::fs::canonicalize(&target_verus_dir)
                .map_err(|x| format!("could not canonicalize target-verus directory ({})", x))?;

            if let (Task::Clean, Some("vstd")) = (task, package) {
                clean_vstd(&target_verus_dir)
            } else {
                let mut cargo = std::process::Command::new("cargo");
                let cargo = cargo
                    .env("RUSTC_BOOTSTRAP", "1")
                    .env("VARGO_TARGET_DIR", target_verus_dir_absolute)
                    .args(&args);
                log_command(&cargo, verbose);
                let status = cargo
                    .status()
                    .map_err(|x| format!("could not execute cargo ({})", x))?;

                match task {
                    Task::Clean => {
                        if !status.success() {
                            return Err(format!(
                                "`cargo clean` returned status code {:?}",
                                status.code()
                            ));
                        }

                        std::fs::remove_dir_all(&target_verus_dir)
                            .map_err(|x| format!("could not remove target-verus directory ({})", x))
                    }
                    _ => std::process::exit(status.code().unwrap_or(1)),
                }
            }
        }
        (Task::Test { nextest: _ }, None, false) => {
            return Err(format!("`vargo test` must be run with a specific package"));
        }
        (Task::Test { nextest }, Some(_package), false) => {
            if nextest {
                args.get(cmd_position + 1)
                    .and_then(|x| (x.as_str() == "run").then(|| ()))
                    .ok_or(format!("vargo only supports `vargo nextest run` for now"))?;
                let current_exe =
                    std::env::current_exe().expect("no path for the current executable");
                let mut cargo = std::process::Command::new("cargo");
                let cargo = cargo
                    .env("RUSTC_BOOTSTRAP", "1")
                    .env("VARGO_IN_NEXTEST", "1")
                    .env("VERUS_IN_VARGO", "1")
                    .env("CARGO", current_exe)
                    .args(&args);
                log_command(&cargo, verbose);
                let status = cargo
                    .status()
                    .map_err(|x| format!("could not execute cargo ({})", x))?;
                std::process::exit(status.code().unwrap_or(1));
            } else {
                let mut cargo = std::process::Command::new("cargo");
                let cargo = cargo
                    .env("RUSTC_BOOTSTRAP", "1")
                    .env("VERUS_IN_VARGO", "1")
                    .args(&args);
                log_command(&cargo, verbose);
                let status = cargo
                    .status()
                    .map_err(|x| format!("could not execute cargo ({})", x))?;
                std::process::exit(status.code().unwrap_or(1));
            }
        }
        (Task::Metadata | Task::Test { .. }, _, true) => {
            let mut cargo = std::process::Command::new("cargo");
            let cargo = cargo
                .env("RUSTC_BOOTSTRAP", "1")
                .env("VERUS_IN_VARGO", "1")
                .args(&args);
            log_command(&cargo, verbose);
            cargo
                .status()
                .map_err(|x| format!("could not execute cargo ({})", x))
                .and_then(|x| {
                    if x.success() {
                        Ok(())
                    } else {
                        Err(format!("cargo returned status code {:?}", x.code()))
                    }
                })
        }
        (Task::Build, Some("air"), false) => {
            let mut cargo = std::process::Command::new("cargo");
            let cargo = cargo
                .env("RUSTC_BOOTSTRAP", "1")
                .env("VERUS_IN_VARGO", "1")
                .args(args);
            log_command(&cargo, verbose);
            let status = cargo
                .status()
                .map_err(|x| format!("could not execute cargo ({})", x))?;

            std::process::exit(status.code().unwrap_or(1));
        }
        (Task::Build, package, false) => {
            if args_bucket.len() > 0 {
                return Err(format!(
                    "unexpected or unsupported arguments: {}",
                    args_bucket.join(", ")
                ));
            }

            fn build_target(
                release: bool,
                target: &str,
                extra_args: &[String],
                package: Option<&str>,
                exclude: &[String],
                verbose: bool,
            ) -> Result<(), String> {
                if package == Some(target)
                    || package == None && !exclude.iter().find(|x| x.as_str() == target).is_some()
                {
                    info(format!("building {}", target).as_str());
                    let mut cmd = std::process::Command::new("cargo");
                    let mut cmd = cmd
                        .env("RUSTC_BOOTSTRAP", "1")
                        .env("VERUS_IN_VARGO", "1")
                        .arg("build")
                        .arg("-p")
                        .arg(target);
                    if release {
                        cmd = cmd.arg("--release");
                    }
                    cmd = cmd.args(extra_args);
                    log_command(&cmd, verbose);
                    cmd.status()
                        .map_err(|x| format!("could not execute cargo ({})", x))
                        .and_then(|x| {
                            if x.success() {
                                Ok(())
                            } else {
                                Err(format!("cargo returned status code {:?}", x.code()))
                            }
                        })
                } else {
                    Ok(())
                }
            }

            let packages = &[
                "rust_verify",
                "builtin",
                "builtin_macros",
                "state_machines_macros",
                "vstd_build",
            ];

            let build_vstd = {
                (if let Some(package) = package {
                    if packages.contains(&package) {
                        false
                    } else if package == "vstd" {
                        true
                    } else {
                        return Err(format!("unknown package {package}"));
                    }
                } else {
                    true
                }) && !exclude.iter().find(|x| x.as_str() == "vstd").is_some()
            };

            for p in packages {
                let rust_verify_forward_args;
                let extra_args = if p == &"rust_verify" {
                    rust_verify_forward_args = cargo_forward_args
                        .iter()
                        .chain(feature_args.iter())
                        .cloned()
                        .collect::<Vec<_>>();
                    &rust_verify_forward_args
                } else {
                    &cargo_forward_args
                };
                build_target(release, p, &extra_args[..], package, &exclude[..], verbose)?;
            }

            let mut dependencies_mtime = None;
            let mut dependency_missing = false;

            for from_f_name in [
                format!("libbuiltin.rlib"),
                format!("{}builtin_macros.{}", LIB_PRE, LIB_DL),
                format!("{}state_machines_macros.{}", LIB_PRE, LIB_DL),
                format!("rust_verify{}", EXE),
            ]
            .into_iter()
            {
                let from_f = target_dir.join(&from_f_name);
                if from_f.exists() {
                    let from_f_meta = from_f
                        .metadata()
                        .map_err(|x| format!("cannot obtain metadata for {from_f_name} ({x:?})"))?;
                    dependencies_mtime = Some(
                        dependencies_mtime
                            .unwrap_or(FFileTime::zero())
                            .max(FFileTime::from_last_modification_time(&from_f_meta)),
                    );
                    let to_f = target_verus_dir.join(&from_f_name);
                    // info(&format!(
                    //     "copying {} to {}",
                    //     from_f.display(),
                    //     to_f.display()
                    // ));
                    std::fs::copy(&from_f, &to_f)
                        .map_err(|x| format!("could not copy file ({})", x))?;
                } else {
                    dependency_missing = true;
                }
            }

            let fingerprint_path = target_verus_dir.join(".vstd-fingerprint");

            for f in [format!("vstd.vir"), format!("{LIB_PRE}vstd.rlib")] {
                if !target_verus_dir.join(f).exists() {
                    if fingerprint_path.exists() {
                        info(&format!("removing {}", fingerprint_path.display()));
                        std::fs::remove_file(&fingerprint_path).map_err(|x| {
                            format!("could not delete file {} ({x})", fingerprint_path.display())
                        })?;
                    }
                }
            }

            let stored_fingerprint = if fingerprint_path.exists() {
                let s = std::fs::read_to_string(&fingerprint_path)
                    .map_err(|x| format!("cannot read {} ({x:?})", fingerprint_path.display()))?;
                let f = toml::from_str::<Fingerprint>(&s).map_err(|x| {
                    format!(
                        "cannot parse {}, try `vargo clean` ({x})",
                        fingerprint_path.display()
                    )
                })?;
                Some(f)
            } else {
                None
            };

            if build_vstd {
                if dependency_missing {
                    info("not all of the vstd dependencies are built, skipping vstd build");

                    clean_vstd(&target_verus_dir)?;
                } else {
                    let dependencies_mtime: FileTime = dependencies_mtime
                        .expect("dependencies_mtime should be Some here")
                        .into();

                    let pervasive_path = std::path::Path::new("pervasive");
                    let vstd_mtime: FileTime = util::mtime_recursive(&pervasive_path)?.into();

                    let current_fingerprint = Fingerprint {
                        dependencies_mtime,
                        vstd_mtime,
                    };

                    if stored_fingerprint
                        .map(|s| current_fingerprint > s)
                        .unwrap_or(true)
                    {
                        info("vstd outdated, rebuilding");
                        let mut vstd_build = std::process::Command::new("cargo");
                        let mut vstd_build = vstd_build
                            .env("RUSTC_BOOTSTRAP", "1")
                            .env("VERUS_IN_VARGO", "1")
                            .arg("run")
                            .arg("-p")
                            .arg("vstd_build")
                            .arg("--")
                            .arg(&target_verus_dir);
                        if release {
                            vstd_build = vstd_build.arg("--release");
                        }
                        if vstd_no_verify {
                            vstd_build = vstd_build.arg("--no-verify");
                        }
                        if verbose {
                            vstd_build = vstd_build.arg("--verbose");
                        }
                        log_command(&vstd_build, verbose);
                        vstd_build
                            .status()
                            .map_err(|x| format!("could not execute cargo ({})", x))
                            .and_then(|x| {
                                if x.success() {
                                    Ok(())
                                } else {
                                    Err(format!("vstd_build returned status code {:?}", x.code()))
                                }
                            })?;

                        std::fs::write(
                            &fingerprint_path,
                            toml::to_string(&current_fingerprint)
                                .expect("failed to serialize fingerprint"),
                        )
                        .map_err(|x| format!("cannot write fingerprint file ({x})"))?;
                    } else {
                        info("vstd fresh");
                    }
                }
            }
            Ok(())
        }
        otherwise => panic!("unexpected state: {:?}", otherwise),
    }
}
