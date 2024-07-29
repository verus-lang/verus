// Vargo is a wrapper around cargo that sets up the environment for building
// Verus and collects build artifacts for libraries used by vstd and client
// code so that later compilation stages (building, verifying vstd and running tests)
// can use them. This is necessary because cargo only builds libraries in
// `target/debug` or `target/release` when they are the main build target, and
// not when they're a dependency of another target.

#[path = "../../common/consts.rs"]
mod consts;

const MINIMUM_VERUSFMT_VERSION: [u64; 3] = [0, 4, 0];

mod util;

use filetime::FileTime as FFileTime;
use regex::Regex;
use serde::{Deserialize, Serialize};

fn test_rust_min_stack() -> String {
    (20 * 1024 * 1024).to_string()
}

const VARGO_SOURCE_FILES: &[(&'static str, &'static [u8])] = &[
    ("src/main.rs", include_bytes!("main.rs")),
    ("src/util.rs", include_bytes!("util.rs")),
];

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

#[derive(Clone)]
pub enum SmtSolverType {
    Z3,
    Cvc5,
}

impl SmtSolverType {
    pub fn executable_name(&self) -> String {
        let base = match self {
            SmtSolverType::Z3 => "z3",
            SmtSolverType::Cvc5 => "cvc5",
        };
        if cfg!(target_os = "windows") {
            format!(".\\{}.exe", base)
        } else {
            format!("./{}", base)
        }
    }

    pub fn env_var_name(&self) -> &str {
        match self {
            SmtSolverType::Z3 => "VERUS_Z3_PATH",
            SmtSolverType::Cvc5 => "VERUS_CVC5_PATH",
        }
    }

    pub fn to_str(&self) -> &str {
        match self {
            SmtSolverType::Z3 => "Z3",
            SmtSolverType::Cvc5 => "cvc5",
        }
    }

    pub fn version_re(&self) -> Regex {
        match self {
            SmtSolverType::Z3 => Regex::new(r"Z3 version (\d+\.\d+\.\d+) - \d+ bit")
                .expect("failed to compile Z3 version regex"),
            SmtSolverType::Cvc5 => Regex::new(r"This is cvc5 version (\d+\.\d+\.\d+)")
                .expect("failed to compile cvc5 version regex"),
        }
    }

    pub fn expected_version(&self) -> String {
        match self {
            SmtSolverType::Z3 => consts::EXPECTED_Z3_VERSION.to_string(),
            SmtSolverType::Cvc5 => consts::EXPECTED_CVC5_VERSION.to_string(),
        }
    }
}

pub struct SmtSolverBinary {
    pub stype: SmtSolverType,
    pub path: std::path::PathBuf,
}

impl SmtSolverBinary {
    pub fn find_path(solver_type: SmtSolverType, vargo_nest: u64) -> Option<Self> {
        let find_path_inner = || {
            let file_name = if std::env::var(solver_type.env_var_name()).is_ok() {
                std::env::var(solver_type.env_var_name()).unwrap()
            } else {
                solver_type.executable_name()
            };
            let path = std::path::Path::new(&file_name);

            if !path.is_file() && vargo_nest == 0 {
                // When we fail to find Z3, we warn the user but optimistically continue
                // Since we don't currently use cvc5, we don't warn the user about it, and we bail out
                match solver_type {
                    SmtSolverType::Z3 => warn(format!("{file_name} not found -- this is likely to cause errors or a broken build\nrun `tools/get-z3.(sh|ps1)` first").as_str()),
                    SmtSolverType::Cvc5 => return None,
                }
            }
            if std::env::var(solver_type.env_var_name()).is_err() && path.is_file() {
                std::env::set_var(solver_type.env_var_name(), path);
            }
            Some(path.to_path_buf())
        };
        let path = find_path_inner();
        if matches!(solver_type, SmtSolverType::Z3) {
            assert!(path.is_some());
        }
        path.map(|path| SmtSolverBinary {
            stype: solver_type,
            path,
        })
    }

    fn check_version(&self) -> Result<(), String> {
        let output = std::process::Command::new(&self.path)
            .arg("--version")
            .output()
            .map_err(|x| format!("could not execute {}: {}", self.stype.to_str(), x))?;
        if !output.status.success() {
            return Err(format!(
                "{} returned non-zero exit code",
                self.stype.to_str()
            ));
        }
        let stdout_str = std::str::from_utf8(&output.stdout)
            .map_err(|x| {
                format!(
                    "{} version output is not valid utf8 ({})",
                    self.stype.to_str(),
                    x
                )
            })?
            .to_string();

        let version = self
            .stype
            .version_re()
            .captures(&stdout_str)
            .and_then(|captures| {
                let mut captures = captures.iter();
                let _ = captures.next()?;
                let version = captures.next()?;
                if captures.next() != None {
                    return None;
                }
                Some(version?.as_str())
            })
            .ok_or(format!(
                "unexpected {} version output ({})",
                self.stype.to_str(),
                stdout_str
            ))?;
        if version != self.stype.expected_version() {
            let name = self.stype.to_str().to_lowercase();
            return Err(format!(
                "Verus expects {name} version \"{}\", found version \"{}\"\n\
            Run ./tools/get-{name}.(sh|ps1) to update {name} first.\n\
            If you need a build with a custom {name} version, re-run with --no-solver-version-check.",
                self.stype.expected_version(),
                version
            ));
        } else {
            Ok(())
        }
    }

    pub fn copy_to_target_dir(
        &self,
        target_verus_dir: &std::path::PathBuf,
        macos_prepare_script: &mut String,
    ) -> Result<(), String> {
        if self.path.is_file() {
            let from_f = &self.path;
            let to_f = target_verus_dir.join(self.stype.executable_name());
            if to_f.exists() {
                // If we directly overwrite a binary it can cause
                // a code-signing issue on macs. To work around this, we
                // delete the old file first before moving the new one.
                std::fs::remove_file(&to_f).unwrap();
            }
            std::fs::copy(&from_f, &to_f).map_err(|x| format!("could not copy file ({})", x))?;

            let dest_file_name = to_f.file_name().ok_or(format!(
                "could not get file name for {}",
                self.stype.to_str()
            ))?;
            macos_prepare_script.push_str(
                format!(
                    "\nxattr -d com.apple.quarantine {}\n",
                    dest_file_name.to_string_lossy()
                )
                .as_str(),
            );
        }
        Ok(())
    }
}

#[derive(Debug, Deserialize, Serialize, Eq, PartialEq)]
struct Fingerprint {
    dependencies_mtime: FileTime,
    vstd_mtime: FileTime,
    vstd_no_std: bool,
    vstd_no_alloc: bool,
}

impl PartialOrd for Fingerprint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.vstd_no_std != other.vstd_no_std || self.vstd_no_alloc != other.vstd_no_alloc {
            None
        } else {
            use std::cmp::Ordering::*;
            match (
                self.dependencies_mtime.cmp(&other.dependencies_mtime),
                self.vstd_mtime.cmp(&other.vstd_mtime),
            ) {
                (Less, Less) => Some(Less),
                (Equal, Equal) => Some(Equal),
                (Greater, Greater) => Some(Greater),
                _ => None,
            }
        }
    }
}

const RUST_FLAGS: &str = "--cfg proc_macro_span --cfg verus_keep_ghost --cfg span_locations";

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
    "build", "test", "nextest", "run", "clean", "fmt", "metadata", "cmd", "update",
];

// Arguments that cause vargo to be verbose.
const VARGO_VERBOSE_ARGS: &[&str] = &["-v", "-vv", "--verbose", "--vargo-verbose"];

// Arguments to forward to cargo
const CARGO_FORWARD_ARGS: &[&str] = &["-v", "-vv", "--verbose", "--offline"];
// Argument to forward to cargo which also require us to forward the following argument
// (e.g., `--color always`)
const CARGO_FORWARD_ARGS_NEXT: &[&str] = &["--color"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Task {
    Build,
    Test { nextest: bool },
    Run,
    Clean,
    Metadata,
    Fmt,
    Cmd,
    Update,
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

const VSTD_FILES: &[&str] = &["vstd.vir", "libvstd.rlib", ".vstd-fingerprint"];

const VERUS_ROOT_FILE: &str = "verus-root";

fn clean_vstd(target_verus_dir: &std::path::PathBuf) -> Result<(), String> {
    for f in VSTD_FILES.iter() {
        let f = target_verus_dir.join(f);
        if f.is_file() && f.exists() {
            info(format!("removing {}", f.display()).as_str());
            std::fs::remove_file(&f)
                .map_err(|x| format!("could not delete file {} ({x})", f.display()))?;
        }
    }
    Ok(())
}

fn filter_features(
    feature_args: &Vec<String>,
    accepted: std::collections::HashSet<&'static str>,
) -> Vec<String> {
    let feature_args: Vec<_> = feature_args
        .iter()
        .flat_map(|x| x.split(",").map(|x| x.to_owned()).collect::<Vec<_>>())
        .filter(|a| accepted.contains(a.as_str()))
        .collect();
    feature_args
        .into_iter()
        .flat_map(|f| vec!["--features".to_owned(), f])
        .collect()
}

fn run() -> Result<(), String> {
    let vargo_nest = {
        let vargo_nest = std::env::var("VARGO_NEST")
            .ok()
            .and_then(|x| x.parse().ok().map(|x: u64| x + 1))
            .unwrap_or(0);
        *VARGO_NEST.write().unwrap() = vargo_nest;
        std::env::set_var("VARGO_NEST", format!("{}", vargo_nest));
        vargo_nest
    };

    let mut args = std::env::args().skip(1).collect::<Vec<_>>();

    // Check for any argument signalling verbose-mode (either --vargo-verbose
    // or a verbose argument that would get forwarded to cargo)
    let verbose = args
        .iter()
        .any(|x| VARGO_VERBOSE_ARGS.contains(&x.as_str()));
    args.iter()
        .position(|x| x.as_str() == "--vargo-verbose")
        .map(|p| args.remove(p));

    let vstd_no_verify = args
        .iter()
        .position(|x| x.as_str() == "--vstd-no-verify")
        .map(|p| args.remove(p))
        .is_some();

    let vstd_no_std = args
        .iter()
        .position(|x| x.as_str() == "--vstd-no-std")
        .map(|p| args.remove(p))
        .is_some();

    let vstd_no_alloc = args
        .iter()
        .position(|x| x.as_str() == "--vstd-no-alloc")
        .map(|p| args.remove(p))
        .is_some();

    let vstd_trace = args
        .iter()
        .position(|x| x.as_str() == "--vstd-trace")
        .map(|p| args.remove(p))
        .is_some();

    let no_solver_version_check = args
        .iter()
        .position(|x| x.as_str() == "--no-solver-version-check")
        .map(|p| args.remove(p))
        .is_some();

    let vstd_log_all = args
        .iter()
        .position(|x| x.as_str() == "--vstd-log-all")
        .map(|p| args.remove(p))
        .is_some();

    let vstd_no_verusfmt = args
        .iter()
        .position(|x| x.as_str() == "--vstd-no-verusfmt")
        .map(|p| args.remove(p))
        .is_some();

    if vstd_no_alloc && !vstd_no_std {
        return Err(format!("--vstd-no-alloc requires --vstd-no-std"));
    }

    let mut args_bucket = args.clone();
    let in_nextest = std::env::var("VARGO_IN_NEXTEST").is_ok();

    let (repo_root, rust_toolchain_toml) = {
        let current_dir = std::env::current_dir()
            .map_err(|x| format!("could not obtain the current directory ({})", x))?;
        let repo_root = current_dir
            .parent()
            .ok_or(format!(
                "current dir does not have a parent\nrun vargo in `source`"
            ))?
            .to_owned();
        let rust_toolchain_toml = toml::from_str::<toml::Value>(
            &std::fs::read_to_string(repo_root.join("rust-toolchain.toml")).map_err(|x| {
                format!(
                    "could not read rust-toolchain.toml ({})\nrun vargo in `source`",
                    x
                )
            })?,
        )
        .map_err(|x| format!("could not parse Cargo.toml ({})\nrun vargo in `source`", x))?;
        (repo_root, rust_toolchain_toml)
    };
    if vargo_nest == 0 {
        let files = crate::util::vargo_file_contents(&repo_root.join("tools").join("vargo"));
        let build_hash = &crate::util::hash_file_contents(VARGO_SOURCE_FILES.to_vec());
        let cur_hash = &crate::util::hash_file_contents(
            files.iter().map(|(f, n)| (f.as_str(), &n[..])).collect(),
        );
        if build_hash != cur_hash {
            return Err(format!(
                "vargo sources have changed since it was last built, please re-build vargo"
            ));
        }
    }

    let rust_toolchain_toml_channel = rust_toolchain_toml.get("toolchain").and_then(|t| t.get("channel"))
        .and_then(|t| if let toml::Value::String(s) = t { Some(s) } else { None })
        .ok_or(
            format!("rust-toolchain.toml does not contain the toolchain.channel key, or it isn't a string\nrun vargo in `source`"))?;

    let toolchain = if !in_nextest {
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
            r"^(([A-Za-z0-9.-]+)-(?:aarch64|x86_64)-[A-Za-z0-9]+-[A-Za-z0-9-]+) \(overridden by '(.*)'\)"
        )
        .unwrap();
        let stdout = std::str::from_utf8(&output.stdout)
            .map_err(|_| format!("rustup output is invalid utf8"))?;
        let mut captures = active_toolchain_re.captures_iter(&stdout);
        if let Some(cap) = captures.next() {
            let channel = &cap[2];
            let toolchain = cap[1].to_string();
            if rust_toolchain_toml_channel != channel {
                return Err(format!("rustup is using a toolchain with channel {channel}, we expect {rust_toolchain_toml_channel}\ndo you have a rustup override set?"));
            }
            Some(toolchain)
        } else {
            return Err(format!("unexpected output from `rustup show active-toolchain`\nexpected a toolchain override\ngot: {stdout}"));
        }
    } else {
        None
    };

    if let Some(ref toolchain) = toolchain {
        std::env::set_var("VARGO_TOOLCHAIN", toolchain);
    }

    let solver_binary_z3 = SmtSolverBinary::find_path(SmtSolverType::Z3, vargo_nest)
        .expect("find_path for Z3 always returns a path");
    let solver_binary_cvc5 = SmtSolverBinary::find_path(SmtSolverType::Cvc5, vargo_nest);

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
        "cmd" => Task::Cmd,
        "update" => Task::Update,
        _ => panic!("unexpected command"),
    };

    if vargo_nest == 0 && task != Task::Fmt && !no_solver_version_check {
        solver_binary_z3.check_version()?;
        if let Some(cvc5) = &solver_binary_cvc5 {
            cvc5.check_version()?;
        }
    }

    if task == Task::Cmd {
        return std::process::Command::new("rustup")
            .env("RUST_MIN_STACK", test_rust_min_stack())
            .arg("run")
            .arg(toolchain.expect("not in nextest"))
            .args(args_bucket)
            .stderr(std::process::Stdio::inherit())
            .stdout(std::process::Stdio::inherit())
            .status()
            .map_err(|x| format!("vargo could not execute rustup ({})", x))
            .and_then(|x| {
                if x.success() {
                    Ok(())
                } else {
                    Err(format!("vargo returned status code {:?}", x.code()))
                }
            });
    }

    let release = args_bucket
        .iter()
        .position(|x| x.as_str() == "--release" || x.as_str() == "-r")
        .map(|p| args_bucket.remove(p))
        .is_some();

    let verus_version = match util::version_info(&repo_root) {
        Ok(version_info) => {
            std::env::set_var("VARGO_BUILD_VERSION", &version_info.version);
            std::env::set_var("VARGO_BUILD_SHA", &version_info.sha);
            Some(version_info)
        }
        Err(err) => {
            warn(
                format!("could not obtain version info from git, this will result in a binary with an unknown version: {}", err).as_str()
            );
            None
        }
    };

    std::env::set_var(
        "VARGO_BUILD_PROFILE",
        if release { "release" } else { "debug" },
    );

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
                if vstd_no_verify {
                    vargo = vargo.arg("--vstd-no-verify");
                }
                if verbose {
                    vargo = vargo.arg("--vargo-verbose");
                }
                vargo = vargo.args(&cargo_forward_args);
                vargo = vargo.args(&feature_args);
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
            info(&format!("creating {}", parent_dir.display()));
            std::fs::create_dir(&parent_dir)
                .map_err(|x| format!("could not create target-verus directory ({})", x))?;
        }
        let target_verus_dir = parent_dir.join(if release { "release" } else { "debug" });

        if !target_verus_dir.exists() {
            info(&format!("creating {}", target_verus_dir.display()));
            std::fs::create_dir(&target_verus_dir)
                .map_err(|x| format!("could not create target-verus directory ({})", x))?;
        }
        target_verus_dir
    };

    let target_dir =
        std::path::PathBuf::from("target").join(if release { "release" } else { "debug" });

    let dashdash_pos =
        (!in_nextest && matches!(task, Task::Test { nextest: _ } | Task::Fmt)).then(|| {
            args.iter().position(|x| x == "--").unwrap_or_else(|| {
                args.push("--".to_string());
                args.len() - 1
            })
        });

    if let Some(pos) = dashdash_pos {
        args.insert(
            if task == (Task::Test { nextest: true }) {
                pos
            } else {
                pos + 1
            },
            "--color=always".to_string(),
        );
    }

    match (task, package.as_ref().map(|x| x.as_str()), in_nextest) {
        (Task::Clean | Task::Fmt | Task::Run | Task::Metadata | Task::Update, package, false) => {
            let original_args = args.clone();

            if let Task::Fmt = task {
                let pos = dashdash_pos.unwrap();

                info(format!("formatting source").as_str());

                args.insert(pos + 1, "--config".to_string());
                args.insert(pos + 2, "unstable_features=true,version=Two".to_string());
            }

            let target_verus_dir_absolute = std::fs::canonicalize(&target_verus_dir)
                .map_err(|x| format!("could not canonicalize target-verus directory ({})", x))?;

            if let (Task::Clean, Some("vstd")) = (task, package) {
                clean_vstd(&std::path::Path::new("target-verus").join("release"))?;
                if !release {
                    clean_vstd(&std::path::Path::new("target-verus").join("debug"))?;
                }
                Ok(())
            } else {
                let mut cargo = std::process::Command::new("cargo");
                let cargo = cargo
                    .env("RUST_MIN_STACK", test_rust_min_stack())
                    .env("RUSTC_BOOTSTRAP", "1")
                    .env("VARGO_TARGET_DIR", target_verus_dir_absolute)
                    .env("RUSTFLAGS", RUST_FLAGS)
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

                        let target_verus_release_dir =
                            std::path::Path::new("target-verus").join("release");
                        if target_verus_release_dir.is_dir() && target_verus_release_dir.exists() {
                            info(
                                format!("removing {}", target_verus_release_dir.display()).as_str(),
                            );
                            std::fs::remove_dir_all(target_verus_release_dir).map_err(|x| {
                                format!("could not remove target-verus directory ({})", x)
                            })?;
                        }
                        if !release {
                            let target_verus_debug_dir =
                                std::path::Path::new("target-verus").join("debug");
                            if target_verus_debug_dir.is_dir() && target_verus_debug_dir.exists() {
                                info(
                                    format!("removing {}", target_verus_debug_dir.display())
                                        .as_str(),
                                );
                                std::fs::remove_dir_all(target_verus_debug_dir).map_err(|x| {
                                    format!("could not remove target-verus directory ({})", x)
                                })?;
                            }
                        }
                        Ok(())
                    }
                    Task::Fmt => {
                        if !status.success() {
                            return Err(format!(
                                "`cargo fmt` returned status code {:?}",
                                status.code()
                            ));
                        }

                        let original_args = original_args
                            .iter()
                            .map(|x| x.as_str())
                            .collect::<std::collections::HashSet<&str>>();
                        if !original_args.is_subset(&std::collections::HashSet::from([
                            "--",
                            "--check",
                            "fmt",
                            "--color=always",
                        ])) {
                            return Err(format!("some of the arguments to fmt are unsupported"));
                        }
                        let fmt_check = original_args.contains("--check");

                        info(format!("formatting syn").as_str());

                        let syn_path = std::path::Path::new("../dependencies/syn");
                        let mut syn_fmt = std::process::Command::new("cargo");
                        syn_fmt.current_dir(syn_path).arg("fmt");
                        if fmt_check {
                            syn_fmt.arg("--check");
                        }
                        let syn_fmt_status = syn_fmt.status().expect("failed to run cargo");
                        if !syn_fmt_status.success() {
                            return Err(format!(
                                "cargo fmt on syn returned status code {:?}",
                                syn_fmt_status.code()
                            ));
                        }

                        info(format!("formatting prettyplease").as_str());

                        let syn_path = std::path::Path::new("../dependencies/prettyplease");
                        let mut syn_fmt = std::process::Command::new("cargo");
                        syn_fmt.current_dir(syn_path).arg("fmt");
                        if fmt_check {
                            syn_fmt.arg("--check");
                        }
                        let syn_fmt_status = syn_fmt.status().expect("failed to run cargo");
                        if !syn_fmt_status.success() {
                            return Err(format!(
                                "cargo fmt on prettyplease returned status code {:?}",
                                syn_fmt_status.code()
                            ));
                        }

                        if exclude.contains(&"vstd".to_owned()) {
                            return Ok(());
                        }

                        let verusfmt_path =
                            std::env::var("VARGO_VERUSFMT_PATH").unwrap_or("verusfmt".to_string());

                        if !vstd_no_verusfmt {
                            match std::process::Command::new(&verusfmt_path)
                                .arg("--version")
                                .output()
                            {
                                Ok(output) => {
                                    if !output.status.success() {
                                        return Err(format!(
                                            "`verusfmt` returned status code {:?}",
                                            status.code()
                                        ));
                                    }
                                    let verusfmt_version_stdout = String::from_utf8(output.stdout)
                                        .map_err(|_| format!("invalid output from verusfmt"))?;
                                    let verusfmt_version_re = Regex::new(
                                        r"^verusfmt ([0-9]+)\.([0-9]+)\.([0-9]+)(?:-.*)?\n$",
                                    )
                                    .unwrap();
                                    let verusfmt_version = verusfmt_version_re
                                        .captures(&verusfmt_version_stdout)
                                        .ok_or(format!("invalid output from verusfmt"))?
                                        .extract::<3>()
                                        .1
                                        .iter()
                                        .map(|v| v.parse::<u64>().unwrap())
                                        .collect::<Vec<u64>>();
                                    for (cv, ev) in
                                        verusfmt_version.iter().zip(MINIMUM_VERUSFMT_VERSION.iter())
                                    {
                                        if ev > cv {
                                            return Err(format!("expected `verusfmt` version to be at least {}.{}.{}, found {}.{}.{}; refer to https://github.com/verus-lang/verusfmt/blob/main/README.md#installing-and-using-verusfmt for installation instructions",
                                                MINIMUM_VERUSFMT_VERSION[0], MINIMUM_VERUSFMT_VERSION[1], MINIMUM_VERUSFMT_VERSION[2],
                                                verusfmt_version[0], verusfmt_version[1], verusfmt_version[2]));
                                        } else if cv > ev {
                                            break;
                                        }
                                    }
                                }
                                Err(err) => match err.kind() {
                                    std::io::ErrorKind::NotFound => {
                                        warn(format!("cannot execute verusfmt, refer to https://github.com/verus-lang/verusfmt/blob/main/README.md#installing-and-using-verusfmt for installation instructions\nvstd will not be formatted").as_str());
                                        return Ok(());
                                    }
                                    _ => return Err(format!("cannot execute verusfmt: {}", err)),
                                },
                            };

                            info(format!("formatting vstd").as_str());

                            let vstd_path = std::path::Path::new("vstd");
                            let all_vstd_files = walkdir::WalkDir::new(vstd_path)
                                .follow_links(true)
                                .into_iter()
                                .filter_map(|e| e.ok())
                                .filter(|x| {
                                    x.path().extension() == Some(std::ffi::OsStr::new("rs"))
                                })
                                .map(|x| x.path().to_owned())
                                .collect::<Vec<_>>();

                            let mut verusfmt = std::process::Command::new(&verusfmt_path);
                            if fmt_check {
                                verusfmt.arg("--check");
                            }
                            verusfmt.args(all_vstd_files);
                            let verusfmt_status = verusfmt.status().expect("failed to run vstd");

                            if !verusfmt_status.success() {
                                warn(
                                    format!(
                                        "verusfmt returned error code {:?}",
                                        verusfmt_status.code(),
                                    )
                                    .as_str(),
                                );
                                std::process::exit(verusfmt_status.code().unwrap_or(1))
                            }
                        }

                        Ok(())
                    }
                    _ => std::process::exit(status.code().unwrap_or(1)),
                }
            }
        }
        (Task::Test { nextest: _ }, None, false) => {
            return Err(format!("`vargo test` must be run with a specific package"));
        }
        (Task::Test { nextest }, Some(_package), false) => {
            let (feature_args, new_args): (Vec<_>, Vec<_>) =
                args.iter().cloned().enumerate().partition(|(i, y)| {
                    args.get(i - 1)
                        .map(|x| x.as_str() == "-F" || x.as_str() == "--features")
                        .unwrap_or(false)
                        || y.as_str() == "-F"
                        || y.as_str() == "--features"
                });
            let (feature_args, mut new_args): (Vec<_>, Vec<_>) = (
                feature_args.into_iter().map(|(_, x)| x).collect(),
                new_args.into_iter().map(|(_, x)| x).collect(),
            );
            let dashdash_pos = new_args.iter().position(|x| x == "--").expect("-- in args");
            let feature_args = filter_features(
                &feature_args,
                ["singular", "axiom-usage-info"].into_iter().collect(),
            );
            new_args.splice(dashdash_pos..dashdash_pos, feature_args);
            if nextest {
                args.get(cmd_position + 1)
                    .and_then(|x| (x.as_str() == "run").then(|| ()))
                    .ok_or(format!("vargo only supports `vargo nextest run` for now"))?;
                let current_exe =
                    std::env::current_exe().expect("no path for the current executable");
                let mut cargo = std::process::Command::new("cargo");
                let cargo = cargo
                    .env("RUST_MIN_STACK", test_rust_min_stack())
                    .env("RUSTC_BOOTSTRAP", "1")
                    .env("VARGO_IN_NEXTEST", "1")
                    .env("VERUS_IN_VARGO", "1")
                    .env("RUSTFLAGS", RUST_FLAGS)
                    .env("CARGO", current_exe)
                    .args(&new_args);
                log_command(&cargo, verbose);
                let status = cargo
                    .status()
                    .map_err(|x| format!("could not execute cargo ({})", x))?;
                std::process::exit(status.code().unwrap_or(1));
            } else {
                let mut cargo = std::process::Command::new("cargo");
                let cargo = cargo
                    .env("RUST_MIN_STACK", test_rust_min_stack())
                    .env("RUSTC_BOOTSTRAP", "1")
                    .env("VERUS_IN_VARGO", "1")
                    .env("RUSTFLAGS", RUST_FLAGS)
                    .args(&new_args);
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
                .env("RUST_MIN_STACK", test_rust_min_stack())
                .env("RUSTC_BOOTSTRAP", "1")
                .env("VERUS_IN_VARGO", "1")
                .env("RUSTFLAGS", RUST_FLAGS)
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
        (Task::Build, Some("air" | "verusdoc"), false) => {
            let mut cargo = std::process::Command::new("cargo");
            let cargo = cargo
                .env("RUST_MIN_STACK", test_rust_min_stack())
                .env("RUSTC_BOOTSTRAP", "1")
                .env("VERUS_IN_VARGO", "1")
                .env("RUSTFLAGS", RUST_FLAGS)
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
                        .env("RUST_MIN_STACK", test_rust_min_stack())
                        .env("RUSTC_BOOTSTRAP", "1")
                        .env("VERUS_IN_VARGO", "1")
                        .env("RUSTFLAGS", RUST_FLAGS)
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
                "verus",
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
                    let feature_args = filter_features(
                        &feature_args,
                        ["singular", "axiom-usage-info"].into_iter().collect(),
                    );
                    rust_verify_forward_args = cargo_forward_args
                        .iter()
                        .chain(feature_args.iter())
                        .cloned()
                        .collect::<Vec<_>>();
                    &rust_verify_forward_args
                } else if p == &"verus" {
                    let feature_args =
                        filter_features(&feature_args, ["record-history"].into_iter().collect());
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

            let mut macos_prepare_script = format!(
                r#"
#!/bin/bash
set -e
set -x

"#
            );
            use std::fmt::Write;

            for from_f_name in [
                format!("libbuiltin.rlib"),
                format!("{}builtin_macros.{}", LIB_PRE, LIB_DL),
                format!("{}state_machines_macros.{}", LIB_PRE, LIB_DL),
                format!("rust_verify{}", EXE),
                format!("verus{}", EXE),
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

                    if to_f.exists() {
                        // If we directly overwrite a binary it can cause
                        // a code-signing issue on macs. To work around this, we
                        // delete the old file first before moving the new one.
                        std::fs::remove_file(&to_f).unwrap();
                    }

                    std::fs::copy(&from_f, &to_f)
                        .map_err(|x| format!("could not copy file ({})", x))?;

                    writeln!(
                        &mut macos_prepare_script,
                        "xattr -d com.apple.quarantine {}",
                        from_f_name
                    )
                    .map_err(|x| format!("could not write to macos prepare script ({})", x))?;
                } else {
                    dependency_missing = true;
                }
            }

            solver_binary_z3.copy_to_target_dir(&target_verus_dir, &mut macos_prepare_script)?;
            if let Some(cvc5) = &solver_binary_cvc5 {
                cvc5.copy_to_target_dir(&target_verus_dir, &mut macos_prepare_script)?;
            }

            let fingerprint_path = target_verus_dir.join(".vstd-fingerprint");

            for f in [format!("vstd.vir"), format!("libvstd.rlib")] {
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
                        "cannot parse {}, try `vargo clean -p vstd` (first), or `vargo clean` ({x})",
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

                    let vstd_path = std::path::Path::new("vstd");
                    let vstd_mtime: FileTime = util::mtime_recursive(&vstd_path)?.into();

                    let current_fingerprint = Fingerprint {
                        dependencies_mtime,
                        vstd_mtime,
                        vstd_no_std,
                        vstd_no_alloc,
                    };

                    if stored_fingerprint
                        .map(|s| !(current_fingerprint <= s))
                        .unwrap_or(true)
                    {
                        info("vstd outdated, rebuilding");
                        let mut vstd_build = std::process::Command::new("cargo");
                        let mut vstd_build = vstd_build
                            .env("RUSTC_BOOTSTRAP", "1")
                            .env("VERUS_IN_VARGO", "1")
                            .env("RUSTFLAGS", RUST_FLAGS)
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
                        if vstd_no_std {
                            vstd_build = vstd_build.arg("--no-std");
                        }
                        if vstd_no_alloc {
                            vstd_build = vstd_build.arg("--no-alloc");
                        }
                        if vstd_trace {
                            vstd_build = vstd_build.arg("--trace");
                        }
                        if vstd_log_all {
                            vstd_build = vstd_build.arg("--log-all");
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

            #[cfg(target_os = "macos")]
            {
                let macos_prepare_script_path = target_verus_dir.join("macos_allow_gatekeeper.sh");
                std::fs::write(&macos_prepare_script_path, macos_prepare_script)
                    .map_err(|x| format!("could not write to macos prepare script ({})", x))?;
                std::fs::set_permissions(
                    &macos_prepare_script_path,
                    <std::fs::Permissions as std::os::unix::fs::PermissionsExt>::from_mode(0o755),
                )
                .map_err(|x| {
                    format!("could not set permissions on macos prepare script ({})", x)
                })?;
            }

            if let Some(version_info) = verus_version {
                let version_info_path = target_verus_dir.join("version.txt");
                std::fs::write(&version_info_path, version_info.version)
                    .map_err(|x| format!("could not write to version file ({})", x))?;
            }

            let verus_root_path = target_verus_dir.join(VERUS_ROOT_FILE);
            if dependency_missing
                || VSTD_FILES.iter().any(|f| {
                    let f = target_verus_dir.join(f);
                    !f.is_file()
                })
            {
                info(format!("removing {}", verus_root_path.display()).as_str());
                std::fs::remove_file(&verus_root_path).map_err(|x| {
                    format!("could not delete file {} ({x})", verus_root_path.display())
                })?;
            } else {
                std::mem::drop(
                    std::fs::OpenOptions::new()
                        .create(true)
                        .write(true)
                        .open(&verus_root_path)
                        .map_err(|x| {
                            format!("could not touch file {} ({x})", verus_root_path.display())
                        })?,
                );
            }
            Ok(())
        }
        otherwise => panic!("unexpected state: {:?}", otherwise),
    }
}
