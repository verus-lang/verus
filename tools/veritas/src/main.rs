const REPOS_CACHE_PATH_VAR: &str = "REPOS_CACHE_PATH";
const WORKDIR_PATH_VAR: &str = "WORKDIR_PATH";
const Z3_CACHE_PATH_VAR: &str = "Z3_CACHE_PATH";
const OUTPUT_PATH_VAR: &str = "OUTPUT_PATH";
const RUNNER_PATH_VAR: &str = "VERITAS_RUNNER_PATH";
const RUNNER_PATH_DEFAULT: &str = "/root/veritas";
const BUILD_VERUS_SCRIPT_FILENAME: &str = "build_verus.sh";
const GET_Z3_SCRIPT_FILENAME: &str = "get-z3.sh";
const VERUS_PROJECT_NAME: &str = "verus";

struct VeritasError {
    loc: (String, u32, u32),
    message: String,
}

mod printing {
    use super::VeritasError;
    use yansi::{self, Paint};

    macro_rules! verror {
        ($($arg:tt)*) => {{
            $crate::VeritasError {
                loc: (::std::file!().to_string(), ::std::line!(), ::std::column!()),
                message: ::std::format!($($arg)*),
            }
        }};
    }

    pub(crate) use verror;

    pub fn error(VeritasError { loc, message }: &VeritasError) -> ! {
        println!(
            "{}",
            format!("error [{}:{}:{}]: {}", loc.0, loc.1, loc.2, message).red()
        );
        std::process::exit(1);
    }

    pub fn info(msg: &str) {
        eprintln!("■■■ {} ■■■", format!("info: {}", msg).blue());
    }

    #[allow(dead_code)]
    pub fn warn(msg: &str) {
        eprintln!("■■■ {} ■■■", format!("warn: {}", msg).yellow());
    }

    pub fn log_command(cmd: &mut std::process::Command) -> &mut std::process::Command {
        eprintln!("▶▶▶ {} ◀◀◀", format!("running: {:?}", &cmd).magenta());
        cmd
    }
}

use std::{
    path::{Path, PathBuf},
    process::Command,
};

#[allow(unused_imports)]
use printing::{info, log_command, verror, warn};
use serde::{Deserialize, Serialize};

mod digest {
    use sha2::{Digest, Sha256};

    pub fn str_digest(s: &str) -> String {
        let mut hasher = Sha256::new();
        hasher.update(s.as_bytes());
        let hash = hasher.finalize();
        let mut hex_string = String::with_capacity(64);
        for b in hash[..].iter().map(|b| format!("{:02x}", b)) {
            hex_string.push_str(&b);
        }
        hex_string
    }

    struct Sha256Hasher {
        inner: Sha256,
    }

    impl Sha256Hasher {
        fn new() -> Self {
            Sha256Hasher {
                inner: Sha256::new(),
            }
        }

        fn finalize(self) -> Vec<u8> {
            self.inner.finalize().to_vec()
        }
    }

    impl std::hash::Hasher for Sha256Hasher {
        fn finish(&self) -> u64 {
            panic!("unexpected call to finish");
        }

        fn write(&mut self, bytes: &[u8]) {
            self.inner.update(bytes);
        }
    }

    pub fn obj_digest<V: std::hash::Hash>(v: V) -> String {
        let mut hasher = Sha256Hasher::new();
        v.hash(&mut hasher);
        let hash = hasher.finalize();
        let mut hex_string = String::with_capacity(64);
        for b in hash[..].iter().map(|b| format!("{:02x}", b)) {
            hex_string.push_str(&b);
        }
        hex_string
    }
}

trait ExitStatusExt {
    fn success_or_err(&self) -> Result<(), VeritasError>;
}

impl ExitStatusExt for std::process::ExitStatus {
    fn success_or_err(&self) -> Result<(), VeritasError> {
        if self.success() {
            Ok(())
        } else {
            Err(verror!(
                "process returned failure (exit code {})",
                self.code()
                    .as_ref()
                    .map(|x| x.to_string())
                    .unwrap_or("unknown".to_owned())
            ))
        }
    }
}

struct ReposCache {
    repos_cache_path: PathBuf,
}

fn runner_path() -> PathBuf {
    std::env::var(RUNNER_PATH_VAR)
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from(RUNNER_PATH_DEFAULT))
}

fn display_path(path: &std::path::Path) -> String {
    path.strip_prefix("/root")
        .unwrap_or(path)
        .display()
        .to_string()
}

fn env_var_dir_or_err(var: &str) -> Result<PathBuf, VeritasError> {
    let path = std::env::var(var)
        .map_err(|_| verror!("{} env var not set", var))
        .map(std::path::PathBuf::from)?;
    if !path.is_dir() {
        return Err(verror!("REPOS_CACHE env var is not a directory"));
    }
    Ok(path)
}

impl ReposCache {
    fn init() -> Result<Self, VeritasError> {
        let repos_cache_path = env_var_dir_or_err(REPOS_CACHE_PATH_VAR)?;
        Ok(ReposCache { repos_cache_path })
    }

    fn ensure_cache_repo(
        &mut self,
        repo_name: &str,
        repo_url: &str,
    ) -> Result<git2::Repository, VeritasError> {
        let repo_path = self
            .repos_cache_path
            .join(repo_name.to_owned() + "-" + &digest::str_digest(&repo_url));

        let repo = git2::Repository::init_bare(&repo_path)
            .map_err(|e| verror!("failed to init bare repo: {}", e))?;
        let mut origin_remote = repo
            .find_remote("origin")
            .ok()
            .or_else(|| repo.remote("origin", repo_url).ok())
            .expect("failed to create anonymous remote");
        info(&format!("fetching {repo_url} into {}", repo_path.display()));
        origin_remote
            .fetch(
                &["+refs/heads/*:refs/heads/*", "+refs/tags/*:refs/tags/*"],
                None,
                None,
            )
            .map_err(|e| verror!("failed to fetch origin: {}", e))?;
        std::mem::drop(origin_remote);

        Ok(repo)
    }
}

struct Z3Cache {
    z3_cache_path: PathBuf,
}

impl Z3Cache {
    fn init() -> Result<Self, VeritasError> {
        let z3_cache_path = env_var_dir_or_err(Z3_CACHE_PATH_VAR)?;
        Ok(Z3Cache { z3_cache_path })
    }

    fn ensure_z3_version(
        &mut self,
        workdir: &mut WorkDir,
        version: &str,
    ) -> Result<PathBuf, VeritasError> {
        let z3_path = self.z3_cache_path.join("z3-".to_owned() + version);
        if z3_path.exists() {
            return Ok(z3_path);
        }
        let scratch_dir = workdir.scratch()?;

        let result = log_command(
            Command::new("/bin/bash")
                .current_dir(scratch_dir)
                .arg(runner_path().join(GET_Z3_SCRIPT_FILENAME))
                .arg(version)
                .arg(&z3_path),
        )
        .status()
        .map_err(|e| verror!("cannot execute verus build script: {}", e))?;
        result.success_or_err()?;
        Ok(z3_path)
    }
}

struct WorkDir {
    workdir_path: PathBuf,
}

struct Checkout {
    workdir: PathBuf,
    hash: String,
}

impl WorkDir {
    fn init() -> Result<Self, VeritasError> {
        let workdir_path = env_var_dir_or_err(WORKDIR_PATH_VAR)?;
        let workdir_path = workdir_path.join("work");
        if workdir_path.exists() {
            std::fs::remove_dir_all(&workdir_path)
                .map_err(|e| verror!("cannot delete workdir {}: {}", workdir_path.display(), e))?;
        }
        std::fs::create_dir(&workdir_path)
            .map_err(|e| verror!("cannot create workdir {}: {}", workdir_path.display(), e))?;

        Ok(WorkDir { workdir_path })
    }

    fn checkout(
        &mut self,
        cache: &mut ReposCache,
        repo_name: &str,
        repo_url: &str,
        revspec: &str,
    ) -> Result<Checkout, VeritasError> {
        let work_path = self
            .workdir_path
            .join(repo_name.to_owned() + "-" + &digest::str_digest(revspec));

        let cached_repo = cache.ensure_cache_repo(repo_name, repo_url)?;
        let repository = git2::Repository::init(&work_path)
            .map_err(|e| verror!("failed to init repo in work path: {}", e))?;
        let mut origin_remote = repository
            .find_remote("origin")
            .ok()
            .or_else(|| {
                repository
                    .remote("origin", &cached_repo.path().to_string_lossy())
                    .ok()
            })
            .expect("failed to create anonymous remote");
        let mut fetch_options = git2::FetchOptions::new();
        fetch_options.depth(1);
        origin_remote
            .fetch(&[revspec], Some(&mut fetch_options), None)
            .map_err(|e| verror!("failed to fetch {} from origin: {}", revspec, e))?;
        std::mem::drop(origin_remote);
        let remote_revspec = format!("remotes/origin/{revspec}");
        let (object, reference) = repository
            .revparse_ext(&remote_revspec)
            .or_else(|_e| repository.revparse_ext(revspec))
            .map_err(|e| verror!("failed to find {}: {}", revspec, e))?;
        repository
            .checkout_tree(&object, None)
            .map_err(|e| verror!("cannot checkout {}: {}", revspec, e))?;
        match &reference {
            Some(gref) => repository
                .set_head(gref.name().unwrap())
                .map_err(|e| verror!("cannot set head: {}", e))?,
            None => repository
                .set_head_detached(object.id())
                .map_err(|e| verror!("cannot set head: {}", e))?,
        }
        let hash = object.id().to_string();
        std::mem::drop(object);
        std::mem::drop(reference);

        Ok(Checkout {
            workdir: work_path,
            hash,
        })
    }

    fn checkout_local(
        &mut self,
        repo_name: &str,
        local_path: &str,
    ) -> Result<Checkout, VeritasError> {
        let local_path = Path::new(local_path);
        if !local_path.exists() {
            return Err(verror!(
                "local checkout path does not exist: {}",
                local_path.display()
            ));
        }
        let work_path = self.workdir_path.join(
            repo_name.to_owned()
                + "-local-"
                + &digest::str_digest(local_path.to_string_lossy().as_ref()),
        );
        copy_directory(local_path, &work_path)?;
        Ok(Checkout {
            workdir: work_path,
            hash: local_checkout_hash(local_path)?,
        })
    }

    fn scratch(&mut self) -> Result<PathBuf, VeritasError> {
        let scratch_path = self.workdir_path.join("scratch");
        if scratch_path.exists() {
            std::fs::remove_dir_all(&scratch_path).map_err(|e| {
                verror!(
                    "cannot delete scratch dir {}: {}",
                    scratch_path.display(),
                    e
                )
            })?;
        }
        std::fs::create_dir(&scratch_path).map_err(|e| {
            verror!(
                "cannot create scratch dir {}: {}",
                scratch_path.display(),
                e
            )
        })?;
        Ok(scratch_path)
    }
}

fn copy_directory(src: &Path, dst: &Path) -> Result<(), VeritasError> {
    if !src.is_dir() {
        return Err(verror!("{} is not a directory", src.display()));
    }
    std::fs::create_dir(dst)
        .map_err(|e| verror!("cannot create {}: {}", dst.display(), e))?;
    for entry in
        std::fs::read_dir(src).map_err(|e| verror!("cannot read {}: {}", src.display(), e))?
    {
        let entry = entry.map_err(|e| verror!("cannot read directory entry: {}", e))?;
        let entry_path = entry.path();
        let entry_name = entry.file_name();
        if should_skip_local_copy_entry(&entry_name) {
            continue;
        }
        let dst_path = dst.join(&entry_name);
        let file_type = entry
            .file_type()
            .map_err(|e| verror!("cannot stat {}: {}", entry_path.display(), e))?;
        if file_type.is_dir() {
            copy_directory(&entry_path, &dst_path)?;
        } else if file_type.is_symlink() {
            let target = std::fs::read_link(&entry_path)
                .map_err(|e| verror!("cannot read symlink {}: {}", entry_path.display(), e))?;
            #[cfg(unix)]
            std::os::unix::fs::symlink(&target, &dst_path)
                .map_err(|e| verror!("cannot create symlink {}: {}", dst_path.display(), e))?;
            #[cfg(not(unix))]
            {
                return Err(verror!(
                    "symlink copy unsupported on this platform: {}",
                    entry_path.display()
                ));
            }
        } else {
            std::fs::copy(&entry_path, &dst_path).map_err(|e| {
                verror!(
                    "cannot copy {} to {}: {}",
                    entry_path.display(),
                    dst_path.display(),
                    e
                )
            })?;
        }
    }
    Ok(())
}

fn should_skip_local_copy_entry(entry_name: &std::ffi::OsStr) -> bool {
    matches!(
        entry_name.to_str(),
        Some(".git" | ".verus-solver-log" | "target" | "target-verus")
    )
}

fn local_checkout_hash(local_path: &Path) -> Result<String, VeritasError> {
    let repository = match git2::Repository::discover(local_path) {
        Ok(repository) => repository,
        Err(_) => {
            return Ok(format!(
                "local-{}",
                digest::str_digest(local_path.to_string_lossy().as_ref())
            ));
        }
    };
    let head = repository
        .head()
        .ok()
        .and_then(|head| head.target())
        .map(|oid| oid.to_string())
        .unwrap_or_else(|| "HEAD".to_owned());
    let mut status_options = git2::StatusOptions::new();
    status_options
        .include_untracked(true)
        .recurse_untracked_dirs(true);
    let dirty = repository
        .statuses(Some(&mut status_options))
        .map_err(|e| verror!("cannot read git status for {}: {}", local_path.display(), e))?
        .iter()
        .any(|entry| entry.status() != git2::Status::CURRENT);
    Ok(if dirty {
        format!("{head}-dirty")
    } else {
        head
    })
}

fn find_verus_support_artifact(deps_dir: &Path, crate_name: &str) -> Result<PathBuf, VeritasError> {
    let prefix = format!("lib{crate_name}-");
    let mut matches = Vec::new();
    for entry in std::fs::read_dir(deps_dir)
        .map_err(|e| verror!("cannot read {}: {}", deps_dir.display(), e))?
    {
        let entry = entry.map_err(|e| verror!("cannot read directory entry: {}", e))?;
        let path = entry.path();
        let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if file_name.starts_with(&prefix)
            && (file_name.ends_with(".rlib")
                || file_name.ends_with(".so")
                || file_name.ends_with(".dylib")
                || file_name.ends_with(".dll"))
        {
            let modified = std::fs::metadata(&path)
                .and_then(|metadata| metadata.modified())
                .unwrap_or(std::time::SystemTime::UNIX_EPOCH);
            matches.push((modified, path));
        }
    }
    matches
        .into_iter()
        .max_by_key(|(modified, _path)| *modified)
        .map(|(_modified, path)| path)
        .ok_or_else(|| verror!("cannot find verus support artifact for {}", crate_name))
}

fn push_verus_support_extern(
    args: &mut Vec<String>,
    deps_dir: &Path,
    extern_name: &str,
    crate_name: &str,
) -> Result<(), VeritasError> {
    let artifact = find_verus_support_artifact(deps_dir, crate_name)?;
    args.push("--extern".to_owned());
    args.push(format!("{extern_name}={}", artifact.display()));
    Ok(())
}

fn verus_support_args(verus_binary_path: &Path) -> Result<Vec<String>, VeritasError> {
    let release_dir = verus_binary_path
        .parent()
        .ok_or_else(|| verror!("verus binary has no parent directory"))?;
    let deps_dir = release_dir
        .parent()
        .and_then(|target_verus_dir| target_verus_dir.parent())
        .map(|source_dir| source_dir.join("target/release/deps"))
        .filter(|deps_dir| deps_dir.is_dir())
        .unwrap_or_else(|| release_dir.join("vstd/target/debug/deps"));
    if !deps_dir.is_dir() {
        return Err(verror!(
            "cannot find verus support deps directory {}",
            deps_dir.display()
        ));
    }
    let mut args = vec!["-L".to_owned(), format!("dependency={}", deps_dir.display())];
    push_verus_support_extern(&mut args, &deps_dir, "builtin", "verus_builtin")?;
    push_verus_support_extern(&mut args, &deps_dir, "builtin_macros", "verus_builtin_macros")?;
    push_verus_support_extern(
        &mut args,
        &deps_dir,
        "state_machines_macros",
        "verus_state_machines_macros",
    )?;
    push_verus_support_extern(&mut args, &deps_dir, "verus_builtin", "verus_builtin")?;
    push_verus_support_extern(
        &mut args,
        &deps_dir,
        "verus_builtin_macros",
        "verus_builtin_macros",
    )?;
    push_verus_support_extern(
        &mut args,
        &deps_dir,
        "verus_state_machines_macros",
        "verus_state_machines_macros",
    )?;
    Ok(args)
}

fn refresh_local_vstd(verus_workdir: &Path, verus_binary_path: &Path) -> Result<(), VeritasError> {
    let verus_target_path = verus_binary_path
        .parent()
        .ok_or_else(|| verror!("verus binary has no parent directory"))?;
    let mut cmd = Command::new("cargo");
    cmd.current_dir(verus_workdir.join("source"))
        .env("VERUS_IN_VARGO", "1")
        .env("RUSTC_BOOTSTRAP", "1")
        .arg("run")
        .arg("--locked")
        .arg("--offline")
        .arg("-p")
        .arg("vstd_build")
        .arg("--")
        .arg(verus_target_path);
    match verus_target_path.file_name().and_then(|name| name.to_str()) {
        Some("release") => {
            cmd.arg("--release");
        }
        Some("debug") => {}
        _ => {
            warn(&format!(
                "unknown verus target profile directory {}; rebuilding vstd without explicit profile flag",
                verus_target_path.display()
            ));
        }
    }
    cmd.arg("--no-solver-version-check");
    let result = log_command(&mut cmd)
        .status()
        .map_err(|e| verror!("cannot execute vstd build helper: {}", e))?;
    result.success_or_err()
}

#[derive(Debug, Serialize, Deserialize, Hash, Clone)]
struct RunConfigurationProject {
    name: String,
    git_url: String,
    revspec: String,
    local_path: Option<String>,
    crate_root: String,
    extra_args: Option<Vec<String>>,
    prepare_script: Option<String>,
}

fn verus_verify_vstd_default() -> bool {
    true
}

#[derive(Debug, Serialize, Deserialize, Hash)]
struct RunConfiguration {
    verus_git_url: String,
    verus_revspec: String,
    verus_local_path: Option<String>,
    verus_binary_path: Option<String>,
    verus_features: Vec<String>,
    #[serde(default = "verus_verify_vstd_default")]
    verus_verify_vstd: bool,

    #[serde(rename = "project")]
    #[serde(default)]
    projects: Vec<RunConfigurationProject>,
}

#[derive(Deserialize, Hash)]
#[serde(rename_all = "kebab-case")]
struct VerusOutputTimesMs {
    estimated_cpu_time: u64,
    total: u64,
    smt: VerusOutputSmtTimesMs,
}

#[derive(Deserialize, Hash)]
#[serde(rename_all = "kebab-case")]
struct VerusOutputSmtTimesMs {
    smt_init: u64,
    smt_run: u64,
    total: u64,
}

#[derive(Debug, Serialize, Deserialize, Hash, Clone)]
#[serde(rename_all = "kebab-case")]
struct VerusOutputVerificationResults {
    encountered_vir_error: bool,
    success: Option<bool>,
    verified: Option<u64>,
    errors: Option<u64>,
    is_verifying_entire_crate: Option<bool>,
}

#[derive(Deserialize, Hash)]
#[serde(rename_all = "kebab-case")]
struct VerusOutput {
    times_ms: VerusOutputTimesMs,
    verification_results: VerusOutputVerificationResults,
}

fn run(run_configuration_path: &str) -> Result<(), VeritasError> {
    let run_configuration_path = std::path::Path::new(run_configuration_path);
    let run_configuration: RunConfiguration = {
        let mut run_configuration: RunConfiguration = toml::from_str(
            &std::fs::read_to_string(run_configuration_path).map_err(|e| {
                verror!(
                    "cannot read configuration file {}: {}",
                    run_configuration_path.display(),
                    e
                )
            })?,
        )
        .map_err(|e| verror!("cannot parse run configuration: {}", e))?;
        if run_configuration.verus_verify_vstd {
            run_configuration.projects.insert(
                0,
                RunConfigurationProject {
                    name: "verus-vstd".to_owned(),
                    git_url: run_configuration.verus_git_url.clone(),
                    revspec: run_configuration.verus_revspec.clone(),
                    local_path: run_configuration.verus_local_path.clone(),
                    crate_root: "source/vstd/vstd.rs".to_owned(),
                    extra_args: Some(vec![
                        "--is-vstd".to_owned(),
                        "--crate-type=lib".to_owned(),
                        // "-V".to_owned(),
                        // "use-crate-name".to_owned(),
                    ]),
                    prepare_script: None,
                },
            );
        }
        run_configuration
    };
    dbg!(&run_configuration);

    let mut repos_cache = ReposCache::init()?;
    let mut workdir = WorkDir::init()?;
    let mut z3_cache = Z3Cache::init()?;

    let verus_checkout = if let Some(local_path) = &run_configuration.verus_local_path {
        info(&format!("copying local verus from {}", local_path));
        workdir.checkout_local(VERUS_PROJECT_NAME, local_path)?
    } else {
        info(&format!(
            "checking out verus {}",
            run_configuration.verus_revspec
        ));
        workdir.checkout(
            &mut repos_cache,
            VERUS_PROJECT_NAME,
            &run_configuration.verus_git_url,
            &run_configuration.verus_revspec,
        )?
    };
    info(&format!("checked out verus commit {}", verus_checkout.hash));
    let verus_workdir = verus_checkout.workdir.as_path();
    let (verus_build_duration, verus_binary_path) =
        if let Some(verus_binary_path) = &run_configuration.verus_binary_path {
            let verus_binary_path = PathBuf::from(verus_binary_path);
            if !verus_binary_path.exists() {
                return Err(verror!(
                    "configured verus binary does not exist: {}",
                    verus_binary_path.display()
                ));
            }
            info(&format!(
                "using existing verus binary {}",
                verus_binary_path.display()
            ));
            if run_configuration.verus_local_path.is_some() {
                info("refreshing bundled vstd from the checked-out local verus source");
                refresh_local_vstd(verus_workdir, &verus_binary_path)?;
            }
            (std::time::Duration::ZERO, verus_binary_path)
        } else {
            info("building verus");
            let z3_version = {
                let get_z3_src =
                    std::fs::read_to_string(verus_workdir.join("source/tools/get-z3.sh"))
                        .map_err(|e| verror!("cannot read get-z3.sh: {}", e))?;
                let z3_version_regex = regex::Regex::new(r#"z3_version="([^"]+)""#)
                    .expect("invalid regex for z3_version");
                z3_version_regex
                    .captures(&get_z3_src)
                    .ok_or_else(|| verror!("cannot find z3_version in get_z3.sh"))?
                    .get(1)
                    .expect("no capture group")
                    .as_str()
                    .to_string()
            };
            info(&format!("getting z3 {z3_version}"));
            let z3_cached = z3_cache.ensure_z3_version(&mut workdir, &z3_version)?;
            std::fs::copy(&z3_cached, verus_workdir.join("source/z3"))
                .map_err(|e| verror!("cannot copy z3 to verus source: {}", e))?;

            let features_args = if run_configuration.verus_features.len() > 0 {
                Some("--features".to_string())
                    .into_iter()
                    .chain(run_configuration.verus_features.iter().cloned())
                    .collect::<Vec<_>>()
                    .join(" ")
            } else {
                String::new()
            };

            let verus_build_start = std::time::Instant::now();
            let result = log_command(
                Command::new("/bin/bash")
                    .current_dir(verus_workdir)
                    .env("VERUS_FEATURES_ARGS", &features_args)
                    .arg(runner_path().join(BUILD_VERUS_SCRIPT_FILENAME)),
            )
            .status()
            .map_err(|e| verror!("cannot execute verus build script: {}", e))?;
            result.success_or_err()?;

            info("verus ready");
            (
                verus_build_start.elapsed(),
                verus_workdir.join("source/target-verus/release/verus"),
            )
        };
    // TODO perform line counting? (once line_count is fixed)
    // let _verus_line_count_path = verus_workdir.join("source/target/release/line_count");
    let verus_support_args = verus_support_args(&verus_binary_path)?;

    let output_path = env_var_dir_or_err(OUTPUT_PATH_VAR)?;
    let date = chrono::Utc::now()
        .format("%Y-%m-%d-%H-%M-%S-%3f")
        .to_string();
    let run_configuration_digest = digest::obj_digest(&run_configuration);
    let run_output_path = output_path.join(date + "-" + &run_configuration_digest);
    info(&format!(
        "producing output at {}",
        run_output_path.display()
    ));
    std::fs::create_dir(&run_output_path).map_err(|e| {
        verror!(
            "cannot create output dir {}: {}",
            run_output_path.display(),
            e
        )
    })?;

    let mut project_summaries = Vec::new();

    info("running projects");
    for project in run_configuration.projects.iter() {
        info(&format!("running project {}", project.name));
        let proj_checkout = if let Some(local_path) = &project.local_path {
            workdir.checkout_local(&project.name, local_path)?
        } else {
            workdir.checkout(
                &mut repos_cache,
                &project.name,
                &project.git_url,
                &project.revspec,
            )?
        };
        let proj_workdir = proj_checkout.workdir.as_path();
        if let Some(prepare_script) = &project.prepare_script {
            let result = log_command(
                Command::new("/bin/bash")
                    .current_dir(proj_workdir)
                    .env_remove("CARGO_TARGET_DIR")
                    .arg("-c")
                    .arg(prepare_script),
            )
            .status()
            .map_err(|e| verror!("cannot execute prepare script for {}: {}", &project.name, e))?;
            result.success_or_err()?;
        }
        let project_verification_start = std::time::Instant::now();
        let output = log_command(
            Command::new(&verus_binary_path)
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::inherit())
                .current_dir(proj_workdir)
                .arg(&project.crate_root)
                .args(project.extra_args.as_ref().map(|ea| &ea[..]).unwrap_or(&[]))
                .args(if project.name == "verus-vstd" {
                    &[][..]
                } else {
                    &verus_support_args[..]
                })
                .arg("--output-json")
                .arg("--time")
                .arg("--no-report-long-running"),
        )
        .output()
        .map_err(|e| verror!("cannot execute verus on {}: {}", &project.name, e))?;
        let project_verification_duration = project_verification_start.elapsed();

        let project_run_configuration_digest = digest::obj_digest(&project);
        let project_output_path_json = run_output_path
            .join(project.name.to_owned() + "-" + &project_run_configuration_digest)
            .with_extension("json");

        let (output_json, verus_output) =
            match serde_json::from_slice::<serde_json::Value>(&output.stdout) {
                Ok(mut output_json) => {
                    let verus_output: Option<VerusOutput> =
                        match serde_json::from_value(output_json.clone()) {
                            Ok(v) => Some(v),
                            Err(e) => {
                                warn(&format!(
                                    "cannot parse verus output for {}: {}",
                                    &project.name, e
                                ));
                                None
                            }
                        };
                    let duration_ms_value = serde_json::Value::Number(
                        serde_json::Number::from_f64(
                            project_verification_duration.as_millis() as f64
                        )
                        .expect("valid verus_build_duration"),
                    );
                    output_json["runner"] = serde_json::json!({
                        "success": output.status.success(),
                        "stderr": String::from_utf8_lossy(&output.stderr),
                        "verus_git_url": run_configuration.verus_git_url,
                        "verus_revspec": run_configuration.verus_revspec,
                        "verus_features": run_configuration.verus_features,
                        "run_configuration": project,
                        "verification_duration_ms": duration_ms_value,
                    });
                    (output_json, verus_output)
                }
                Err(e) => {
                    warn(&format!(
                        "cannot parse verus output for {}: {}",
                        &project.name, e
                    ));
                    (
                        serde_json::json!({
                            "runner": {
                                "success": output.status.success(),
                                "stderr": String::from_utf8_lossy(&output.stderr),
                                "invalid_output_json": true,
                            }
                        }),
                        None,
                    )
                }
            };
        std::fs::write(
            &project_output_path_json,
            serde_json::to_string_pretty(&output_json).unwrap(),
        )
        .map_err(|e| verror!("cannot write output json: {}", e))?;

        project_summaries.push((
            project.clone(),
            output.status.success(),
            proj_checkout.hash,
            project_verification_duration,
            verus_output,
        ));
    }

    let summary_output_path = run_output_path.join("summary.json");
    let summary = {
        #[derive(Debug, Serialize)]
        #[serde(rename_all = "kebab-case")]
        struct ProjectSummaryTimesMs {
            estimated_cpu_time: u64,
            total: u64,
            smt_init: u64,
            smt_run: u64,
            smt_total: u64,
        }

        #[derive(Debug, Serialize)]
        #[serde(rename_all = "kebab-case")]
        #[serde(tag = "type")]
        enum ProjectSummary {
            FullSummary {
                run_configuration: RunConfigurationProject,
                verification_results: VerusOutputVerificationResults,
                times_ms: ProjectSummaryTimesMs,
                verification_duration_ms: u128,
                project_commit_hash: String,
            },
            ParseFailure {
                run_configuration: RunConfigurationProject,
                project_commit_hash: String,
            },
        }

        let run_configuration_json_value: serde_json::Value =
            serde_json::to_value(&run_configuration)
                .map_err(|e| verror!("cannot convert run configuration to json: {}", e))?;
        let project_summaries = project_summaries
            .iter()
            .map(
                |(
                    run_configuration,
                    runner_success,
                    project_checkout_hash,
                    project_verification_duration,
                    project_summary,
                )| {
                    let valid_output = project_summary.is_some();
                    let project_summary_json =
                        serde_json::to_value(if let Some(project_summary) = project_summary {
                            ProjectSummary::FullSummary {
                                run_configuration: run_configuration.clone(),
                                verification_results: project_summary.verification_results.clone(),
                                times_ms: ProjectSummaryTimesMs {
                                    estimated_cpu_time: project_summary.times_ms.estimated_cpu_time,
                                    total: project_summary.times_ms.total,
                                    smt_init: project_summary.times_ms.smt.total,
                                    smt_run: project_summary.times_ms.smt.smt_run,
                                    smt_total: project_summary.times_ms.smt.total,
                                },
                                verification_duration_ms: project_verification_duration.as_millis(),
                                project_commit_hash: project_checkout_hash.clone(),
                            }
                        } else {
                            ProjectSummary::ParseFailure {
                                run_configuration: run_configuration.clone(),
                                project_commit_hash: project_checkout_hash.clone(),
                            }
                        })
                        .map_err(|e| verror!("cannot convert summary to json: {}", e))?;
                    let serde_json::Value::Object(mut project_summary_json_map) =
                        project_summary_json
                    else {
                        panic!("unexpected json value for project summary");
                    };
                    project_summary_json_map.insert(
                        "valid_output".to_owned(),
                        serde_json::Value::Bool(valid_output),
                    );
                    project_summary_json_map.insert(
                        "runner_success".to_owned(),
                        serde_json::Value::Bool(*runner_success),
                    );
                    Ok(serde_json::Value::Object(project_summary_json_map))
                },
            )
            .collect::<Result<Vec<_>, VeritasError>>()?;
        let project_summaries_json_value: serde_json::Value =
            serde_json::to_value(&project_summaries)
                .map_err(|e| verror!("cannot convert summary to json: {}", e))?;

        let mut summary = serde_json::Map::new();
        summary.insert("run_configuration".to_owned(), run_configuration_json_value);
        summary.insert(
            "verus_build_duration_ms".to_owned(),
            serde_json::Value::Number(
                serde_json::Number::from_f64(verus_build_duration.as_millis() as f64)
                    .expect("valid verus_build_duration"),
            ),
        );
        summary.insert(
            "verus_commit_hash".to_owned(),
            serde_json::Value::String(verus_checkout.hash.clone()),
        );
        summary.insert("project_summaries".to_owned(), project_summaries_json_value);
        let summary = serde_json::Value::Object(summary);

        summary
    };
    std::fs::write(
        &summary_output_path,
        serde_json::to_string_pretty(&summary).expect("valid json"),
    )
    .map_err(|e| verror!("cannot write summary toml: {}", e))?;
    info(&format!(
        "output written to {}",
        display_path(&run_output_path)
    ));
    info(&format!(
        "summary written to {}",
        display_path(&summary_output_path)
    ));

    {
        let mut summary_md = String::with_capacity(1024);
        use std::fmt::Write;
        writeln!(
            &mut summary_md,
            "veritas report for verus `{}` (`{}`) with features: `{}`",
            run_configuration.verus_revspec,
            verus_checkout.hash,
            run_configuration.verus_features.join(" ")
        )
        .unwrap();
        writeln!(&mut summary_md).unwrap();
        writeln!(
            &mut summary_md,
            "| project | revspec | outcome | total verus time (ms) | smt run time (ms) |"
        )
        .unwrap();
        writeln!(
            &mut summary_md,
            "| ------- | ------- | ------- | --------------------- | ----------------- |"
        )
        .unwrap();
        for (
            project_run_configuration,
            project_runner_success,
            project_checkout_hash,
            project_verification_duration,
            project_summary,
        ) in project_summaries.iter()
        {
            writeln!(
                &mut summary_md,
                "| {} | {} | {} | {} | {} |",
                project_run_configuration.name,
                format!(
                    "`{}` (`{}`)",
                    &project_run_configuration.revspec, &project_checkout_hash
                ),
                project_summary
                    .as_ref()
                    .and_then(|t| t.verification_results.success.map(|s| {
                        let mut outcome = if *project_runner_success && s {
                            "success"
                        } else {
                            "failure"
                        }
                        .to_owned();
                        if let (Some(verified), Some(errors)) = (
                            t.verification_results.verified,
                            t.verification_results.errors,
                        ) {
                            outcome += &format!(" ({verified} verified, {errors} errors)");
                        }
                        outcome
                    }))
                    .unwrap_or("unknown".to_owned()),
                project_verification_duration.as_millis(),
                project_summary
                    .as_ref()
                    .map(|t| format!("{}", t.times_ms.smt.smt_run))
                    .unwrap_or("unknown".to_owned()),
            )
            .unwrap();
        }
        let summary_md_output_path = run_output_path.join("summary.md");
        let mut summary_md_file = std::fs::File::options()
            .create(true)
            .write(true)
            .open(&summary_md_output_path)
            .map_err(|e| {
                verror!(
                    "cannot open {} for writing: {}",
                    summary_md_output_path.display(),
                    e
                )
            })?;
        std::io::Write::write(&mut summary_md_file, &summary_md.as_bytes()).map_err(|e| {
            verror!(
                "cannot write to {}: {}",
                summary_md_output_path.display(),
                e
            )
        })?;
        std::mem::drop(summary_md_file);
        info(&format!(
            "markdown table written to {}",
            display_path(&summary_md_output_path)
        ));
    }

    Ok(())
}

fn main() {
    use printing::error;

    let mut args = std::env::args();
    let program = args.next().expect("no program name");
    let args: Vec<_> = args.collect();

    let mut opts = getopts::Options::new();
    opts.optflag("h", "help", "print this help menu");

    let matches = match opts.parse(&args) {
        Ok(m) => m,
        Err(f) => {
            error(&verror!("{}", f));
        }
    };

    fn print_usage(program: &str, opts: getopts::Options) {
        let brief = format!("Usage: {} run_configuration.json [options]", program);
        print!("{}", opts.usage(&brief));
    }

    if matches.opt_present("h") {
        print_usage(&program, opts);
        return;
    }

    let run_configuration_path = if matches.free.len() == 1 {
        matches.free[0].clone()
    } else {
        print_usage(&program, opts);
        return;
    };

    match run(&run_configuration_path) {
        Ok(_) => {}
        Err(err) => error(&err),
    }
}
