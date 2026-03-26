use crate::config::RunConfiguration;
use crate::config::RunConfigurationProject;
use crate::dependencies::inject_verus_patches;
use crate::output::VerusOutput;
use anyhow::anyhow;
use clap::Parser as ClapParser;
use git2::Repository;
use regex::Regex;
use std::{fs, path::Path, path::PathBuf};
use tempdir::TempDir;
use tracing::{debug, error, info, warn};
use xshell::{cmd, Shell};

pub mod config;
pub mod dependencies;
pub mod output;

#[derive(ClapParser)]
#[command(version, about)]
struct Args {
    /// Base of the Verus repository
    #[arg(short, long)]
    verus_repo: PathBuf,
    /// Path to the Singular algebra solver
    #[arg(short, long)]
    singular: Option<PathBuf>,
    /// Path to a run configuration file
    config: PathBuf,
    /// Label for the run
    #[arg(short, long)]
    label: String,
    /// Enable debug output; repeat for more detail (-d: debug, -dd: trace).
    /// Also causes verita to retain the project repos it clones.
    #[arg(short = 'd', long = "debug", action = clap::ArgAction::Count)]
    debug_level: u8,
    /// Run projects even if they are marked `ignore = true` in the configuration.
    #[arg(long)]
    run_ignored: bool,
    /// Run only the named project(s); may be given multiple times.
    /// Projects not listed here are skipped.  The `ignore` flag and
    /// `--run-ignored` still apply to the named projects.
    #[arg(long = "project", value_name = "NAME")]
    projects: Vec<String>,
    /// Exit with a non-zero status if any active project fails verification.
    #[arg(long)]
    fail_on_error: bool,
}

fn get_solver_version(
    verus_repo: &Path,
    solver_exe: &str,
    fmt_str: &str,
) -> anyhow::Result<String> {
    let sh = Shell::new()?;
    let solver_path =
        verus_repo
            .join("source")
            .join(format!("{}{}", solver_exe, std::env::consts::EXE_SUFFIX));
    let output = cmd!(sh, "{solver_path} --version").output()?;
    //dbg!(&output);
    let output_str = String::from_utf8(output.stdout)?;
    let fmt = format!("{fmt_str} ([0-9.]*) ");
    let v = Regex::new(&fmt)?
        .captures(&output_str)
        .ok_or_else(|| anyhow!("Failed to find {solver_exe} version"))?
        .get(1)
        .expect("missing capture group")
        .as_str()
        .to_string();
    debug!("Found {solver_exe} version: {v}");
    Ok(v)
}

pub fn log_command(cmd: std::process::Command) -> std::process::Command {
    debug!("running: {:?}", &cmd);
    cmd
}

type ProjectSummary = (
    RunConfigurationProject,
    bool,
    String,
    std::time::Duration,
    Option<VerusOutput>,
);

/// Shared context for processing projects and targets within a run.
struct RunContext<'a> {
    sh: &'a Shell,
    verus_binary_path: &'a Path,
    cargo_verus_binary_path: &'a Path,
    verus_repo: &'a Path,
    run_configuration: &'a RunConfiguration,
    output_path: &'a Path,
    label: &'a str,
    date: &'a str,
    z3_version: &'a str,
    cvc5_version: &'a str,
}

/// Compute the output-file suffix for a given crate-root target.
///
/// For targets like `"capybaraKV/capybarakv"` the suffix is the parent
/// directory path with `/` replaced by `-` (e.g. `"capybaraKV"`).  For
/// targets without a parent directory (e.g. `"pmemlog"`), we fall back to
/// the target name itself so that each multi-target project gets a unique
/// output filename.
fn target_output_suffix(target: &str) -> String {
    let dir: String = Path::new(target)
        .parent()
        .map(|p| {
            p.components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join("-")
        })
        .unwrap_or_default();
    if dir.is_empty() {
        // Bare name like "pmemlog" – use the file/dir stem itself.
        Path::new(target)
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_default()
    } else {
        dir
    }
}

/// Process a single crate root target within a project.
/// Returns (summary, verus_failed, warnings) or an error.
fn process_target(
    ctx: &RunContext,
    project: &RunConfigurationProject,
    repo_path: &Path,
    target: &str,
    target_index: usize,
    total_targets: usize,
    hash: &str,
) -> anyhow::Result<(ProjectSummary, bool, Vec<String>)> {
    let sh = ctx.sh;
    let verus_binary_path = ctx.verus_binary_path;
    let cargo_verus_binary_path = ctx.cargo_verus_binary_path;

    info!(
        "running target {target} ({} of {})",
        target_index + 1,
        total_targets
    );
    let project_verification_start = std::time::Instant::now();
    let output = if project.cargo_verus {
        // Run cargo-verus focus in the target directory
        let target_dir = repo_path.join(target);
        sh.change_dir(&target_dir);

        // Override any Verus crate dependencies to use the local Verus repo
        if let Err(e) = inject_verus_patches(
            &target_dir,
            repo_path,
            ctx.verus_repo,
            &ctx.run_configuration.verus_git_url,
        ) {
            warn!(
                "Failed to inject Verus patches for {} target {}: {}",
                project.name, target, e
            );
        }

        // If the crate has both src/lib.rs and src/main.rs, cargo-verus will
        // produce separate JSON output for each target. Detect this and pass
        // --bin <name> to only verify the binary target.
        let mut cargo_target_args: Vec<String> = Vec::new();
        if target_dir.join("src/lib.rs").exists() && target_dir.join("src/main.rs").exists() {
            // Read the package name from Cargo.toml to use as the bin target name
            let cargo_toml_path = target_dir.join("Cargo.toml");
            let cargo_toml: toml::Value = toml::from_str(
                &std::fs::read_to_string(&cargo_toml_path)
                    .map_err(|e| anyhow!("cannot read {}: {}", cargo_toml_path.display(), e))?,
            )
            .map_err(|e| anyhow!("cannot parse {}: {}", cargo_toml_path.display(), e))?;
            if let Some(name) = cargo_toml
                .get("package")
                .and_then(|p| p.get("name"))
                .and_then(|n| n.as_str())
            {
                debug!(
                    "Detected both src/lib.rs and src/main.rs in {}; selecting --bin {}",
                    target, name
                );
                cargo_target_args.push("--bin".to_string());
                cargo_target_args.push(name.to_string());
            }
        }

        log_command(
            cmd!(sh, "{cargo_verus_binary_path} verus focus")
                .args(project.extra_cargo_args.iter().flatten())
                .args(&cargo_target_args)
                .args(["--", "--output-json", "--time"])
                .args(ctx.run_configuration.verus_extra_args.iter().flatten())
                .args(project.extra_verus_args.iter().flatten())
                .into(),
        )
        .output()
        .map_err(|e| anyhow!("cannot execute cargo verus on {}: {}", &project.name, e))?
    } else {
        log_command(
            cmd!(sh, "{verus_binary_path} --output-json --time {target}")
                .args(ctx.run_configuration.verus_extra_args.iter().flatten())
                .args(project.extra_verus_args.iter().flatten())
                .into(),
        )
        .output()
        .map_err(|e| anyhow!("cannot execute verus on {}: {}", &project.name, e))?
    };
    let project_verification_duration = project_verification_start.elapsed();

    let verus_failed = !output.status.success();
    if verus_failed {
        let stderr_str = String::from_utf8_lossy(&output.stderr);
        warn!(
            "Verus exited non-zero for {} target {} \
             (may not have reached verification)",
            &project.name, target
        );
        if !stderr_str.trim().is_empty() {
            warn!("Verus stderr:\n{}", stderr_str.trim_end());
        }
    }

    // Build output filename: use project name alone for single targets,
    // or "project-crate-root-dir" for multiple targets
    let output_name = if total_targets == 1 {
        project.name.clone()
    } else {
        let suffix = target_output_suffix(target);
        if suffix.is_empty() {
            project.name.clone()
        } else {
            format!("{}-{}", project.name, suffix)
        }
    };
    let project_output_path_json = ctx.output_path.join(&output_name).with_extension("json");

    let mut warnings = Vec::new();

    // Use a streaming deserializer to handle cases where cargo-verus
    // outputs multiple JSON objects (e.g., one per crate target, including
    // no-verify dependency runs like vstd)
    let stream =
        serde_json::Deserializer::from_slice(&output.stdout).into_iter::<serde_json::Value>();

    // Parse all JSON objects and filter out no-verify dependency outputs
    // (those with success: true and verified: 0)
    let mut all_objects = Vec::new();
    let mut skipped_count = 0usize;
    for item in stream {
        match item {
            Ok(obj) => {
                let is_noverify_dep = obj
                    .get("verification-results")
                    .map(|vr| {
                        vr.get("success") == Some(&serde_json::Value::Bool(true))
                            && vr.get("verified") == Some(&serde_json::json!(0))
                    })
                    .unwrap_or(false);
                if is_noverify_dep {
                    skipped_count += 1;
                } else {
                    all_objects.push(obj);
                }
            }
            Err(e) => {
                error!("cannot parse verus output for {}: {}", &project.name, e);
                error!("got: {}", &String::from_utf8_lossy(&output.stdout));
                break;
            }
        }
    }
    if skipped_count > 0 {
        debug!(
            "Skipped {} no-verify dependency output(s) for {} target {}",
            skipped_count, project.name, target
        );
    }
    if all_objects.len() > 1 {
        let warning_msg = format!(
            "{} target {}: {} JSON outputs remained after filtering \
             (expected 1); using the first",
            project.name,
            target,
            all_objects.len()
        );
        warn!("{}", warning_msg);
        warnings.push(warning_msg);
    }

    let (output_json, verus_output) = if let Some(mut output_json) = all_objects.into_iter().next()
    {
        let verus_output: Option<VerusOutput> = match serde_json::from_value(output_json.clone()) {
            Ok(v) => Some(v),
            Err(e) => {
                if verus_failed {
                    // Verus already logged a warning above; the incomplete
                    // JSON (e.g., missing `smt`) is expected in this case.
                    debug!(
                        "Verus JSON for {} is incomplete (failed before \
                             verification): {}",
                        &project.name, e
                    );
                } else {
                    error!(
                        "cannot parse verus json output for {}: {}",
                        &project.name, e
                    );
                    let stderr_str = String::from_utf8_lossy(&output.stderr);
                    if !stderr_str.trim().is_empty() {
                        error!("Verus stderr: {}", stderr_str.trim_end());
                    }
                }
                None
            }
        };
        let duration_ms_value = serde_json::Value::Number(
            serde_json::Number::from_f64(project_verification_duration.as_millis() as f64)
                .expect("valid verus_build_duration"),
        );
        output_json["runner"] = serde_json::json!({
            "success": output.status.success(),
            "stderr": String::from_utf8_lossy(&output.stderr),
            "verus_git_url": ctx.run_configuration.verus_git_url,
            "verus_refspec": ctx.run_configuration.verus_refspec,
            "verus_features": ctx.run_configuration.verus_features,
            "run_configuration": project,
            "verification_duration_ms": duration_ms_value,
            "z3_version": ctx.z3_version,
            "cvc5_version": ctx.cvc5_version,
            "label": ctx.label,
            "date": ctx.date,
        });
        (output_json, verus_output)
    } else {
        error!(
            "cannot parse verus output for {}: no valid output \
             (had {} no-verify dependency output(s))",
            &project.name, skipped_count
        );
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
    };
    std::fs::write(
        &project_output_path_json,
        serde_json::to_string_pretty(&output_json)?,
    )
    .map_err(|e| anyhow!("cannot write output json: {}", e))?;

    Ok((
        (
            project.clone(),
            output.status.success(),
            hash.to_string(),
            project_verification_duration,
            verus_output,
        ),
        verus_failed,
        warnings,
    ))
}

/// Process a single project: clone, checkout, prepare, and run all crate root targets.
/// Returns (summaries, any_verus_failure, warnings) or an error.
fn process_project(
    ctx: &RunContext,
    project: &RunConfigurationProject,
    workdir: &Path,
) -> anyhow::Result<(Vec<ProjectSummary>, bool, Vec<String>)> {
    info!("running project {}", project.name);

    debug!("Cloning project");
    let repo_path = workdir.join(&project.name);
    let project_repo = Repository::clone(&project.git_url, &repo_path)?;
    let (rev, _reference) = project_repo
        .revparse_ext(&project.refspec)
        .map_err(|e| anyhow!("failed to find {}: {}", project.refspec, e))?;
    project_repo.checkout_tree(&rev, None)?;
    let hash = rev.id().to_string();
    ctx.sh.change_dir(&repo_path);

    // Select the appropriate prepare script for this platform
    let platform_script: Option<&str> = if cfg!(windows) {
        if let Some(s) = project.prepare_script_windows.as_deref() {
            Some(s)
        } else if project.prepare_script.is_some() {
            warn!(
                "Project {} has prepare_script but no prepare_script_windows; \
                 skipping prepare step on Windows",
                project.name
            );
            None
        } else {
            None
        }
    } else {
        project.prepare_script.as_deref()
    };

    if let Some(prepare_script) = platform_script {
        let status = if cfg!(windows) {
            log_command(cmd!(ctx.sh, "powershell -Command {prepare_script}").into()).status()
        } else {
            log_command(cmd!(ctx.sh, "bash -c {prepare_script}").into()).status()
        };
        let exit_status = status
            .map_err(|e| anyhow!("cannot execute prepare script for {}: {}", &project.name, e))?;
        if !exit_status.success() {
            return Err(anyhow!(
                "prepare script for {} failed with {}",
                &project.name,
                exit_status
            ));
        }
    }

    let mut summaries = Vec::new();
    let mut any_verus_failure = false;
    let mut all_warnings = Vec::new();

    for (target_index, target) in project.crate_roots.iter().enumerate() {
        match process_target(
            ctx,
            project,
            &repo_path,
            target,
            target_index,
            project.crate_roots.len(),
            &hash,
        ) {
            Ok((summary, verus_failed, warnings)) => {
                if verus_failed {
                    any_verus_failure = true;
                }
                all_warnings.extend(warnings);
                summaries.push(summary);
            }
            Err(e) => {
                error!(
                    "Failed to process target {} for project {}: {}",
                    target, project.name, e
                );
                // Write an error JSON so the failure is recorded in output
                let output_name = if project.crate_roots.len() == 1 {
                    project.name.clone()
                } else {
                    let suffix = target_output_suffix(target);
                    if suffix.is_empty() {
                        project.name.clone()
                    } else {
                        format!("{}-{}", project.name, suffix)
                    }
                };
                let error_json = serde_json::json!({
                    "runner": {
                        "success": false,
                        "error": format!("{}", e),
                        "run_configuration": project,
                    }
                });
                let error_path = ctx.output_path.join(&output_name).with_extension("json");
                if let Err(write_err) = std::fs::write(
                    &error_path,
                    serde_json::to_string_pretty(&error_json).unwrap(),
                ) {
                    error!(
                        "Failed to write error json for {} target {}: {}",
                        project.name, target, write_err
                    );
                }
                any_verus_failure = true;
            }
        }
    }

    Ok((summaries, any_verus_failure, all_warnings))
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    tracing_subscriber::fmt()
        .with_timer(tracing_subscriber::fmt::time::uptime())
        .with_level(true)
        .with_target(false)
        .with_max_level(match args.debug_level {
            0 => tracing::Level::INFO,
            1 => tracing::Level::DEBUG,
            _ => tracing::Level::TRACE,
        })
        .init();
    let verus_repo = dunce::canonicalize(args.verus_repo)?;

    let z3_version = match get_solver_version(&verus_repo, "z3", "Z3 version") {
        Ok(v) => v,
        Err(_) => "unknown".to_string(),
    };
    let cvc5_version = match get_solver_version(&verus_repo, "cvc5", "This is cvc5 version") {
        Ok(v) => v,
        Err(_) => "unknown".to_string(),
    };

    // let verus_repo = Repository::open(args.verus_repo)?;
    // println!("Found repo with head {:?}, state {:?}, ", verus_repo.head()?.name().unwrap(), verus_repo.state());

    // Check that verus executable is present
    let verus_binary_path = verus_repo
        .join("source/target-verus/release")
        .join(format!("verus{}", std::env::consts::EXE_SUFFIX));
    if fs::metadata(&verus_binary_path).is_err() {
        return Err(anyhow!(
            "failed to find verus binary: {}",
            verus_binary_path.display()
        ));
    }
    debug!("Found verus binary");

    let cargo_verus_binary_path = verus_repo
        .join("source/target-verus/release")
        .join(format!("cargo-verus{}", std::env::consts::EXE_SUFFIX));

    let run_configuration: RunConfiguration =
        toml::from_str(&std::fs::read_to_string(&args.config).map_err(|e| {
            anyhow!(
                "cannot read configuration file {}: {}",
                args.config.display(),
                e
            )
        })?)
        .map_err(|e| anyhow!("cannot parse run configuration: {}", e))?;

    debug!("Loaded run configuration:");

    // Check that extra_cargo_args is only used with cargo_verus projects
    let invalid_cargo_args: Vec<&str> = run_configuration
        .projects
        .iter()
        .filter(|p| !p.cargo_verus && p.extra_cargo_args.is_some())
        .map(|p| p.name.as_str())
        .collect();
    if !invalid_cargo_args.is_empty() {
        return Err(anyhow!(
            "the following projects set `extra_cargo_args` but do not have \
             `cargo_verus = true`: {}",
            invalid_cargo_args.join(", ")
        ));
    }

    // Check that cargo-verus executable is present if any project needs it
    if run_configuration.projects.iter().any(|p| p.cargo_verus) {
        if fs::metadata(&cargo_verus_binary_path).is_err() {
            return Err(anyhow!(
                "failed to find cargo-verus binary: {}",
                cargo_verus_binary_path.display()
            ));
        }
        debug!("Found cargo-verus binary");
    }

    // Check that --singular was provided (or VERUS_SINGULAR_PATH is already set)
    // if any active project requires it
    let singular_required: Vec<&str> = run_configuration
        .projects
        .iter()
        .filter(|p| (!p.ignore || args.run_ignored) && p.requires_singular)
        .map(|p| p.name.as_str())
        .collect();
    if !singular_required.is_empty()
        && args.singular.is_none()
        && std::env::var("VERUS_SINGULAR_PATH").is_err()
    {
        return Err(anyhow!(
            "the following projects require Singular (set `requires_singular = true` \
             in their config) but --singular was not specified and \
             VERUS_SINGULAR_PATH is not set: {}",
            singular_required.join(", ")
        ));
    }

    debug!("Running projects");
    let sh = Shell::new()?;

    // For each solver path: use the explicit verus-repo default only when the
    // corresponding environment variable isn't already set by the caller.
    if std::env::var("VERUS_Z3_PATH").is_ok() {
        debug!("Respecting existing VERUS_Z3_PATH from environment");
    } else {
        sh.set_var(
            "VERUS_Z3_PATH",
            verus_repo
                .join("source")
                .join(format!("z3{}", std::env::consts::EXE_SUFFIX)),
        );
    }
    if std::env::var("VERUS_CVC5_PATH").is_ok() {
        debug!("Respecting existing VERUS_CVC5_PATH from environment");
    } else {
        sh.set_var(
            "VERUS_CVC5_PATH",
            verus_repo
                .join("source")
                .join(format!("cvc5{}", std::env::consts::EXE_SUFFIX)),
        );
    }

    // If --singular was given, validate and set the path; otherwise fall back
    // to VERUS_SINGULAR_PATH if already present in the environment.
    if let Some(p) = args.singular {
        if fs::metadata(&p).is_err() {
            return Err(anyhow!(
                "failed to find specified Singular binary: {}",
                p.display()
            ));
        }
        sh.set_var("VERUS_SINGULAR_PATH", p);
    } else if std::env::var("VERUS_SINGULAR_PATH").is_ok() {
        debug!("Respecting existing VERUS_SINGULAR_PATH from environment");
    }

    let date = chrono::Utc::now()
        .format("%Y-%m-%d-%H-%M-%S-%3f")
        .to_string();
    let output_path = Path::new("output").join(format!("{}-{}", &date, &args.label));
    let tmp_dir = TempDir::new("verita")?;
    let perm_temp_dir = std::env::temp_dir().join("verita").join(&date);
    std::fs::create_dir_all(&output_path)?;
    let workdir = if args.debug_level > 0 {
        // Use a directory that won't disappear after we run, so we can debug any issues that arise
        std::fs::create_dir_all(&perm_temp_dir)?;
        perm_temp_dir.as_path()
    } else {
        // Use a directory that will be automatically reclaimed after we terminate
        tmp_dir.path()
    };
    debug!("Work directory: {}", &workdir.display());

    let ctx = RunContext {
        sh: &sh,
        verus_binary_path: &verus_binary_path,
        cargo_verus_binary_path: &cargo_verus_binary_path,
        verus_repo: &verus_repo,
        run_configuration: &run_configuration,
        output_path: &output_path,
        label: &args.label,
        date: &date,
        z3_version: &z3_version,
        cvc5_version: &cvc5_version,
    };

    let mut project_summaries = Vec::new();
    let mut failed_projects: Vec<(String, Option<PathBuf>)> = Vec::new();
    let mut succeeded_projects: Vec<String> = Vec::new();
    let mut ignored_projects: Vec<String> = Vec::new();
    let mut all_warnings: Vec<String> = Vec::new();

    for project in run_configuration.projects.iter() {
        if !args.projects.is_empty() && !args.projects.contains(&project.name) {
            debug!(
                "Skipping project {} (not in --project filter)",
                project.name
            );
            continue;
        }
        if project.ignore && !args.run_ignored {
            info!("Skipping ignored project {}", project.name);
            ignored_projects.push(project.name.clone());
            continue;
        }
        match process_project(&ctx, project, workdir) {
            Ok((summaries, any_verus_failure, warnings)) => {
                all_warnings.extend(warnings);
                // If any target had Verus failures and we're in auto-cleanup mode,
                // preserve the repo for debugging
                let mut preserved_path = None;
                if any_verus_failure && args.debug_level == 0 {
                    let src = workdir.join(&project.name);
                    let dest = perm_temp_dir.join(&project.name);
                    if src.exists() {
                        if let Err(e) = fs::create_dir_all(&perm_temp_dir) {
                            warn!(
                                "Failed to create persistent directory for {}: {}",
                                project.name, e
                            );
                        } else {
                            // Use a rename if possible (same filesystem), otherwise warn
                            if let Err(e) = fs::rename(&src, &dest) {
                                warn!(
                                    "Failed to preserve repo for {} (rename failed: {})",
                                    project.name, e
                                );
                            } else {
                                println!(
                                    "Preserved repo for {} (had verification errors) at: {}",
                                    project.name,
                                    dest.display()
                                );
                                preserved_path = Some(dest);
                            }
                        }
                    }
                } else if any_verus_failure && args.debug_level > 0 {
                    preserved_path = Some(workdir.join(&project.name));
                }

                if any_verus_failure {
                    failed_projects.push((project.name.clone(), preserved_path));
                } else {
                    succeeded_projects.push(project.name.clone());
                }
                project_summaries.extend(summaries);
            }
            Err(e) => {
                error!("Failed to process project {}: {}", project.name, e);
                failed_projects.push((project.name.clone(), None));
                // Write an error JSON so the failure is recorded in output
                let error_json = serde_json::json!({
                    "runner": {
                        "success": false,
                        "error": format!("{}", e),
                        "run_configuration": project,
                    }
                });
                let error_path = output_path.join(&project.name).with_extension("json");
                if let Err(write_err) = std::fs::write(
                    &error_path,
                    serde_json::to_string_pretty(&error_json).unwrap(),
                ) {
                    error!(
                        "Failed to write error json for {}: {}",
                        project.name, write_err
                    );
                }
            }
        }
    }

    // Print summary
    println!("\n--- Run Summary ---");
    println!(
        "Total projects: {}",
        succeeded_projects.len() + failed_projects.len() + ignored_projects.len()
    );
    if !succeeded_projects.is_empty() {
        println!(
            "Succeeded ({}): {}",
            succeeded_projects.len(),
            succeeded_projects.join(", ")
        );
    }
    if !failed_projects.is_empty() {
        println!("Failed ({}):", failed_projects.len());
        for (name, preserved_path) in &failed_projects {
            if let Some(path) = preserved_path {
                println!("  {} (repo preserved at: {})", name, path.display());
            } else {
                println!("  {}", name);
            }
        }
    }
    if !ignored_projects.is_empty() {
        println!(
            "Ignored ({}): {}",
            ignored_projects.len(),
            ignored_projects.join(", ")
        );
    }
    if !all_warnings.is_empty() {
        println!("Warnings ({}):", all_warnings.len());
        for w in &all_warnings {
            println!("  {}", w);
        }
    }
    println!("Output: {}", output_path.display());

    if args.fail_on_error && !failed_projects.is_empty() {
        return Err(anyhow!(
            "{} project(s) failed verification: {}",
            failed_projects.len(),
            failed_projects
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }

    Ok(())
}
