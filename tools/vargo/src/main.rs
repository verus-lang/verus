// Vargo is a wrapper around cargo that sets up the environment for building
// Verus and collects build artifacts for libraries used by vstd and client
// code so that later compilation stages (building, verifying vstd and running tests)
// can use them. This is necessary because cargo only builds libraries in
// `target/debug` or `target/release` when they are the main build target, and
// not when they're a dependency of another target.
// To do this, vargo runs cargo with the `--message-format=json` flag, and
// parses the output to find the artifacts as the are built, and it copies them
// to a known location (in `target-verus`), so they can be found by the build
// scripts for vstd and tests.
// Vargo always deletes the `target-verus` directory before running cargo, and
// build steps wait for their dependency to appear, to ensure they get the most
// up-to-date version of the artifact.
// Cargo will emit messages for fresh build artifacts, so we can copy them again
// to `target-verus` for each new run of vargo.

use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct CompilerMessage {
    pub rendered: String,
}

#[derive(Debug, Deserialize)]
pub struct CompilerTarget {
    pub kind: Vec<String>,
    pub name: String,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "reason")]
pub enum Message {
    #[serde(rename = "compiler-message")]
    CompilierMessage { message: CompilerMessage },
    #[serde(rename = "compiler-artifact")]
    CompilierArtifact {
        target: CompilerTarget,
        filenames: Vec<String>,
        executable: Option<String>,
    },
    #[serde(rename = "build-script-executed")]
    BuildScriptExecuted {},
    #[serde(rename = "build-finished")]
    BuildFinished {},
}

const RELEVANT_TARGET_NAMES: &[&str] = &[
    "builtin",
    "builtin_macros",
    "state_machines_macros",
    "rust_verify",
    "vstd",
    "vstd_dummy",
];

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
    eprintln!("{}", yansi::Paint::blue(format!("info: {}", msg)));
}

const SUPPORTED_COMMANDS: &[&str] = &["build", "test", "nextest", "run", "clean", "fmt", "metadata"];

fn run() -> Result<(), String> {
    let mut args = std::env::args().skip(1).collect::<Vec<_>>();
    let in_nextest = std::env::var("VARGO_IN_NEXTEST").is_ok();
    let release = args.iter().find(|x| x.as_str() == "--release").is_some();

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

    let cmd_position = args
        .iter()
        .position(|x| SUPPORTED_COMMANDS.contains(&x.as_str()))
        .ok_or(format!(
            "vargo supports the following cargo commands: {}",
            SUPPORTED_COMMANDS.join(", ")
        ))?;
    let cmd = args[cmd_position].clone();

    let package = args
        .iter()
        .position(|x| x == "--package" || x == "-p")
        .map(|pos| args[pos + 1].clone());

    if cmd == "run" {
        let release = args.iter().find(|x| x.as_str() == "--release").is_some();
        match package.as_ref().map(|x| x.as_str()) {
            Some("rust_verify") => {
                info(&format!(
                    "rebuilding first{}",
                    if release { " (release)" } else { "" }
                ));
                let current_exe =
                    std::env::current_exe().expect("no path for the current executable");
                let mut vargo = std::process::Command::new(current_exe);
                let mut vargo = vargo.arg("build");
                if release {
                    vargo = vargo.arg("--release");
                }
                vargo = vargo.arg("--all");
                vargo
                    .spawn()
                    .and_then(|mut x| x.wait())
                    .map_err(|x| format!("vargo could not execute vargo ({})", x))?;
            }
            Some("air") => (),
            _ => return Err(format!("unexpected package for `vargo run`")),
        }
    }

    let target_verus_dir = {
        let parent_dir = std::path::PathBuf::from("target-verus");
        // TODO info(&format!(
        // TODO     "creating target-verus directory at `{}`",
        // TODO     parent_dir.display()
        // TODO ));
        if !parent_dir.exists() {
            std::fs::create_dir(&parent_dir)
                .map_err(|x| format!("could not create target-verus directory ({})", x))?;
        }
        let target_verus_dir = parent_dir.join(if release { "release" } else { "debug" });
        if cmd != "run" && cmd != "nextest" && cmd != "metadata" && cmd != "fmt" && target_verus_dir.exists() {
            std::fs::remove_dir_all(&target_verus_dir)
                .map_err(|x| format!("could not remove target-verus directory ({})", x))?;
        }
        if !target_verus_dir.exists() {
            std::fs::create_dir(&target_verus_dir)
                .map_err(|x| format!("could not create target-verus directory ({})", x))?;
        }
        target_verus_dir
    };

    let target_dir =
        std::path::PathBuf::from("target").join(if release { "release" } else { "debug" });

    let target_deps_dir = target_dir.join("deps");

    let dashdash_pos = (!in_nextest && (cmd == "test" || cmd == "nextest" || cmd == "fmt")).then(|| {
        args.iter().position(|x| x == "--").unwrap_or_else(|| {
            args.push("--".to_string());
            args.len() - 1
        })
    });

    if let Some(pos) = dashdash_pos {
        args.insert(if cmd == "nextest" { pos } else { pos + 1 }, "--color=always".to_string());
    }

    if cmd == "fmt" {
        let pos = dashdash_pos.unwrap();

        args.insert(pos + 1, "--config".to_string());
        args.insert(pos + 2, "unstable_features=true,version=Two".to_string());
    }

    let target_verus_dir_absolute = std::fs::canonicalize(&target_verus_dir)
        .map_err(|x| format!("could not canonicalize target-verus directory ({})", x))?;

    // for `clean`, `fmt`, and `run`, run cargo without `--message-format=json-diagnostic-rendered-ansi`
    if cmd == "clean" || cmd == "fmt" || cmd == "run" || cmd == "metadata" {
        let status = std::process::Command::new("cargo")
            .env("RUSTC_BOOTSTRAP", "1")
            .env("VARGO_TARGET_DIR", target_verus_dir_absolute)
            .args(&args)
            .status()
            .map_err(|x| format!("could not execute cargo ({})", x))?;
        std::process::exit(status.code().unwrap_or(1));
    }

    // for `build` and `test`, run cargo with `--message-format=json-diagnostic-rendered-ansi`
    if cmd == "test" || cmd == "nextest" {
        if package.is_none() {
            return Err(format!("`vargo test` must be run with a specific package"));
        }
    }

    if cmd == "nextest" {
        args.get(cmd_position + 1).and_then(|x| (x.as_str() == "run").then(|| ())).ok_or(format!(
            "vargo only supports `vargo nextest run` for now"))?;
        let current_exe =
            std::env::current_exe().expect("no path for the current executable");
        let status = std::process::Command::new("cargo")
            .env("RUSTC_BOOTSTRAP", "1")
            .env("VARGO_IN_NEXTEST", "1")
            .env("VERUS_IN_VARGO", "1")
            .env("CARGO", current_exe)
            .args(&args)
            .status()
            .map_err(|x| format!("could not execute cargo ({})", x))?;
        std::process::exit(status.code().unwrap_or(1));
    }

    if in_nextest {
        let message_format_idx = args.iter().position(|x| x.as_str() == "--message-format")
            .ok_or(format!("could not find `--message-format` in nextest-issued command"))?;
        args.remove(message_format_idx);
        args.remove(message_format_idx);
    }

    args.insert(
        cmd_position + 1,
        "--message-format=json-diagnostic-rendered-ansi".to_string(),
    );

    let mut cargo = std::process::Command::new("cargo")
        .env("RUSTC_BOOTSTRAP", "1")
        .env("VERUS_IN_VARGO", "1")
        .args(&args)
        .stdout(std::process::Stdio::piped())
        .spawn()
        .map_err(|x| format!("could not execute cargo ({})", x))?;
    use std::io::BufRead;
    let output = std::io::BufReader::new(cargo.stdout.take().unwrap());

    #[cfg(target_os = "macos")]
    let (pre, dl) = ("lib", "dylib");

    #[cfg(target_os = "linux")]
    let (pre, dl) = ("lib", "so");

    #[cfg(target_os = "windows")]
    let (pre, dl) = ("", "dll");

    let rlib_re =
        regex::Regex::new((pre.to_string() + r"([a-zA-Z0-9_]+)(-([a-zA-Z0-9_]+))?\.rlib").as_str())
            .unwrap();

    let proc_macro_re = regex::Regex::new(
        // note: on Windows, there are .dll.exp and .dll.lib files; be sure not to match those
        (pre.to_string() + r"([a-zA-Z0-9_]+)(-([a-zA-Z0-9_]+))?\." + dl + "$").as_str(),
    )
    .unwrap();

    let bin_re = regex::Regex::new(r"([a-zA-Z0-9_]+)(-([a-zA-Z0-9_]+))?(\.[a-zA-Z]+)?").unwrap();

    let mut finished = false;

    for l in output.lines() {
        let l = l.unwrap();
        // once the build finishes, just forward the output
        if finished {
            println!("{}", l);
            continue;
        } else if in_nextest {
            println!("{}", l);
        }
        if let Some(m) = serde_json::from_str::<Message>(&l).ok() {
            match m {
                Message::CompilierMessage { message } => {
                    println!("{}", message.rendered);
                }
                Message::CompilierArtifact { ref target, .. }
                    if target.kind.len() == 1 && target.kind[0] == "test" => {}
                Message::CompilierArtifact {
                    ref target,
                    ref filenames,
                    ref executable,
                } if RELEVANT_TARGET_NAMES.contains(&target.name.as_str()) => {
                    assert_eq!(target.kind.len(), 1);
                    match target.kind[0].as_str() {
                        "lib" => {
                            if target.name == "vstd_dummy" {
                                info(&format!(
                                    "copying {} to {}",
                                    target_deps_dir.join("libvstd.rlib").display(),
                                    target_verus_dir.join("libvstd.rlib").display()
                                ));
                                std::fs::copy(
                                    &target_deps_dir.join("libvstd.rlib"),
                                    &target_verus_dir.join("libvstd.rlib"),
                                )
                                .map_err(|x| format!("could not copy file ({})", x))?;
                                info(&format!(
                                    "copying {} to {}",
                                    target_deps_dir.join("vstd.vir").display(),
                                    target_verus_dir.join("vstd.vir").display()
                                ));
                                std::fs::copy(
                                    &target_deps_dir.join("vstd.vir"),
                                    &target_verus_dir.join("vstd.vir"),
                                )
                                .map_err(|x| format!("could not copy file ({})", x))?;
                            } else if target.name == "rust_verify" {
                                // skip
                            } else {
                                for from_f in filenames {
                                    let from_f = std::path::PathBuf::from(from_f);
                                    let to_f = {
                                        let name = from_f.file_name().unwrap();
                                        let Some(matches) = rlib_re.captures(name.to_str().unwrap()) else {
                                            continue;
                                        };
                                        let name = matches.get(1).unwrap().as_str();
                                        let name = format!("{}{}.rlib", pre, name);
                                        target_verus_dir.join(name)
                                    };
                                    info(&format!(
                                        "copying {} to {}",
                                        from_f.display(),
                                        to_f.display()
                                    ));
                                    std::fs::copy(&from_f, &to_f)
                                        .map_err(|x| format!("could not copy file ({})", x))?;
                                }
                            }
                        }
                        "proc-macro" => {
                            for from_f in filenames {
                                let from_f = std::path::PathBuf::from(from_f);
                                let to_f = {
                                    let name = from_f.file_name().unwrap();
                                    let Some(matches) = proc_macro_re.captures(name.to_str().unwrap()) else {
                                        continue;
                                    };
                                    let name = matches.get(1).unwrap().as_str();
                                    let name = format!("{}{}.{}", pre, name, dl);
                                    target_verus_dir.join(name)
                                };
                                info(&format!(
                                    "copying {} to {}",
                                    from_f.display(),
                                    to_f.display()
                                ));
                                std::fs::copy(&from_f, &to_f)
                                    .map_err(|x| format!("could not copy file ({})", x))?;
                            }
                        }
                        "bin" => {
                            let from_f = std::path::PathBuf::from(executable.as_ref().unwrap());
                            let to_f = {
                                let name = from_f.file_name().unwrap();
                                let Some(matches) = bin_re.captures(name.to_str().unwrap()) else {
                                    continue;
                                };
                                let name = matches.get(1).unwrap().as_str();
                                let ext = matches.get(4).map(|x| x.as_str()).unwrap_or("");
                                let name = format!("{}{}", name, ext);
                                target_verus_dir.join(name)
                            };
                            info(&format!(
                                "copying {} to {}",
                                from_f.display(),
                                to_f.display()
                            ));
                            std::fs::copy(&from_f, &to_f)
                                .map_err(|x| format!("could not copy file ({})", x))?;
                        }
                        _ => panic!("unexpected target kind: {:?}", target.kind),
                    }
                }
                Message::BuildFinished { .. } => {
                    finished = true;
                }
                _ => {}
            }
        } else {
            eprintln!("stderr: {}", yansi::Paint::white(l).dimmed());
        }
    }

    std::process::exit(cargo.wait().unwrap().code().unwrap_or(1));
}
