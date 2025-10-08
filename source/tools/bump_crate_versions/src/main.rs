use std::{fs, path::Path, process::Stdio, sync::LazyLock};
use toml_edit::DocumentMut;
use regex::Regex;
use clap::Parser as ClapParser;


/// This tool scans for modified crates in the Verus repository and updates the version numbers
/// in their respective Cargo.toml files. In cases where one crate depends on another, we also
/// update the version of the dependency in the dependent crate's Cargo.toml.  Finally, when vstd
/// is modified, we also update the version in the cargo-verus template.  The code is optimized
/// for readability and maintainability, rather than performance.
///
/// Usage: Run this tool from the root of the Verus repository.

#[derive(ClapParser)]
#[command(version, about)]
struct Args {
    /// If set, publishes the updated crates to crates.io.  Otherwise runs the publish step in dry-run mode
    #[arg(long = "publish")]
    publish: bool,
}

// Path to cargo-verus's main file, where we have a static string
// indicating which version of vstd to use
const CARGO_VERUS_MAIN: &str = "source/cargo-verus/src/main.rs";

// Generates a fresh version string of the form "0.0.0-year-month-day-time",
// which we'll assign to any updated crate.  Using a const + LazyLock ensures
// we only compute this once and then use it consistently throughout.
static NEW_VERSION: LazyLock<String> = LazyLock::new(|| {
    use chrono::{Datelike,Timelike,Utc};

    let now = Utc::now();
    format!(
        "0.0.0-{}-{:02}-{:02}-{:04}",
        now.year(),
        now.month(),
        now.day(),
        now.hour() * 100 + now.minute()
    )
});


#[derive(Clone)]
struct Crate {
    // Crate's official name
    name: String,
    // Path to the crate's directory, relative to the repository root
    path: String,
}

// Given a path to a directory, run git to check for the most recent change to the Cargo.toml file
fn last_commit(dir: &Path) -> Option<String> {
    use std::process::Command;

    let output = Command::new("git")
        .arg("-C")
        .arg(dir)
        .arg("log")
        .arg("-1")
        .arg("--pretty=format:%H")
        .arg("--")
        .arg("Cargo.toml")
        .output()
        .expect("Failed to execute git command");
    if output.status.success() {
        Some(String::from_utf8_lossy(&output.stdout).trim().to_string())
    } else {
        None
    }
}

// Given the most recent commit hash, run git to check if the src directory has been modified
fn src_modified(dir: &Path, commit: &str) -> bool {
    use std::process::Command;

    let status = Command::new("git")
        .arg("-C")
        .arg(dir)
        .arg("diff")
        .arg("--exit-code")
        .arg(format!("{}..HEAD", commit))
        .arg("--")
        .arg("src")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .expect("Failed to execute git command");

    !status.success()   // A successful exit code of 0 means no changes
}

fn update_toml_version(dir: &Path) {
    let cargo_toml_path = dir.join("Cargo.toml");

    // Read the Cargo.toml file
    let content = fs::read_to_string(&cargo_toml_path).expect(format!("Failed to read {}", cargo_toml_path.display()).as_str());
    let mut doc = content.parse::<DocumentMut>().expect("Failed to parse Cargo.toml");

    // Replace the version line
    doc["package"]["version"] = (*NEW_VERSION).clone().into();

    // Write the updated content back to Cargo.toml
    let content = doc.to_string();
    fs::write(&cargo_toml_path, content).expect("Failed to write Cargo.toml");
}

fn update_toml_dependencies(dir: &Path, dependencies: &Vec<Crate>) {
    let cargo_toml_path = dir.join("Cargo.toml");

    // Read the Cargo.toml file
    let content = fs::read_to_string(&cargo_toml_path).expect(format!("Failed to read {}", cargo_toml_path.display()).as_str());
    let mut doc = content.parse::<DocumentMut>().expect("Failed to parse Cargo.toml");

    // Update dependencies with the new version
    for krate in dependencies {
        if doc.contains_key("dependencies") && doc["dependencies"].get(&krate.name).is_some() {
            doc["dependencies"][&krate.name]["version"] = toml_edit::value(format!("={}", *NEW_VERSION));
        }
    }

    // Write the updated content back to Cargo.toml
    let content = doc.to_string();
    fs::write(&cargo_toml_path, content).expect("Failed to write Cargo.toml");
}

fn publish(dir: &Path, publish: bool) {
    use std::process::Command;

    let mut cmd = Command::new("cargo");
    cmd.arg("publish");
    if !publish {
        cmd.arg("--dry-run");
    }
    let status = cmd
        .current_dir(dir)
        .status()
        .expect("Failed to execute cargo publish");

    if !status.success() {
        panic!("cargo publish{} failed for {}", 
            if publish { " --dry-run" } else { "" },
            dir.display()
        );
    }
}

fn update_cargo_verus_template() {
    let main = Path::new(CARGO_VERUS_MAIN);
    let content = fs::read_to_string(main).expect("Failed to read cargo-verus main.rs");

    // Replace the version in the template
    let re = Regex::new("(?m)^vstd =.*$").expect("Failed to create regex");
    let count = re.find_iter(&content).count();
    if count != 1 {
        panic!("Expected to find exactly one occurence of 'vstd = ' in {}.  Found {}.", CARGO_VERUS_MAIN, count);
    }
    let updated_content = re.replace(&content, format!("vstd = \"={}\"", *NEW_VERSION).as_str());
    println!("Updated cargo-verus main.rs:\n{}", updated_content);

    // Write the updated content back to the file
    fs::write(main, updated_content.to_string()).expect("Failed to write cargo-verus main.rs");
}

fn main() {
    let  args = Args::parse();

    println!("Scanning for modified crates...");
    let crates = vec![
        Crate {
            name: "vstd".to_string(),
            path: "source/vstd".to_string(),
        },
        Crate {
            name: "verus_builtin".to_string(),
            path: "source/builtin".to_string(),
        },
        Crate {
            name: "verus_builtin_macros".to_string(),
            path: "source/builtin_macros".to_string(),
        },
        Crate {
            name: "verus_state_machine_macros".to_string(),
            path: "source/state_machines_macros".to_string(),
        },
        Crate {
            name: "verus_prettyplease".to_string(),
            path: "dependencies/prettyplease".to_string(),
        },
        Crate {
            name: "verus_syn".to_string(),
            path: "dependencies/syn".to_string(),
        },
    ];

    let mut modified_crates = Vec::new();
    for krate in &crates {
        if let Some(commit) = last_commit(&Path::new(&krate.path)) {
            if src_modified(&Path::new(&krate.path), &commit) {
                println!("\t{}:\n\t\thas been modified since commit {}.\n\t\tUpdating version to {}", krate.name, commit, *NEW_VERSION);
                update_toml_version(&Path::new(&krate.path));
                modified_crates.push(krate.clone());
                if krate.name == "vstd" {
                    update_cargo_verus_template();
                }
            } else {
                println!("\t{}:\n\t\t has not been modified since commit {}", krate.name, commit);
            }
        } else {
            println!("{}: Could not find last commit for {}", krate.name, krate.path);
        }
    }

    if !modified_crates.is_empty() {
        for krate in &crates{
            println!("Updating dependencies for {}", krate.name);
            update_toml_dependencies(&Path::new(&krate.path), &modified_crates);
        }
    }

    for krate in modified_crates {
        println!("Publishing modified crate {}", krate.name);
        publish(&Path::new(&krate.path), args.publish);
    }
}
