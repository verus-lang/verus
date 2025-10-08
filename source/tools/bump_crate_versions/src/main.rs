use std::{collections::{HashMap, HashSet}, fs, path::Path, process::Stdio, sync::LazyLock};
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


#[derive(Clone,Debug,PartialEq,Eq,Hash,PartialOrd,Ord)]
struct Crate {
    // Crate's official name
    name: String,
    // Path to the crate's directory, relative to the repository root
    path: String,
}

// For each crate, identify the other crates (in `crates`) that depend on it
fn compute_immediate_deps(crates: &Vec<Crate>) -> HashMap<Crate, Vec<Crate>> {
    let mut dep_map: HashMap<Crate, Vec<Crate>> = HashMap::new();
    for krate in crates {
        let cargo_toml_path = Path::new(&krate.path).join("Cargo.toml");

        // Read the Cargo.toml file
        let content = fs::read_to_string(&cargo_toml_path).expect(format!("Failed to read {}", cargo_toml_path.display()).as_str());
        let doc = content.parse::<DocumentMut>().expect("Failed to parse Cargo.toml");

        for maybe_dep in crates {
            if doc.contains_key("dependencies") && doc["dependencies"].get(&maybe_dep.name).is_some() {
                // krate depends on maybe_dep, so add an edge: maybe_dep -> krate,
                // so if maybe_dep is updated, we know that krate needs to be updated too
                dep_map.entry(maybe_dep.clone()).and_modify(|v: &mut Vec<Crate>| v.push(krate.clone())).or_insert(vec![krate.clone()]);
            }
        }
    }
    dep_map
}

fn display_dep_map(dep_map: &HashMap<Crate, Vec<Crate>>, tab_depth: usize) {
    for (krate, dependents) in dep_map {
        print!("{}{}: ", "\t".repeat(tab_depth), krate.name);
        let names = dependents.iter().map(|c| c.name.clone()).collect::<Vec<String>>();
        println!("{}", names.join(", "));
    }
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

fn update_toml_dependencies(dir: &Path, dependencies: &Vec<&Crate>) {
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
    //println!("Updated cargo-verus main.rs:\n{}", updated_content);
    println!("Updated cargo-verus main.rs\n");

    // Write the updated content back to the file
    fs::write(main, updated_content.to_string()).expect("Failed to write cargo-verus main.rs");
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
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

    let test_path = Path::new(&crates[0].path);
    if !Path::exists(test_path) {
        return Err(format!("Failed to find path: {}.  Hint: This tool expects to run in the root of the Verus repo", test_path.display()).into());
    }

    // Compute directly modified crates
    println!("\nScanning for crates with modified source code...");
    let mut modified_crates: HashSet<&Crate> = HashSet::new();
    for krate in &crates {
        if let Some(commit) = last_commit(&Path::new(&krate.path)) {
            if src_modified(&Path::new(&krate.path), &commit) {
                println!("\t{}:\n\t\tHAS been modified since commit {}.\n", krate.name, commit);
                modified_crates.insert(&krate);
            } else {
                println!("\t{}:\n\t\t has NOT been modified since commit {}.\n", krate.name, commit);
            }
        } else {
            println!("{}: Could not find last commit for {}", krate.name, krate.path);
        }
    }

    // Compute crates that (transitively) depend on modified crates, and hence themselves need a version update
    println!("\nScanning for crates that depend on modified crates...");
    let dep_map = compute_immediate_deps(&crates);
    println!("\tworking from the following map A: [B1, ..., BN], where each Bi depends on A");
    display_dep_map(&dep_map, 2);
    println!("\tidentifying transitively affected crates...");
    loop {
        let mut new_modifications = HashSet::new();
        for krate in &modified_crates {
            if dep_map.contains_key(krate) {
                for dependent in &dep_map[krate] {
                    // For each dependent that relies on a modified krate,
                    // if it hasn't already been marked for modification, mark it now.
                    if !modified_crates.contains(&dependent) {
                        new_modifications.insert(dependent);
                        println!("\t\t{}: depends on modified crate {}", dependent.name, krate.name);
                    }
                }
            }
        }

        if new_modifications.len() == 0 {
            break;
        } else {
            modified_crates.extend(new_modifications.iter());
        }
    }

    // Do the modifications
    if modified_crates.len() > 0 {
        println!("\nModifying each of the following crates to version {} and updating their dependencies ...", *NEW_VERSION);
        let mut modified_crates: Vec<&Crate> = modified_crates.into_iter().collect();
        modified_crates.sort();
        for krate in &modified_crates {
            println!("\t{}", krate.name);
            update_toml_version(&Path::new(&krate.path));
            update_toml_dependencies(&Path::new(&krate.path), &modified_crates);

            if krate.name == "vstd" {
                update_cargo_verus_template();
            }
        }

        for krate in modified_crates {
            if args.publish {
                println!("Publishing modified crate {}", krate.name);
            } else {
                println!("Performing a dry-run publish of modified crate {}", krate.name);
            }
            publish(&Path::new(&krate.path), args.publish);
        }
    }

    Ok(())
}
