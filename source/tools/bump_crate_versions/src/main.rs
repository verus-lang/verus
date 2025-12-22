use clap::Parser as ClapParser;
use crates_io_api::SyncClient;
use petgraph::algo::toposort;
use petgraph::graph::DiGraph;
use regex::Regex;
use std::{
    collections::{HashMap, HashSet},
    fs,
    path::Path,
    process::Stdio,
    sync::LazyLock,
};
use toml_edit::DocumentMut;
//use petgraph::dot::{Dot, Config}; // Used for debugging graphs

const LINE_COUNT_DIR: &str = "source/tools/line_count";

/// This tool scans for modified crates in the Verus repository and updates the version numbers
/// in their respective Cargo.toml files. In cases where one crate depends on another, we also
/// update the version of the dependency in the dependent crate's Cargo.toml.  Finally, when vstd
/// is modified, we also update the version in the cargo-verus template.  The code is optimized
/// for readability and maintainability, rather than performance.
///
/// Usage: Run this tool from the root of the Verus repository.

#[derive(clap::Subcommand)]
enum Command {
    /// Update version numbers
    Update,
    /// Publish any updated crates to crates.io
    Publish {
        /// Operate in dry-run mode, instead of actually publishing
        #[arg(long = "dry-run")]
        dry_run: bool,
    },
}

#[derive(ClapParser)]
#[command(version, about)]
struct Args {
    #[command(subcommand)]
    command: Command,
}

// Path to cargo-verus's main file, where we have a static string
// indicating which version of vstd to use
const CARGO_VERUS_TEMPLATE_FILE: &str = "source/cargo-verus/src/subcommands.rs";

// Generates a fresh version string of the form "0.0.0-year-month-day-time",
// which we'll assign to any updated crate.  Using a const + LazyLock ensures
// we only compute this once and then use it consistently throughout.
static NEW_VERSION: LazyLock<String> = LazyLock::new(|| {
    use chrono::{Datelike, Timelike, Utc};

    let now = Utc::now();
    format!(
        "0.0.0-{}-{:02}-{:02}-{:04}",
        now.year(),
        now.month(),
        now.day(),
        now.hour() * 100 + now.minute()
    )
});

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
        let content = fs::read_to_string(&cargo_toml_path)
            .expect(format!("Failed to read {}", cargo_toml_path.display()).as_str());
        let doc = content.parse::<DocumentMut>().expect("Failed to parse Cargo.toml");

        for maybe_dep in crates {
            if doc.contains_key("dependencies")
                && doc["dependencies"].get(&maybe_dep.name).is_some()
            {
                // krate depends on maybe_dep, so add an edge: maybe_dep -> krate,
                // so if maybe_dep is updated, we know that krate needs to be updated too
                dep_map
                    .entry(maybe_dep.clone())
                    .and_modify(|v: &mut Vec<Crate>| v.push(krate.clone()))
                    .or_insert(vec![krate.clone()]);
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

fn dep_map_to_graph(dep_map: &HashMap<Crate, Vec<Crate>>) -> DiGraph<Crate, ()> {
    let mut graph = DiGraph::<Crate, ()>::new();
    let mut node_indices: HashMap<Crate, petgraph::prelude::NodeIndex> = HashMap::new();

    // Add nodes
    for krate in dep_map.keys() {
        let index = graph.add_node(krate.clone());
        node_indices.insert(krate.clone(), index);
    }
    for dependents in dep_map.values() {
        for krate in dependents {
            if !node_indices.contains_key(krate) {
                let index = graph.add_node(krate.clone());
                node_indices.insert(krate.clone(), index);
            }
        }
    }

    // Add edges
    for (krate, dependents) in dep_map {
        let from_index = node_indices.get(krate).unwrap();
        for dependent in dependents {
            let to_index = node_indices.get(dependent).unwrap();
            graph.add_edge(*from_index, *to_index, ());
        }
    }

    graph
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

    !status.success() // A successful exit code of 0 means no changes
}

fn read_toml_version(dir: &Path) -> String {
    let cargo_toml_path = dir.join("Cargo.toml");

    // Read the Cargo.toml file
    let content = fs::read_to_string(&cargo_toml_path)
        .expect(format!("Failed to read {}", cargo_toml_path.display()).as_str());
    let doc = content.parse::<DocumentMut>().expect("Failed to parse Cargo.toml");

    doc["package"]["version"].as_str().expect("Version must be a string").to_string()
}

fn update_toml_version(dir: &Path) {
    let cargo_toml_path = dir.join("Cargo.toml");

    // Read the Cargo.toml file
    let content = fs::read_to_string(&cargo_toml_path)
        .expect(format!("Failed to read {}", cargo_toml_path.display()).as_str());
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
    let content = fs::read_to_string(&cargo_toml_path)
        .expect(format!("Failed to read {}", cargo_toml_path.display()).as_str());
    let mut doc = content.parse::<DocumentMut>().expect("Failed to parse Cargo.toml");

    // Update dependencies with the new version
    for krate in dependencies {
        if doc.contains_key("dependencies") && doc["dependencies"].get(&krate.name).is_some() {
            doc["dependencies"][&krate.name]["version"] =
                toml_edit::value(format!("={}", *NEW_VERSION));
        }
        if doc.contains_key("dev-dependencies")
            && doc["dev-dependencies"].get(&krate.name).is_some()
        {
            doc["dev-dependencies"][&krate.name]["version"] =
                toml_edit::value(format!("={}", *NEW_VERSION));
        }
    }

    // Write the updated content back to Cargo.toml
    let content = doc.to_string();
    fs::write(&cargo_toml_path, content).expect("Failed to write Cargo.toml");
}

fn publish(dir: &Path, dry_run: bool) {
    use std::process::Command;

    let mut cmd = Command::new("cargo");
    cmd.arg("publish");
    if dry_run {
        cmd.arg("--dry-run");
    }
    let status = cmd.current_dir(dir).status().expect("Failed to execute cargo publish");

    if !status.success() {
        panic!(
            "cargo publish{} failed for {}",
            if dry_run { " --dry-run" } else { "" },
            dir.display()
        );
    }
}

fn update_cargo_verus_template() {
    let main = Path::new(CARGO_VERUS_TEMPLATE_FILE);
    let content = fs::read_to_string(main).expect("Failed to read cargo-verus main.rs");

    // Replace the version in the template
    let re = Regex::new("(?m)^vstd =.*$").expect("Failed to create regex");
    let count = re.find_iter(&content).count();
    if count != 1 {
        panic!(
            "Expected to find exactly one occurence of 'vstd = ' in {}.  Found {}.",
            CARGO_VERUS_TEMPLATE_FILE, count
        );
    }
    let updated_content = re.replace(&content, format!("vstd = \"={}\"", *NEW_VERSION).as_str());
    //println!("Updated cargo-verus main.rs:\n{}", updated_content);
    println!("Updated cargo-verus main.rs\n");

    // Write the updated content back to the file
    fs::write(main, updated_content.to_string()).expect("Failed to write cargo-verus main.rs");
}

fn update_crates(crates: Vec<Crate>) {
    // Compute directly modified crates
    println!("\nScanning for crates with modified source code...");
    let mut modified_crates: HashSet<&Crate> = HashSet::new();
    for krate in &crates {
        if let Some(commit) = last_commit(&Path::new(&krate.path)) {
            if src_modified(&Path::new(&krate.path), &commit) {
                println!("\t{}:\n\t\tHAS been modified since commit {}.\n", krate.name, commit);
                modified_crates.insert(&krate);
            } else {
                println!(
                    "\t{}:\n\t\t has NOT been modified since commit {}.\n",
                    krate.name, commit
                );
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
                        println!(
                            "\t\t{}: depends on modified crate {}",
                            dependent.name, krate.name
                        );
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
        println!(
            "\nModifying each of the following crates to version {} and updating their dependencies ...",
            *NEW_VERSION
        );
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

        // Finally, update the line count tool's dependencies if needed
        update_toml_dependencies(Path::new(LINE_COUNT_DIR), &modified_crates);
    }
}

fn publish_crates(
    crate_graph: DiGraph<Crate, ()>,
    dry_run: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    let crates_io_client =
        SyncClient::new("verus-version-bumper", std::time::Duration::from_secs(1))?;
    let sorted_nodes = toposort(&crate_graph, None).expect("Dependency graph has cycles");
    //println!("{:?}", Dot::with_config(&crate_graph, &[Config::EdgeNoLabel]));
    for node_index in sorted_nodes {
        let krate = &crate_graph[node_index];
        // Before publishing, check if this version already exists on crates.io
        let crate_version = read_toml_version(&Path::new(&krate.path));
        let metadata = crates_io_client.get_crate(&krate.name)?;
        let version_exists = metadata.versions.iter().any(|v| v.num == crate_version && !v.yanked);
        if version_exists {
            println!(
                "Crate {} version {} already exists on crates.io, skipping publish.",
                krate.name, crate_version
            );
            continue;
        }

        if dry_run {
            println!("Performing a dry-run publish of crate {}", krate.name);
        } else {
            println!("Publishing crate {}", krate.name);
        }
        publish(&Path::new(&krate.path), dry_run);
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let crates = vec![
        Crate { name: "vstd".to_string(), path: "source/vstd".to_string() },
        Crate { name: "verus_builtin".to_string(), path: "source/builtin".to_string() },
        Crate {
            name: "verus_builtin_macros".to_string(),
            path: "source/builtin_macros".to_string(),
        },
        Crate {
            name: "verus_state_machines_macros".to_string(),
            path: "source/state_machines_macros".to_string(),
        },
        Crate {
            name: "verus_prettyplease".to_string(),
            path: "dependencies/prettyplease".to_string(),
        },
        Crate { name: "verus_syn".to_string(), path: "dependencies/syn".to_string() },
    ];

    let test_path = Path::new(&crates[0].path);
    if !Path::exists(test_path) {
        return Err(format!("Failed to find path: {}.  Hint: This tool expects to run in the root of the Verus repo", test_path.display()).into());
    }

    match &args.command {
        Command::Update => update_crates(crates),
        Command::Publish { dry_run } => {
            let dep_map = compute_immediate_deps(&crates);
            let graph = dep_map_to_graph(&dep_map);
            display_dep_map(&dep_map, 2);
            publish_crates(graph, *dry_run)?
        }
    }

    Ok(())
}
