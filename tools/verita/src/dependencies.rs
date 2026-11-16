use anyhow::anyhow;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};
use tracing::{debug, warn};

/// Scan `{verus_repo}/source/` and return a map from package name to its directory path.
fn build_verus_crate_map(verus_repo: &Path) -> HashMap<String, PathBuf> {
    let mut map = HashMap::new();
    let source_dir = verus_repo.join("source");
    let entries = match std::fs::read_dir(&source_dir) {
        Ok(e) => e,
        Err(_) => return map,
    };
    for entry in entries.flatten() {
        let cargo_toml_path = entry.path().join("Cargo.toml");
        let content = match std::fs::read_to_string(&cargo_toml_path) {
            Ok(c) => c,
            Err(_) => continue,
        };
        let manifest: toml::Value = match toml::from_str(&content) {
            Ok(v) => v,
            Err(_) => continue,
        };
        if let Some(name) = manifest
            .get("package")
            .and_then(|p| p.get("name"))
            .and_then(|n| n.as_str())
        {
            map.insert(name.to_string(), entry.path());
        }
    }
    map
}

/// Walk up from `target_dir` to `repo_root`, returning the highest ancestor that
/// has a `[workspace]` section in its `Cargo.toml`. Falls back to `target_dir`.
fn find_workspace_root(target_dir: &Path, repo_root: &Path) -> PathBuf {
    let mut ancestors: Vec<PathBuf> = Vec::new();
    let mut current = target_dir.to_path_buf();
    loop {
        ancestors.push(current.clone());
        if current == repo_root {
            break;
        }
        match current.parent() {
            Some(parent) if parent != current => current = parent.to_path_buf(),
            _ => break,
        }
    }
    // Search from repo_root toward target_dir; return first one with [workspace]
    for dir in ancestors.iter().rev() {
        if let Ok(content) = std::fs::read_to_string(dir.join("Cargo.toml")) {
            if let Ok(value) = toml::from_str::<toml::Value>(&content) {
                if value.get("workspace").is_some() {
                    return dir.clone();
                }
            }
        }
    }
    target_dir.to_path_buf()
}

fn visit_dependency_sections(
    table: &mut dyn toml_edit::TableLike,
    visit: &mut impl FnMut(&str, &mut toml_edit::Item),
) {
    for section in &["dependencies", "dev-dependencies", "build-dependencies"] {
        if let Some(deps) = table.get_mut(section).and_then(|d| d.as_table_like_mut()) {
            for (name, dep) in deps.iter_mut() {
                visit(name.get(), dep);
            }
        }
    }
    if let Some(targets) = table.get_mut("target").and_then(|t| t.as_table_like_mut()) {
        for (_, target) in targets.iter_mut() {
            if let Some(target) = target.as_table_like_mut() {
                visit_dependency_sections(target, visit);
            }
        }
    }
}

fn visit_dependencies(
    table: &mut dyn toml_edit::TableLike,
    visit: &mut impl FnMut(&str, &mut toml_edit::Item),
) {
    visit_dependency_sections(table, visit);
    if let Some(workspace) = table
        .get_mut("workspace")
        .and_then(|w| w.as_table_like_mut())
    {
        visit_dependency_sections(workspace, visit);
    }
}

fn collect_dep_names(manifest: &mut toml_edit::DocumentMut) -> HashSet<String> {
    let mut names = HashSet::new();
    visit_dependencies(manifest.as_table_mut(), &mut |name, _| {
        names.insert(name.to_string());
    });
    names
}

fn expand_workspace_paths(
    workspace_root: &Path,
    patterns: Option<&toml_edit::Item>,
) -> anyhow::Result<Vec<PathBuf>> {
    let mut paths = Vec::new();
    if let Some(patterns) = patterns.and_then(|p| p.as_array()) {
        let root = glob::Pattern::escape(&workspace_root.to_string_lossy().replace('\\', "/"));
        for pattern in patterns.iter().filter_map(|p| p.as_str()) {
            for path in glob::glob(&format!("{root}/{}", pattern.replace('\\', "/")))? {
                let path = path?;
                if path.is_dir() {
                    paths.push(dunce::canonicalize(path)?);
                }
            }
        }
    }
    Ok(paths)
}

/// Discover members without Cargo metadata, which cannot load broken path dependencies.
fn collect_workspace_manifests(
    workspace_root: &Path,
    target_dir: &Path,
    verus_crate_map: &HashMap<String, PathBuf>,
) -> anyhow::Result<Vec<PathBuf>> {
    let workspace_root = dunce::canonicalize(workspace_root)?;
    let root_manifest = std::fs::read_to_string(workspace_root.join("Cargo.toml"))?
        .parse::<toml_edit::DocumentMut>()?;
    let workspace = root_manifest.get("workspace");
    let excluded: HashSet<PathBuf> =
        expand_workspace_paths(&workspace_root, workspace.and_then(|w| w.get("exclude")))?
            .into_iter()
            .collect();
    let mut pending = vec![
        workspace_root.join("Cargo.toml"),
        target_dir.join("Cargo.toml"),
    ];
    pending.extend(
        expand_workspace_paths(&workspace_root, workspace.and_then(|w| w.get("members")))?
            .into_iter()
            .map(|path| path.join("Cargo.toml")),
    );
    let mut manifests = BTreeSet::new();
    while let Some(path) = pending.pop() {
        let path = match dunce::canonicalize(path) {
            Ok(path) => path,
            Err(_) => continue,
        };
        let dir = path.parent().expect("manifest must have a parent");
        if excluded.contains(dir) || !manifests.insert(path.clone()) {
            continue;
        }
        let content = std::fs::read_to_string(&path)?;
        let mut manifest = content.parse::<toml_edit::DocumentMut>()?;
        visit_dependency_sections(manifest.as_table_mut(), &mut |name, dep| {
            // These paths will be redirected, so the old Verus checkout is not a member.
            if verus_crate_map.contains_key(name) {
                return;
            }
            let (dep, base) = if dep.get("workspace").and_then(|w| w.as_bool()) == Some(true) {
                match workspace
                    .and_then(|w| w.get("dependencies"))
                    .and_then(|d| d.get(name))
                {
                    Some(dep) => (dep, workspace_root.as_path()),
                    None => return,
                }
            } else {
                (&*dep, dir)
            };
            if let Some(path) = dep.get("path").and_then(|p| p.as_str()) {
                if let Ok(path) = dunce::canonicalize(base.join(path)) {
                    // Cargo implicitly includes path dependencies inside the workspace.
                    if path.starts_with(&workspace_root) {
                        pending.push(path.join("Cargo.toml"));
                    }
                }
            }
        });
    }
    Ok(manifests.into_iter().collect())
}

/// Read `package.version` from a local crate's `Cargo.toml`.
fn get_local_version(crate_path: &Path) -> Option<String> {
    let content = std::fs::read_to_string(crate_path.join("Cargo.toml")).ok()?;
    let manifest: toml::Value = toml::from_str(&content).ok()?;
    manifest
        .get("package")
        .and_then(|p| p.get("version"))
        .and_then(|v| v.as_str())
        .map(|s| s.to_string())
}

/// Update a single dependency item in place if it carries an exact version pin
/// (`=X.Y.Z`) that doesn't match `local_ver`. Returns `true` if modified.
///
/// Handles both the plain-string form (`vstd = "=0.0.0-old"`) and the
/// inline/regular-table form (`vstd = { version = "=0.0.0-old", ... }`).
fn relax_dep_item(dep: &mut toml_edit::Item, local_ver: &str) -> bool {
    // ── String form ──────────────────────────────────────────────────────────
    // Bind to an owned String first so the &str borrow on `dep` is fully
    // released before we potentially write `*dep = ...`.
    let cur_str: Option<String> = dep.as_str().map(str::to_owned);
    if let Some(s) = cur_str {
        if s.starts_with('=') && s.trim_start_matches('=') != local_ver {
            debug!("  relaxing exact version pin {} -> ={}", s, local_ver);
            *dep = toml_edit::value(format!("={}", local_ver));
            return true;
        }
        return false; // it's a string but already correct (or not an exact pin)
    }

    // ── Table form ───────────────────────────────────────────────────────────
    if let Some(tbl) = dep.as_table_like_mut() {
        if let Some(v_item) = tbl.get_mut("version") {
            let cur_str: Option<String> = v_item.as_str().map(str::to_owned);
            if let Some(s) = cur_str {
                if s.starts_with('=') && s.trim_start_matches('=') != local_ver {
                    debug!("  relaxing exact version pin {} -> ={}", s, local_ver);
                    *v_item = toml_edit::value(format!("={}", local_ver));
                    return true;
                }
            }
        }
    }
    false
}

fn update_string_value(value: &mut toml_edit::Value, new_value: &str) -> bool {
    if value.as_str() == Some(new_value) {
        return false;
    }
    let decor = value.decor().clone();
    *value = toml_edit::Value::from(new_value);
    *value.decor_mut() = decor;
    true
}

fn update_dep_item(dep: &mut toml_edit::Item, crate_path: &Path, local_ver: Option<&str>) -> bool {
    let mut changed = false;
    let mut path_dependency = false;
    if let Some(table) = dep.as_table_like_mut() {
        if let Some(path) = table.get_mut("path").and_then(|p| p.as_value_mut()) {
            path_dependency = true;
            let path_str = crate_path.to_string_lossy().replace('\\', "/");
            changed |= update_string_value(path, &path_str);
        }
        if path_dependency {
            if let Some(local_ver) = local_ver {
                if let Some(version) = table.get_mut("version").and_then(|v| v.as_value_mut()) {
                    changed |= update_string_value(version, &format!("={local_ver}"));
                }
            }
        }
    }
    if !path_dependency {
        if let Some(local_ver) = local_ver {
            changed |= relax_dep_item(dep, local_ver);
        }
    }
    changed
}

/// Redirect Verus path dependencies and their version requirements to the local
/// checkout. For registry/git dependencies, update only mismatched exact pins.
///
/// Uses `toml_edit` so that the rest of the file is left byte-for-byte
/// identical (key order, comments, blank lines, etc.).
fn update_verus_dependencies(
    path: &Path,
    patches: &[(String, PathBuf)],
    local_versions: &HashMap<String, String>,
) -> anyhow::Result<()> {
    let content = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(_) => return Ok(()),
    };
    let mut doc = match content.parse::<toml_edit::DocumentMut>() {
        Ok(d) => d,
        Err(_) => return Ok(()),
    };
    let mut changed = false;

    visit_dependencies(doc.as_table_mut(), &mut |name, dep| {
        for (crate_name, crate_path) in patches {
            if name == crate_name {
                changed |= update_dep_item(
                    dep,
                    crate_path,
                    local_versions.get(crate_name).map(String::as_str),
                );
            }
        }
    });

    if changed {
        debug!(
            "Updated Verus dependency paths and version pins in {}",
            path.display()
        );
        std::fs::write(path, doc.to_string())
            .map_err(|e| anyhow!("cannot write {}: {}", path.display(), e))?;
    }
    Ok(())
}

/// If the project's workspace references any Verus crates, add `[patch]` entries
/// to the workspace root `Cargo.toml` so those crates resolve to the local Verus
/// repo rather than whatever version/source the project specified.
///
/// Two patch sources are written – `crates-io` and the Verus git URL – and
/// existing path dependencies are redirected to the local Verus repo.
///
/// Uses `toml_edit` so that the rest of the file is left byte-for-byte
/// identical (key order, comments, blank lines, etc.).
pub fn inject_verus_patches(
    target_dir: &Path,
    repo_root: &Path,
    verus_repo: &Path,
    verus_git_url: &str,
) -> anyhow::Result<()> {
    let verus_crate_map = build_verus_crate_map(verus_repo);
    if verus_crate_map.is_empty() {
        return Ok(());
    }

    let workspace_root = find_workspace_root(target_dir, repo_root);
    let workspace_cargo_toml = workspace_root.join("Cargo.toml");
    let manifests = collect_workspace_manifests(&workspace_root, target_dir, &verus_crate_map)?;

    let mut all_dep_names: HashSet<String> = HashSet::new();
    for path in &manifests {
        if let Ok(content) = std::fs::read_to_string(path) {
            if let Ok(mut manifest) = content.parse::<toml_edit::DocumentMut>() {
                all_dep_names.extend(collect_dep_names(&mut manifest));
            }
        }
    }

    // Filter to only Verus crates that the project actually references
    let patches: Vec<(String, PathBuf)> = verus_crate_map
        .into_iter()
        .filter(|(name, _)| all_dep_names.contains(name))
        .collect();

    if patches.is_empty() {
        return Ok(());
    }

    debug!(
        "Injecting path patches for {} Verus crate(s) into {}",
        patches.len(),
        workspace_cargo_toml.display()
    );

    let content = std::fs::read_to_string(&workspace_cargo_toml)
        .map_err(|e| anyhow!("cannot read {}: {}", workspace_cargo_toml.display(), e))?;
    let mut doc = content
        .parse::<toml_edit::DocumentMut>()
        .map_err(|e| anyhow!("cannot parse {}: {}", workspace_cargo_toml.display(), e))?;

    // Ensure [patch] table exists
    if doc.get("patch").is_none() {
        doc["patch"] = toml_edit::table();
    }
    let patch_section = doc["patch"]
        .as_table_mut()
        .ok_or_else(|| anyhow!("[patch] is not a table"))?;

    for source in &["crates-io", verus_git_url] {
        if !patch_section.contains_key(source) {
            patch_section[*source] = toml_edit::table();
        }
        let source_section = patch_section[*source]
            .as_table_mut()
            .ok_or_else(|| anyhow!("[patch.{}] is not a table", source))?;

        for (crate_name, crate_path) in &patches {
            let path_str = crate_path.to_string_lossy().replace('\\', "/");
            let mut entry = toml_edit::InlineTable::new();
            entry.insert("path", toml_edit::Value::from(path_str.as_str()));
            source_section.insert(
                crate_name.as_str(),
                toml_edit::Item::Value(toml_edit::Value::InlineTable(entry)),
            );
            debug!("  {} -> {}", crate_name, crate_path.display());
        }
    }

    std::fs::write(&workspace_cargo_toml, doc.to_string())
        .map_err(|e| anyhow!("cannot write {}: {}", workspace_cargo_toml.display(), e))?;

    // Path dependencies need direct updates: registry/git patches do not
    // replace their source, and Cargo still tries to load the original path.
    let local_versions: HashMap<String, String> = patches
        .iter()
        .filter_map(|(name, path)| get_local_version(path).map(|v| (name.clone(), v)))
        .collect();

    for path in &manifests {
        if let Err(e) = update_verus_dependencies(path, &patches, &local_versions) {
            warn!(
                "Failed to update Verus dependencies in {}: {}",
                path.display(),
                e
            );
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::process::Command;
    use tempdir::TempDir;

    fn write_crate(path: &Path, name: &str, extra: &str) {
        fs::create_dir_all(path.join("src")).unwrap();
        fs::write(path.join("src/lib.rs"), "").unwrap();
        fs::write(
            path.join("Cargo.toml"),
            format!("[package]\nname = \"{name}\"\nversion = \"0.1.0\"\n{extra}"),
        )
        .unwrap();
    }

    fn setup_verus(root: &Path) -> PathBuf {
        let verus = root.join("verus");
        for (dir, name) in [
            ("vstd", "vstd"),
            ("builtin", "verus_builtin"),
            ("builtin_macros", "verus_builtin_macros"),
        ] {
            write_crate(&verus.join("source").join(dir), name, "");
        }
        verus
    }

    fn assert_local_dependencies(project: &Path, verus: &Path) {
        let output = Command::new(env!("CARGO"))
            .args([
                "metadata",
                "--offline",
                "--all-features",
                "--format-version",
                "1",
            ])
            .current_dir(project)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let metadata: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        for name in ["vstd", "verus_builtin", "verus_builtin_macros"] {
            let package = metadata["packages"]
                .as_array()
                .unwrap()
                .iter()
                .find(|package| package["name"] == name)
                .unwrap();
            assert!(Path::new(package["manifest_path"].as_str().unwrap()).starts_with(verus));
        }
    }

    #[test]
    fn redirects_inline_path_dependencies() {
        let temp = TempDir::new("verita-path-dependencies").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        write_crate(&project.join("helper"), "helper", "");
        write_crate(
            &project,
            "project",
            r#"
[dependencies]
vstd = { path = "../../missing/verus/source/vstd", version = "=0.0.0", default-features = false } # keep
verus_builtin = { path = "../../missing/verus/source/builtin" }
verus_builtin_macros = { path = "../../missing/verus/source/builtin_macros", optional = true }
helper = { path = "helper" } # unrelated
"#,
        );

        inject_verus_patches(
            &project,
            &project,
            &verus,
            "https://github.com/verus-lang/verus",
        )
        .unwrap();

        let content = fs::read_to_string(project.join("Cargo.toml")).unwrap();
        let manifest: toml::Value = toml::from_str(&content).unwrap();
        assert_eq!(
            manifest["dependencies"]["vstd"]["version"].as_str(),
            Some("=0.1.0")
        );
        assert_eq!(
            manifest["dependencies"]["vstd"]["default-features"].as_bool(),
            Some(false)
        );
        assert_eq!(
            manifest["dependencies"]["verus_builtin_macros"]["optional"].as_bool(),
            Some(true)
        );
        assert!(content.contains("} # keep"));
        assert!(content.contains("helper = { path = \"helper\" } # unrelated"));
        assert_local_dependencies(&project, &verus);

        inject_verus_patches(
            &project,
            &project,
            &verus,
            "https://github.com/verus-lang/verus",
        )
        .unwrap();
        assert_eq!(
            fs::read_to_string(project.join("Cargo.toml")).unwrap(),
            content
        );
    }

    #[test]
    fn redirects_workspace_and_regular_table_path_dependencies() {
        let temp = TempDir::new("verita-workspace-paths").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        let target = project.join("member");
        write_crate(
            &target,
            "member",
            r#"
[dependencies]
vstd.workspace = true

[dev-dependencies.verus_builtin]
path = "../../../missing/verus/source/builtin" # keep
version = "=0.0.0"

[build-dependencies.verus_builtin_macros]
path = "../../../missing/verus/source/builtin_macros"
"#,
        );
        fs::write(
            project.join("Cargo.toml"),
            r#"[workspace]
members = ["member"]

[workspace.dependencies]
vstd = { path = "../../missing/verus/source/vstd" }
"#,
        )
        .unwrap();

        inject_verus_patches(
            &target,
            &project,
            &verus,
            "https://github.com/verus-lang/verus",
        )
        .unwrap();

        let content = fs::read_to_string(target.join("Cargo.toml")).unwrap();
        let manifest: toml::Value = toml::from_str(&content).unwrap();
        assert_eq!(
            manifest["dependencies"]["vstd"]["workspace"].as_bool(),
            Some(true)
        );
        assert_eq!(
            manifest["dev-dependencies"]["verus_builtin"]["version"].as_str(),
            Some("=0.1.0")
        );
        assert!(content.contains(" # keep"));
        assert_local_dependencies(&target, &verus);
    }

    #[test]
    fn preserves_registry_and_git_dependency_overrides() {
        let temp = TempDir::new("verita-version-pins").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        write_crate(
            &project,
            "project",
            r#"
[dependencies]
vstd = "=0.0.0"
verus_builtin = { git = "https://github.com/verus-lang/verus", version = "=0.0.0" }
verus_builtin_macros = { version = "0.1", default-features = false }
"#,
        );

        inject_verus_patches(
            &project,
            &project,
            &verus,
            "https://github.com/verus-lang/verus",
        )
        .unwrap();

        let content = fs::read_to_string(project.join("Cargo.toml")).unwrap();
        let manifest: toml::Value = toml::from_str(&content).unwrap();
        assert_eq!(manifest["dependencies"]["vstd"].as_str(), Some("=0.1.0"));
        assert_eq!(
            manifest["dependencies"]["verus_builtin"]["version"].as_str(),
            Some("=0.1.0")
        );
        assert_eq!(
            manifest["dependencies"]["verus_builtin_macros"]["version"].as_str(),
            Some("0.1")
        );
        assert!(manifest["dependencies"]["verus_builtin_macros"]
            .get("path")
            .is_none());
        assert_local_dependencies(&project, &verus);
    }

    #[test]
    fn updates_all_path_version_requirements() {
        for local_version in ["0.1.0", "0.1.0-local"] {
            let temp = TempDir::new("verita-path-versions").unwrap();
            let verus = setup_verus(temp.path());
            fs::write(
                verus.join("source/vstd/Cargo.toml"),
                format!("[package]\nname = \"vstd\"\nversion = \"{local_version}\"\n"),
            )
            .unwrap();
            let project = temp.path().join("project");
            for requirement in ["0.2", "^0.2", "~0.2", ">=0.2, <0.3", "*", "=0.1.0"] {
                write_crate(
                    &project,
                    "project",
                    &format!(
                        r#"
[dependencies]
verus_builtin = {{ path = "../missing/builtin" }}
verus_builtin_macros = {{ path = "../missing/builtin_macros" }}

[dependencies.vstd]
path = "../missing/vstd" # keep path comment
version = "{requirement}" # keep version comment
"#,
                    ),
                );

                inject_verus_patches(
                    &project,
                    &project,
                    &verus,
                    "https://github.com/verus-lang/verus",
                )
                .unwrap();

                let content = fs::read_to_string(project.join("Cargo.toml")).unwrap();
                let manifest: toml::Value = toml::from_str(&content).unwrap();
                assert_eq!(
                    manifest["dependencies"]["vstd"]["version"].as_str(),
                    Some(format!("={local_version}").as_str()),
                    "requirement {requirement}"
                );
                assert!(content.contains("# keep path comment"));
                assert!(content.contains("# keep version comment"));
                assert!(manifest["dependencies"]["verus_builtin"]
                    .get("version")
                    .is_none());
                assert_local_dependencies(&project, &verus);
            }
        }
    }

    #[test]
    fn redirects_target_specific_dependency_sections() {
        let temp = TempDir::new("verita-target-paths").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        write_crate(
            &project,
            "project",
            r#"
[target.'cfg(unix)'.dependencies]
vstd = { path = "../missing/vstd", version = "^0.2" }

[target.'cfg(unix)'.dev-dependencies.verus_builtin]
path = "../missing/builtin"
version = "~0.2"

[target.'cfg(windows)'.build-dependencies]
verus_builtin_macros = { path = "../missing/builtin_macros", version = ">=0.2" }
"#,
        );

        inject_verus_patches(
            &project,
            &project,
            &verus,
            "https://github.com/verus-lang/verus",
        )
        .unwrap();

        assert_local_dependencies(&project, &verus);
    }

    #[test]
    fn redirects_dependencies_in_unselected_workspace_member() {
        let temp = TempDir::new("verita-sibling-paths").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        let target = project.join("a");
        write_crate(&target, "a", "");
        write_crate(
            &project.join("b"),
            "b",
            r#"
[dependencies]
vstd = { path = "../../missing/vstd" }
verus_builtin = { path = "../../missing/builtin" }
verus_builtin_macros = { path = "../../missing/builtin_macros" }
"#,
        );
        fs::write(
            project.join("Cargo.toml"),
            "[workspace]\nmembers = [\"a\", \"b\"]\n",
        )
        .unwrap();

        inject_verus_patches(
            &target,
            &project,
            &verus,
            "https://github.com/verus-lang/verus",
        )
        .unwrap();

        assert_local_dependencies(&target, &verus);
    }

    #[test]
    fn discovers_globbed_and_implicit_members_but_not_excluded_crates() {
        let temp = TempDir::new("verita-member-paths").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        let target = project.join("members/a");
        write_crate(
            &target,
            "a",
            "[dependencies]\nhelper = { path = \"../../helper\" }\n",
        );
        write_crate(
            &project.join("helper"),
            "helper",
            "[dev-dependencies]\nverus_builtin = { path = \"../../missing/builtin\" }\n",
        );
        write_crate(
            &project.join("members/b"),
            "b",
            r#"
[dependencies]
vstd = { path = "../../../missing/vstd" }
verus_builtin_macros = { path = "../../../missing/builtin_macros" }
"#,
        );
        let excluded = project.join("members/excluded/Cargo.toml");
        write_crate(
            excluded.parent().unwrap(),
            "excluded",
            "[dependencies]\nvstd = { path = \"../../../missing/vstd\" }\n",
        );
        let excluded_content = fs::read_to_string(&excluded).unwrap();
        fs::write(
            project.join("Cargo.toml"),
            r#"[workspace]
members = ["members/*"]
exclude = ["members/excluded"]
"#,
        )
        .unwrap();

        inject_verus_patches(
            &target,
            &project,
            &verus,
            "https://github.com/verus-lang/verus",
        )
        .unwrap();

        assert_eq!(fs::read_to_string(&excluded).unwrap(), excluded_content);
        assert_local_dependencies(&target, &verus);
    }

    #[test]
    fn discovers_inherited_members_without_loading_unused_workspace_dependencies() {
        let temp = TempDir::new("verita-inherited-members").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        let target = project.join("member");
        write_crate(
            &target,
            "member",
            "[dependencies]\nhelper.workspace = true\n",
        );
        write_crate(
            &project.join("helper"),
            "helper",
            r#"
[dependencies]
vstd = { path = "../../missing/vstd" }
verus_builtin = { path = "../../missing/builtin" }
verus_builtin_macros = { path = "../../missing/builtin_macros" }
"#,
        );
        fs::create_dir_all(project.join("unused")).unwrap();
        let unused = project.join("unused/Cargo.toml");
        fs::write(&unused, "not a valid manifest\n").unwrap();
        fs::write(
            project.join("Cargo.toml"),
            r#"[workspace]
members = ["member"]

[workspace.dependencies]
helper = { path = "helper" }
unused = { path = "unused" }
"#,
        )
        .unwrap();

        inject_verus_patches(
            &target,
            &project,
            &verus,
            "https://github.com/verus-lang/verus",
        )
        .unwrap();

        assert_eq!(
            fs::read_to_string(&unused).unwrap(),
            "not a valid manifest\n"
        );
        assert_local_dependencies(&target, &verus);
    }
}
