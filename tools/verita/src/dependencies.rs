use anyhow::anyhow;
use std::collections::{hash_map::Entry, BTreeSet, HashMap, HashSet};
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

fn normalize_join(base: &Path, relative: &str) -> PathBuf {
    let mut path = PathBuf::new();
    for component in base.join(relative).components() {
        match component {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                path.pop();
            }
            component => path.push(component),
        }
    }
    path
}

/// Mirror Cargo's literal prefix matching, where explicit `members` entries override `exclude`.
fn workspace_excludes(
    workspace_root: &Path,
    members: &[&str],
    exclude: &[&str],
    manifest_path: &Path,
) -> bool {
    let under = |entries: &[&str]| {
        entries
            .iter()
            .any(|entry| manifest_path.starts_with(normalize_join(workspace_root, entry)))
    };
    !under(members) && under(exclude)
}

fn toml_strings(value: Option<&toml::Value>) -> Vec<&str> {
    value
        .and_then(|v| v.as_array())
        .map(|a| a.iter().filter_map(|v| v.as_str()).collect())
        .unwrap_or_default()
}

fn toml_edit_strings(value: Option<&toml_edit::Item>) -> Vec<&str> {
    value
        .and_then(|v| v.as_array())
        .map(|a| a.iter().filter_map(|v| v.as_str()).collect())
        .unwrap_or_default()
}

/// Resolve the package's own workspace, an explicit `package.workspace`, or the
/// nearest ancestor workspace that does not exclude the package.
fn find_workspace_root(target_dir: &Path, repo_root: &Path) -> anyhow::Result<PathBuf> {
    let target_dir = dunce::canonicalize(target_dir)?;
    let repo_root = dunce::canonicalize(repo_root)?;
    if !target_dir.starts_with(&repo_root) {
        return Err(anyhow!(
            "package {} is outside the repository",
            target_dir.display()
        ));
    }
    let target_manifest = target_dir.join("Cargo.toml");
    let mut current = target_dir.as_path();
    loop {
        if let Ok(content) = std::fs::read_to_string(current.join("Cargo.toml")) {
            let manifest: toml::Value = toml::from_str(&content)?;
            if let Some(workspace) = manifest.get("workspace") {
                if current == target_dir
                    || !workspace_excludes(
                        current,
                        &toml_strings(workspace.get("members")),
                        &toml_strings(workspace.get("exclude")),
                        &target_manifest,
                    )
                {
                    return Ok(current.to_path_buf());
                }
            }
            if current == target_dir {
                if let Some(workspace) = manifest
                    .get("package")
                    .and_then(|p| p.get("workspace"))
                    .and_then(|w| w.as_str())
                {
                    let workspace = dunce::canonicalize(current.join(workspace))?;
                    if !workspace.starts_with(&repo_root) {
                        return Err(anyhow!(
                            "workspace {} is outside the repository",
                            workspace.display()
                        ));
                    }
                    return Ok(workspace);
                }
            }
        }
        if current == repo_root {
            break;
        }
        match current.parent() {
            Some(parent) => current = parent,
            _ => break,
        }
    }
    Ok(target_dir)
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
    // Inherited entries are handled at their workspace declaration.
    let mut visit_declared = |name: &str, dep: &mut toml_edit::Item| {
        if dep.get("workspace").and_then(|w| w.as_bool()) != Some(true) {
            visit(name, dep);
        }
    };
    visit_dependency_sections(table, &mut visit_declared);
    if let Some(workspace) = table
        .get_mut("workspace")
        .and_then(|w| w.as_table_like_mut())
    {
        visit_dependency_sections(workspace, &mut visit_declared);
    }
}

fn dependency_package_name<'a>(name: &'a str, dep: &'a toml_edit::Item) -> &'a str {
    dep.get("package").and_then(|p| p.as_str()).unwrap_or(name)
}

fn visit_patch_dependencies(
    table: &mut dyn toml_edit::TableLike,
    visit: &mut impl FnMut(&str, &mut toml_edit::Item),
) {
    if let Some(sources) = table.get_mut("patch").and_then(|p| p.as_table_like_mut()) {
        for (_, source) in sources.iter_mut() {
            if let Some(deps) = source.as_table_like_mut() {
                for (name, dep) in deps.iter_mut() {
                    visit(name.get(), dep);
                }
            }
        }
    }
}

fn collect_dep_names(
    manifest: &mut toml_edit::DocumentMut,
    include_patches: bool,
) -> HashSet<String> {
    let mut names = HashSet::new();
    let mut collect = |name: &str, dep: &mut toml_edit::Item| {
        names.insert(dependency_package_name(name, dep).to_string());
    };
    visit_dependencies(manifest.as_table_mut(), &mut collect);
    if include_patches {
        visit_patch_dependencies(manifest.as_table_mut(), &mut collect);
    }
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
            let normalized = pattern.replace('\\', "/");
            let full_pattern = if Path::new(pattern).is_absolute() {
                normalized
            } else {
                format!("{root}/{normalized}")
            };
            for path in glob::glob(&full_pattern)? {
                let path = path?;
                if path.is_dir() {
                    paths.push(dunce::canonicalize(path)?);
                }
            }
        }
    }
    Ok(paths)
}

fn queue_local_dependency(
    name: &str,
    dep: &toml_edit::Item,
    base: &Path,
    repo_root: &Path,
    verus_crate_map: &HashMap<String, PathBuf>,
    pending: &mut Vec<PathBuf>,
) {
    // These paths will be redirected, so the old Verus checkout must not be loaded.
    if verus_crate_map.contains_key(dependency_package_name(name, dep)) {
        return;
    }
    if let Some(path) = dep.get("path").and_then(|p| p.as_str()) {
        if let Ok(path) = dunce::canonicalize(base.join(path)) {
            if path.starts_with(repo_root) {
                pending.push(path.join("Cargo.toml"));
            }
        }
    }
}

/// Discover members and reachable in-repo dependencies without loading Cargo metadata.
fn collect_workspace_manifests(
    workspace_root: &Path,
    target_dir: &Path,
    repo_root: &Path,
    verus_crate_map: &HashMap<String, PathBuf>,
) -> anyhow::Result<Vec<PathBuf>> {
    let workspace_root = dunce::canonicalize(workspace_root)?;
    let repo_root = dunce::canonicalize(repo_root)?;
    let mut root_manifest = std::fs::read_to_string(workspace_root.join("Cargo.toml"))?
        .parse::<toml_edit::DocumentMut>()?;
    let workspace = root_manifest.get("workspace");
    let members = toml_edit_strings(workspace.and_then(|w| w.get("members")));
    let exclude = toml_edit_strings(workspace.and_then(|w| w.get("exclude")));
    let mut pending = vec![
        workspace_root.join("Cargo.toml"),
        target_dir.join("Cargo.toml"),
    ];
    pending.extend(
        expand_workspace_paths(&workspace_root, workspace.and_then(|w| w.get("members")))?
            .into_iter()
            .map(|path| path.join("Cargo.toml"))
            .filter(|path| !workspace_excludes(&workspace_root, &members, &exclude, path)),
    );
    visit_patch_dependencies(root_manifest.as_table_mut(), &mut |name, dep| {
        queue_local_dependency(
            name,
            dep,
            &workspace_root,
            &repo_root,
            verus_crate_map,
            &mut pending,
        );
    });
    let mut workspaces = HashMap::from([(workspace_root, root_manifest)]);
    let mut manifests = BTreeSet::new();
    let mut visited = HashSet::new();
    while let Some(path) = pending.pop() {
        let path = match dunce::canonicalize(path) {
            Ok(path) => path,
            Err(_) => continue,
        };
        let dir = path.parent().expect("manifest must have a parent");
        if !path.starts_with(&repo_root) || !visited.insert(path.clone()) {
            continue;
        }
        manifests.insert(path.clone());
        let content = std::fs::read_to_string(&path)?;
        let mut manifest = content.parse::<toml_edit::DocumentMut>()?;
        let package_workspace = find_workspace_root(dir, &repo_root)?;
        let workspace_path = package_workspace.join("Cargo.toml");
        // Other workspaces supply declarations, not additional member roots to traverse.
        manifests.insert(workspace_path.clone());
        let workspace_manifest = match workspaces.entry(package_workspace.clone()) {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(
                std::fs::read_to_string(workspace_path)?.parse::<toml_edit::DocumentMut>()?,
            ),
        };
        let workspace = workspace_manifest.get("workspace");
        visit_dependency_sections(manifest.as_table_mut(), &mut |name, dep| {
            let (dep, base) = if dep.get("workspace").and_then(|w| w.as_bool()) == Some(true) {
                match workspace
                    .and_then(|w| w.get("dependencies"))
                    .and_then(|d| d.get(name))
                {
                    Some(dep) => (dep, package_workspace.as_path()),
                    None => return,
                }
            } else {
                (&*dep, dir)
            };
            queue_local_dependency(name, dep, base, &repo_root, verus_crate_map, &mut pending);
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
        if let Some((crate_name, crate_path)) = patches
            .iter()
            .find(|(crate_name, _)| dependency_package_name(name, dep) == crate_name)
        {
            changed |= update_dep_item(
                dep,
                crate_path,
                local_versions.get(crate_name).map(String::as_str),
            );
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

    let workspace_root = find_workspace_root(target_dir, repo_root)?;
    let workspace_cargo_toml = workspace_root.join("Cargo.toml");
    let manifests =
        collect_workspace_manifests(&workspace_root, target_dir, repo_root, &verus_crate_map)?;

    let mut all_dep_names: HashSet<String> = HashSet::new();
    for path in &manifests {
        if let Ok(content) = std::fs::read_to_string(path) {
            if let Ok(mut manifest) = content.parse::<toml_edit::DocumentMut>() {
                all_dep_names.extend(collect_dep_names(
                    &mut manifest,
                    path == &workspace_cargo_toml,
                ));
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
        .as_table_like_mut()
        .ok_or_else(|| anyhow!("[patch] is not a table"))?;

    for source in &["crates-io", verus_git_url] {
        if !patch_section.contains_key(source) {
            patch_section.insert(source, toml_edit::table());
        }
    }
    for (source, entries) in patch_section.iter_mut() {
        let source = source.get();
        let source_section = entries
            .as_table_like_mut()
            .ok_or_else(|| anyhow!("[patch.{}] is not a table", source))?;
        for (crate_name, crate_path) in &patches {
            let existing: Vec<String> = source_section
                .iter()
                .filter(|(name, dep)| dependency_package_name(name, dep) == crate_name)
                .map(|(name, _)| name.to_string())
                .collect();
            if existing.is_empty() && source != "crates-io" && source != verus_git_url {
                continue;
            }
            let key = existing.first().cloned().unwrap_or_else(|| {
                let mut key = crate_name.clone();
                while source_section.contains_key(&key) {
                    key.push('_');
                }
                key
            });
            // Redirected aliases all provide the same local package version.
            for duplicate in existing.iter().skip(1) {
                source_section.remove(duplicate);
            }
            let path_str = crate_path.to_string_lossy().replace('\\', "/");
            let mut entry = toml_edit::InlineTable::new();
            entry.insert("path", toml_edit::Value::from(path_str.as_str()));
            if key != *crate_name {
                entry.insert("package", toml_edit::Value::from(crate_name.as_str()));
            }
            source_section.insert(
                &key,
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

    fn cargo_metadata(project: &Path) -> serde_json::Value {
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
        serde_json::from_slice(&output.stdout).unwrap()
    }

    fn assert_local_dependencies(project: &Path, verus: &Path) {
        let metadata = cargo_metadata(project);
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
    fn discovers_absolute_workspace_members() {
        let temp = TempDir::new("verita-absolute-members").unwrap();
        let verus = setup_verus(temp.path());
        let project = dunce::canonicalize(temp.path()).unwrap().join("project");
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
        let absolute_member = project.join("b").to_string_lossy().replace('\\', "/");
        fs::write(
            project.join("Cargo.toml"),
            format!("[workspace]\nmembers = [\"a\", \"{absolute_member}\"]\n"),
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
    fn matches_workspace_excludes_literally_by_path_prefix() {
        let temp = TempDir::new("verita-literal-excludes").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        let target = project.join("c/a");
        write_crate(
            &target,
            "a",
            "[dependencies]\nvstd = { path = \"../../../missing/vstd\" }\n",
        );
        let old_deps = r#"
[dependencies]
vstd = { path = "../../../missing/vstd" }
verus_builtin = { path = "../../../missing/builtin" }
verus_builtin_macros = { path = "../../../missing/builtin_macros" }
"#;
        write_crate(&project.join("c/ex-1"), "ex-1", old_deps);
        write_crate(&project.join("vendor/kept"), "kept", old_deps);
        let excluded = project.join("vendor/h/Cargo.toml");
        write_crate(excluded.parent().unwrap(), "h", old_deps);
        let excluded_content = fs::read_to_string(&excluded).unwrap();
        fs::write(
            project.join("Cargo.toml"),
            r#"[workspace]
members = ["c/*", "vendor/*", "vendor/kept"]
exclude = ["c/ex-*", "vendor"]
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
    fn skips_ancestor_workspaces_that_exclude_the_package() {
        let temp = TempDir::new("verita-excluding-ancestor").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        let target = project.join("inner/x");
        write_crate(
            &target,
            "x",
            r#"
[dependencies]
vstd.workspace = true
verus_builtin.workspace = true
verus_builtin_macros.workspace = true
"#,
        );
        fs::write(
            project.join("inner/Cargo.toml"),
            "[workspace]\nexclude = [\"x\"]\n",
        )
        .unwrap();
        let inner_content = fs::read_to_string(project.join("inner/Cargo.toml")).unwrap();
        fs::write(
            project.join("Cargo.toml"),
            r#"[workspace]
members = ["inner/x"]

[workspace.dependencies]
vstd = { path = "../missing/vstd" }
verus_builtin = { path = "../missing/builtin" }
verus_builtin_macros = { path = "../missing/builtin_macros" }
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
            fs::read_to_string(project.join("inner/Cargo.toml")).unwrap(),
            inner_content
        );
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

    #[test]
    fn redirects_aliased_verus_packages_without_redirecting_non_verus_aliases() {
        let temp = TempDir::new("verita-package-aliases").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        fs::create_dir_all(temp.path().join("old/vstd")).unwrap();
        fs::write(
            temp.path().join("old/vstd/Cargo.toml"),
            "invalid manifest\n",
        )
        .unwrap();
        write_crate(
            &project.join("helper"),
            "custom-vstd",
            r#"
[dependencies]
std_alias = { package = "vstd", path = "../../old/vstd", version = "^0.2" }
builtin_alias = { package = "verus_builtin", version = "=0.0.0" }
macros_alias = { package = "verus_builtin_macros", git = "https://github.com/verus-lang/verus", version = "=0.0.0" }
"#,
        );
        write_crate(
            &project,
            "project",
            r#"
[dependencies]
vstd = { package = "custom-vstd", path = "helper", version = "0.1" } # keep
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
        assert!(content.contains(
            "vstd = { package = \"custom-vstd\", path = \"helper\", version = \"0.1\" } # keep"
        ));
        let content = fs::read_to_string(project.join("helper/Cargo.toml")).unwrap();
        let manifest: toml::Value = toml::from_str(&content).unwrap();
        for alias in ["std_alias", "builtin_alias", "macros_alias"] {
            assert_eq!(
                manifest["dependencies"][alias]["version"].as_str(),
                Some("=0.1.0")
            );
        }
        assert_local_dependencies(&project, &verus);
    }

    #[test]
    fn resolves_inherited_aliases_before_deciding_which_paths_to_follow() {
        let temp = TempDir::new("verita-workspace-aliases").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        let target = project.join("member");
        fs::create_dir_all(temp.path().join("old/vstd")).unwrap();
        fs::write(
            temp.path().join("old/vstd/Cargo.toml"),
            "invalid manifest\n",
        )
        .unwrap();
        write_crate(
            &target,
            "member",
            "[dependencies]\nvstd.workspace = true\nstd_alias.workspace = true\n",
        );
        let member_content = fs::read_to_string(target.join("Cargo.toml")).unwrap();
        write_crate(
            &project.join("helper"),
            "custom-vstd",
            r#"
[dependencies]
builtin_alias = { package = "verus_builtin", path = "../../missing/builtin" }
macros_alias = { package = "verus_builtin_macros", path = "../../missing/builtin_macros" }
"#,
        );
        fs::write(
            project.join("Cargo.toml"),
            r#"[workspace]
members = ["member"]

[workspace.dependencies]
vstd = { package = "custom-vstd", path = "helper", version = "0.1" }
std_alias = { package = "vstd", path = "../old/vstd", version = "~0.2" }
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
            fs::read_to_string(target.join("Cargo.toml")).unwrap(),
            member_content
        );
        let content = fs::read_to_string(project.join("Cargo.toml")).unwrap();
        let manifest: toml::Value = toml::from_str(&content).unwrap();
        assert_eq!(
            manifest["workspace"]["dependencies"]["vstd"]["path"].as_str(),
            Some("helper")
        );
        assert_eq!(
            manifest["workspace"]["dependencies"]["vstd"]["version"].as_str(),
            Some("0.1")
        );
        assert_local_dependencies(&target, &verus);
    }

    #[test]
    fn leaves_non_verus_workspace_aliases_unchanged() {
        let temp = TempDir::new("verita-custom-workspace-alias").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        let target = project.join("member");
        write_crate(&target, "member", "[dependencies]\nvstd.workspace = true\n");
        write_crate(&project.join("helper"), "custom-vstd", "");
        let workspace_content = r#"[workspace]
members = ["member"]

[workspace.dependencies]
vstd = { package = "custom-vstd", path = "helper" }
"#;
        fs::write(project.join("Cargo.toml"), workspace_content).unwrap();

        inject_verus_patches(
            &target,
            &project,
            &verus,
            "https://github.com/verus-lang/verus",
        )
        .unwrap();

        assert_eq!(
            fs::read_to_string(project.join("Cargo.toml")).unwrap(),
            workspace_content
        );
        cargo_metadata(&target);
    }

    #[test]
    fn rewrites_reachable_excluded_helpers_but_not_unused_excluded_crates() {
        for (inherited, outside_workspace) in [(false, false), (true, false), (true, true)] {
            let temp = TempDir::new("verita-excluded-helpers").unwrap();
            let verus = setup_verus(temp.path());
            let project = temp.path().join("project");
            let workspace = if outside_workspace {
                project.join("workspace")
            } else {
                project.clone()
            };
            let target = workspace.join("crates/member");
            let helper_path = if outside_workspace {
                "../crates/excluded-helper"
            } else {
                "crates/excluded-helper"
            };
            let unused_path = if outside_workspace {
                "../crates/excluded-unused"
            } else {
                "crates/excluded-unused"
            };
            let dependency = if inherited {
                "helper.workspace = true"
            } else {
                "helper = { path = \"../excluded-helper\" }"
            };
            write_crate(
                &target,
                "member",
                &format!("[dependencies]\n{dependency}\n"),
            );
            write_crate(
                &project.join("crates/excluded-helper"),
                "helper",
                r#"
[dependencies]
vstd = { path = "../../../missing/vstd" }
verus_builtin = { path = "../../../missing/builtin" }

[build-dependencies]
verus_builtin_macros = { path = "../../../missing/builtin_macros" }
"#,
            );
            let unused = project.join("crates/excluded-unused/Cargo.toml");
            fs::create_dir_all(unused.parent().unwrap()).unwrap();
            fs::write(&unused, "invalid manifest\n").unwrap();
            fs::write(
                workspace.join("Cargo.toml"),
                format!(
                    r#"[workspace]
members = ["crates/*"]
exclude = ["{helper_path}", "{unused_path}"]

[workspace.dependencies]
helper = {{ path = "{helper_path}" }}
"#
                ),
            )
            .unwrap();

            inject_verus_patches(
                &target,
                &project,
                &verus,
                "https://github.com/verus-lang/verus",
            )
            .unwrap();

            assert_eq!(fs::read_to_string(&unused).unwrap(), "invalid manifest\n");
            assert_local_dependencies(&target, &verus);
        }
    }

    #[test]
    fn resolves_dependencies_from_each_packages_own_workspace() {
        for explicit_workspace in [false, true] {
            let temp = TempDir::new("verita-owning-workspace").unwrap();
            let verus = setup_verus(temp.path());
            let project = temp.path().join("project");
            let target = project.join("app");
            let vendor = project.join("vendor-ws");
            let helper = if explicit_workspace {
                project.join("linked-helper")
            } else {
                vendor.join("helper")
            };
            write_crate(
                &target,
                "app",
                &format!(
                    "[dependencies]\nhelper = {{ path = \"../{}\" }}\n",
                    if explicit_workspace {
                        "linked-helper"
                    } else {
                        "vendor-ws/helper"
                    }
                ),
            );
            write_crate(
                &helper,
                "helper",
                &format!(
                    "{}\n[dependencies]\nstd_alias.workspace = true\nsupport.workspace = true\n",
                    if explicit_workspace {
                        "workspace = \"../vendor-ws\""
                    } else {
                        ""
                    }
                ),
            );
            let inherited_content = fs::read_to_string(helper.join("Cargo.toml")).unwrap();
            write_crate(
                &vendor.join("support"),
                "support",
                r#"
[dependencies]
builtin_alias = { package = "verus_builtin", path = "../../missing/builtin" }
macros_alias = { package = "verus_builtin_macros", path = "../../missing/builtin_macros" }
"#,
            );
            fs::create_dir_all(vendor.join("unused-member")).unwrap();
            fs::write(
                vendor.join("unused-member/Cargo.toml"),
                "invalid manifest\n",
            )
            .unwrap();
            fs::write(
                vendor.join("Cargo.toml"),
                format!(
                    r#"[workspace]
members = ["{}", "support", "unused-member"]

[workspace.dependencies]
std_alias = {{ package = "vstd", path = "../missing/vstd", version = "^0.2" }}
support = {{ path = "support" }}
"#,
                    if explicit_workspace {
                        "../linked-helper"
                    } else {
                        "helper"
                    }
                ),
            )
            .unwrap();
            fs::write(
                project.join("Cargo.toml"),
                r#"[workspace]
members = ["app"]
exclude = ["vendor-ws", "linked-helper"]

[workspace.dependencies]
std_alias = { package = "custom-vstd", path = "unused" }
support = { path = "unused" }
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
                fs::read_to_string(helper.join("Cargo.toml")).unwrap(),
                inherited_content
            );
            assert_eq!(
                fs::read_to_string(vendor.join("unused-member/Cargo.toml")).unwrap(),
                "invalid manifest\n"
            );
            let content = fs::read_to_string(vendor.join("Cargo.toml")).unwrap();
            let manifest: toml::Value = toml::from_str(&content).unwrap();
            assert_eq!(
                manifest["workspace"]["dependencies"]["std_alias"]["version"].as_str(),
                Some("=0.1.0")
            );
            assert_local_dependencies(&target, &verus);
        }
    }

    #[test]
    fn injects_patches_into_the_selected_packages_nearest_workspace() {
        let temp = TempDir::new("verita-nested-workspace").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        let nested = project.join("nested");
        let target = nested.join("member");
        write_crate(&project, "outer", "[workspace]\nexclude = [\"nested\"]\n");
        let outer_content = fs::read_to_string(project.join("Cargo.toml")).unwrap();
        write_crate(
            &target,
            "member",
            r#"
[dependencies]
vstd.workspace = true
verus_builtin.workspace = true
verus_builtin_macros.workspace = true
"#,
        );
        fs::write(
            nested.join("Cargo.toml"),
            r#"[workspace]
members = ["member"]

[workspace.dependencies]
vstd = "=0.0.0"
verus_builtin = "=0.0.0"
verus_builtin_macros = "=0.0.0"
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
            fs::read_to_string(project.join("Cargo.toml")).unwrap(),
            outer_content
        );
        assert_local_dependencies(&target, &verus);
    }

    #[test]
    fn discovers_local_patch_helpers_but_ignores_dependency_patch_sections() {
        for (git_source, patch_alias) in [(false, "helper"), (false, "vstd"), (true, "vstd")] {
            let temp = TempDir::new("verita-local-patches").unwrap();
            let verus = setup_verus(temp.path());
            let project = temp.path().join("project");
            let source = if git_source {
                "https://github.com/verus-lang/verus"
            } else {
                "crates-io"
            };
            let dependency = if git_source {
                r#"helper = { git = "https://github.com/verus-lang/verus", version = "0.1" }"#
            } else {
                r#"helper = "0.1""#
            };
            write_crate(
                &project,
                "app",
                &format!(
                    r#"
[workspace]
exclude = ["helper"]

[dependencies]
{dependency}

[patch."{source}"]
{patch_alias} = {{ package = "helper", path = "helper" }} # keep helper patch
"#
                ),
            );
            write_crate(
                &project.join("helper"),
                "helper",
                r#"
[workspace]

[dependencies]
vstd = { path = "../../missing/vstd" }
verus_builtin = { path = "../../missing/builtin" }
verus_builtin_macros = { path = "../../missing/builtin_macros" }

[patch.crates-io]
ignored = { path = "ignored" }
"#,
            );
            let ignored = project.join("helper/ignored/Cargo.toml");
            fs::create_dir_all(ignored.parent().unwrap()).unwrap();
            fs::write(&ignored, "invalid manifest\n").unwrap();

            inject_verus_patches(
                &project,
                &project,
                &verus,
                "https://github.com/verus-lang/verus",
            )
            .unwrap();

            let content = fs::read_to_string(project.join("Cargo.toml")).unwrap();
            assert!(content.contains(&format!(
                "{patch_alias} = {{ package = \"helper\", path = \"helper\" }} # keep helper patch"
            )));
            assert_eq!(fs::read_to_string(&ignored).unwrap(), "invalid manifest\n");
            assert_local_dependencies(&project, &verus);
        }
    }

    #[test]
    fn redirects_aliased_verus_patches_without_loading_the_old_checkout() {
        let temp = TempDir::new("verita-verus-patches").unwrap();
        let verus = setup_verus(temp.path());
        let project = temp.path().join("project");
        fs::create_dir_all(temp.path().join("old/vstd")).unwrap();
        fs::write(
            temp.path().join("old/vstd/Cargo.toml"),
            "invalid manifest\n",
        )
        .unwrap();
        write_crate(
            &project,
            "app",
            r#"
[dependencies]
vstd = "=0.0.0"
verus_builtin = { path = "../missing/builtin" }
verus_builtin_macros = { path = "../missing/builtin_macros" }

[patch."https://example.invalid/compat"]
std_one = { package = "vstd", path = "../old/vstd" }
std_two = { package = "vstd", path = "../old/vstd" }
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
}
