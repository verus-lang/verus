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
