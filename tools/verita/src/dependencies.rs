use anyhow::anyhow;
use std::collections::{HashMap, HashSet};
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

/// Collect all dependency names declared in a manifest (all dep sections +
/// workspace.dependencies).
fn collect_dep_names(manifest: &toml::Value) -> HashSet<String> {
    let mut names = HashSet::new();
    for section in &["dependencies", "dev-dependencies", "build-dependencies"] {
        if let Some(deps) = manifest.get(section).and_then(|d| d.as_table()) {
            names.extend(deps.keys().cloned());
        }
    }
    if let Some(wdeps) = manifest
        .get("workspace")
        .and_then(|w| w.get("dependencies"))
        .and_then(|d| d.as_table())
    {
        names.extend(wdeps.keys().cloned());
    }
    names
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

/// In the `Cargo.toml` at `path`, rewrite any exact-version pins (`=X.Y.Z`)
/// on crates in `local_versions` that don't match the local version. This
/// allows Cargo's `[patch]` entries to take effect: Cargo only applies a patch
/// when the patch version satisfies the dependency's version constraint.
///
/// Uses `toml_edit` so that the rest of the file is left byte-for-byte
/// identical (key order, comments, blank lines, etc.).
fn relax_exact_version_pins(
    path: &Path,
    local_versions: &HashMap<String, String>,
) -> anyhow::Result<()> {
    if local_versions.is_empty() {
        return Ok(());
    }
    let content = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(_) => return Ok(()),
    };
    let mut doc = match content.parse::<toml_edit::DocumentMut>() {
        Ok(d) => d,
        Err(_) => return Ok(()),
    };
    let mut changed = false;

    for section in &["dependencies", "dev-dependencies", "build-dependencies"] {
        if let Some(deps) = doc.get_mut(section).and_then(|d| d.as_table_mut()) {
            for (crate_name, local_ver) in local_versions {
                if let Some(dep) = deps.get_mut(crate_name.as_str()) {
                    changed |= relax_dep_item(dep, local_ver);
                }
            }
        }
    }

    // [workspace.dependencies] requires two levels of navigation.
    if doc
        .get("workspace")
        .and_then(|w| w.get("dependencies"))
        .is_some()
    {
        if let Some(wdeps) = doc["workspace"]
            .as_table_mut()
            .and_then(|w| w.get_mut("dependencies"))
            .and_then(|d| d.as_table_mut())
        {
            for (crate_name, local_ver) in local_versions {
                if let Some(dep) = wdeps.get_mut(crate_name.as_str()) {
                    changed |= relax_dep_item(dep, local_ver);
                }
            }
        }
    }

    if changed {
        debug!("Updated exact version pins in {}", path.display());
        std::fs::write(path, doc.to_string())
            .map_err(|e| anyhow!("cannot write {}: {}", path.display(), e))?;
    }
    Ok(())
}

/// If the project's workspace references any Verus crates, add `[patch]` entries
/// to the workspace root `Cargo.toml` so those crates resolve to the local Verus
/// repo rather than whatever version/source the project specified.
///
/// Two patch sources are written – `crates-io` and the Verus git URL – so the
/// override works regardless of how the project declared its dependency.
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

    // Collect dep names from both the workspace root and the target crate
    let mut all_dep_names: HashSet<String> = HashSet::new();
    for path in [&workspace_cargo_toml, &target_dir.join("Cargo.toml")] {
        if let Ok(content) = std::fs::read_to_string(path) {
            if let Ok(manifest) = toml::from_str::<toml::Value>(&content) {
                all_dep_names.extend(collect_dep_names(&manifest));
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

    // Relax exact-version pins on the patched crates so Cargo actually uses the
    // patches. Cargo only applies a [patch] when its version satisfies the
    // dependency's constraint; an exact pin like `=0.0.0-old` won't match a
    // local crate at a newer version, causing the patch to be silently ignored.
    let local_versions: HashMap<String, String> = patches
        .iter()
        .filter_map(|(name, path)| get_local_version(path).map(|v| (name.clone(), v)))
        .collect();

    if !local_versions.is_empty() {
        // Process the workspace root and, if different, the target crate's Cargo.toml.
        let target_cargo_toml = target_dir.join("Cargo.toml");
        for path in [&workspace_cargo_toml, &target_cargo_toml] {
            if let Err(e) = relax_exact_version_pins(path, &local_versions) {
                warn!("Failed to relax version pins in {}: {}", path.display(), e);
            }
        }
    }

    Ok(())
}
