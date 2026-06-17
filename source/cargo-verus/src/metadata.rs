use std::{
    collections::{BTreeMap, BTreeSet as Set, VecDeque},
    path::PathBuf,
};

use anyhow::{Context, Result};
use cargo_metadata::{Metadata, MetadataCommand, Package, PackageId, Source, semver::Version};
use serde::Deserialize;
use sha2::{Digest, Sha256};

#[derive(Debug, Default, Deserialize)]
pub struct VerusMetadata {
    #[serde(default)]
    pub verify: bool,
    #[serde(rename = "no-vstd", default)]
    pub no_vstd: bool,
    #[serde(rename = "is-vstd", default)]
    pub is_vstd: bool,
    #[serde(rename = "is-core", default)]
    pub is_core: bool,
    #[serde(rename = "is-builtin", default)]
    pub is_builtin: bool,
    #[serde(rename = "is-builtin-macros", default)]
    pub is_builtin_macros: bool,
}

impl VerusMetadata {
    pub fn parse_from_package(package: &cargo_metadata::Package) -> Result<VerusMetadata> {
        match package.metadata.as_object().and_then(|obj| obj.get("verus")) {
            Some(value) => {
                serde_json::from_value::<VerusMetadata>(value.clone()).with_context(|| {
                    format!("Failed to parse {}-{}.metadata.verus", package.name, package.version)
                })
            }
            None => Ok(Default::default()),
        }
    }
}

pub struct MetadataIndex<'a> {
    entries: BTreeMap<&'a PackageId, MetadataIndexEntry<'a>>,
}

pub struct MetadataIndexEntry<'a> {
    package: &'a Package,
    verus_metadata: VerusMetadata,
    deps: BTreeMap<&'a PackageId, &'a cargo_metadata::NodeDep>,
}

impl<'a> MetadataIndex<'a> {
    pub fn new(metadata: &'a Metadata) -> Result<Self> {
        assert!(metadata.resolve.is_some());
        let mut deps_by_package = BTreeMap::new();
        for node in &metadata.resolve.as_ref().unwrap().nodes {
            let mut deps = BTreeMap::new();
            for dep in &node.deps {
                assert!(deps.insert(&dep.pkg, dep).is_none());
            }
            assert!(deps_by_package.insert(&node.id, deps).is_none());
        }
        let mut entries = BTreeMap::new();
        for package in &metadata.packages {
            assert!(
                entries
                    .insert(
                        &package.id,
                        MetadataIndexEntry {
                            package,
                            verus_metadata: VerusMetadata::parse_from_package(package)?,
                            deps: deps_by_package.remove(&package.id).unwrap(),
                        }
                    )
                    .is_none()
            );
        }
        assert!(deps_by_package.is_empty());
        Ok(Self { entries })
    }

    pub fn get(&self, id: &PackageId) -> &MetadataIndexEntry<'a> {
        self.entries.get(id).unwrap()
    }

    pub fn get_transitive_closure(&self, roots: Set<PackageId>) -> Set<PackageId> {
        // Breadth-first traversal to collect transitive deps of `roots`
        let mut visited = roots;
        let mut queue = VecDeque::from_iter(visited.iter().cloned());
        while let Some(id) = queue.pop_front() {
            let entry = self.get(&id);
            for dep in entry.deps.values() {
                if !visited.contains(&dep.pkg) {
                    visited.insert(dep.pkg.clone());
                    queue.push_back(dep.pkg.clone());
                }
            }
        }
        visited
    }

    /// Names to pass via `--import-dep-if-present` for every `verify=true`
    /// crate transitively reachable from `root` (excluding `root` itself).
    ///
    /// rustc only exposes direct deps as `--extern`, but when a re-exporting
    /// facade pulls items in by canonical path rustc still loads the deeper
    /// crate's metadata and Verus needs the matching `.vir`. Direct deps use
    /// the consumer-side dep name (so `package = "..."` renames are honored);
    /// deeper deps fall back to the lib target name, since there is no alias
    /// from the consumer's perspective. Crates with no lib target are skipped.
    pub fn transitive_verified_import_names(&self, root: &PackageId) -> Vec<String> {
        let mut visited: Set<&PackageId> = Set::new();
        let mut queue: VecDeque<(&PackageId, Option<String>)> = VecDeque::new();
        for dep in self.get(root).deps.values() {
            queue.push_back((&dep.pkg, Some(dep.name.clone())));
        }
        let mut names = Vec::new();
        while let Some((pkg_id, name_override)) = queue.pop_front() {
            if !visited.insert(pkg_id) {
                continue;
            }
            let entry = self.get(pkg_id);
            if entry.verus_metadata.verify {
                let import_name = name_override.or_else(|| {
                    entry.package.targets.iter().find(|t| t.is_lib()).map(|t| t.name.clone())
                });
                if let Some(name) = import_name {
                    names.push(name);
                }
            }
            for dep in entry.deps.values() {
                queue.push_back((&dep.pkg, None));
            }
        }
        names
    }

    /// Collect sources of `vstd` that appear in the build.
    pub fn collect_vstd_sources(&self) -> Vec<PackageMetadata> {
        self.entries
            .values()
            .filter(|entry| entry.verus_metadata.is_vstd)
            .map(|entry| PackageMetadata::from(entry.package))
            .collect()
    }
}

/// Metadata about a package.
#[derive(Debug, Clone)]
pub struct PackageMetadata {
    pub version: Version,
    pub source: PackageSource,
}

/// Metadata about a package.
#[derive(Debug, Clone)]
pub enum PackageSource {
    Registry { registry: String },
    Git { git: String, rev: Option<String> },
    Unsupported,
}

impl From<&Package> for PackageMetadata {
    fn from(package: &Package) -> Self {
        let version = package.version.clone();
        let source = PackageSource::from(package.source.as_ref());
        PackageMetadata { version, source }
    }
}

impl From<Option<&Source>> for PackageSource {
    fn from(source: Option<&Source>) -> Self {
        let Some(source) = source else {
            return PackageSource::Unsupported;
        };

        let repr = &source.repr;
        if let Some(registry) = repr.strip_prefix("registry+") {
            PackageSource::Registry { registry: registry.to_string() }
        } else if let Some(git_source) = repr.strip_prefix("git+") {
            if let Some((git, rev)) = git_source.rsplit_once('#') {
                PackageSource::Git { git: git.to_string(), rev: Some(rev.to_string()) }
            } else {
                PackageSource::Git { git: git_source.to_string(), rev: None }
            }
        } else {
            PackageSource::Unsupported
        }
    }
}

impl<'a> MetadataIndexEntry<'a> {
    pub fn package(&self) -> &'a Package {
        self.package
    }

    pub fn verus_metadata(&self) -> &VerusMetadata {
        &self.verus_metadata
    }
}

pub fn make_package_id(
    name: impl AsRef<str>,
    version: impl AsRef<str>,
    manifest_path: impl AsRef<str>,
) -> String {
    let manifest_path_hash = {
        let mut hasher = Sha256::new();
        hasher.update(manifest_path.as_ref().as_bytes());
        hex::encode(hasher.finalize())
    };
    format!("{}-{}-{}", name.as_ref(), version.as_ref(), &manifest_path_hash[..12])
}

pub fn fetch_metadata(metadata_args: Vec<String>, current_dir: PathBuf) -> Result<Metadata> {
    let mut cmd = MetadataCommand::new();
    cmd.other_options(metadata_args);
    cmd.current_dir(current_dir);
    let metadata = cmd.exec()?;
    Ok(metadata)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_utils::{MockDep, MockPackage, MockWorkspace};

    #[test]
    fn metadata_index_duplicate_dep_names() {
        let workspace = MockWorkspace::new()
            .members([
                MockPackage::new("serde-core").version("1.0.0").lib(),
                MockPackage::new("serde").version("1.0.0").lib(),
                MockPackage::new("consumer")
                    .lib()
                    .deps([MockDep::registry("serde-core", "1.0.0").alias("serde")])
                    .target_deps(
                        "cfg(any())",
                        [MockDep::registry("serde", "1.0.0").alias("serde")],
                    ),
            ])
            .materialize();

        let manifest_path: String =
            workspace.path().join("Cargo.toml").to_string_lossy().to_string();

        let metadata = fetch_metadata(
            vec!["--offline".to_string(), "--manifest-path".to_string(), manifest_path],
            workspace.path().to_path_buf(),
        )
        .unwrap();

        let _index = MetadataIndex::new(&metadata).unwrap();
    }

    #[test]
    fn transitive_verified_import_names_walks_closure() {
        let workspace = MockWorkspace::new()
            .members([
                MockPackage::new("deeper").lib().verify(true),
                MockPackage::new("mid").lib().verify(true).deps([MockDep::workspace("deeper")]),
                MockPackage::new("not_verified")
                    .lib()
                    .verify(false)
                    .deps([MockDep::workspace("deeper")]),
                MockPackage::new("consumer").lib().verify(true).deps([
                    MockDep::path("mid", "../mid").alias("renamed"),
                    MockDep::workspace("not_verified"),
                ]),
            ])
            .materialize();

        let manifest_path: String =
            workspace.path().join("Cargo.toml").to_string_lossy().to_string();
        let metadata = fetch_metadata(
            vec!["--manifest-path".to_string(), manifest_path],
            workspace.path().to_path_buf(),
        )
        .unwrap();
        let index = MetadataIndex::new(&metadata).unwrap();

        let consumer_id = &metadata
            .packages
            .iter()
            .find(|p| p.name.as_str() == "consumer")
            .expect("consumer package")
            .id;

        let mut names = index.transitive_verified_import_names(consumer_id);
        names.sort();

        // - `mid` (a direct verified dep) is emitted using the consumer-side
        //   alias `renamed`, not the package name `mid`.
        // - `deeper` (a deeper verified dep, only reachable through `mid` /
        //   `not_verified`) is emitted using its lib target name. It appears
        //   exactly once even though two paths reach it.
        // - `not_verified` is not emitted, but the walk still descends into
        //   its deps to reach `deeper`.
        assert_eq!(names, vec!["deeper".to_string(), "renamed".to_string()]);
    }
}
