use std::collections::BTreeMap;

use anyhow::{Context, Result};
use cargo_metadata::{Metadata, MetadataCommand, Package, PackageId};
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

    pub fn entries(&self) -> impl Iterator<Item = &MetadataIndexEntry<'a>> {
        self.entries.values()
    }
}

impl<'a> MetadataIndexEntry<'a> {
    pub fn package(&self) -> &'a Package {
        self.package
    }

    pub fn verus_metadata(&self) -> &VerusMetadata {
        &self.verus_metadata
    }

    pub fn deps(&self) -> impl Iterator<Item = &&'a cargo_metadata::NodeDep> {
        self.deps.values()
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

pub fn fetch_metadata(metadata_args: &[String]) -> Result<Metadata> {
    let mut cmd = MetadataCommand::new();
    cmd.other_options(metadata_args.to_owned());
    let metadata = cmd.exec()?;
    Ok(metadata)
}
