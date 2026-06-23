use cargo_metadata::{PackageId, semver::Version};

use cargo_verus::metadata::{MetadataIndex, PackageMetadata, PackageSource, fetch_metadata};
use cargo_verus::test_utils::{MockDep, MockPackage};

use std::str::FromStr;
use std::{collections::BTreeSet as Set, fs, path::PathBuf};

const CRATES_IO_INDEX_URL: &str = "https://github.com/rust-lang/crates.io-index";
const VERUS_GITHUB_URL: &str = "https://github.com/verus-lang/verus";
const VERUS_GITHUB_COMMIT_SHORT: &str = "4c4bed7";
const VERUS_GITHUB_COMMIT_FULL: &str = "4c4bed77b7c5a3dce0a5a8f377d9c26b15c2ba56";
const VSTD_VERSION: &str = "0.0.0-2026-06-14-0213";

#[test]
fn package_depends_on_vstd_directly_via_registry() {
    let package = MockPackage::new("vstd_consumer")
        .lib()
        .deps([MockDep::registry("vstd", VSTD_VERSION).alias("vstd_via_registry")])
        .materialize();

    let expected = vec![PackageMetadata {
        version: Version::from_str(VSTD_VERSION).expect("parse `vstd` version"),
        source: PackageSource::Registry { url: CRATES_IO_INDEX_URL.into() },
    }];

    print_cargo_toml(package.path().join("Cargo.toml"));

    let metadata = fetch_metadata(vec![], package.path().to_owned()).expect("fetch metadata");
    let metadata_index = MetadataIndex::new(&metadata).expect("index metadata");
    let all_packages: Set<PackageId> = metadata_index.iter_package_ids().cloned().collect();

    let observed = metadata_index.collect_vstd_metadata(&all_packages);

    for metadata in &observed {
        println!("version = {:?}", metadata.version.to_string());
        println!("source = {:?}", metadata.source);
        println!();
    }

    assert_eq!(observed, expected);
}

#[test]
fn package_depends_on_vstd_directly_via_git_commit() {
    let package = MockPackage::new("vstd_consumer")
        .lib()
        .deps([MockDep::git("vstd", VERUS_GITHUB_URL, VERUS_GITHUB_COMMIT_SHORT)
            .alias("vstd_via_git_commit")])
        .materialize();

    let expected = vec![PackageMetadata {
        version: Version::from_str(VSTD_VERSION).expect("parse `vstd` version"),
        source: PackageSource::Git {
            url: VERUS_GITHUB_URL.into(),
            rev: Some(VERUS_GITHUB_COMMIT_FULL.into()),
        },
    }];

    print_cargo_toml(package.path().join("Cargo.toml"));

    let metadata = fetch_metadata(vec![], package.path().to_owned()).expect("fetch metadata");
    let metadata_index = MetadataIndex::new(&metadata).expect("index metadata");
    let all_packages: Set<PackageId> = metadata_index.iter_package_ids().cloned().collect();

    let observed = metadata_index.collect_vstd_metadata(&all_packages);

    for metadata in &observed {
        println!("version = {:?}", metadata.version.to_string());
        println!("source = {:?}", metadata.source);
        println!();
    }

    assert_eq!(observed, expected);
}

fn print_cargo_toml(path: PathBuf) {
    let contents = fs::read_to_string(&path).unwrap_or_else(|_| panic!("read {path:?}"));
    println!("== {} ==\n{contents}", path.display());
}
