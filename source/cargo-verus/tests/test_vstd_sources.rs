use cargo_metadata::{PackageId, semver::Version};

use cargo_verus::metadata::{MetadataIndex, PackageMetadata, PackageSource, fetch_metadata};
use cargo_verus::test_utils::{MockDep, MockPackage, MockWorkspace};

use std::collections::BTreeSet as Set;
use std::str::FromStr;

const CRATES_IO_INDEX_URL: &str = "https://github.com/rust-lang/crates.io-index";
const VERUS_GITHUB_URL: &str = "https://github.com/verus-lang/verus";
const VERUS_GITHUB_COMMIT_SHORT: &str = "4c4bed7";
const VERUS_GITHUB_COMMIT_FULL: &str = "4c4bed77b7c5a3dce0a5a8f377d9c26b15c2ba56";
const VSTD_VERSION: &str = "0.0.0-2026-06-14-0213";

#[test]
fn package_depends_on_vstd_directly_via_registry() {
    let package = MockPackage::new("vstd_consumer")
        .lib()
        .deps([MockDep::registry("vstd", &format!("={VSTD_VERSION}")).alias("vstd_via_registry")])
        .verify(true)
        .materialize();

    let expected = Set::from_iter([PackageMetadata {
        version: Version::from_str(VSTD_VERSION).expect("parse `vstd` version"),
        source: PackageSource::Registry { url: CRATES_IO_INDEX_URL.into() },
    }]);

    let metadata = fetch_metadata(vec![], package.path().to_owned()).expect("fetch metadata");
    let metadata_index = MetadataIndex::new(&metadata).expect("index metadata");
    let all_packages: Set<PackageId> = metadata_index.iter_package_ids().cloned().collect();

    let observed = metadata_index.collect_vstd_metadata(&all_packages);

    assert_eq!(observed, expected);
}

#[test]
fn package_depends_on_vstd_directly_via_git_rev() {
    let package = MockPackage::new("vstd_consumer")
        .lib()
        .deps([MockDep::git_rev("vstd", VERUS_GITHUB_URL, VERUS_GITHUB_COMMIT_SHORT)
            .alias("vstd_via_git_commit")])
        .verify(true)
        .materialize();

    let expected = Set::from_iter([PackageMetadata {
        version: Version::from_str(VSTD_VERSION).expect("parse `vstd` version"),
        source: PackageSource::Git {
            url: VERUS_GITHUB_URL.into(),
            rev: Some(VERUS_GITHUB_COMMIT_FULL.into()),
        },
    }]);

    let metadata = fetch_metadata(vec![], package.path().to_owned()).expect("fetch metadata");
    let metadata_index = MetadataIndex::new(&metadata).expect("index metadata");
    let all_packages: Set<PackageId> = metadata_index.iter_package_ids().cloned().collect();

    let observed = metadata_index.collect_vstd_metadata(&all_packages);

    assert_eq!(observed, expected);
}

#[test]
fn package_depends_on_vstd_directly_via_git_tag() {
    let package = MockPackage::new("vstd_consumer")
        .lib()
        .deps([MockDep::git_tag("vstd", VERUS_GITHUB_URL, "release/0.2026.06.20.911e4e7")
            .alias("vstd_via_git_tag")])
        .verify(true)
        .materialize();

    let expected = Set::from_iter([PackageMetadata {
        version: Version::from_str("0.0.0-2026-06-14-0213").expect("parse `vstd` version"),
        source: PackageSource::Git {
            url: VERUS_GITHUB_URL.into(),
            rev: Some("911e4e70ed8e90888bef4b2e4bc6ce5534e65be4".into()),
        },
    }]);

    let metadata = fetch_metadata(vec![], package.path().to_owned()).expect("fetch metadata");
    let metadata_index = MetadataIndex::new(&metadata).expect("index metadata");
    let all_packages: Set<PackageId> = metadata_index.iter_package_ids().cloned().collect();

    let observed = metadata_index.collect_vstd_metadata(&all_packages);

    assert_eq!(observed, expected);
}

#[test]
fn package_depends_on_vstd_directly_via_path() {
    let workspace = MockWorkspace::new()
        .members([
            MockPackage::new("vstd_consumer")
                .lib()
                .deps([MockDep::path("vstd", "../vstd").alias("vstd_via_path")])
                .verify(true),
            MockPackage::new("vstd").version(VSTD_VERSION).lib().mark_as_vstd(),
        ])
        .materialize();

    let expected = Set::from_iter([PackageMetadata {
        version: Version::from_str(VSTD_VERSION).expect("parse `vstd` version"),
        source: PackageSource::Unsupported,
    }]);

    let metadata = fetch_metadata(vec![], workspace.path().to_owned()).expect("fetch metadata");
    let metadata_index = MetadataIndex::new(&metadata).expect("index metadata");
    let all_packages: Set<PackageId> = metadata_index.iter_package_ids().cloned().collect();

    let observed = metadata_index.collect_vstd_metadata(&all_packages);

    assert_eq!(observed, expected);
}

#[test]
fn package_depends_on_vstd_directly_via_workspace_path() {
    let workspace = MockWorkspace::new()
        .members([
            MockPackage::new("vstd_consumer").lib().deps([MockDep::workspace("vstd")]).verify(true),
            MockPackage::new("vstd").version(VSTD_VERSION).lib().mark_as_vstd(),
        ])
        .materialize();

    let expected = Set::from_iter([PackageMetadata {
        version: Version::from_str(VSTD_VERSION).expect("parse `vstd` version"),
        source: PackageSource::Unsupported,
    }]);

    let metadata = fetch_metadata(vec![], workspace.path().to_owned()).expect("fetch metadata");
    let metadata_index = MetadataIndex::new(&metadata).expect("index metadata");
    let all_packages: Set<PackageId> = metadata_index.iter_package_ids().cloned().collect();

    let observed = metadata_index.collect_vstd_metadata(&all_packages);

    assert_eq!(observed, expected);
}
