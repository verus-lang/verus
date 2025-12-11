use serde::Deserialize;
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::process::{Command, ExitStatus};

pub const MEMBER_OPTIN: &str = "member-optin";
pub const MEMBER_OPTOUT: &str = "member-optout";
pub const MEMBER_UNSET: &str = "member-unset";
pub const MEMBER_HASDEPS: &str = "member-hasdeps";

const FIXTURES_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures");

#[derive(Debug, Deserialize)]
pub struct CargoData {
    pub args: Vec<String>,
    pub env: BTreeMap<String, String>,
}

impl CargoData {
    pub fn assert_env_has(&self, key: &str) {
        assert!(self.env.contains_key(key), "Cargo env MUST have key {}", key);
    }

    pub fn assert_env_sets(&self, key: &str, value: &str) {
        assert_eq!(
            self.env.get(key).map(String::as_str),
            Some(value),
            "Cargo env MUST have entry {} = {}",
            key,
            value,
        );
    }

    pub fn assert_env_sets_key_prefix(&self, key_prefix: &str, value: &str) {
        assert!(
            self.env.iter().any(|(k, v)| k.starts_with(key_prefix) && v == value),
            "Cargo env MUST have entry with key prefix {}* = {}",
            key_prefix,
            value,
        );
    }

    pub fn assert_env_has_no_key_prefix(&self, key_prefix: &str) {
        assert!(
            !self.env.keys().any(|k| k.starts_with(key_prefix)),
            "Cargo env MUST NOT have a key with prefix {}*",
            key_prefix,
        );
    }
}

pub fn run_cargo_verus(setup: impl Fn(&mut Command)) -> (ExitStatus, CargoData) {
    let temp_dir = tempfile::tempdir().expect("create temp dir for CargoData JSON");
    let data_file = temp_dir.path().join("CargoData.json");
    println!("Capturing CargoData to {:?}", &data_file);

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("cargo-verus"));
    setup(&mut cmd);
    cmd.env("CARGO", assert_cmd::cargo::cargo_bin!("fake-cargo"));
    cmd.env("FAKE_CARGO_DATA_FILE", &data_file);
    let status = cmd.status().expect("run cargo-verus and get output");

    let cargo_data = read_cargo_data(&data_file);

    (status, cargo_data)
}

pub struct MockPackage {
    name: String,
    has_lib: bool,
    bin_names: Vec<String>,
    dep_names: Vec<String>,
    verus_verify: Option<bool>,
}

impl MockPackage {
    pub fn new(name: &str) -> Self {
        MockPackage {
            name: name.to_owned(),
            has_lib: false,
            bin_names: vec![],
            dep_names: vec![],
            verus_verify: None,
        }
    }

    pub fn lib(mut self) -> Self {
        self.has_lib = true;
        self
    }

    pub fn bin(mut self, name: &str) -> Self {
        self.bin_names.push(name.to_owned());
        self
    }

    pub fn dep(mut self, name: &str) -> Self {
        self.dep_names.push(name.to_owned());
        self
    }

    pub fn verify(mut self, setting: bool) -> Self {
        self.verus_verify = Some(setting);
        self
    }

    pub fn materialize(self) -> tempfile::TempDir {
        let root = tempfile::tempdir().expect("create temp dir");
        self.materialize_in_dir(root.path());
        root
    }

    fn materialize_in_dir(self, root: &Path) {
        let mut manifest_lines: Vec<String> = vec![
            format!("[package]"),
            format!("publish = false"),
            format!("name = \"{}\"", self.name),
            format!("version = \"0.1.0\""),
            format!("edition = \"2021\""),
            format!(""),
        ];

        manifest_lines.push(format!("[dependencies]"));
        for name in self.dep_names {
            manifest_lines.push(format!("{name} = {{ workspace = true }}"));
        }
        manifest_lines.push(format!(""));

        if let Some(verus_verify) = self.verus_verify {
            manifest_lines.push(format!("[package.metadata.verus]"));
            manifest_lines.push(format!("verify = {verus_verify}"));
            manifest_lines.push(format!(""));
        }

        let manifest = root.join("Cargo.toml");
        std::fs::write(&manifest, manifest_lines.join("\n"))
            .expect(&format!("write manifest to {manifest:?}"));

        if !self.has_lib || self.bin_names.is_empty() {
            let src = root.join("src");
            fs::create_dir(&src).expect("create dir {src}");

            if self.has_lib {
                let lib = src.join("lib.rs");
                std::fs::write(&lib, "").expect(&format!("write {lib:?}"));
            }

            for name in self.bin_names {
                let bin = src.join(format!("{name}.rs"));
                std::fs::write(&bin, "").expect(&format!("write {bin:?}"));
            }
        }
    }
}

pub struct MockWorkspace {
    members: Vec<MockPackage>,
}

impl MockWorkspace {
    pub fn new() -> Self {
        MockWorkspace { members: vec![] }
    }

    pub fn member(mut self, package: MockPackage) -> Self {
        self.members.push(package);
        self
    }

    pub fn materialize(self) -> tempfile::TempDir {
        let root = tempfile::tempdir().expect("create temp dir");

        let mut member_names = vec![];
        for member in self.members {
            let name = member.name.clone();
            let package_dir = root.path().join(&name);
            std::fs::create_dir(&package_dir).expect("create package dir {package_dir:?}");
            member.materialize_in_dir(&package_dir);
            member_names.push(name);
        }

        let mut manifest_lines = vec![format!("[workspace]")];

        manifest_lines.push(format!("members = ["));
        for name in &member_names {
            manifest_lines.push(format!("    \"{name}\","));
        }
        manifest_lines.push(format!("]"));
        manifest_lines.push(format!(""));

        manifest_lines.push(format!("[workspace.dependencies]"));
        for name in &member_names {
            manifest_lines.push(format!("{name} = {{ path = \"{name}\" }}"));
        }
        manifest_lines.push(format!(""));

        let manifest = root.path().join("Cargo.toml");
        std::fs::write(&manifest, manifest_lines.join("\n"))
            .expect(&format!("write manifest to {manifest:?}"));

        root
    }
}

fn read_cargo_data(path: &Path) -> CargoData {
    let bytes = fs::read(path).expect(&format!("read CargoData bytes from {:?}", path));
    let data = serde_json::from_slice(&bytes).expect(&format!("parse CargoData from {:?}", path));
    data
}
