#[cfg(not(feature = "integration-tests"))]
compile_error!("Enable the `integration-tests` feature to run these tests.");

use serde::Deserialize;
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::process::{Command, ExitStatus};

pub use cargo_verus::test_utils::{MockDep, MockPackage, MockWorkspace};

pub const VERUS_DRIVER_ARGS_SEP: &str = "__VERUS_DRIVER_ARGS_SEP__";

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

    pub fn parse_driver_args(&self, key: &str) -> Vec<&str> {
        let encoded_args = self.env.get(key).expect(&format!("retrieve env var `{}`", key));
        encoded_args.split(VERUS_DRIVER_ARGS_SEP).collect()
    }

    pub fn parse_driver_args_for_key_prefix(&self, key_prefix: &str) -> Vec<&str> {
        let Some((_, value)) = self.env.iter().find(|(k, _)| k.starts_with(key_prefix)) else {
            return vec![];
        };
        value.split(VERUS_DRIVER_ARGS_SEP).collect()
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

fn read_cargo_data(path: &Path) -> CargoData {
    let bytes = fs::read(path).expect(&format!("read CargoData bytes from {:?}", path));
    let data = serde_json::from_slice(&bytes).expect(&format!("parse CargoData from {:?}", path));
    data
}
