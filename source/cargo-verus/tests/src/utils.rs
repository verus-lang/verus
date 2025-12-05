use serde::Deserialize;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::time::{SystemTime, UNIX_EPOCH};

pub const SINGLE_OPTIN: &str = "single-optin";
pub const SINGLE_OPTOUT: &str = "single-optout";

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
            !self.env.iter().any(|(k, v)| k.starts_with(key_prefix)),
            "Cargo env MUST NOT have a key with prefix {}*",
            key_prefix,
        );
    }
}

pub fn run_cargo_verus(setup: impl Fn(&mut Command)) -> (ExitStatus, CargoData) {
    let data_file = temp_data_file();
    println!("Capturing CargoData to {}", data_file.to_string_lossy());

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("cargo-verus"));
    setup(&mut cmd);
    cmd.env("CARGO", assert_cmd::cargo::cargo_bin!("fake-cargo"));
    cmd.env("FAKE_CARGO_DATA_FILE", &data_file);
    let status = cmd.status().expect("run cargo-verus and get output");

    let cargo_data = read_cargo_data(&data_file);

    (status, cargo_data)
}

pub fn clone_fixture(name: &str) -> PathBuf {
    let fixture = Path::new(FIXTURES_DIR).join(name);
    let dest = temp_fixture_dir(name);

    match fs::remove_dir_all(&dest) {
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => Err(e),
        _ => Ok(()),
    }
    .expect("remove existing destination dir");

    copy_dir(&fixture, &dest).expect("copy fixture to destination dir");

    dest
}

fn temp_fixture_dir(name: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!("cargo-verus-tests-{name}-{}", std::process::id()));
    path
}

fn copy_dir(src: &Path, dst: &Path) -> anyhow::Result<()> {
    fs::create_dir_all(dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        let dest_path = dst.join(entry.file_name());
        if ty.is_dir() {
            copy_dir(&entry.path(), &dest_path)?;
        } else {
            fs::copy(entry.path(), dest_path)?;
        }
    }
    Ok(())
}

fn read_cargo_data(path: &Path) -> CargoData {
    let bytes = fs::read(path).expect(&format!("read CargoData bytes from {:?}", path));
    let data = serde_json::from_slice(&bytes).expect(&format!("parse CargoData from {:?}", path));
    data
}

fn temp_data_file() -> PathBuf {
    let mut path = std::env::temp_dir();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("get duration since Unix Epoch")
        .as_nanos();
    path.push(format!("cargo-verus-tests-data-{}-{nanos}.json", std::process::id()));
    path
}
