use serde::Deserialize;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::time::{SystemTime, UNIX_EPOCH};

pub const SINGLE_CRATE: &str = "single-crate";

const FIXTURES_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures");

#[derive(Debug, Deserialize)]
pub struct CargoData {
    pub args: Vec<String>,
    pub env: BTreeMap<String, String>,
}

impl CargoData {
    pub fn has_env_key(&self, key: &str) -> bool {
        self.env.contains_key(key)
    }

    pub fn has_env_entry(&self, key: &str, value: &str) -> bool {
        self.env.get(key).map(String::as_str) == Some(value)
    }
}

pub fn run_cargo_verus(setup: impl Fn(&mut Command)) -> (ExitStatus, CargoData) {
    let data_file = temp_data_file();

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("cargo-verus"));
    setup(&mut cmd);
    cmd.env("CARGO", assert_cmd::cargo::cargo_bin!("fake-cargo"));
    cmd.env("FAKE_CARGO_DATA_FILE", &data_file);
    let status = cmd.status().expect("run cargo-verus and get output");

    let cargo_data = read_cargo_data(&data_file);

    (status, cargo_data)
}

pub fn assert_verus_command_env(data: &CargoData) {
    assert!(data.has_env_entry("__CARGO_DEFAULT_LIB_METADATA", "verus"));
    assert!(data.has_env_entry("__VERUS_DRIVER_VIA_CARGO__", "1"));
    assert!(data.has_env_key("RUSTC_WRAPPER"));
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
