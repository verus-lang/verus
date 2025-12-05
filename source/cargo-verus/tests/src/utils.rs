use serde::Deserialize;
use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{SystemTime, UNIX_EPOCH};

pub const SINGLE_CRATE: &str = "single-crate";

const FIXTURES_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures");

#[derive(Debug, Deserialize)]
pub struct CargoData {
    pub args: Vec<String>,
    pub env: BTreeMap<String, String>,
}

pub fn run_cargo_verus(setup: impl Fn(&mut Command)) -> anyhow::Result<(Output, CargoData)> {
    let data_file = temp_data_file()?;

    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("cargo-verus"));
    setup(&mut cmd);
    cmd.env("CARGO", assert_cmd::cargo::cargo_bin!("fake-cargo"));
    cmd.env("FAKE_CARGO_DATA_FILE", &data_file);
    let output = cmd.output()?;

    let cargo_data = read_cargo_data(&data_file)?;

    Ok((output, cargo_data))
}

pub fn clone_fixture(name: &str) -> PathBuf {
    let fixture = Path::new(FIXTURES_DIR).join(name);
    let dest = temp_fixture_dir(name);
    let _ = fs::remove_dir_all(&dest);
    copy_dir(&fixture, &dest).expect("failed to copy fixture to temp dir");
    dest
}

fn temp_fixture_dir(name: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!("cargo-verus-tests-{name}-{}", std::process::id()));
    path
}

fn copy_dir(src: &Path, dst: &Path) -> io::Result<()> {
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

fn read_cargo_data(path: &Path) -> anyhow::Result<CargoData> {
    let bytes = fs::read(path)?;
    let data = serde_json::from_slice(&bytes)?;
    Ok(data)
}

fn temp_data_file() -> anyhow::Result<PathBuf> {
    let mut path = std::env::temp_dir();
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH)?.as_nanos();
    path.push(format!("cargo-verus-tests-data-{}-{nanos}.json", std::process::id()));
    Ok(path)
}
