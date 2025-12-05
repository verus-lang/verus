use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

pub const SINGLE_CRATE: &str = "single-crate";

const FIXTURES_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures");

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

pub fn run_cargo_verus_verify(manifest_path: &Path) -> std::process::Output {
    Command::new(assert_cmd::cargo::cargo_bin!("cargo-verus"))
        .arg("verify")
        .arg("--manifest-path")
        .arg(manifest_path)
        .env("CARGO", assert_cmd::cargo::cargo_bin!("fake-cargo"))
        .output()
        .expect("failed to run cargo-verus")
}
