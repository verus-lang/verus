use std::collections::BTreeMap;
use std::path::Path;

use serde::Serialize;

#[derive(Serialize)]
struct CargoData {
    args: Vec<String>,
    env: BTreeMap<String, String>,
}

fn main() {
    let path = std::env::var_os("FAKE_CARGO_DATA_FILE").expect("read env var FAKE_CARGO_DATA_FILE");
    let data = CargoData { args: std::env::args().collect(), env: std::env::vars().collect() };
    write_data(Path::new(&path), &data);

    let status = std::process::Command::new("cargo")
        .args(std::env::args().skip(1))
        .status()
        .expect("run real cargo");

    match status.code() {
        Some(code) => std::process::exit(code),
        None => {
            // terminated by signal on Unix; pick a nonzero exit
            std::process::exit(1);
        }
    }
}

fn write_data(path: &Path, data: &CargoData) {
    let json = serde_json::to_vec(data).expect("serialize CargoData to JSON");
    std::fs::write(path, json).expect(&format!("write CargoData JSON to {:?}", path))
}
