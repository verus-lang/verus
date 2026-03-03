use std::collections::BTreeMap;
use std::path::Path;

use serde::Serialize;

#[derive(Serialize)]
struct CargoData {
    args: Vec<String>,
    env: BTreeMap<String, String>,
}

fn main() {
    if is_subcommand("metadata") {
        let status = std::process::Command::new("cargo")
            .args(std::env::args().skip(1))
            .status()
            .expect("run real cargo");

        std::process::exit(status.code().unwrap_or(1));
    }

    let path = std::env::var_os("FAKE_CARGO_DATA_FILE").expect("read env var FAKE_CARGO_DATA_FILE");
    let data =
        CargoData { args: std::env::args().skip(1).collect(), env: std::env::vars().collect() };
    write_data(Path::new(&path), &data);
}

fn is_subcommand(name: &str) -> bool {
    match std::env::args().skip(1).next() {
        Some(command) => command == name,
        None => false,
    }
}

fn write_data(path: &Path, data: &CargoData) {
    let mut json = serde_json::to_vec(data).expect("serialize CargoData to JSON");
    json.push(b'\n');
    std::fs::write(path, json).expect(&format!("write CargoData JSON to {:?}", path))
}
