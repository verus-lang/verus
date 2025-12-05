use std::collections::BTreeMap;
use std::path::Path;

use serde::Serialize;

#[derive(Serialize)]
struct CargoData {
    args: Vec<String>,
    env: BTreeMap<String, String>,
}

fn main() {
    let mut args_iter = std::env::args();
    let _program = args_iter.next();
    let args: Vec<String> = args_iter.collect();

    if let Some(path) = std::env::var_os("FAKE_CARGO_DATA_FILE") {
        let data = CargoData { args: args.clone(), env: std::env::vars().collect() };
        if let Err(err) = write_data(Path::new(&path), &data) {
            eprintln!("fake-cargo failed to write data: {err}");
            std::process::exit(1);
        }
    }

    match args.split_first() {
        Some((cmd, rest)) if cmd == "metadata" => {
            let real_cargo = std::env::var("FAKE_CARGO_REAL").unwrap_or_else(|_| "cargo".into());
            let status = std::process::Command::new(real_cargo)
                .arg("metadata")
                .args(rest)
                .status()
                .expect("failed to run real cargo metadata");
            std::process::exit(status.code().unwrap_or(1));
        }
        _ => {
            println!("FAKE-CARGO");
        }
    }
}

fn write_data(path: &Path, data: &CargoData) -> std::io::Result<()> {
    let json = serde_json::to_vec(data).expect("failed to serialize CargoData");
    std::fs::write(path, json)
}
