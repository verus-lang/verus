fn main() {
    let mut args = std::env::args();
    let _program = args.next();
    match args.next().as_deref() {
        Some("metadata") => {
            let real_cargo = std::env::var("FAKE_CARGO_REAL").unwrap_or_else(|_| "cargo".into());
            let status = std::process::Command::new(real_cargo)
                .arg("metadata")
                .args(args)
                .status()
                .expect("failed to run real cargo metadata");
            std::process::exit(status.code().unwrap_or(1));
        }
        _ => {
            println!("FAKE-CARGO");
        }
    }
}
