fn main() {
    if let Err(e) = mcdc::cli::run() {
        eprintln!("mcdc: {}", e);
        std::process::exit(2);
    }
}
