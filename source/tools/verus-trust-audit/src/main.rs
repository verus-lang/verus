use anyhow::Result;
use clap::Parser;
use std::path::PathBuf;

#[derive(Parser)]
#[command(about = "Render an auditable source snapshot from a Verus trust manifest")]
struct Args {
    /// Manifest emitted by Verus with --emit-trust-manifest
    manifest: PathBuf,

    /// Directory in which to write the source snapshot
    output: PathBuf,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let written = verus_trust_audit::render_manifest(&args.manifest, &args.output)?;
    for path in written {
        println!("{}", path.display());
    }
    Ok(())
}
