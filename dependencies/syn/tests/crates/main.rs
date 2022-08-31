// Run parser on contents of all *.crate files in a specified directory. This is
// intended to discover panics in syn or its dependencies.
//
//    cargo run --release -- path/to/crates
//
// Published *.crate files from crates.io can be downloaded like this:
//
//    git clone https://github.com/rust-lang/crates.io-index
//    grep -hr . crates.io-index/*/ \
//        | jq '"https://static.crates.io/crates/" + .name + "/" + .name + "-" + .vers + ".crate"' -r \
//        | xargs -P10 -n100 wget -nc

#![allow(clippy::let_underscore_drop)]

use anyhow::{ensure, Result};
use flate2::read::GzDecoder;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rayon::ThreadPoolBuilder;
use std::env;
use std::ffi::OsStr;
use std::fs::{self, File};
use std::io::{BufReader, Read};
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use tar::Archive;

fn main() -> Result<()> {
    let mut args = env::args_os();
    ensure!(args.len() == 2);
    args.next().unwrap();
    let dir = args.next().unwrap();

    let mut paths = Vec::new();
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.extension() == Some(OsStr::new("crate")) {
            paths.push(path);
        }
    }

    ThreadPoolBuilder::new()
        .stack_size(20 * 1024 * 1024)
        .build_global()
        .unwrap();

    let oversize_count = AtomicUsize::new(0);
    paths.par_iter().for_each(|path| {
        if let Err(err) = parse(path, &oversize_count) {
            eprintln!("{}: {}", path.display(), err);
        }
    });

    let oversize_count = oversize_count.into_inner();
    if oversize_count > 0 {
        eprintln!("{} oversized source files not checked", oversize_count);
    }

    Ok(())
}

fn parse(path: &Path, oversize_count: &AtomicUsize) -> Result<()> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    let tar = GzDecoder::new(reader);
    let mut archive = Archive::new(tar);
    for entry in archive.entries()? {
        let mut entry = entry?;
        if entry.size() > 10 * 1024 * 1024 {
            oversize_count.fetch_add(1, Ordering::Relaxed);
            continue;
        }
        let path = entry.path()?;
        if path.extension() != Some(OsStr::new("rs")) {
            continue;
        }
        let mut contents = String::new();
        if entry.read_to_string(&mut contents).is_err() {
            break;
        }
        let _ = syn::parse_file(&contents);
    }
    Ok(())
}
