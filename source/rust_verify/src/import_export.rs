use crate::config::Args;
use crate::spans::FileStartEndPos;
use crate::verifier::io_vir_err;
use serde::{Deserialize, Serialize};
use vir::ast::{Krate, VirErr};

use std::collections::HashMap;

#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct CrateMetadata {
    pub crate_id: u64,
    pub original_files: HashMap<Vec<u8>, FileStartEndPos>,
}

#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct CrateWithMetadata {
    krate: Krate,
    metadata: CrateMetadata,
}

pub(crate) struct ImportOutput {
    pub(crate) crate_names: Vec<String>,
    pub(crate) vir_crates: Vec<Krate>,
    pub(crate) metadatas: Vec<CrateMetadata>,
}

pub(crate) fn import_crates(args: &Args) -> Result<ImportOutput, VirErr> {
    let mut metadatas = Vec::new();
    let mut crate_names = Vec::new();
    let mut vir_crates = Vec::new();
    for (crate_name, file_path) in &args.import {
        crate_names.push(crate_name.clone());
        let file = std::io::BufReader::new(match std::fs::File::open(file_path) {
            Ok(file) => file,
            Err(err) => {
                return Err(io_vir_err(
                    format!("could not open imported library file `{file_path}`"),
                    err,
                ));
            }
        });
        let CrateWithMetadata { krate, metadata } =
            bincode::deserialize_from(file).expect("read crate from file");
        //   let libcrate: Krate = serde_json::from_reader(file).expect("read crate from file");
        // We can also look at other packages: https://github.com/djkoloski/rust_serialization_benchmark
        vir_crates.push(krate);
        metadatas.push(metadata);
    }
    Ok(ImportOutput { crate_names, vir_crates, metadatas })
}

pub(crate) fn export_crate(
    args: &Args,
    vir_metadata: CrateMetadata,
    vir_crate: Krate,
) -> Result<(), VirErr> {
    if let Some(file_path) = &args.export {
        // TODO: we should prune out all non-public data before serializing the crate
        // (it probably doesn't matter much yet, but it will matter as the libraries grow.)
        let file = std::io::BufWriter::new(match std::fs::File::create(file_path) {
            Ok(file) => file,
            Err(err) => {
                return Err(io_vir_err(
                    format!("could not create exported library file `{file_path}`"),
                    err,
                ));
            }
        });
        let krate_with_metadata = CrateWithMetadata { krate: vir_crate, metadata: vir_metadata };
        bincode::serialize_into(file, &krate_with_metadata).expect("write crate to file");
        //serde_json::to_writer(file, &vir_crate).expect("write crate to file");
        //serde_json::to_writer_pretty(file, &vir_crate).expect("write crate to file");
    }
    Ok(())
}
