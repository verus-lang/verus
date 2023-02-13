use crate::config::Args;
use crate::verifier::io_vir_err;
use vir::ast::{Krate, VirErr};

pub(crate) fn import_crates(
    args: &Args,
    crate_names: &mut Vec<String>,
    vir_crates: &mut Vec<Krate>,
) -> Result<(), VirErr> {
    for (crate_name, file_path) in &args.import {
        crate_names.push(crate_name.clone());
        let buf = match std::fs::read(file_path) {
            Ok(file) => file,
            Err(err) => {
                return Err(io_vir_err(
                    format!("could not open imported library file `{file_path}`"),
                    err,
                ));
            }
        };
        let libcrate: Krate = bincode::deserialize(&buf).expect("read crate from file");
        // Note: there are also deserializers directly from files, but for some reason,
        // they are much slower:
        //   let libcrate: Krate = bincode::deserialize_from(file).expect("read crate from file");
        //   let libcrate: Krate = serde_json::from_reader(file).expect("read crate from file");
        // We can also look at other packages: https://github.com/djkoloski/rust_serialization_benchmark
        vir_crates.push(libcrate);
    }
    Ok(())
}

pub(crate) fn export_crate(args: &Args, vir_crate: &Krate) -> Result<(), VirErr> {
    if let Some(file_path) = &args.export {
        // TODO: we should prune out all non-public data before serializing the crate
        // (it probably doesn't matter much yet, but it will matter as the libraries grow.)
        let file = match std::fs::File::create(file_path) {
            Ok(file) => file,
            Err(err) => {
                return Err(io_vir_err(
                    format!("could not create exported library file `{file_path}`"),
                    err,
                ));
            }
        };
        bincode::serialize_into(file, &vir_crate).expect("write crate to file");
        //serde_json::to_writer(file, &vir_crate).expect("write crate to file");
        //serde_json::to_writer_pretty(file, &vir_crate).expect("write crate to file");
    }
    Ok(())
}
