#[cfg(target_os = "macos")]
mod lib_exe_names {
    pub const LIB_PRE: &str = "lib";
    pub const LIB_DL: &str = "dylib";
}

#[cfg(target_os = "linux")]
mod lib_exe_names {
    pub const LIB_PRE: &str = "lib";
    pub const LIB_DL: &str = "so";
}

#[cfg(target_os = "windows")]
mod lib_exe_names {
    pub const LIB_PRE: &str = "";
    pub const LIB_DL: &str = "dll";
}

use lib_exe_names::{LIB_DL, LIB_PRE};

#[derive(Debug)]
pub struct VerusExterns {
    pub verus_root: std::path::PathBuf,
    pub has_vstd: bool,
    pub has_builtin: bool,
}

pub enum VerusExtern {
    Macros,
    Builtin,
    Vstd,
}

fn verus_builtin_std() -> Box<[(VerusExtern, &'static str, String)]> {
    vec![
        (
            VerusExtern::Macros,
            "verus_builtin_macros",
            format!("{LIB_PRE}verus_builtin_macros.{LIB_DL}"),
        ),
        (
            VerusExtern::Macros,
            "verus_state_machines_macros",
            format!("{LIB_PRE}verus_state_machines_macros.{LIB_DL}"),
        ),
        (VerusExtern::Builtin, "verus_builtin", format!("libverus_builtin.rlib")),
        (VerusExtern::Vstd, "vstd", format!("libvstd.rlib")),
    ]
    .into_boxed_slice()
}

impl VerusExterns {
    pub fn to_args(&self) -> impl Iterator<Item = String> + use<> {
        let mut args = Vec::new();
        args.push(format!("-L"));
        args.push(format!("dependency={}", self.verus_root.to_str().unwrap()));
        for (extern_, name, file) in verus_builtin_std().iter() {
            match extern_ {
                VerusExtern::Macros => {}
                VerusExtern::Builtin => {
                    if !self.has_builtin {
                        continue;
                    }
                }
                VerusExtern::Vstd => {
                    if !self.has_vstd {
                        continue;
                    }
                }
            }
            let path = self.verus_root.join(file);
            let path = path.to_str().unwrap();
            args.push(format!("--extern"));
            args.push(format!("{}={}", name, path));
        }
        args.into_iter()
    }

    pub fn to_path_mappings(&self) -> Box<[(String, std::path::PathBuf)]> {
        let mut args = Vec::new();
        for (extern_, name, _file) in verus_builtin_std().iter() {
            match extern_ {
                VerusExtern::Macros => {}
                VerusExtern::Builtin => {
                    if !self.has_builtin {
                        continue;
                    }
                }
                VerusExtern::Vstd => {
                    if !self.has_vstd {
                        continue;
                    }
                }
            }
            let path = self.verus_root.join(name);
            args.push((name.to_string(), path));
        }
        args.into_boxed_slice()
    }
}
