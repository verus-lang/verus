#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_span;
extern crate rustc_typeck;

use rust_verify::config;
use rust_verify::erase::CompilerCallbacks;
use rust_verify::verifier::Verifier;

#[cfg(target_family = "windows")]
fn os_setup() -> Result<(), Box<dyn std::error::Error>> {
    // Configure Windows to kill the child SMT process if the parent is killed
    let job = win32job::Job::create()?;
    let mut info = job.query_extended_limit_info()?;
    info.limit_kill_on_job_close();
    job.set_extended_limit_info(&mut info)?;
    job.assign_current_process()?;
    // dropping the job object would kill us immediately, so just let it live forever instead:
    std::mem::forget(job);
    Ok(())
}

#[cfg(target_family = "unix")]
fn os_setup() -> Result<(), Box<dyn std::error::Error>> {
    Ok(())
}

// TODO: factor out
struct PervasiveFileLoader {
    pervasive_path: Option<String>,
    real_file_loader: rustc_span::source_map::RealFileLoader,
}

impl PervasiveFileLoader {
    fn remap_pervasive_path(&self, path: &std::path::Path) -> std::path::PathBuf {
        if let Some(pervasive_path) = &self.pervasive_path {
            if path.parent().and_then(|x| x.file_name()) == Some(std::ffi::OsStr::new("pervasive"))
            {
                if let Some(file_name) = path.file_name() {
                    return std::path::Path::new(pervasive_path).join(file_name).into();
                }
            }
        }
        return path.into();
    }
}

impl rustc_span::source_map::FileLoader for PervasiveFileLoader {
    fn file_exists(&self, path: &std::path::Path) -> bool {
        let path = self.remap_pervasive_path(path);
        self.real_file_loader.file_exists(&path)
    }

    fn read_file(&self, path: &std::path::Path) -> Result<String, std::io::Error> {
        let path = self.remap_pervasive_path(path);
        self.real_file_loader.read_file(&path)
    }
}

pub fn main() {
    let _ = os_setup();

    let mut args = std::env::args();
    let program = args.next().unwrap();
    let (our_args, rustc_args) = config::parse_args(&program, args);
    let lifetime = our_args.lifetime;
    let compile = our_args.compile;
    let pervasive_path = our_args.pervasive_path.clone();

    // Run verifier callback to build VIR tree and run verifier

    let mut verifier = Verifier::new(our_args);
    let file_loader = PervasiveFileLoader {
        pervasive_path: pervasive_path.clone(),
        real_file_loader: rustc_span::source_map::RealFileLoader,
    };
    let mut compiler = rustc_driver::RunCompiler::new(&rustc_args, &mut verifier);
    compiler.set_file_loader(Some(Box::new(file_loader)));
    let status = compiler.run();
    if !verifier.encountered_vir_error {
        println!(
            "Verification results:: verified: {} errors: {}",
            verifier.count_verified,
            verifier.errors.len()
        );
    }
    match status {
        Ok(_) => {}
        Err(_) => {
            std::process::exit(1);
        }
    }

    // Run borrow checker with both #[code] and #[proof]
    if lifetime {
        let erasure_hints = verifier.erasure_hints.clone().expect("erasure_hints");
        let mut callbacks = CompilerCallbacks { erasure_hints, lifetimes_only: true };
        let status = rustc_driver::RunCompiler::new(&rustc_args, &mut callbacks).run();
        match status {
            Ok(_) => {}
            Err(_) => {
                std::process::exit(1);
            }
        }
    }

    // Run borrow checker and compiler on #[code] (if enabled)
    if compile {
        let erasure_hints = verifier.erasure_hints.clone().expect("erasure_hints").clone();
        let mut callbacks = CompilerCallbacks { erasure_hints };
        let file_loader = PervasiveFileLoader {
            pervasive_path: pervasive_path.clone(),
            real_file_loader: rustc_span::source_map::RealFileLoader,
        };
        let mut compiler = rustc_driver::RunCompiler::new(&rustc_args, &mut callbacks);
        compiler.set_file_loader(Some(Box::new(file_loader)));
        compiler.run().expect("RunCompiler.run() failed");
    }
}
