use std::collections::{HashMap, HashSet};
use vir::{
    ast::{Fun, Krate, Path},
    ast_util::fun_as_friendly_rust_name,
};

// A "bucket" is a group of functions that are processed together
// with the same pruning context.
//
// In general, a bucket can be an arbitrary subset of a module (we need visibility
// to be coherent for a single bucket, so a bucket cannot be cross-module).
//
// More precisely, we determine the buckets based off the spinoff_prover attribute
// (see get_buckets).

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum BucketId {
    /// Bucket for everything in the given module (except for any functions that
    /// get their own bucket)
    Module(Path),
    /// Bucket contains a single function (the Path is for the owning module)
    Fun(Path, Fun),
}

#[derive(Clone, Debug)]
pub struct Bucket {
    pub funs: HashSet<Fun>,
}

impl BucketId {
    pub fn to_log_string(&self) -> String {
        match self {
            BucketId::Module(m) => {
                if m.segments.len() == 0 {
                    "root".to_string()
                } else {
                    m.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("__")
                }
            }
            BucketId::Fun(_, f) => {
                f.path.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("__")
            }
        }
    }

    pub fn friendly_name(&self) -> String {
        let module = self.module();
        let mstring = if module.segments.len() == 0 {
            "root module".to_string()
        } else {
            "module ".to_string()
                + &module.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("::")
        };
        match self {
            BucketId::Module(_) => mstring,
            BucketId::Fun(_, f) => {
                format!("{}, function {}", mstring, fun_as_friendly_rust_name(f),)
            }
        }
    }

    /// Get the module for this bucket.
    pub fn module(&self) -> &Path {
        match self {
            BucketId::Module(module) => module,
            BucketId::Fun(module, _) => module,
        }
    }

    /// Get the exact function in this bucket, if it is a singleton bucket.
    pub fn function(&self) -> Option<&Fun> {
        match self {
            BucketId::Module(_) => None,
            BucketId::Fun(_, f) => Some(f),
        }
    }
}

impl Bucket {
    pub fn contains(&self, fun: &Fun) -> bool {
        self.funs.contains(fun)
    }
}

/// Arrange the given modules into buckets.
/// Typically, this means 1 bucket per module;
/// However, any functions marked 'spinoff_prover' get their own bucket.
pub fn get_buckets(
    krate: &Krate,
    modules_to_verify: &Vec<vir::ast::Module>,
) -> Vec<(BucketId, Bucket)> {
    let mut map: HashMap<BucketId, Vec<Fun>> = HashMap::new();
    let module_set: HashSet<&Path> = modules_to_verify.iter().map(|m| &m.x.path).collect();
    for func in &krate.functions {
        if let Some(owning_module) = &func.x.owning_module {
            if module_set.contains(owning_module) {
                let bucket_id = if func.x.attrs.spinoff_prover {
                    BucketId::Fun(owning_module.clone(), func.x.name.clone())
                } else {
                    BucketId::Module(owning_module.clone())
                };

                if !map.contains_key(&bucket_id) {
                    map.insert(bucket_id.clone(), vec![]);
                }
                map.get_mut(&bucket_id).unwrap().push(func.x.name.clone());
            }
        }
    }

    // Sorting this way puts all the modules first, and individual spinoffs last
    let mut buckets: Vec<_> = map.into_iter().collect();
    buckets.sort_by_key(|kv| kv.0.clone());

    buckets
        .into_iter()
        .map(|(bucket_id, vec)| (bucket_id, Bucket { funs: vec.into_iter().collect() }))
        .collect()
}
