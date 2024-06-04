use std::collections::{BTreeMap, BTreeSet};
use std::env::{self, VarError};
use std::path::PathBuf;

use rustc_span::symbol::Symbol;

use crate::callback_utils::ConfigCallback;

#[derive(Debug, Default)]
pub(crate) struct DepTracker {
    env: BTreeMap<String, Option<String>>,
    files: BTreeSet<PathBuf>,
}

impl DepTracker {
    pub(crate) fn get_env(&mut self, var: &str) -> Option<String> {
        let val = match env::var(var) {
            Ok(s) => Some(s),
            Err(VarError::NotPresent) => None,
            Err(VarError::NotUnicode(invalid)) => panic!(
                "the value of environment variable {var:?} is not value unicode: {invalid:?}"
            ),
        };
        self.env.insert(var.to_owned(), val.clone());
        val
    }

    pub(crate) fn compare_env(&mut self, var: &str, val: &str) -> bool {
        self.get_env(var).as_deref() == Some(val)
    }

    pub(crate) fn mark_file(&mut self, path: PathBuf) {
        self.files.insert(path);
    }
}

#[derive(Clone)]
pub(crate) struct DepTrackerConfigCallback<T> {
    dep_tracker: T,
}

impl<T> DepTrackerConfigCallback<T> {
    pub(crate) fn new(dep_tracker: T) -> Self {
        Self { dep_tracker }
    }
}

impl<T: AsRef<DepTracker> + Clone + Send + 'static> ConfigCallback for DepTrackerConfigCallback<T> {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        let dep_tracker = self.dep_tracker.clone();
        config.parse_sess_created = Some(Box::new(move |psess| {
            for (var, val) in dep_tracker.as_ref().env.iter() {
                psess
                    .env_depinfo
                    .get_mut()
                    .insert((Symbol::intern(var), val.as_deref().map(Symbol::intern)));
            }
            for path in dep_tracker.as_ref().files.iter() {
                psess.file_depinfo.get_mut().insert(Symbol::intern(
                    path.to_str().unwrap_or_else(|| panic!("path {path:?} is not valid unicode")),
                ));
            }
        }));
    }
}
