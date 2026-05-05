use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use crate::subcommands::CargoRunPlan;

pub use crate::subcommands::{
    CARGO_DEFAULT_LIB_METADATA, RUSTC_WRAPPER, VERUS_DRIVER_ARGS, VERUS_DRIVER_ARGS_FOR,
    VERUS_DRIVER_ARGS_SEP, VERUS_DRIVER_IS_BUILTIN, VERUS_DRIVER_IS_BUILTIN_MACROS,
    VERUS_DRIVER_VERIFY, VERUS_DRIVER_VIA_CARGO,
};

pub struct MockWorkspace {
    members: Vec<MockPackage>,
}

pub struct MockPackage {
    name: String,
    version: String,
    has_lib: bool,
    bin_names: Vec<String>,
    example_names: Vec<String>,
    deps: Vec<(DepKind, Option<String>, MockDep)>,
    features: Vec<String>,
    verus_verify: Option<bool>,
}

#[derive(Clone)]
pub struct MockDep {
    alias: Option<String>,
    package: String,
    source: DepSource,
}

#[derive(Clone)]
enum DepSource {
    Registry { version: String },
    Path(String),
    Workspace,
}

impl MockDep {
    pub fn registry(package: &str, version: &str) -> Self {
        Self {
            alias: None,
            package: package.to_owned(),
            source: DepSource::Registry { version: version.to_owned() },
        }
    }

    pub fn path(package: &str, path: &str) -> Self {
        Self { alias: None, package: package.to_owned(), source: DepSource::Path(path.to_owned()) }
    }

    pub fn workspace(package: &str) -> Self {
        Self { alias: None, package: package.to_owned(), source: DepSource::Workspace }
    }

    pub fn alias(mut self, alias: &str) -> Self {
        self.alias = Some(alias.to_owned());
        self
    }
}

#[derive(Clone, Copy)]
enum DepKind {
    Normal,
    Build,
    Dev,
}

impl MockWorkspace {
    pub fn new() -> Self {
        MockWorkspace { members: vec![] }
    }

    pub fn members(mut self, packages: impl IntoIterator<Item = MockPackage>) -> Self {
        self.members.extend(packages);
        self
    }

    pub fn materialize(self) -> tempfile::TempDir {
        let root = tempfile::tempdir().expect("create temp dir");

        let mut member_names = vec![];
        for member in self.members {
            let name = member.name.clone();
            let package_dir = root.path().join(&name);
            std::fs::create_dir(&package_dir).expect("create package dir {package_dir:?}");
            member.materialize_in_dir(&package_dir);
            member_names.push(name);
        }

        let mut manifest_lines = vec!["[workspace]".to_owned()];
        manifest_lines.push("net.offline = true".to_owned());

        manifest_lines.push("members = [".to_owned());
        for name in &member_names {
            manifest_lines.push(format!("    \"{name}\","));
        }
        manifest_lines.push("]".to_owned());
        manifest_lines.push("".to_owned());

        manifest_lines.push("[workspace.dependencies]".to_owned());
        for name in &member_names {
            manifest_lines.push(format!("{name} = {{ path = \"{name}\" }}"));
        }
        manifest_lines.push("".to_owned());

        manifest_lines.push("[patch.crates-io]".to_owned());
        for name in &member_names {
            manifest_lines.push(format!("{name} = {{ path = \"{name}\" }}"));
        }
        manifest_lines.push("".to_owned());

        let manifest = root.path().join("Cargo.toml");
        std::fs::write(&manifest, manifest_lines.join("\n"))
            .unwrap_or_else(|_| panic!("write manifest to {manifest:?}"));

        root
    }
}

impl MockPackage {
    pub fn new(name: &str) -> Self {
        MockPackage {
            name: name.to_owned(),
            version: "0.1.0".to_owned(),
            has_lib: false,
            bin_names: vec![],
            example_names: vec![],
            deps: vec![],
            features: vec![],
            verus_verify: None,
        }
    }

    pub fn version(mut self, version: &str) -> Self {
        self.version = version.to_owned();
        self
    }

    pub fn lib(mut self) -> Self {
        self.has_lib = true;
        self
    }

    pub fn bin(mut self, name: &str) -> Self {
        self.bin_names.push(name.to_owned());
        self
    }

    pub fn example(mut self, name: &str) -> Self {
        self.example_names.push(name.to_owned());
        self
    }

    pub fn features(mut self, names: impl IntoIterator<Item = impl AsRef<str>>) -> Self {
        self.features.extend(names.into_iter().map(|n| n.as_ref().to_owned()));
        self
    }

    pub fn deps(mut self, deps: impl IntoIterator<Item = MockDep>) -> Self {
        self.deps.extend(deps.into_iter().map(|d| (DepKind::Normal, None, d)));
        self
    }

    pub fn build_deps(mut self, deps: impl IntoIterator<Item = MockDep>) -> Self {
        self.deps.extend(deps.into_iter().map(|d| (DepKind::Build, None, d)));
        self
    }

    pub fn dev_deps(mut self, deps: impl IntoIterator<Item = MockDep>) -> Self {
        self.deps.extend(deps.into_iter().map(|d| (DepKind::Dev, None, d)));
        self
    }

    pub fn target_deps(mut self, cfg: &str, deps: impl IntoIterator<Item = MockDep>) -> Self {
        self.deps.extend(deps.into_iter().map(|d| (DepKind::Normal, Some(cfg.to_owned()), d)));
        self
    }

    pub fn verify(mut self, setting: bool) -> Self {
        self.verus_verify = Some(setting);
        self
    }

    pub fn materialize(self) -> tempfile::TempDir {
        let root = tempfile::tempdir().expect("create temp dir");
        self.materialize_in_dir(root.path());
        root
    }

    pub fn materialize_in_dir(self, root: &Path) {
        let mut manifest_lines: Vec<String> = vec![
            "[package]".to_owned(),
            "publish = false".to_owned(),
            format!("name = \"{}\"", self.name),
            format!("version = \"{}\"", self.version),
            "edition = \"2021\"".to_owned(),
            "".to_owned(),
        ];

        let mut normal = vec![];
        let mut build = vec![];
        let mut dev = vec![];
        let mut targets: BTreeMap<String, Vec<String>> = Default::default();
        for (kind, cfg, dep) in self.deps {
            let name = dep.alias.as_ref().unwrap_or(&dep.package);
            let package_part = dep
                .alias
                .as_ref()
                .map(|_| format!("package = \"{}\",", dep.package))
                .unwrap_or(String::new());
            let entry = match dep.source {
                DepSource::Workspace => {
                    format!("{name} = {{ {package_part} workspace = true }}")
                }
                DepSource::Path(path) => {
                    format!("{name} = {{ {package_part} path = \"{}\" }}", path)
                }
                DepSource::Registry { version } => {
                    format!("{name} = {{ {package_part} version = \"{}\" }}", version)
                }
            };

            match (kind, cfg) {
                (DepKind::Normal, None) => normal.push(entry),
                (DepKind::Build, None) => build.push(entry),
                (DepKind::Dev, None) => dev.push(entry),
                (DepKind::Normal, Some(cfg)) => {
                    targets.entry(cfg).or_default().push(entry);
                }
                (DepKind::Build, Some(_)) => {
                    unimplemented!()
                }
                (DepKind::Dev, Some(_)) => {
                    unimplemented!()
                }
            }
        }

        if !normal.is_empty() {
            manifest_lines.push("[dependencies]".to_owned());
            manifest_lines.extend(normal);
            manifest_lines.push("".to_owned());
        }

        if !build.is_empty() {
            manifest_lines.push("[build-dependencies]".to_owned());
            manifest_lines.extend(build);
            manifest_lines.push("".to_owned());
        }

        if !dev.is_empty() {
            manifest_lines.push("[dev-dependencies]".to_owned());
            manifest_lines.extend(dev);
            manifest_lines.push("".to_owned());
        }

        for (cfg, entries) in targets {
            manifest_lines.push(format!("[target.'{}'.dependencies]", cfg));
            manifest_lines.extend(entries);
            manifest_lines.push("".to_owned());
        }

        if !self.features.is_empty() {
            manifest_lines.push("[features]".to_owned());
            manifest_lines.extend(self.features);
            manifest_lines.push("".to_owned());
        }

        if let Some(verus_verify) = self.verus_verify {
            manifest_lines.push("[package.metadata.verus]".to_owned());
            manifest_lines.push(format!("verify = {verus_verify}"));
            manifest_lines.push("".to_owned());
        }

        let manifest = root.join("Cargo.toml");
        std::fs::write(&manifest, manifest_lines.join("\n"))
            .unwrap_or_else(|_| panic!("write manifest to {manifest:?}"));

        if !self.has_lib || self.bin_names.is_empty() {
            let src = root.join("src");
            fs::create_dir(&src).expect("create dir {src}");

            if self.has_lib {
                let lib = src.join("lib.rs");
                std::fs::write(&lib, "").unwrap_or_else(|_| panic!("write {lib:?}"));
            }

            for name in self.bin_names {
                let bin = src.join(format!("{name}.rs"));
                std::fs::write(&bin, "").unwrap_or_else(|_| panic!("write {bin:?}"));
            }
        }

        if !self.example_names.is_empty() {
            let examples = root.join("examples");
            fs::create_dir(&examples).expect("create dir {examples}");

            for name in self.example_names {
                let example = examples.join(format!("{name}.rs"));
                std::fs::write(&example, "fn main() {}")
                    .unwrap_or_else(|_| panic!("write {example:?}"));
            }
        }
    }
}

impl CargoRunPlan {
    pub fn assert_env_has(&self, key: &str) {
        assert!(self.env.contains_key(key), "Cargo env MUST have key {}", key);
    }

    pub fn assert_env_sets(&self, key: &str, value: &str) {
        assert_eq!(
            self.env.get(key).map(String::as_str),
            Some(value),
            "Cargo env MUST have entry {} = {}",
            key,
            value,
        );
    }

    pub fn assert_env_sets_key_prefix(&self, key_prefix: &str, value: &str) {
        assert!(
            self.env.iter().any(|(k, v)| k.starts_with(key_prefix) && v == value),
            "Cargo env MUST have entry with key prefix {}* = {}",
            key_prefix,
            value,
        );
    }

    pub fn assert_env_has_no_key_prefix(&self, key_prefix: &str) {
        assert!(
            !self.env.keys().any(|k| k.starts_with(key_prefix)),
            "Cargo env MUST NOT have a key with prefix {}*",
            key_prefix,
        );
    }

    pub fn parse_driver_args(&self, key: &str) -> Vec<&str> {
        let encoded_args =
            self.env.get(key).unwrap_or_else(|| panic!("retrieve env var `{}`", key));
        encoded_args.split(VERUS_DRIVER_ARGS_SEP).collect()
    }

    pub fn parse_driver_args_for_key_prefix(&self, key_prefix: &str) -> Vec<&str> {
        let Some((_, value)) = self.env.iter().find(|(k, _)| k.starts_with(key_prefix)) else {
            return vec![];
        };
        value.split(VERUS_DRIVER_ARGS_SEP).collect()
    }
}
