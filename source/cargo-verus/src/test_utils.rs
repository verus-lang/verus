use std::fs;
use std::path::Path;

pub struct MockPackage {
    name: String,
    has_lib: bool,
    bin_names: Vec<String>,
    dep_names: Vec<String>,
    verus_verify: Option<bool>,
}

impl MockPackage {
    pub fn new(name: &str) -> Self {
        MockPackage {
            name: name.to_owned(),
            has_lib: false,
            bin_names: vec![],
            dep_names: vec![],
            verus_verify: None,
        }
    }

    pub fn lib(mut self) -> Self {
        self.has_lib = true;
        self
    }

    pub fn bin(mut self, name: &str) -> Self {
        self.bin_names.push(name.to_owned());
        self
    }

    pub fn dep(mut self, name: &str) -> Self {
        self.dep_names.push(name.to_owned());
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
            "version = \"0.1.0\"".to_owned(),
            "edition = \"2021\"".to_owned(),
            "".to_owned(),
        ];

        manifest_lines.push("[dependencies]".to_owned());
        for name in self.dep_names {
            manifest_lines.push(format!("{name} = {{ workspace = true }}"));
        }
        manifest_lines.push("".to_owned());

        if let Some(verus_verify) = self.verus_verify {
            manifest_lines.push("[package.metadata.verus]".to_owned());
            manifest_lines.push(format!("verify = {verus_verify}"));
            manifest_lines.push("".to_owned());
        }

        let manifest = root.join("Cargo.toml");
        std::fs::write(&manifest, manifest_lines.join("\n"))
            .expect(&format!("write manifest to {manifest:?}"));

        if !self.has_lib || self.bin_names.is_empty() {
            let src = root.join("src");
            fs::create_dir(&src).expect("create dir {src}");

            if self.has_lib {
                let lib = src.join("lib.rs");
                std::fs::write(&lib, "").expect(&format!("write {lib:?}"));
            }

            for name in self.bin_names {
                let bin = src.join(format!("{name}.rs"));
                std::fs::write(&bin, "").expect(&format!("write {bin:?}"));
            }
        }
    }
}

pub struct MockWorkspace {
    members: Vec<MockPackage>,
}

impl MockWorkspace {
    pub fn new() -> Self {
        MockWorkspace { members: vec![] }
    }

    pub fn member(mut self, package: MockPackage) -> Self {
        self.members.push(package);
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

        let manifest = root.path().join("Cargo.toml");
        std::fs::write(&manifest, manifest_lines.join("\n"))
            .expect(&format!("write manifest to {manifest:?}"));

        root
    }
}
