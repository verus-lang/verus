use std::fs;
use tempfile::tempdir;
use verus_trust_audit::{
    MANIFEST_VERSION, Manifest, Node, NodeKind, SourceFile, SourceRange, Trust, render_manifest,
    source_hash,
};

#[test]
fn renders_verus_wrapper_and_omits_untrusted_body() {
    let temp = tempdir().unwrap();
    let source_path = temp.path().join("input.rs");
    let manifest_path = temp.path().join("manifest.json");
    let output_path = temp.path().join("out");
    let source = "use vstd::prelude::*;\n\nverus! {\n// trusted comment\n#[verus::trusted]\nproof fn trusted() { assume(true); }\n\nproof fn omitted() {}\n\n#[verus::trusted(spec)]\nproof fn interface()\n    ensures true,\n{\n    assert(true);\n}\n}\n";
    fs::write(&source_path, source).unwrap();
    let trusted_start = source.find("#[verus::trusted]\n").unwrap();
    let trusted_item = source.find("fn trusted").unwrap();
    let trusted_end = source[trusted_item..].find('}').unwrap() + trusted_item + 1;
    let omitted_start = source.find("proof fn omitted").unwrap();
    let omitted_end = source[omitted_start..].find('}').unwrap() + omitted_start + 1;
    let spec_start = source.find("#[verus::trusted(spec)]").unwrap();
    let spec_item = source.find("fn interface").unwrap();
    let body_start = source[spec_item..].find('{').unwrap() + spec_item;
    let spec_end = source[body_start..].find('}').unwrap() + body_start + 1;
    let file = source_path.canonicalize().unwrap().to_string_lossy().into_owned();
    let range = |start, end| SourceRange { file: file.clone(), start, end };
    let manifest = Manifest {
        format_version: MANIFEST_VERSION,
        crate_name: "test".to_string(),
        root_trust: Trust::Untrusted,
        crate_attributes: vec![],
        files: vec![SourceFile { path: file.clone(), sha256: source_hash(source.as_bytes()) }],
        nodes: vec![
            Node {
                id: 1,
                parent: None,
                name: "trusted".to_string(),
                kind: NodeKind::Function,
                trust: Trust::Trusted,
                range: range(trusted_start, trusted_end),
                body: None,
                from_expansion: false,
                call_site: None,
            },
            Node {
                id: 2,
                parent: None,
                name: "omitted".to_string(),
                kind: NodeKind::Function,
                trust: Trust::Untrusted,
                range: range(omitted_start, omitted_end),
                body: None,
                from_expansion: false,
                call_site: None,
            },
            Node {
                id: 3,
                parent: None,
                name: "interface".to_string(),
                kind: NodeKind::Function,
                trust: Trust::TrustedSpec,
                range: range(spec_start, spec_end),
                body: Some(range(body_start, spec_end)),
                from_expansion: false,
                call_site: None,
            },
        ],
    };
    fs::write(&manifest_path, serde_json::to_vec_pretty(&manifest).unwrap()).unwrap();
    let written = render_manifest(&manifest_path, &output_path).unwrap();
    assert_eq!(written.len(), 1);
    let rendered = fs::read_to_string(&written[0]).unwrap();
    assert!(rendered.contains("verus! {"));
    assert!(rendered.contains("proof fn trusted() { assume(true); }"));
    assert!(!rendered.contains("fn omitted"));
    assert!(rendered.contains("/* untrusted code omitted */"));
    assert!(!rendered.contains("assert(true)"));
}

#[test]
fn rejects_changed_source() {
    let temp = tempdir().unwrap();
    let source_path = temp.path().join("input.rs");
    let manifest_path = temp.path().join("manifest.json");
    fs::write(&source_path, "fn a() {}\n").unwrap();
    let file = source_path.canonicalize().unwrap().to_string_lossy().into_owned();
    let manifest = Manifest {
        format_version: MANIFEST_VERSION,
        crate_name: "test".to_string(),
        root_trust: Trust::Untrusted,
        crate_attributes: vec![],
        files: vec![SourceFile { path: file, sha256: source_hash(b"different") }],
        nodes: vec![],
    };
    fs::write(&manifest_path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    assert!(render_manifest(&manifest_path, &temp.path().join("out")).is_err());
}

#[test]
fn untrusted_only_edits_do_not_change_snapshot() {
    fn render(source: &str) -> String {
        let temp = tempdir().unwrap();
        let source_path = temp.path().join("input.rs");
        let manifest_path = temp.path().join("manifest.json");
        let output_path = temp.path().join("out");
        fs::write(&source_path, source).unwrap();
        let file = source_path.canonicalize().unwrap().to_string_lossy().into_owned();
        let trusted_start = source.find("#[verus::trusted]").unwrap();
        let trusted_end = source[trusted_start..].find('}').unwrap() + trusted_start + 1;
        let omitted_start = source.find("proof fn omitted").unwrap();
        let omitted_end = source[omitted_start..].find('}').unwrap() + omitted_start + 1;
        let range = |start, end| SourceRange { file: file.clone(), start, end };
        let manifest = Manifest {
            format_version: MANIFEST_VERSION,
            crate_name: "test".to_string(),
            root_trust: Trust::Untrusted,
            crate_attributes: vec![],
            files: vec![SourceFile { path: file.clone(), sha256: source_hash(source.as_bytes()) }],
            nodes: vec![
                Node {
                    id: 1,
                    parent: None,
                    name: "trusted".to_string(),
                    kind: NodeKind::Function,
                    trust: Trust::Trusted,
                    range: range(trusted_start, trusted_end),
                    body: None,
                    from_expansion: false,
                    call_site: None,
                },
                Node {
                    id: 2,
                    parent: None,
                    name: "omitted".to_string(),
                    kind: NodeKind::Function,
                    trust: Trust::Untrusted,
                    range: range(omitted_start, omitted_end),
                    body: None,
                    from_expansion: false,
                    call_site: None,
                },
            ],
        };
        fs::write(&manifest_path, serde_json::to_vec(&manifest).unwrap()).unwrap();
        let output = render_manifest(&manifest_path, &output_path).unwrap();
        fs::read_to_string(&output[0]).unwrap()
    }

    let first = "verus! {\n#[verus::trusted]\nproof fn trusted() { assume(true); }\nproof fn omitted() {}\n}\n";
    let second = "verus! {\n#[verus::trusted]\nproof fn trusted() { assume(true); }\n\n// changed\nproof fn omitted() {\n    assert(true);\n}\n}\n";
    assert_eq!(render(first), render(second));
}
