use verus_exec::strip_source;

fn check(input: &str, expected: &str) {
    let output = strip_source(input).unwrap();
    assert_eq!(output, expected);
    // Repeated snapshots must be stable.
    assert_eq!(strip_source(&output).unwrap(), output);
}

#[test]
fn binary_search() {
    check(
        r#"verus! {
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i: int| 0 <= i < v.len() && k == v[i],
    ensures
        r < v.len(),
        k == v[r as int],
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
        invariant
            i2 < v.len(),
            exists|i: int| i1 <= i <= i2 && k == v[i],
            forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        decreases i2 - i1,
    {
        let ix = i1 + (i2 - i1) / 2;
        if v[ix] < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }
    }
    i1
}
}
"#,
        r#"fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
    {
        let ix = i1 + (i2 - i1) / 2;
        if v[ix] < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }
    }
    i1
}
"#,
    );
}

#[test]
fn ordinary_rust_is_identical() {
    let input = r##"#!/usr/bin/env rust-script

// assert(false); verus! { proof fn f() {} }
#[derive(Debug)]
struct S { s: &'static str }

fn f() {
	let s  = r#"proof { assert(false); }"#;
    /* keep this */ assert!(s.len() > 0);
    assert_eq!(s, s);  // keep this too
    custom! { proof fn opaque_macro_payload() {} }
}

"##;
    check(input, input);
}

#[test]
fn assertions_proof_blocks_and_ghost_locals() {
    check(
        r#"verus! {
fn f(x: u64) {
    // executable comment
    let y  = x + 1; // keep spacing
    let ghost g = x as int;
    let tracked t = make_token();
    assert(y > x);
    assert(y > x) by { lemma(); }
    assert forall|i: int| i == i by {}
    assume(x < 100);
    reveal(lemma);
    hide(lemma);
    proof { lemma(); }
    assert!(y > x);
    println!("assert(false)");
}
}
"#,
        r#"fn f(x: u64) {
    // executable comment
    let y  = x + 1; // keep spacing
    assert!(y > x);
    println!("assert(false)");
}
"#,
    );
}

#[test]
fn attribute_syntax_and_verifier_attributes() {
    check(
        r#"#[verus_verify]
#[verifier::loop_isolation(false)]
#[allow(unused)]
#[verus_spec(r => requires x < 100, ensures r > x,)]
fn f(x: u32) -> u32 {
    let r = x + 1;
    proof! { assert(r > x); }
    proof_decl! { let ghost g = x as int; }
    proof_with!(Ghost(g));
    #[verus_spec(with Ghost(g))]
    let n = identity(r);
    #[verus_spec(invariant i <= n, decreases n - i,)]
    for i in 0..n {
        assert!(i < n);
    }
    n
}
"#,
        r#"#[allow(unused)]
fn f(x: u32) -> u32 {
    let r = x + 1;
    let n = identity(r);
    for i in 0..n {
        assert!(i < n);
    }
    n
}
"#,
    );
}

#[test]
fn nested_spec_and_proof_items() {
    check(
        r#"verus! {
/// documentation for a proof function
pub proof fn lemma() {}
pub open spec fn model() -> int { 0 }
spec const MODEL: int = 0;
assume_specification [external](x: u32) -> u32
    requires x < 100,
    ensures true,
;
struct S { value: u32, model: Ghost<int>, token: Tracked<Token> }
impl S {
    proof fn lemma(&self) {}
    spec fn model(&self) -> int { 0 }
    fn get(&self) -> u32 requires true, { self.value }
}
trait T {
    proof fn lemma();
    spec fn model(&self) -> int;
    fn get(&self) -> u32 ensures true,;
}
mod nested {
    proof fn lemma() {}
    fn f() {
        proof fn local_lemma() {}
        assert!(true);
    }
}
}
"#,
        r#"struct S { value: u32, model: Ghost<int>, token: Tracked<Token> }
impl S {
    fn get(&self) -> u32  { self.value }
}
trait T {
    fn get(&self) -> u32 ;
}
mod nested {
    fn f() {
        assert!(true);
    }
}
"#,
    );
}

#[test]
fn all_loop_forms_and_closure_contracts() {
    check(
        r#"verus! {
fn f() {
    for i in iter: 0..10
        invariant_except_break true,
        invariant i <= 10,
        ensures true,
        decreases 10 - i,
    {
        assert!(i < 10);
    }
    loop
        invariant true,
        invariant_ensures true,
        ensures true,
        decreases 1,
    { break; }
    while false
        invariant_except_break true,
        invariant true,
        invariant_ensures true,
        ensures true,
        decreases 1,
    { break; }
    let c = |x: u32| -> u32 requires x < 10, ensures true, { x + 1 };
}
}
"#,
        r#"fn f() {
    for i in  0..10
    {
        assert!(i < 10);
    }
    loop
    { break; }
    while false
    { break; }
    let c = |x: u32| -> u32   { x + 1 };
}
"#,
    );
}

#[test]
fn executable_ghost_wrappers_are_retained() {
    check(
        "verus! { fn f(g: Ghost<int>) -> Tracked<Token> { let g = Ghost(0int); make(g) } }\n",
        " fn f(g: Ghost<int>) -> Tracked<Token> { let g = Ghost(0int); make(g) } \n",
    );
}

#[test]
fn unicode_and_crlf() {
    check(
        "verus! {\r\nfn café() { let résumé = \"🦀\"; assert(true); assert!(résumé.len() > 0); }\r\n}\r\n",
        "fn café() { let résumé = \"🦀\";  assert!(résumé.len() > 0); }\r\n",
    );
}

#[test]
fn cfg_attr_preserves_rust_attributes() {
    check(
        "#[cfg_attr(feature = \"verify\", verifier::external_body, allow(unused))]\nfn f() {}\n",
        "#[cfg_attr(feature = \"verify\",  allow(unused))]\nfn f() {}\n",
    );
    check(
        "#[cfg_attr(feature = \"verify\", allow(unused), verus_verify)]\nfn f() {}\n",
        "#[cfg_attr(feature = \"verify\", allow(unused) )]\nfn f() {}\n",
    );
    check("#[cfg_attr(feature = \"verify\", verus_verify)]\nfn f() {}\n", "fn f() {}\n");
}

#[test]
fn malformed_verus_is_an_error() {
    assert!(strip_source("verus! { fn f() requires true, }").is_err());
}

#[test]
fn wrapper_boundary_blank_lines() {
    check("verus! {\n\nfn f() {}\n\n}\n", "fn f() {}\n");
    check("    verus! {\n\n    fn f() {}\n\n    }\n", "    fn f() {}\n");
    check(
        "verus! {\n// keep wrapper comment\n\nfn f() {}\n\n// keep trailing comment\n}\n",
        "// keep wrapper comment\n\nfn f() {}\n\n// keep trailing comment\n",
    );
}

#[test]
fn impl_wrappers_and_qualified_names() {
    check(
        "struct S;\nimpl S {\n    verus_builtin_macros::verus_impl! {\n        proof fn lemma() {}\n        fn f() {}\n    }\n}\n",
        "struct S;\nimpl S {\n        fn f() {}\n}\n",
    );
    check(
        "#[verus_builtin_macros::verus_spec(requires true,)]\nfn f() {\n    verus_builtin_macros::proof! { assert(true); }\n}\n",
        "fn f() {\n}\n",
    );
}

#[test]
fn complete_function_contract() {
    check(
        "verus! {\nexec fn f() -> (r: u32)\n    requires true,\n    ensures true,\n    returns 1u32,\n    decreases 1,\n    opens_invariants none\n    no_unwind\n{ 1 }\n}\n",
        " fn f() -> (r: u32)\n{ 1 }\n",
    );
}

#[test]
fn removed_statements_keep_neighboring_comments() {
    check(
        "verus! {\nfn f() {\n    assert(true); // keep this comment\n    /* keep this too */ proof { assert(true); }\n    assert!(true);\n}\n}\n",
        "fn f() {\n     // keep this comment\n    /* keep this too */ \n    assert!(true);\n}\n",
    );
}

#[test]
fn ordinary_rust_assert_and_assume_functions() {
    let input = "fn assert(b: bool, message: &str) { assert!(b, \"{}\", message); }\nfn assume(b: bool) { assert(b, \"message\"); }\nfn f() { assume(true); assert(true, \"message\"); }\n";
    check(input, input);
    check(
        "#[verus_verify]\nimpl S {\n    fn f() { assert(true); assert!(true); }\n}\n",
        "impl S {\n    fn f() { assert(true); assert!(true); }\n}\n",
    );
}

#[test]
fn byte_order_mark_and_shebang() {
    check("\u{feff}verus! {\nfn f() {}\n}\n", "\u{feff}fn f() {}\n");
    check(
        "#!/usr/bin/env rust-script\nverus! {\nfn f() { assert(true); }\n}\n",
        "#!/usr/bin/env rust-script\nfn f() {  }\n",
    );
}

#[test]
fn broadcast_functions_and_contract_commas() {
    check(
        "verus! {\nbroadcast proof fn lemma() {}\nfn f<T>() where T: Copy,\n    opens_invariants any,\n{}\n}\n",
        "fn f<T>() where T: Copy,\n{}\n",
    );
}

#[test]
fn ghost_expressions_preserve_executable_control_flow() {
    check(
        "verus! {\nfn f(b: bool) {\n    match b {\n        true => assert(true),\n        false => proof { assert(true); },\n    }\n    if b { assert!(b); } else { proof { assert(true); } }\n    let unit = proof { assert(true); };\n    consume_unit(unit);\n}\n}\n",
        "fn f(b: bool) {\n    match b {\n        true => {},\n        false => {},\n    }\n    if b { assert!(b); } else {  }\n    let unit = {};\n    consume_unit(unit);\n}\n",
    );
}

#[test]
fn attributed_spec_and_proof_functions() {
    check(
        "#[verifier::spec]\nfn model() -> u32 { 0 }\n#[verifier::proof]\nfn lemma() {}\nimpl S {\n    #[verus::internal(spec)]\n    fn model(&self) -> u32 { 0 }\n    fn exec(&self) {}\n}\n",
        "impl S {\n    fn exec(&self) {}\n}\n",
    );
    check(
        "verus! {\n#[verifier::spec]\nfn model() -> u32 { 0 }\nfn exec() {}\n}\n",
        "fn exec() {}\n",
    );
}

#[test]
fn structural_derives_preserve_rust_derives() {
    check(
        "#[derive(Structural)]\nstruct S;\n#[derive(Clone, StructuralEq, Debug)]\nstruct T;\n#[cfg_attr(feature = \"verify\", derive(Clone, Structural))]\nstruct U;\n#[cfg_attr(feature = \"verify\", derive(Structural))]\nstruct V;\n",
        "struct S;\n#[derive(Clone,  Debug)]\nstruct T;\n#[cfg_attr(feature = \"verify\", derive(Clone ))]\nstruct U;\nstruct V;\n",
    );
}
