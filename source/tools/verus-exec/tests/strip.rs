use verus_exec::strip_source;

#[test]
fn expands_atomic_operations_and_preserves_surrounding_source() {
    let input = "// before\nfn f() {\n    let value = atomic_with_ghost!(a => fetch_add(2); update old -> new; returning r; ghost g => { assert(new == old + 2); }); // after\n}\n";
    let output = strip_source(input).unwrap();
    assert!(output.starts_with("// before\nfn f() {\n    let value = {"));
    assert!(output.contains(".patomic") && output.contains(".fetch_add("), "{output}");
    assert!(output.contains("Tracked::assume_new()"), "{output}");
    assert!(output.ends_with("}; // after\n}\n"));
    assert!(!output.contains("assert"));
    assert!(!output.contains("ghost g"));
    assert_eq!(strip_source(&output).unwrap(), output);
}

#[test]
fn nested_atomic_expansions_and_legacy_ghost_shorthand() {
    let input = "fn f() { atomic_with_ghost!(a => store(atomic_with_ghost!(b => load(); g => {})); ghost g => {}); }";
    let output = strip_source(input).unwrap();
    assert!(!output.contains("atomic_with_ghost!"), "{output}");
    assert!(output.contains(".store("), "{output}");
    assert!(output.contains(".load("), "{output}");
    assert_eq!(strip_source(&output).unwrap(), output);
}

#[test]
fn expands_struct_invariants_and_retains_rust_attributes() {
    let input = "// before\nverus! {\nstruct_with_invariants! {\n    #[repr(C)]\n    /// shared atomic\n    pub struct Counter { pub value: AtomicU32<_, (), _>, }\n    closed spec fn wf(&self) -> bool {\n        invariant on value is (v: u32, g: ()) { v < 10 }\n    }\n}\n}\n// after\n";
    let output = strip_source(input).unwrap();
    assert!(output.starts_with("// before\n"));
    assert!(output.ends_with("// after\n"));
    assert!(output.contains("#[repr(C)]"), "{output}");
    assert!(output.contains("shared atomic"), "{output}");
    assert!(output.contains("pub struct Counter"), "{output}");
    assert!(!output.contains("spec fn"));
    assert!(!output.contains("invariant on"));
    assert!(!output.contains("verus!"));
    assert_eq!(strip_source(&output).unwrap(), output);
}

#[test]
fn expands_state_machines_in_both_grammars_and_removes_item_semicolon() {
    for wrapper in ["", "verus! {"] {
        for name in ["state_machine", "tokenized_state_machine", "tokenized_state_machine_vstd"] {
            let sharding = if name == "state_machine" { "" } else { "#[sharding(variable)]" };
            let input = format!(
                "{wrapper}\n{name}! ( Counter {{ fields {{ {sharding} pub value: u32 }} init! {{ initialize() {{ init value = 0; }} }} }} );\n{}",
                if wrapper.is_empty() { "" } else { "}" },
            );
            let output = strip_source(&input).unwrap();
            assert!(output.contains("pub mod Counter"), "{output}");
            assert!(!output.contains("init!"));
            assert!(!output.contains("#[cfg(verus_keep_ghost)]"), "{output}");
            assert!(!output.contains("#[cfg(verus_keep_ghost_body)]"), "{output}");
            assert!(!output.trim_end().ends_with(';'), "{output}");
            assert_eq!(strip_source(&output).unwrap(), output);
        }
    }
}

#[test]
fn preserves_foreign_macros_and_skips_disabled_known_macros() {
    let input = "other::atomic_with_ghost! { invalid }\nother::tokenized_state_machine! { invalid }\n#[cfg(verus_keep_ghost)]\ntokenized_state_machine! { invalid }\n";
    check(
        input,
        "other::atomic_with_ghost! { invalid }\nother::tokenized_state_machine! { invalid }\n",
    );
}

#[test]
fn invalid_known_macros_report_errors() {
    for input in [
        "fn f() { atomic_with_ghost!(a => unknown(); ghost g => {}); }",
        "fn f() { atomic_with_ghost!(a => store(); ghost g => {}); }",
        "struct_with_invariants! { invalid }",
        "tokenized_state_machine! { invalid }",
    ] {
        assert!(strip_source(input).is_err(), "{input}");
    }
    let error = strip_source("fn f() {\n    atomic_with_ghost!(a => store(); ghost g => {});\n}")
        .unwrap_err();
    assert!(format!("{error:#}").contains("at 2:"), "{error:#}");
}

#[test]
fn generated_macros_preserve_crlf_and_indentation() {
    let input = "fn f() {\r\n\tlet x = atomic_with_ghost!(a => load(); ghost g => {});\r\n}\r\n";
    let output = strip_source(input).unwrap();
    assert!(output.starts_with("fn f() {\r\n\tlet x = {\r\n\t"));
    assert!(output.ends_with("\t};\r\n}\r\n"));
    assert!(!output.replace("\r\n", "").contains('\n'));
    assert_eq!(strip_source(&output).unwrap(), output);
}

#[test]
fn generated_types_use_exec_desugaring_without_compiler_context() {
    for spelling in ["spec_fn", "FnSpec"] {
        let input = format!(
            "struct_with_invariants! {{ pub struct S {{ pub callback: Ghost<{spelling}(u8) -> u8>, }} closed spec fn wf(&self) -> bool {{ predicate {{ true }} }} }}"
        );
        let output = strip_source(&input).unwrap();
        assert!(output.contains("FnSpec<"), "{output}");
        assert!(!output.contains("spec_fn("));
        assert_eq!(strip_source(&output).unwrap(), output);
    }
}

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
        r#"fn binary_search(v: &Vec<u64>, k: u64) -> usize
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
fn executable_ghost_wrapper_types_are_retained() {
    check(
        "verus! { fn f(g: Ghost<int>) -> Tracked<Token> { let g = Ghost(0int); make(g) } }\n",
        " fn f(g: Ghost<int>) -> Tracked<Token> { let g = Ghost::assume_new_fallback(|| unreachable!()); make(g) } \n",
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
        " fn f() -> u32\n{ 1 }\n",
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

#[test]
fn expression_wrappers_preserve_precedence() {
    check(
        "fn f() { let x = verus_exec_expr!(1 + 2) * 3; let y = verus_exec_expr!{1 + 2} * 3; let z = verus_exec_expr![1 + 2] * 3; }\n",
        "fn f() { let x = (1 + 2) * 3; let y = (1 + 2) * 3; let z = (1 + 2) * 3; }\n",
    );
    check(
        "verus! { fn f() { let x = verus_exec_expr!(1 + 2) * 3; } }\n",
        " fn f() { let x = (1 + 2) * 3; } \n",
    );
    check(
        "fn f() { verus_exec_expr!{work()} next(); verus_exec_expr!{42} }\n",
        "fn f() { (work()); next(); (42) }\n",
    );
    check(
        "verus! { fn f() { verus_exec_expr!{work()} next(); verus_exec_expr!{42} } }\n",
        " fn f() { (work()); next(); (42) } \n",
    );
    check("verus! { fn f() { verus_exec_expr!{42} proof!{} } }\n", " fn f() { (42);  } \n");
    check("verus! { fn f() { verus_exec_expr!{42} let ghost g = 0; } }\n", " fn f() { (42);  } \n");
}

#[test]
fn proof_macro_values_preserve_executable_control_flow() {
    check(
        "fn f(b: bool) {\n    let unit = proof! { assert(true); };\n    consume(proof!{});\n    match b { true => proof!{}, false => proof!{} }\n}\n",
        "fn f(b: bool) {\n    let unit = {};\n    consume({});\n    match b { true => {}, false => {} }\n}\n",
    );
    check("fn f() { verus_exec_expr!(proof { assert(true); }) }\n", "fn f() { ({}) }\n");
}

#[test]
fn executable_constant_and_static_contracts() {
    check(
        "verus! {\nexec const C: u32 ensures C == 1 { 1 }\nexec static S: u32 ensures S == 2 { 2 }\nimpl T {\n    exec const D: u32 ensures D == 3 { 3 }\n    exec const E: u32 = 4;\n}\n}\n",
        " const C: u32  = { 1 };\n static S: u32  = { 2 };\nimpl T {\n     const D: u32  = { 3 };\n     const E: u32 = 4;\n}\n",
    );
}

#[test]
fn attributed_ghost_constants() {
    check(
        "#[verifier::spec]\nconst C: u32 = 1;\nimpl T {\n    #[verus::internal(spec)]\n    const D: u32 = 2;\n}\ntrait U {\n    #[verifier::spec]\n    const E: u32;\n}\n",
        "impl T {\n}\ntrait U {\n}\n",
    );
}

#[test]
fn ghost_wrappers_still_erase_nested_proof_artifacts() {
    check(
        "verus! { fn f() -> Ghost<int> { Ghost({ proof { assert(true); } 0int }) } }\n",
        " fn f() -> Ghost<int> { Ghost::assume_new_fallback(|| unreachable!()) } \n",
    );
}

#[test]
fn wrapper_constructors_discard_payloads_and_preserve_paths() {
    let input = r#"fn f() -> (Ghost<u32>, Tracked<u32>) {
    // retain this comment
    let g = Ghost /* path comment */ ::< /* type comment */ u32 > /* call comment */ (
        atomic_with_ghost! { invalid ghost-only macro payload },
    );
    let t = Tracked::<u32>(undefined_token.borrow());
    (g, t) // retain this too
}
"#;
    let expected = r#"fn f() -> (Ghost<u32>, Tracked<u32>) {
    // retain this comment
    let g = Ghost /* path comment */ ::< /* type comment */ u32 > /* call comment */ ::assume_new_fallback(|| unreachable!());
    let t = Tracked::<u32>::assume_new_fallback(|| unreachable!());
    (g, t) // retain this too
}
"#;
    check(input, expected);
    check(&format!("verus! {{\n{input}}}\n"), expected);
    check(
        "#[verus_verify]\nfn f() -> Ghost<u32> { Ghost(removed.view()) }\n",
        "fn f() -> Ghost<u32> { Ghost::assume_new_fallback(|| unreachable!()) }\n",
    );
    check(
        "verus! {\r\nfn f() -> Tracked<u32> { Tracked(removed) }\r\n}\r\n",
        "fn f() -> Tracked<u32> { Tracked::assume_new_fallback(|| unreachable!()) }\r\n",
    );
}

#[test]
fn wrapper_patterns_preserve_types_comments_and_exec_bindings() {
    let input = r#"fn f(Tracked /* wrapper comment */ (/* binding */ mut tok /* after */,): Tracked<u32>, Ghost(model,): Ghost<u32>) {
    let (value, Tracked(/* local */ mut next /* after */,), Ghost(g)) = make();
    let S { plain, token: Tracked(t) }: S = other();
    let Some(Ghost(x)) = maybe() else { return; };
    consume(value, plain);
}
"#;
    let expected = r#"fn f( /* wrapper comment */ /* binding */ mut verus_tmp_tok /* after */: Tracked<u32>, verus_tmp_model: Ghost<u32>) {
    let (value, /* local */  verus_tmp_next /* after */, verus_tmp_g) = make();
    let S { plain, token: verus_tmp_t }: S = other();
    let Some(verus_tmp_x) = maybe() else { return; };
    consume(value, plain);
}
"#;
    check(input, expected);
    check(&format!("verus! {{\n{input}}}\n"), expected);
}

#[test]
fn wrapper_patterns_avoid_capture_and_support_raw_identifiers() {
    let input = r#"fn f(Tracked(tok): Tracked<u32>, Ghost(r#type): Ghost<u32>) {
    let verus_tmp_tok = 1;
    let r#verus_tmp_tok_1 = 2;
    let Tracked(tok) = make();
    let Ghost(r#type) = model();
    let (A(Tracked(item)) | B(Tracked(item))) = other();
    opaque! { verus_tmp_item }
    consume(verus_tmp_tok, r#verus_tmp_tok_1);
}
"#;
    let expected = r#"fn f(verus_tmp_tok_2: Tracked<u32>, verus_tmp_type: Ghost<u32>) {
    let verus_tmp_tok = 1;
    let r#verus_tmp_tok_1 = 2;
    let verus_tmp_tok_3 = make();
    let verus_tmp_type_1 = model();
    let (A(verus_tmp_item_1) | B(verus_tmp_item_1)) = other();
    opaque! { verus_tmp_item }
    consume(verus_tmp_tok, r#verus_tmp_tok_1);
}
"#;
    check(input, expected);
    check(&format!("verus! {{\n{input}}}\n"), expected);
}

#[test]
fn unrelated_and_unsupported_wrapper_forms_are_preserved() {
    // The shared compiler rewriter recognizes bare, single-identifier wrappers
    // in function parameters and local let bindings.
    let input = r#"fn f(Plain(x): Plain, other::Ghost(y): other::Ghost<u32>) {
    let Plain(z) = plain();
    let other::Tracked(t) = other();
    let Ghost(ref g) = model();
    let Tracked(t @ _) = token();
    let Ghost((a, b)) = pair();
    let empty = Ghost();
    let many = Tracked(a, b);
    let qualified = other::Ghost(1);
    consume(x, y, z, t, g);
}
"#;
    check(input, input);
    check(&format!("verus! {{\n{input}}}\n"), input);
}

#[test]
fn unrelated_qualified_macros_and_attributes_are_preserved() {
    let input = "#[business::verus_verify]\n#[business::trigger]\nfn f() { business::proof! { executable(); } business::verus! { opaque tokens } }\n";
    check(input, input);
}

#[test]
fn attributed_ghost_locals_blocks_and_checked_spec_functions() {
    let input = "fn f() {\n    #[verifier::spec]\n    let model = 1;\n    #[verifier::proof]\n    let token = make_token();\n    #[verifier::proof_block]\n    { lemma(); };\n    let unit = #[verifier::proof_block] { lemma(); };\n    consume(unit);\n}\n#[verus::internal(spec(checked))]\nfn checked_model() -> u32 { 0 }\n";
    let expected = "fn f() {\n    let unit = {};\n    consume(unit);\n}\n";
    check(input, expected);
    check(&format!("verus! {{\n{input}}}\n"), expected);
}

#[test]
fn ghost_cfg_items_are_removed_in_both_syntaxes() {
    let input = r#"#[cfg(verus_keep_ghost)]
use ghost_crate::*;
#[cfg(verus_keep_ghost)]
mod ghost_module;
#[cfg(verus_keep_ghost)]
mod ghost_inline { verus! { deliberately invalid Verus } }
#[cfg(verus_keep_ghost)]
struct GhostData;
#[cfg(verus_keep_ghost)]
enum GhostEnum { A }
#[cfg(verus_keep_ghost)]
trait GhostTrait {}
#[cfg(verus_keep_ghost)]
type GhostAlias = u32;
#[cfg(verus_keep_ghost)]
const GHOST_CONST: u32 = 1;
#[cfg(verus_keep_ghost)]
static GHOST_STATIC: u32 = 1;
#[cfg(verus_keep_ghost)]
fn ghost_fn() {}
#[cfg(verus_keep_ghost)]
impl S { fn ghost_impl() {} }
#[cfg(verus_keep_ghost)]
custom! { opaque tokens }
struct S;
impl S {
    #[cfg(verus_keep_ghost)]
    fn ghost_method(&self) {}
    #[cfg(verus_keep_ghost)]
    const GHOST: u32 = 1;
    fn exec(&self) {}
}
trait T {
    #[cfg(verus_keep_ghost)]
    fn ghost_method(&self);
    #[cfg(verus_keep_ghost)]
    type GhostType;
    fn exec(&self);
}
extern "C" {
    #[cfg(verus_keep_ghost)]
    fn ghost_foreign();
    fn exec_foreign();
}
fn exec() {
    #[cfg(verus_keep_ghost)]
    fn ghost_local() {}
}
"#;
    let expected = r#"struct S;
impl S {
    fn exec(&self) {}
}
trait T {
    fn exec(&self);
}
extern "C" {
    fn exec_foreign();
}
fn exec() {
}
"#;
    check(input, expected);
    check(&format!("verus! {{\n{input}}}\n"), expected);
}

#[test]
fn ghost_cfg_matching_is_exact() {
    check(
        "#[cfg( /* keep only in Verus */ verus_keep_ghost, )]\nfn ghost() {}\nfn exec() {}\n",
        "fn exec() {}\n",
    );
    let input = "#[cfg(not(verus_keep_ghost))]\nfn exec() {}\n#[cfg(any(verus_keep_ghost, feature = \"other\"))]\nfn conditional() {}\n#[cfg(verus_keep_ghost = \"yes\")]\nfn different_condition() {}\n#[cfg_attr(verus_keep_ghost, allow(unused))]\nfn attributed() {}\n";
    check(input, input);
}

#[test]
fn named_return_bindings_are_removed() {
    check(
        "verus! {\nstruct S;\nimpl S {\n    fn clone(&self) -> (result: Self) { S }\n}\ntrait T {\n    fn clone(&self) -> (result: Self);\n}\nfn tuple() -> ((a, b): (u32, u32)) { (1, 2) }\nfn reference<'a>(x: &'a u32) -> (result: &'a u32) { x }\nfn ghost() -> (result: Ghost<u32>) { Ghost(1) }\nfn tracked() -> (tracked result: Tracked<Token>) { make() }\nfn closure() { let c = || -> (result: u32) { 1 }; }\n}\n",
        "struct S;\nimpl S {\n    fn clone(&self) -> Self { S }\n}\ntrait T {\n    fn clone(&self) -> Self;\n}\nfn tuple() -> (u32, u32) { (1, 2) }\nfn reference<'a>(x: &'a u32) -> &'a u32 { x }\nfn ghost() -> Ghost<u32> { Ghost::assume_new_fallback(|| unreachable!()) }\nfn tracked() -> Tracked<Token> { make() }\nfn closure() { let c = || -> u32 { 1 }; }\n",
    );
    check("fn clone(&self) -> (result: Self) { make() }\n", "fn clone(&self) -> Self { make() }\n");
    let input = "fn tuple() -> (u32, u32) { (1, 2) }\nfn grouped() -> (u32) { 1 }\n";
    check(input, input);
}

#[test]
fn named_return_bindings_preserve_type_comments_and_line_breaks() {
    check(
        "verus! {\nfn f() -> (result: /* keep type comment */ u32 /* keep trailing comment */) { 1 }\nfn g() -> (result:\n    u32\n) { 2 }\n}\n",
        "fn f() -> /* keep type comment */ u32 /* keep trailing comment */ { 1 }\nfn g() -> \n    u32\n { 2 }\n",
    );
    check("verus! {\r\nfn café() -> (résumé: u32) { 1 }\r\n}\r\n", "fn café() -> u32 { 1 }\r\n");
}
