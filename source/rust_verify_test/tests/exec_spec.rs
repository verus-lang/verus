#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    #[allow(unused_imports)] use vstd::prelude::*;
    #[allow(unused_imports)] use vstd::contrib::exec_spec::*;
};

test_verify_one_file! {
    /// Tests basic enum compilation.
    #[test] test_exec_spec_enum IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            pub enum E1 {
                Blob(usize, usize),
                Seq(Seq<Seq<u32>>),
            }

            pub enum E2 {
                E1(E1),
                StructLike {
                    a: u32,
                    b: E1,
                },
                Unit,
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests basic struct compilation.
    #[test] test_exec_spec_struct IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            enum MyOption {
                Some(u32),
                None,
            }
        }

        exec_spec! {
            pub struct S {
                a: u32,
                b: MyOption,
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests that compiler generates exec code with good typing.
    #[test] test_exec_spec_typing IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn id_string(s: SpecString) -> SpecString {
                s
            }

            spec fn id_u32(i: u32) -> u32 {
                i
            }

            spec fn id_seq(s: Seq<u32>) -> Seq<u32> {
                s
            }

            struct S {
                b: SpecString,
            }

            spec fn get(s: S) -> SpecString {
                let b = s.b;
                let a = id_string(b);
                a
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests compilation of literals.
    #[test] test_exec_spec_literals IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn test1(sel: bool, s: Seq<SpecString>) -> Seq<SpecString> {
                let f = if sel {
                    s
                } else {
                    seq![""@]
                };
                f
            }

            spec fn test2(sel: bool, s: Seq<SpecString>) -> Seq<SpecString> {
                let s1 = seq![""@];
                let f = if sel {
                    s
                } else {
                    s1
                };
                f
            }

            spec fn test3() -> bool {
                true
            }

            spec fn test4() -> i32 {
                123
            }

            spec fn test5() -> SpecString {
                "hello"@
            }

            spec fn test6() -> Seq<char> {
                seq!['h', 'e', 'l', 'l', 'o']
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests basic arithemetic operations.
    #[test] test_exec_spec_arith IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn square(x: u32) -> u32
                recommends x * x <= u32::MAX
            {
                (x * x) as u32
            }

            spec fn complex(x: u32) -> u32
                recommends
                    u32::MIN <= x * x <= u32::MAX,
                    u32::MIN <= x * x + x <= u32::MAX,
                    u32::MIN <= x * x + x - 2 <= u32::MAX
            {
                (x * x + x - 2) as u32
            }

            spec fn compare(x: i32, y: i32) -> bool {
                ||| x < y
                ||| x >= y
                ||| x == 1
                ||| x != 1
                ||| x != x - y
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests string indexing.
    #[test] test_exec_spec_index1 IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn test(s: SpecString, i: usize) -> char {
                if 0 <= i && i < s.len() {
                    s[i as int]
                } else {
                    ' '
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests sequence indexing
    #[test] test_exec_spec_index2 IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn test1(s: Seq<Seq<SpecString>>, i: usize, j: usize, n: usize) -> char {
                let c = if i < s.len() &&
                    j < s[i as int].len() &&
                    n < s[i as int][j as int].len() {
                    s[i as int][j as int][n as int]
                } else {
                    ' '
                };
                c
            }

            spec fn test2(s: Seq<char>, i: usize) -> char {
                if i < s.len() {
                    s[i as int]
                } else {
                    ' '
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests equality.
    #[test] test_exec_spec_equality IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn test_eq1(i: usize, j: usize) -> bool {
                i == j
            }

            spec fn test_eq2(a: SpecString, b: SpecString) -> bool {
                a == b
            }

            spec fn test_eq3(a: Seq<usize>, b: Seq<usize>) -> bool {
                a == b
            }

            spec fn test_eq4(a: Seq<SpecString>, b: Seq<SpecString>) -> bool {
                a == b
            }

            spec fn test_eq5(a: Seq<SpecString>) -> bool {
                a == seq!["hello"@, "world"@]
            }

            spec fn test_eq6(a: Seq<Seq<SpecString>>, i: usize) -> bool
                recommends 0 <= i < a.len()
            {
                a[i as int] == seq!["hello"@, "world"@]
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests match expressions.
    #[test] test_exec_spec_match IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            enum EitherString {
                Left { s1: SpecString, s2: SpecString },
                Right(SpecString),
            }

            struct GoodString {
                s: SpecString,
            }

            struct BadString(char, char);

            spec fn test_match1(s: EitherString) -> SpecString {
                match s {
                    EitherString::Left { s1, .. } => s1,
                    EitherString::Right(x) => x,
                }
            }

            spec fn test_match2(s: EitherString) -> SpecString {
                match s {
                    EitherString::Left { s1, s2: _ } => s1,
                    _ => "ello"@,
                }
            }

            spec fn test_match3(s: GoodString) -> SpecString {
                match s {
                    GoodString { s } => s,
                }
            }

            spec fn test_match4(s: BadString) -> char {
                match s {
                    BadString(c1, ..) => c1,
                }
            }

            spec fn test_tuple_struct() -> char {
                test_match4(BadString('a', 'b'))
            }

            spec fn test_match5(s: BadString) -> char {
                match s {
                    BadString(_, c2) => c2,
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for built-in [`Option`] type.
    #[test] test_exec_spec_option IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn test_option1(s: Option<SpecString>) -> SpecString {
                match s {
                    Some(s) => s,
                    None => "hi"@,
                }
            }

            spec fn test_option2(s: Option<SpecString>) -> bool {
                &&& test_option1(s) == match s {
                    Some(s) => s,
                    None => "ww"@,
                }
                &&& s == Some("yes"@)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for built-in tuple types.
    #[test] test_exec_spec_tuple IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn test_tuple1(a: u32, b: u32) -> (u32, u32) {
                (a, b)
            }

            spec fn test_tuple2(a: (SpecString, u32), b: (SpecString, u32)) -> bool {
                &&& a == b
                &&& (a.0, b.1) == (b.0, a.1)
                &&& test_tuple1(a.1, b.1) == test_tuple1(b.1, a.1)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests struct/enum constructors.
    #[test] test_exec_spec_constructor IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            struct A {
                a: u32,
                b: u32,
            }

            enum B {
                C {
                    a: A,
                }
            }

            spec fn test_struct(a: u32, b: u32) -> A {
                A { a, b }
            }

            spec fn test_struct2(a: A) -> (B, (B, B)) {
                let x = B::C { a };
                let y = B::C {
                    a: test_struct(a.a, a.b),
                };
                (B::C {
                    a: A {
                        a: a.a,
                        b: a.b,
                    },
                }, (x, y))
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests `matches`.
    #[test] test_exec_spec_matches IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            enum D {
                E, F
            }

            enum C {
                A, B(D)
            }

            spec fn test_matches1(x: C) -> bool {
                ||| x matches C::B(y) && y matches D::E
                ||| x matches C::B(D::F) ==> x matches C::A
                ||| {
                    &&& x matches C::B(z)
                    &&& z matches D::F
                }
            }

            spec fn test_matches2(x: Option<Option<C>>) -> bool {
                ||| x matches Some(_)
                ||| x matches Some(Some(x)) ==> x matches C::A
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for recursions and `decreases` clauses.
    #[test] test_exec_spec_recursion IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn test_recursion1(n: usize) -> usize
                decreases n
            {
                if n == 0 {
                    0
                } else {
                    test_recursion1((n - 1) as usize)
                }
            }

            spec fn test_recursion2(n: i32) -> i32
                decreases n when n >= 0
            {
                if n == 0 {
                    1
                } else {
                    test_recursion2((n - 1) as i32)
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for recursion with sequence.
    #[test] test_exec_spec_recursion_seq IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn test_all_positive(a: Seq<i32>, i: usize) -> bool
                recommends 0 <= i < a.len()
                decreases a.len() - i when i < usize::MAX
            {
                &&& a[i as int] > 0
                &&& i + 1 < a.len() ==> test_all_positive(a, (i + 1) as usize)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests support for some built-in constants.
    #[test] test_exec_spec_constant IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn test(i: usize) -> bool {
                usize::MAX - i != 0
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests interoperability and generated post/pre-conditions
    #[test] test_exec_spec_interop1 IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn test_all_positive(a: Seq<i32>, i: usize) -> bool
                recommends 0 <= i < a.len()
                decreases a.len() - i when i < usize::MAX
            {
                &&& a[i as int] > 0
                &&& i + 1 < a.len() ==> test_all_positive(a, (i + 1) as usize)
            }
        }

        fn sanity_check() {
            reveal_with_fuel(test_all_positive, 3);
            assert(test_all_positive(seq![1, 2, 3], 0));
            let res = exec_test_all_positive(&[1, 2, 3], 0);
            assert(res);
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests interoperability and generated post/pre-conditions.
    #[test] test_exec_spec_interop2 IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            struct A {
                a: u32,
                b: u32,
            }

            spec fn pred(a: A) -> bool {
                a.a > a.b
            }
        }

        fn sanity_check() {
            let a = ExecA { a: 3, b: 2 };

            if exec_pred(&a) {
                assert(a.a > a.b);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests interoperability and generated post/pre-conditions.
    #[test] test_exec_spec_interop3 IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            struct MyPair(Seq<u32>, Seq<u32>);

            spec fn pred_helper(a: Seq<u32>, b: Seq<u32>, i: usize) -> bool
                recommends 0 <= i < a.len() == b.len()
                decreases a.len() - i when i < usize::MAX
            {
                &&& a[i as int] > b[i as int]
                &&& i + 1 < a.len() ==> pred_helper(a, b, (i + 1) as usize)
            }

            spec fn pred(p: MyPair) -> bool
                recommends p.0.len() == p.1.len()
            {
                if p.0.len() == 0 {
                    true
                } else {
                    pred_helper(p.0, p.1, 0)
                }
            }
        }

        fn test() {
            let a = ExecMyPair(vec![1, 2, 3], vec![0, 1, 2]);

            reveal_with_fuel(pred_helper, 3);

            if exec_pred(&a) {
                assert(a.0@[0] > a.1@[0]);
                assert(a.0@[1] > a.1@[1]);
                assert(a.0@[2] > a.1@[2]);
            } else {
                assert(a.0@[0] <= a.1@[0] || a.0@[1] <= a.1@[1] || a.0@[2] <= a.1@[2]);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests that error spans are accurate.
    #[test] test_exec_spec_error_span IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            struct MyPair(Seq<u32>, Seq<u32>);

            spec fn pred(p: MyPair) -> bool
                recommends p.0.len() != 0
            {
                p.0[0] + 10 > 100 // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    /// Tests that linear variables are compiled correctly.
    #[test] test_exec_spec_linear IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            struct B;

            struct A {
                x: B,
                y: B,
            }

            spec fn test1(a: A) -> bool {
                let b = a;
                let c = b;
                let d = b;
                true
            }

            spec fn test2(a: A) -> B {
                let b = a.x;
                let e = {
                    let c = b;
                    let d = b;
                    d
                };
                e
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests complex structs/enums from the X.509 project.
    #[test] test_exec_spec_certificate IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            pub struct Attribute {
                pub oid: SpecString,
                pub value: SpecString,
            }

            pub struct DistinguishedName(pub Seq<Seq<Attribute>>);

            pub enum GeneralName {
                DNSName(SpecString),
                DirectoryName(DistinguishedName),
                IPAddr(Seq<u8>),
                OtherName,
                Unsupported,
            }

            pub enum SubjectKey {
                RSA {
                    mod_length: usize,
                },
                DSA {
                    p_len: usize,
                    q_len: usize,
                    g_len: usize,
                },
                Other,
            }

            pub struct AuthorityKeyIdentifier {
                pub critical: Option<bool>,
                pub key_id: Option<SpecString>,
                pub issuer: Option<SpecString>,
                pub serial: Option<SpecString>,
            }

            pub struct SubjectKeyIdentifier {
                pub critical: Option<bool>,
                pub key_id: SpecString,
            }

            pub enum ExtendedKeyUsageType {
                ServerAuth,
                ClientAuth,
                CodeSigning,
                EmailProtection,
                TimeStamping,
                OCSPSigning,
                Any,
                Other(SpecString),
            }

            pub struct ExtendedKeyUsage {
                pub critical: Option<bool>,
                pub usages: Seq<ExtendedKeyUsageType>,
            }

            pub struct BasicConstraints {
                pub critical: Option<bool>,
                pub is_ca: bool,
                pub path_len: Option<i64>,
            }

            pub struct KeyUsage {
                pub critical: Option<bool>,
                pub digital_signature: bool,
                pub non_repudiation: bool,
                pub key_encipherment: bool,
                pub data_encipherment: bool,
                pub key_agreement: bool,
                pub key_cert_sign: bool,
                pub crl_sign: bool,
                pub encipher_only: bool,
                pub decipher_only: bool,
            }

            pub struct SubjectAltName {
                pub critical: Option<bool>,
                pub names: Seq<GeneralName>,
            }

            pub struct NameConstraints {
                pub critical: Option<bool>,
                pub permitted: Seq<GeneralName>,
                pub excluded: Seq<GeneralName>,
            }

            pub struct CertificatePolicies {
                pub critical: Option<bool>,
                pub policies: Seq<SpecString>,
            }

            pub struct AuthorityInfoAccess {
                pub critical: Option<bool>,
                // Other info is not encoded
            }

            pub struct SignatureAlgorithm {
                pub id: SpecString,
                pub bytes: SpecString,
            }

            pub struct Extension {
                pub oid: SpecString,
                pub critical: Option<bool>,
            }

            pub struct Certificate {
                pub fingerprint: SpecString,
                pub version: u32,
                pub serial: SpecString,
                pub sig_alg_outer: SignatureAlgorithm,
                pub sig_alg_inner: SignatureAlgorithm,
                pub not_after: u64,
                pub not_before: u64,

                pub issuer: DistinguishedName,
                pub subject: DistinguishedName,
                pub subject_key: SubjectKey,

                pub issuer_uid: Option<SpecString>,
                pub subject_uid: Option<SpecString>,

                pub ext_authority_key_id: Option<AuthorityKeyIdentifier>,
                pub ext_subject_key_id: Option<SubjectKeyIdentifier>,
                pub ext_extended_key_usage: Option<ExtendedKeyUsage>,
                pub ext_basic_constraints: Option<BasicConstraints>,
                pub ext_key_usage: Option<KeyUsage>,
                pub ext_subject_alt_name: Option<SubjectAltName>,
                pub ext_name_constraints: Option<NameConstraints>,
                pub ext_certificate_policies: Option<CertificatePolicies>,
                pub ext_authority_info_access: Option<AuthorityInfoAccess>,

                // All extensions without parameters
                pub all_exts: Option<Seq<Extension>>,
            }

            pub enum Purpose {
                ServerAuth,
            }

            pub struct Task {
                pub hostname: Option<SpecString>,
                pub purpose: Purpose,
                pub now: u64,
            }

            pub enum PolicyError {
                UnsupportedTask,
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests basic `forall` expressions.
    #[test] test_exec_spec_basic_forall IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn zero_vec(a: Seq<u32>) -> bool {
                forall |i: usize| 0 <= i < a.len() ==> a[i as int] != 0
            }
        }

        fn sanity_check() {
            let v = vec![1, 2, 3];
            if exec_zero_vec(&v) {
                assert(v.deep_view()[0] != 0);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests basic `exists` expressions.
    #[test] test_exec_spec_basic_exists IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn non_zero_vec(a: Seq<u32>) -> bool {
                exists |i: usize| 0 <= i < a.len() && a[i as int] != 0
            }
        }

        fn sanity_check() {
            let v = vec![1, 2, 3];
            if exec_non_zero_vec(&v) {
                assert(non_zero_vec(v.deep_view()));
                assert(exists |i: usize| 0 <= i < v.deep_view().len() && v.deep_view()[i as int] != 0);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests nested `forall`s.
    #[test] test_exec_spec_nested_foralls IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn distinct(a: Seq<u32>) -> bool {
                forall |i: usize| #![trigger a[i as int]] 0 <= i < a.len() ==>
                forall |j: usize| #![trigger a[j as int]] 0 <= j < i ==>
                    a[i as int] != a[j as int]
            }
        }

        fn sanity_check(v: Vec<u32>) {
            if exec_distinct(&v) {
                assert(v.deep_view().len() >= 2 ==> v.deep_view()[0] != v.deep_view()[1]);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests nested `exists`s.
    #[test] test_exec_spec_nested_exists IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn has_duplicate(a: Seq<u32>) -> bool {
                exists |i: usize| #![trigger a[i as int]] 0 <= i < a.len() &&
                exists |j: usize| #![trigger a[j as int]] 0 <= j < i &&
                    a[i as int] == a[j as int]
            }
        }

        fn sanity_check(v: Vec<u32>) {
            if exec_has_duplicate(&v) {
                assert(v.deep_view().len() == 2 ==> v.deep_view()[0] == v.deep_view()[1]);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests alternating quantifiers.
    /// Currently ignored because it contains a trigger loop and is thus flaky.
    #[ignore] #[test] test_exec_spec_alt_quants IMPORTS.to_string() + verus_code_str! {
        exec_spec! {
            spec fn has_unique_maximum(a: Seq<u32>) -> bool {
                exists |i: usize| #![trigger a[i as int]] 0 <= i < a.len() &&
                    forall |j: usize| #![trigger a[j as int]] 0 <= j < a.len() ==>
                        i == j || a[i as int] > a[j as int]
            }
        }

        fn sanity_check(v: Vec<u32>) {
            if exec_has_unique_maximum(&v) {
                assert(v.deep_view().len() == 2 ==>
                    v.deep_view()[0] > v.deep_view()[1] ||
                    v.deep_view()[0] < v.deep_view()[1]);
            }
        }
    } => Ok(())
}
