// Branch-condition (MC/DC) coverage tests: the verus! and attribute macros (builtin_macros).
// Each test's comment names the decisions (file:line) and the conditions (atoms, numbered from 0
// in source order) for which the test supplies an evaluation that no other test supplies, so that
// the condition is shown to independently change the decision's outcome. See
// COVERAGE-UNREACHABLE.md for the conditions that no test can cover.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Independence pair for builtin_macros/src/attr_rewrite.rs:332 atom 0 `!self.erase.keep()`
test_verify_one_file_with_options! {
    #[test] ar_const_forloop ["--compile"] => code! {
        use vstd::prelude::*;

        #[verus_spec(r =>
            ensures r == 3
        )]
        pub const fn f() -> u8 {
            let _g = |n: u8| -> u8 {
                let mut s: u8 = 0;
                for i in 0..n {
                    s = s.wrapping_add(i);
                }
                s
            };
            3
        }

        #[verus_spec(r =>
            ensures r == 3
        )]
        pub fn use_f() -> u8 {
            f()
        }

        fn main() {
            let r = use_f();
            assert!(r == 3);
            const K: u8 = f();
            assert!(K == 3);
            println!("use_f() = {} K = {}", r, K);
        }
    } => Ok(())
}

// Independence pair for builtin_macros/src/attr_rewrite.rs:1021 atom 0 `ident == "Tracked"`, atom 1 `ident == "Ghost"`
test_verify_one_file! {
    #[test] attr_proof_with_bad_field code! {
        use vstd::prelude::*;

        #[verus_verify]
        pub struct TestStruct {
            pub x: u32,
            #[cfg(verus_keep_ghost_body)]
            pub y: Ghost<int>,
        }

        #[verus_spec]
        fn mk(x: u32) -> TestStruct {
            proof_with! { y: Some(1) }
            TestStruct { x: x + 1 }
        }
    } => Err(err) => assert_vir_error_msg(err, "A ghost/tracked field must be a tracked/ghost expression. If you want to add ghost/tracked fields")
}

// Independence pair for builtin_macros/src/attr_rewrite.rs:410 atom 2 `attrs.path().segments[1].ident ==...`
test_verify_one_file! {
    #[test] attr_proof_with_fields code! {
        use vstd::prelude::*;

        #[verus_verify]
        pub struct TestStruct {
            pub x: u32,
            #[cfg(verus_keep_ghost_body)]
            pub y: Ghost<int>,
            #[cfg(verus_keep_ghost_body)]
            pub t: Tracked<Ghost<int>>,
        }

        #[verus::trusted]
        #[verus_spec(s =>
            requires x < 100,
            ensures s.x == x + 1, s.y@ == 2 * s.x, s.t@@ == 7,
        )]
        fn mk(x: u32) -> TestStruct {
            proof_with! { y: Ghost(2 * (x + 1)), t: Tracked(Ghost(7int)) }
            TestStruct { x: x + 1 }
        }

        fn main() {
            let s = mk(3);
            println!("{}", s.x);
        }
    } => Ok(())
}

// Independence pair for builtin_macros/src/is_variant.rs:49 atom 0 `!cfg_erase().erase()`
test_verify_one_file_with_options! {
    #[test] erase_is_variant_first ["--compile"] => code! {
        use vstd::prelude::*;

        #[cfg_attr(not(verus_keep_ghost_body), is_variant)]
        pub enum E { A, B }

        fn main() {
            let e = E::A;
            assert!(matches!(e, E::A));
            println!("{}", matches!(e, E::A));
        }
    } => Ok(())
}

// Independence pair for builtin_macros/src/contrib/exec_spec.rs:3309 atom 0 `type_path.qself.is_none()`, atom 1 `type_path.path.segments.len() == 1`
test_verify_one_file! {
    #[test] es_impl_self_errors verus_code! {
        use vstd::prelude::*;
        use vstd::contrib::exec_spec::*;

        pub mod m {
            pub struct S { pub a: u8 }
        }

        pub trait Tr { type A; }
        impl Tr for m::S { type A = m::S; }

        exec_spec_verified! {
            impl m::S {
                spec fn get_a(&self) -> u8 { self.a }
            }
        }

        exec_spec_verified! {
            impl <m::S as Tr>::A {
                spec fn get_a2(&self) -> u8 { self.a }
            }
        }
    } => Err(err) => assert_vir_error_msgs(err, &["exec_spec impl Self type must be a single named type", "exec_spec impl Self type must be a single named type"])
}

// Independence pair for builtin_macros/src/contrib/exec_spec.rs:1018 atoms 1, 2, 3; builtin_macros/src/contrib/exec_spec.rs:1123 atoms 2, 3
test_verify_one_file! {
    #[test] es_paths_result verus_code! {
        use vstd::prelude::*;
        use vstd::contrib::exec_spec::*;

        exec_spec_verified! {
            spec fn none_pat(o: Option<u8>) -> u8 {
                match o {
                    None {} => 0,
                    Some(x) => x,
                }
            }
        }

        exec_spec_verified! {
            spec fn mk(x: u8) -> Result<u8, u8> {
                if x > 0 { Ok(x) } else { Err(x) }
            }

            spec fn get(r: Result<u8, u8>) -> u8 {
                match r {
                    Ok(v) => v,
                    Err(e) => e,
                }
            }
        }
    } => Err(err) => assert_rust_error_msgs(err, &["the trait bound `std::result::Result<u8, u8>: vstd::contrib::exec_spec::ExecSpecType` is not", "the trait bound `std::result::Result<u8, u8>: vstd::contrib::exec_spec::ExecSpecType` is not"])
}

// Independence pair for builtin_macros/src/contrib/exec_spec.rs:1517 atoms 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12; builtin_macros/src/contrib/exec_spec.rs:1537 atoms 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11
test_verify_one_file! {
    #[test] es_quant_type_bad verus_code! {
        use vstd::prelude::*;
        use vstd::contrib::exec_spec::*;

        exec_spec_unverified! {
            spec fn ub(b: bool) -> bool { forall |x: bool| false <= x <= b ==> x }
        }

        exec_spec_verified! {
            spec fn vb(b: bool) -> bool { forall |x: bool| false <= x <= b ==> x }
        }

        exec_spec_verified! {
            spec fn vc(n: char) -> bool { forall |x: char| 'a' <= x < n ==> x != 'q' }
        }
    } => Err(err) => assert_vir_error_msgs(err, &["Unsupported quantified type.", "Unsupported quantified type.", "Unsupported quantified type."])
}

// Independence pair for builtin_macros/src/contrib/exec_spec.rs:1517 atoms 1, 2, 3, 4, 6, 7, 8, 9, 10, 11; builtin_macros/src/contrib/exec_spec.rs:1537 atoms 0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11; builtin_macros/src/contrib/exec_spec.rs:1876 atom 0
test_verify_one_file! {
    #[test] es_quant_types_ok code! {
        use vstd::prelude::*;
        use vstd::contrib::exec_spec::*;

        verus! {

        exec_spec_unverified! {
            spec fn une7_u8(x: u8) -> bool { x != 7 }
            spec fn uf_u8(n: u8) -> bool { forall |x: u8| 0 <= x < n ==> une7_u8(x) }
            spec fn ue_u8(n: u8) -> bool { exists |x: u8| 0 <= x < n && !une7_u8(x) }
            spec fn une7_u16(x: u16) -> bool { x != 7 }
            spec fn uf_u16(n: u16) -> bool { forall |x: u16| 0 <= x < n ==> une7_u16(x) }
            spec fn ue_u16(n: u16) -> bool { exists |x: u16| 0 <= x < n && !une7_u16(x) }
            spec fn une7_u32(x: u32) -> bool { x != 7 }
            spec fn uf_u32(n: u32) -> bool { forall |x: u32| 0 <= x < n ==> une7_u32(x) }
            spec fn ue_u32(n: u32) -> bool { exists |x: u32| 0 <= x < n && !une7_u32(x) }
            spec fn une7_u64(x: u64) -> bool { x != 7 }
            spec fn uf_u64(n: u64) -> bool { forall |x: u64| 0 <= x < n ==> une7_u64(x) }
            spec fn ue_u64(n: u64) -> bool { exists |x: u64| 0 <= x < n && !une7_u64(x) }
            spec fn une7_u128(x: u128) -> bool { x != 7 }
            spec fn uf_u128(n: u128) -> bool { forall |x: u128| 0 <= x < n ==> une7_u128(x) }
            spec fn ue_u128(n: u128) -> bool { exists |x: u128| 0 <= x < n && !une7_u128(x) }
            spec fn une7_usize(x: usize) -> bool { x != 7 }
            spec fn uf_usize(n: usize) -> bool { forall |x: usize| 0 <= x < n ==> une7_usize(x) }
            spec fn ue_usize(n: usize) -> bool { exists |x: usize| 0 <= x < n && !une7_usize(x) }
            spec fn une7_i8(x: i8) -> bool { x != 7 }
            spec fn uf_i8(n: i8) -> bool { forall |x: i8| 0 <= x < n ==> une7_i8(x) }
            spec fn ue_i8(n: i8) -> bool { exists |x: i8| 0 <= x < n && !une7_i8(x) }
            spec fn une7_i16(x: i16) -> bool { x != 7 }
            spec fn uf_i16(n: i16) -> bool { forall |x: i16| 0 <= x < n ==> une7_i16(x) }
            spec fn ue_i16(n: i16) -> bool { exists |x: i16| 0 <= x < n && !une7_i16(x) }
            spec fn une7_i32(x: i32) -> bool { x != 7 }
            spec fn uf_i32(n: i32) -> bool { forall |x: i32| 0 <= x < n ==> une7_i32(x) }
            spec fn ue_i32(n: i32) -> bool { exists |x: i32| 0 <= x < n && !une7_i32(x) }
            spec fn une7_i64(x: i64) -> bool { x != 7 }
            spec fn uf_i64(n: i64) -> bool { forall |x: i64| 0 <= x < n ==> une7_i64(x) }
            spec fn ue_i64(n: i64) -> bool { exists |x: i64| 0 <= x < n && !une7_i64(x) }
            spec fn une7_i128(x: i128) -> bool { x != 7 }
            spec fn uf_i128(n: i128) -> bool { forall |x: i128| 0 <= x < n ==> une7_i128(x) }
            spec fn ue_i128(n: i128) -> bool { exists |x: i128| 0 <= x < n && !une7_i128(x) }
            spec fn une7_isize(x: isize) -> bool { x != 7 }
            spec fn uf_isize(n: isize) -> bool { forall |x: isize| 0 <= x < n ==> une7_isize(x) }
            spec fn ue_isize(n: isize) -> bool { exists |x: isize| 0 <= x < n && !une7_isize(x) }
            spec fn une7_char(x: char) -> bool { x != 'h' }
            spec fn uf_char(n: char) -> bool { forall |x: char| 'a' <= x < n ==> une7_char(x) }
            spec fn ue_char(n: char) -> bool { exists |x: char| 'a' <= x < n && !une7_char(x) }
            spec fn uf_path(n: u8) -> bool { forall |x: core::primitive::u8| 0 <= x < n ==> une7_u8(x) }
        }

        exec_spec_verified! {
            spec fn vne7_u8(x: u8) -> bool { x != 7 }
            spec fn vf_u8(n: u8) -> bool { forall |x: u8| 0 <= x < n ==> vne7_u8(x) }
            spec fn ve_u8(n: u8) -> bool { exists |x: u8| 0 <= x < n && !vne7_u8(x) }
            spec fn vne7_u16(x: u16) -> bool { x != 7 }
            spec fn vf_u16(n: u16) -> bool { forall |x: u16| 0 <= x < n ==> vne7_u16(x) }
            spec fn ve_u16(n: u16) -> bool { exists |x: u16| 0 <= x < n && !vne7_u16(x) }
            spec fn vne7_u32(x: u32) -> bool { x != 7 }
            spec fn vf_u32(n: u32) -> bool { forall |x: u32| 0 <= x < n ==> vne7_u32(x) }
            spec fn ve_u32(n: u32) -> bool { exists |x: u32| 0 <= x < n && !vne7_u32(x) }
            spec fn vne7_u64(x: u64) -> bool { x != 7 }
            spec fn vf_u64(n: u64) -> bool { forall |x: u64| 0 <= x < n ==> vne7_u64(x) }
            spec fn ve_u64(n: u64) -> bool { exists |x: u64| 0 <= x < n && !vne7_u64(x) }
            spec fn vne7_u128(x: u128) -> bool { x != 7 }
            spec fn vf_u128(n: u128) -> bool { forall |x: u128| 0 <= x < n ==> vne7_u128(x) }
            spec fn ve_u128(n: u128) -> bool { exists |x: u128| 0 <= x < n && !vne7_u128(x) }
            spec fn vne7_usize(x: usize) -> bool { x != 7 }
            spec fn vf_usize(n: usize) -> bool { forall |x: usize| 0 <= x < n ==> vne7_usize(x) }
            spec fn ve_usize(n: usize) -> bool { exists |x: usize| 0 <= x < n && !vne7_usize(x) }
            spec fn vne7_i8(x: i8) -> bool { x != 7 }
            spec fn vf_i8(n: i8) -> bool { forall |x: i8| 0 <= x < n ==> vne7_i8(x) }
            spec fn ve_i8(n: i8) -> bool { exists |x: i8| 0 <= x < n && !vne7_i8(x) }
            spec fn vne7_i16(x: i16) -> bool { x != 7 }
            spec fn vf_i16(n: i16) -> bool { forall |x: i16| 0 <= x < n ==> vne7_i16(x) }
            spec fn ve_i16(n: i16) -> bool { exists |x: i16| 0 <= x < n && !vne7_i16(x) }
            spec fn vne7_i32(x: i32) -> bool { x != 7 }
            spec fn vf_i32(n: i32) -> bool { forall |x: i32| 0 <= x < n ==> vne7_i32(x) }
            spec fn ve_i32(n: i32) -> bool { exists |x: i32| 0 <= x < n && !vne7_i32(x) }
            spec fn vne7_i64(x: i64) -> bool { x != 7 }
            spec fn vf_i64(n: i64) -> bool { forall |x: i64| 0 <= x < n ==> vne7_i64(x) }
            spec fn ve_i64(n: i64) -> bool { exists |x: i64| 0 <= x < n && !vne7_i64(x) }
            spec fn vne7_i128(x: i128) -> bool { x != 7 }
            spec fn vf_i128(n: i128) -> bool { forall |x: i128| 0 <= x < n ==> vne7_i128(x) }
            spec fn ve_i128(n: i128) -> bool { exists |x: i128| 0 <= x < n && !vne7_i128(x) }
            spec fn vne7_isize(x: isize) -> bool { x != 7 }
            spec fn vf_isize(n: isize) -> bool { forall |x: isize| 0 <= x < n ==> vne7_isize(x) }
            spec fn ve_isize(n: isize) -> bool { exists |x: isize| 0 <= x < n && !vne7_isize(x) }
        }

        } // verus!

        fn main() {
            let mut bad = 0;
            // spec: uf_u8(5u8) = true, uf_u8(10u8) = false, ue_u8(5u8) = false, ue_u8(10u8) = true
            let r = (exec_uf_u8(5u8), exec_uf_u8(10u8), exec_ue_u8(5u8), exec_ue_u8(10u8));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u u8: {:?}", r); }
            // spec: uf_u16(5u16) = true, uf_u16(10u16) = false, ue_u16(5u16) = false, ue_u16(10u16) = true
            let r = (exec_uf_u16(5u16), exec_uf_u16(10u16), exec_ue_u16(5u16), exec_ue_u16(10u16));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u u16: {:?}", r); }
            // spec: uf_u32(5u32) = true, uf_u32(10u32) = false, ue_u32(5u32) = false, ue_u32(10u32) = true
            let r = (exec_uf_u32(5u32), exec_uf_u32(10u32), exec_ue_u32(5u32), exec_ue_u32(10u32));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u u32: {:?}", r); }
            // spec: uf_u64(5u64) = true, uf_u64(10u64) = false, ue_u64(5u64) = false, ue_u64(10u64) = true
            let r = (exec_uf_u64(5u64), exec_uf_u64(10u64), exec_ue_u64(5u64), exec_ue_u64(10u64));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u u64: {:?}", r); }
            // spec: uf_u128(5u128) = true, uf_u128(10u128) = false, ue_u128(5u128) = false, ue_u128(10u128) = true
            let r = (exec_uf_u128(5u128), exec_uf_u128(10u128), exec_ue_u128(5u128), exec_ue_u128(10u128));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u u128: {:?}", r); }
            // spec: uf_usize(5usize) = true, uf_usize(10usize) = false, ue_usize(5usize) = false, ue_usize(10usize) = true
            let r = (exec_uf_usize(5usize), exec_uf_usize(10usize), exec_ue_usize(5usize), exec_ue_usize(10usize));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u usize: {:?}", r); }
            // spec: uf_i8(5i8) = true, uf_i8(10i8) = false, ue_i8(5i8) = false, ue_i8(10i8) = true
            let r = (exec_uf_i8(5i8), exec_uf_i8(10i8), exec_ue_i8(5i8), exec_ue_i8(10i8));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u i8: {:?}", r); }
            // spec: uf_i16(5i16) = true, uf_i16(10i16) = false, ue_i16(5i16) = false, ue_i16(10i16) = true
            let r = (exec_uf_i16(5i16), exec_uf_i16(10i16), exec_ue_i16(5i16), exec_ue_i16(10i16));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u i16: {:?}", r); }
            // spec: uf_i32(5i32) = true, uf_i32(10i32) = false, ue_i32(5i32) = false, ue_i32(10i32) = true
            let r = (exec_uf_i32(5i32), exec_uf_i32(10i32), exec_ue_i32(5i32), exec_ue_i32(10i32));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u i32: {:?}", r); }
            // spec: uf_i64(5i64) = true, uf_i64(10i64) = false, ue_i64(5i64) = false, ue_i64(10i64) = true
            let r = (exec_uf_i64(5i64), exec_uf_i64(10i64), exec_ue_i64(5i64), exec_ue_i64(10i64));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u i64: {:?}", r); }
            // spec: uf_i128(5i128) = true, uf_i128(10i128) = false, ue_i128(5i128) = false, ue_i128(10i128) = true
            let r = (exec_uf_i128(5i128), exec_uf_i128(10i128), exec_ue_i128(5i128), exec_ue_i128(10i128));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u i128: {:?}", r); }
            // spec: uf_isize(5isize) = true, uf_isize(10isize) = false, ue_isize(5isize) = false, ue_isize(10isize) = true
            let r = (exec_uf_isize(5isize), exec_uf_isize(10isize), exec_ue_isize(5isize), exec_ue_isize(10isize));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u isize: {:?}", r); }
            // spec: uf_char('e') = true, uf_char('z') = false, ue_char('e') = false, ue_char('z') = true
            let r = (exec_uf_char('e'), exec_uf_char('z'), exec_ue_char('e'), exec_ue_char('z'));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH u char: {:?}", r); }
            // spec: vf_u8(5u8) = true, vf_u8(10u8) = false, ve_u8(5u8) = false, ve_u8(10u8) = true
            let r = (exec_vf_u8(5u8), exec_vf_u8(10u8), exec_ve_u8(5u8), exec_ve_u8(10u8));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH v u8: {:?}", r); }
            // spec: vf_u16(5u16) = true, vf_u16(10u16) = false, ve_u16(5u16) = false, ve_u16(10u16) = true
            let r = (exec_vf_u16(5u16), exec_vf_u16(10u16), exec_ve_u16(5u16), exec_ve_u16(10u16));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH v u16: {:?}", r); }
            // spec: vf_u32(5u32) = true, vf_u32(10u32) = false, ve_u32(5u32) = false, ve_u32(10u32) = true
            let r = (exec_vf_u32(5u32), exec_vf_u32(10u32), exec_ve_u32(5u32), exec_ve_u32(10u32));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH v u32: {:?}", r); }
            // spec: vf_u64(5u64) = true, vf_u64(10u64) = false, ve_u64(5u64) = false, ve_u64(10u64) = true
            let r = (exec_vf_u64(5u64), exec_vf_u64(10u64), exec_ve_u64(5u64), exec_ve_u64(10u64));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH v u64: {:?}", r); }
            // spec: vf_u128(5u128) = true, vf_u128(10u128) = false, ve_u128(5u128) = false, ve_u128(10u128) = true
            let r = (exec_vf_u128(5u128), exec_vf_u128(10u128), exec_ve_u128(5u128), exec_ve_u128(10u128));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH v u128: {:?}", r); }
            // spec: vf_usize(5usize) = true, vf_usize(10usize) = false, ve_usize(5usize) = false, ve_usize(10usize) = true
            let r = (exec_vf_usize(5usize), exec_vf_usize(10usize), exec_ve_usize(5usize), exec_ve_usize(10usize));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH v usize: {:?}", r); }
            // spec: vf_i8(5i8) = true, vf_i8(10i8) = false, ve_i8(5i8) = false, ve_i8(10i8) = true
            let r = (exec_vf_i8(5i8), exec_vf_i8(10i8), exec_ve_i8(5i8), exec_ve_i8(10i8));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH v i8: {:?}", r); }
            // spec: vf_i16(5i16) = true, vf_i16(10i16) = false, ve_i16(5i16) = false, ve_i16(10i16) = true
            let r = (exec_vf_i16(5i16), exec_vf_i16(10i16), exec_ve_i16(5i16), exec_ve_i16(10i16));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH v i16: {:?}", r); }
            // spec: vf_i32(5i32) = true, vf_i32(10i32) = false, ve_i32(5i32) = false, ve_i32(10i32) = true
            let r = (exec_vf_i32(5i32), exec_vf_i32(10i32), exec_ve_i32(5i32), exec_ve_i32(10i32));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH v i32: {:?}", r); }
            // spec: vf_i64(5i64) = true, vf_i64(10i64) = false, ve_i64(5i64) = false, ve_i64(10i64) = true
            let r = (exec_vf_i64(5i64), exec_vf_i64(10i64), exec_ve_i64(5i64), exec_ve_i64(10i64));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH v i64: {:?}", r); }
            // spec: vf_i128(5i128) = true, vf_i128(10i128) = false, ve_i128(5i128) = false, ve_i128(10i128) = true
            let r = (exec_vf_i128(5i128), exec_vf_i128(10i128), exec_ve_i128(5i128), exec_ve_i128(10i128));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH v i128: {:?}", r); }
            // spec: vf_isize(5isize) = true, vf_isize(10isize) = false, ve_isize(5isize) = false, ve_isize(10isize) = true
            let r = (exec_vf_isize(5isize), exec_vf_isize(10isize), exec_ve_isize(5isize), exec_ve_isize(10isize));
            if r != (true, false, false, true) { bad += 1; println!("MISMATCH v isize: {:?}", r); }
            let r = (exec_uf_path(5u8), exec_uf_path(10u8));
            if r != (true, false) { bad += 1; println!("MISMATCH uf_path: {:?}", r); }
            println!("mismatches: {}", bad);
        }
    } => Ok(())
}

// Independence pair for builtin_macros/src/contrib/exec_spec.rs:173 atoms 0, 1, 2, 3, 4, 5, 6, 7
test_verify_one_file! {
    #[test] es_type_errors verus_code! {
        use vstd::prelude::*;
        use vstd::contrib::exec_spec::*;
        use std::collections::{HashMap, HashSet};

        exec_spec_unverified! {
            spec fn f0(x: Vec<u8>) -> bool { true }
        }

        exec_spec_unverified! {
            spec fn f1(x: HashMap<u8, u8>) -> bool { true }
        }

        exec_spec_unverified! {
            spec fn f2(x: HashSet<u8>) -> bool { true }
        }

        exec_spec_unverified! {
            spec fn f3(x: ExecMultiset<u8>) -> bool { true }
        }

        exec_spec_unverified! {
            spec fn f4(x: String) -> bool { true }
        }

        exec_spec_unverified! {
            spec fn f5(x: str) -> bool { true }
        }

        exec_spec_unverified! {
            spec fn f6(x: nat) -> bool { true }
        }

        exec_spec_unverified! {
            spec fn f7(x: int) -> bool { true }
        }
    } => Err(err) => assert_vir_error_msgs(err, &["Type cannot be compiled from spec code to exec code. Hint: supported types are primitive integers", "Type cannot be compiled from spec code to exec code. Hint: supported types are primitive integers", "Type cannot be compiled from spec code to exec code. Hint: supported types are primitive integers", "Type cannot be compiled from spec code to exec code. Hint: supported types are primitive integers", "Type cannot be compiled from spec code to exec code. Hint: supported types are primitive integers", "Type cannot be compiled from spec code to exec code. Hint: supported types are primitive integers", "Type cannot be compiled from spec code to exec code. Hint: supported types are primitive integers", "Type cannot be compiled from spec code to exec code. Hint: supported types are primitive integers"])
}

// Independence pair for builtin_macros/src/contrib/set_build.rs:59 atom 1 `input.peek3(Token![:])`
test_verify_one_file! {
    #[test] sb_exists_untyped verus_code! {
        use vstd::prelude::*;

        use vstd::contrib::set_build;

        proof fn t1() {
            let s = set_build!{ (x, x): (u8, u8) | exists x };
        }
    } => Err(err) => assert_vir_error_msg(err, "unexpected token")
}

// Independence pair for builtin_macros/src/contrib/set_build.rs:227 atom 0 `path.qself.is_none()`, atom 1 `path.path.get_ident() == Some(x)`; builtin_macros/src/contrib/set_build.rs:258 atom 0 `path.qself.is_none()`
test_verify_one_file! {
    #[test] sb_paths verus_code! {
        use vstd::prelude::*;

        use vstd::iset::*;
        use vstd::set::*;
        use vstd::contrib::set_build;

        pub trait Tr { const K: u8; }
        pub struct S;
        impl Tr for S { const K: u8 = 7; }

        proof fn t2() {
            let s = set_build!{ <S as Tr>::K: u8 | exists x: u8 };
            let y: u8 = 3;
            let s2 = set_build!{ y: u8 | exists x: u8 };
        }

        proof fn t3() {
            let s = set_build!{ (<S as Tr>::K, x): (u8, u8) | x: u8 };
            assert(s.contains((7u8, 1u8)));
        }
    } => Ok(())
}

// Independence pair for builtin_macros/src/contrib/spec_derive.rs:557 atom 0 `type_path.path.segments.len() == 1`
test_verify_one_file! {
    #[test] sd_str_path verus_code! {
        use vstd::prelude::*;
        use vstd::contrib::{make_spec_type, self_view};

        #[make_spec_type]
        pub struct T1 {
            pub a: u32,
            pub s: &'static core::primitive::str,
        }
    } => Ok(())
}

// Independence pair for builtin_macros/src/syntax_trait.rs:134 atom 1 `attr.path().segments[0].ident == ...`, atom 2 `attr.path().segments[1].ident == ...`; builtin_macros/src/syntax_trait.rs:230 atom 1 `attr.path().segments[0].ident.to_...`
test_verify_one_file! {
    #[test] st_ext_attrs verus_code! {
        use vstd::prelude::*;

        #[verifier::external]
        pub trait T {
            fn f(&self) -> usize;
        }

        #[verifier::external_trait_specification]
        #[rustfmt::skip]
        #[verifier::external_trait_extension(TSpec via TSpecImpl)]
        pub trait ExT {
            type ExternalTraitSpecificationFor: T;

            #[rustfmt::skip]
            #[verifier::opaque]
            spec fn s(&self) -> bool;

            fn f(&self) -> (r: usize)
                ensures self.s() ==> r > 7;
        }

        impl T for u32 {
            fn f(&self) -> (r: usize) { 10 }
        }

        impl TSpecImpl for u32 {
            open spec fn s(&self) -> bool { true }
        }

        fn main() {
            let x: u32 = 0;
            let r = x.f();
        }
    } => Err(err) => assert_vir_error_msg(err, "opaque has no effect on a function without a body")
}

// Independence pair for builtin_macros/src/struct_decl_inv.rs:1089 atom 0 `is_atomic_ghost`, atom 1 `concrete_args.len() != 2`
test_verify_one_file! {
    #[test] swi_bad_atomic verus_code! {
        use vstd::prelude::*;
        use vstd::atomic_ghost::AtomicU64;

        struct_with_invariants!{
            pub struct S {
                x: AtomicU64<_, _>,
            }
            closed spec fn wf(self) -> bool {
                invariant on x is (v: u64, g: ()) { true }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "struct_with_invariants: cannot handle this type")
}

// Independence pair for builtin_macros/src/struct_decl_inv.rs:922 atoms 0, 1; builtin_macros/src/struct_decl_inv.rs:932 atoms 0, 1, 3; builtin_macros/src/struct_decl_inv.rs:947 atoms 0, 1, 3; builtin_macros/src/struct_decl_inv.rs:1367 atoms 0, 1; builtin_macros/src/struct_decl_inv.rs:1388 atom 1; builtin_macros/src/struct_decl_inv.rs:1407 atoms 0, 1, 3
test_verify_one_file! {
    #[test] swi_generics code! {
        use vstd::prelude::*;
        use vstd::atomic_ghost::AtomicU64;
        use vstd::invariant::*;
        pub trait Tr2 { const C: usize; }
        impl Tr2 for u8 { const C: usize = 1; }
        verus! {
        pub trait Tr { type T; spec fn k() -> u64; }
        pub mod m { pub const N: u64 = 3; pub const K: usize = 2; }
        use core::mem::size_of;
        pub struct Pred;
        impl InvariantPredicate<(), u64> for Pred { open spec fn inv(k: (), v: u64) -> bool { true } }

        struct_with_invariants!{
            pub struct S<'a, 'b: 'a + 'static, A: Tr + 'a, B: Copy + Into<u64>, C: 'a + Sized, const N: usize>
                where A::T: Copy, B: Into<u64>, ::core::marker::PhantomData<C>: Sized, Vec<B>: Clone,
                      <A as Tr>::T: Sized, C: Sized, [u8; N]: Sized, [u8; m::K]: Sized, [u8; <u8 as Tr2>::C]: Sized,
                      [u8; ::core::mem::size_of::<u8>()]: Sized, [u8; size_of::<u16>()]: Sized,
            {
                x: AtomicU64<_, (Option<B>, ::core::marker::PhantomData<A>), _>,
                y: AtomicU64<_, Vec<C>, _>,
                w: AtomicU64<_, ([u8; N], [u8; m::K], [u8; <u8 as Tr2>::C], [u8; ::core::mem::size_of::<u8>()], [u8; size_of::<u16>()]), _>,
                z: AtomicInvariant<(), u64, Pred>,
                r: &'a C,
                q: AtomicU64<_, &'b u8, _>,
                r2: &'b u8,
            }
            closed spec fn wf(self) -> bool {
                invariant on x is (v: u64, g: (Option<B>, ::core::marker::PhantomData<A>)) {
                    &&& v <= ::core::primitive::u64::MAX
                    &&& v + 0 == v + (N - N) || v >= m::N || <A as Tr>::k() == v || A::k() == v || g.0 == Option::<B>::None || true
                }
                invariant on w is (v: u64, g: ([u8; N], [u8; m::K], [u8; <u8 as Tr2>::C], [u8; ::core::mem::size_of::<u8>()], [u8; size_of::<u16>()])) {
                    true
                }
                invariant on q is (v: u64, g: &'b u8) { true }
                invariant on y is (v: u64, g: Vec<C>) {
                    v == v && g.len() == g.len()
                }
            }
        }
        }
    } => Ok(())
}

// Independence pair for builtin_macros/src/syntax.rs:6179 atom 0 `t == "int"`
test_verify_one_file! {
    #[test] syn_exec_cast_int_nat verus_code! {
        use vstd::prelude::*;

        fn f(x: u8) {
            let a = x as int;
            let b = x as nat;
            let c = x as u64;
        }
    } => Err(err) => assert_vir_error_msgs(err, &["The Verus types 'nat' and 'int' can only be used in ghost code (e.g., in a 'spec' or 'proof'", "The Verus types 'nat' and 'int' can only be used in ghost code (e.g., in a 'spec' or 'proof'"])
}

// Independence pair for builtin_macros/src/syntax.rs:6050 atoms 1, 2; builtin_macros/src/syntax.rs:6062 atoms 3, 4, 5
test_verify_one_file! {
    #[test] syn_external_const verus_code! {
        use vstd::prelude::*;

        #[verifier(external)]
        const A: u8 = 1;
        #[verifier(external_body)]
        const B: u8 = 2;
        #[allow(dead_code)]
        const C: u8 = 3;
        #[verifier::external]
        const D: u8 = 4;
        #[verifier::loop_isolation(false)]
        open fn e1() {}
        #[verus::internal(something)]
        open fn e2() {}
        #[verifier::a::b]
        const F: u8 = 6;
        #[rustfmt::skip]
        const E: u8 = 5;
        #[verus::other(x)]
        open fn e3() {}
        #[allow(dead_code)]
        const fn cf() -> u8 { 1 }
    } => Err(err) => assert_vir_error_msgs(err, &["only `spec` functions can be marked `open`, `closed`, or `uninterp`", "only `spec` functions can be marked `open`, `closed`, or `uninterp`", "only `spec` functions can be marked `open`, `closed`, or `uninterp`"])
}

// Independence pair for builtin_macros/src/syntax.rs:4302 atom 1 `trigger.len() == 0`; builtin_macros/src/syntax.rs:4305 atom 1 `trigger.len() == 0`
test_verify_one_file! {
    #[test] syn_trigger_attr_args verus_code! {
        use vstd::prelude::*;

        spec fn f(x: int) -> bool;
        spec fn a() -> bool { forall|x: int| #![auto(f(x))] f(x) }
        spec fn b() -> bool { forall|x: int| #![all_triggers(f(x))] f(x) }
    } => Err(err) => assert_vir_error_msgs(err, &["expected trigger", "expected trigger"])
}

// Independence pair for builtin_macros/src/unerased_proxies.rs:117 atom 0 `is_simple_const_expr(&e.left)`, atom 1 `is_simple_const_expr(&e.right)`; builtin_macros/src/unerased_proxies.rs:163 atom 1 `!is_external(&impl_item_fn.attrs)`
test_verify_one_file! {
    #[test] up_consts verus_code! {
        use vstd::prelude::*;

        pub const fn k() -> (r: u8) ensures r == 3 { 3 }

        pub trait Tr1 { const D: u8; }
        pub trait Tr2 { const C: u8; }

        pub struct S;

        impl Tr1 for S {
            const D: u8 = 1 + k();
        }

        impl Tr2 for S {
            const C: u8 = k() + 1;
        }

        impl S {
            #[verifier::external]
            pub const fn g() -> u8 { 1 }
        }
    } => Err(err) => assert_vir_error_msgs(err, &["Verus does not support const items in traits, except for simple expressions and external_body", "Verus does not support const items in traits, except for simple expressions and external_body"])
}
