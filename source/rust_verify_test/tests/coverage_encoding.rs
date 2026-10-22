// Branch-condition (MC/DC) coverage tests: VIR to SST to AIR encoding, polymorphism, simplification and error expansion.
// Each test's comment names the decisions (file:line) and the conditions (atoms, numbered from 0
// in source order) for which the test supplies an evaluation that no other test supplies, so that
// the condition is shown to independently change the decision's outcome. See
// COVERAGE-UNREACHABLE.md for the conditions that no test can cover.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Independence pair for vir/src/ast_util.rs:273 atoms 0, 1; vir/src/ast_util.rs:278 atoms 0, 1, 2; vir/src/ast_util.rs:280 atom 0
test_verify_one_file! {
    #[test] ast_util_bounds_merge code! {
        use vstd::prelude::*;

        pub trait Two { type X; type Y; }
        pub trait Tr<const N: usize, const M: u8>:
            Two<X = u8, Y = u16> + core::ops::Add<u8, Output = u8> + core::ops::Add<u16, Output = u8> + Iterator<Item = u8>
        {
            fn a(&self) -> u8;
            fn b(&self) -> u8;
        }

        verus! {
        #[verifier::external_trait_specification]
        pub trait ExTwo {
            type ExternalTraitSpecificationFor: Two;
            type X;
            type Y;
        }

        #[verifier::external_trait_specification]
        pub trait ExTr1<const N: usize, const M: u8>:
            Two<X = u8, Y = u16> + core::ops::Add<u8, Output = u8> + core::ops::Add<u16, Output = u8> + Iterator<Item = u8>
        {
            type ExternalTraitSpecificationFor: Tr<N, M>;
            fn a(&self) -> u8;
        }

        #[verifier::external_trait_specification]
        pub trait ExTr2<const N: usize, const M: u8>:
            Two<X = u8, Y = u16> + core::ops::Add<u8, Output = u8> + core::ops::Add<u16, Output = u8> + Iterator<Item = u8>
        {
            type ExternalTraitSpecificationFor: Tr<N, M>;
            fn b(&self) -> u8;
        }

        }
    } => Ok(())
}

// Independence pair for vir/src/ast_util.rs:278 atom 3 `types_equal(t1, t2)`
test_verify_one_file! {
    #[test] ast_util_bounds_typequality_autospec verus_code! {
        use vstd::prelude::*;

        pub open spec fn sf<X: Iterator<Item = u16>>(x: X) -> u8 { 0 }

        #[verifier::when_used_as_spec(sf)]
        pub fn f<X: Iterator<Item = u8>>(x: X) -> (r: u8)
            ensures r == 0
        { 0 }
    } => Err(err) => assert_vir_error_msg(err, "when_used_as_spec function should have the same type bounds")
}

// Independence pair for vir/src/ast_util.rs:158 atom 0 `n_types_equal(ts1, ts2)`
test_verify_one_file! {
    #[test] ast_util_closure_get_variant_field verus_code! {
        use vstd::prelude::*;

        pub enum E<F> { V(F) }

        spec fn same<A>(a: A, b: A) -> bool { a == b }

        fn diff_params() {
            let c1 = |x: u8| x;
            let c2 = |x: u16| x;
            let e = E::V(c1);
            assert(same(verus_builtin::get_variant_field(e, "V", "0"), c2));
        }
    } => Err(err) => assert_vir_error_msg(err, "field has the wrong type")
}

// Independence pair for vir/src/ast_util.rs:158 atom 3 `kind1 == kind2`
test_verify_one_file! {
    #[test] ast_util_closure_get_variant_field_id verus_code! {
        use vstd::prelude::*;

        pub enum E<F> { V(F) }

        spec fn same<A>(a: A, b: A) -> bool { a == b }

        fn diff() {
            let c1 = |x: u8| x;
            let c2 = |x: u8| x;
            let e = E::V(c1);
            assert(same(verus_builtin::get_variant_field(e, "V", "0"), c2));
        }
    } => Err(err) => assert_vir_error_msg(err, "field has the wrong type")
}

// Independence pair for vir/src/ast_util.rs:158 atom 2 `id1 == id2`
test_verify_one_file! {
    #[test] ast_util_closure_get_variant_field_kind verus_code! {
        use vstd::prelude::*;

        pub enum E<F> { V(F) }

        spec fn same<A>(a: A, b: A) -> bool { a == b }

        fn diff_kind(v: Vec<u8>) {
            let c1 = |x: u8| x;
            let c2 = move |x: u8| { let w = v; x };
            let e = E::V(c1);
            assert(same(verus_builtin::get_variant_field(e, "V", "0"), c2));
        }
    } => Err(err) => assert_vir_error_msg(err, "field has the wrong type")
}

// Independence pair for vir/src/ast_util.rs:158 atom 1 `types_equal(t1, t2)`
test_verify_one_file! {
    #[test] ast_util_closure_get_variant_field_ret verus_code! {
        use vstd::prelude::*;

        pub enum E<F> { V(F) }

        spec fn same<A>(a: A, b: A) -> bool { a == b }

        fn diff() {
            let c1 = |x: u8| x;
            let c2 = |x: u8| x as u16;
            let e = E::V(c1);
            assert(same(verus_builtin::get_variant_field(e, "V", "0"), c2));
        }
    } => Err(err) => assert_vir_error_msg(err, "field has the wrong type")
}

// Independence pair for vir/src/ast_util.rs:167 atom 2 `(match (a1, a2) { (None, None) =>...`
test_verify_one_file! {
    #[test] ast_util_types_equal_box_alloc verus_code! {
        use vstd::prelude::*;
        use std::alloc::Global;

        uninterp spec fn gt<F>() -> int;

        proof fn n_box_alloc() {
            assert(gt::<Box<u8, Global>>() == gt::<Box<u8, &'static Global>>()) by (compute); // FAILS
        }
        proof fn m_box_alloc() {
            assert(gt::<Box<u8, Global>>() != gt::<Box<u8, &'static Global>>()) by (compute); // FAILS
        }
        proof fn p_box_alloc() {
            assert(gt::<Box<u8, &'static Global>>() == gt::<Box<u8, &'static Global>>()) by (compute);
        }
    } => Err(err) => assert_fails(err, 2)
}

// Independence pair for vir/src/ast_util.rs:202 atoms 0, 1; vir/src/ast_util.rs:209 atoms 0, 1
test_verify_one_file! {
    #[test] ast_util_types_equal_fnvals verus_code! {
        use vstd::prelude::*;

        uninterp spec fn gg<F>(f: F) -> int;

        fn one(x: u8) -> u8 { x }
        fn two(x: u8) -> u8 { x }
        fn idf<T>(x: T) -> T { x }
        fn mk1() -> impl Fn(u8) -> u8 { |x: u8| x }
        fn mk2() -> impl Fn(u8) -> u8 { |x: u8| x }
        fn mkg<T>(t: T) -> impl Fn(u8) -> u8 { |x: u8| x }

        fn n_closure_params() {
            let c1 = |x: u8| x;
            let c3 = |x: u16| x;
            assert(gg(c1) == gg(c3)) by (compute); // FAILS
        }
        fn n_closure_ret() {
            let c1 = |x: u8| x;
            let c4 = |x: u8| x as u16;
            assert(gg(c1) == gg(c4)) by (compute); // FAILS
        }
        fn n_closure_id() {
            let c1 = |x: u8| x;
            let c2 = |x: u8| x;
            assert(gg(c1) == gg(c2)) by (compute); // FAILS
        }
        fn p_closure_same() {
            let c1 = |x: u8| x;
            assert(gg(c1) == gg(c1)) by (compute);
        }
        fn n_fndef_name() {
            assert(gg(one) == gg(two)) by (compute); // FAILS
        }
        fn n_fndef_args() {
            assert(gg(idf::<u8>) == gg(idf::<u16>)) by (compute); // FAILS
        }
        fn p_fndef_same() {
            assert(gg(idf::<u8>) == gg(idf::<u8>)) by (compute);
        }
        fn n_opaque_path() {
            let a = mk1();
            let b = mk2();
            assert(gg(a) == gg(b)) by (compute); // FAILS
        }
        fn n_opaque_args() {
            let a = mkg(1u8);
            let b = mkg(1u16);
            assert(gg(a) == gg(b)) by (compute); // FAILS
        }
        fn p_opaque_same() {
            let a = mk1();
            assert(gg(a) == gg(a)) by (compute);
        }
        // e != v direction: two calls at different type arguments are not definitely different either.
        fn m_fndef_name() { assert(gg(one) != gg(two)) by (compute); } // FAILS
        /* FAILS */ fn m_opaque_path() { let a = mk1(); let b = mk2(); assert(gg(a) != gg(b)) by (compute); }
    } => Err(err) => assert_fails(err, 9)
}

// Independence pair for vir/src/autospec.rs:92 atom 0 `!is_trait_default`, atom 1 `functions.contains_key(&new_resol...`
test_verify_one_file! {
    #[test] autospec_trait_default code! {
        use vstd::prelude::*;
        verus! {
        trait T {
            spec fn f() -> bool { true }

            #[verifier::when_used_as_spec(f)]
            fn g() -> (r: bool)
                ensures r == Self::f();

            #[verifier::when_used_as_spec(f)]
            fn h() -> (r: bool)
                ensures r == Self::f()
            {
                proof { assert(Self::f() == Self::f()); }
                let r = Self::g();
                r
            }
        }

        struct S;
        impl T for S {
            fn g() -> bool { true }
        }

        struct U;
        impl T for U {
            spec fn f() -> bool { false }
            fn g() -> bool { false }
        }

        proof fn test_s() {
            assert(S::g() == S::f());
            assert(S::g());
            assert(S::h());
            assert(U::h() == U::f());
            assert(!U::h());
        }

        fn exec_check() {
            let a = S::h();
            assert(a);
            let b = U::h();
            assert(!b);
        }
        }

        #[verifier::external]
        fn main() {
            assert!(S::g() && S::h());
            assert!(!U::g() && !U::h());
            exec_check();
            println!("autospec_trait_default: runtime checks passed");
        }
    } => Ok(())
}

// Independence pair for vir/src/bitvector_to_air.rs:1070 atom 0 `lhs_extend == Extend::Zero`
test_verify_one_file! {
    #[test] bv_nat_cast_lhs_signed verus_code! {
        use vstd::prelude::*;

        proof fn lhs_signed(a: i8, b: u8) {
            assert(((a as int) + (b as int)) as nat >= 0) by (bit_vector);
        }
    } => Err(err) => assert_vir_error_msg(err, "not supported: nat cast here")
}

// Independence pair for vir/src/bitvector_to_air.rs:1070 atom 1 `rhs_extend == Extend::Zero`
test_verify_one_file! {
    #[test] bv_nat_cast_rhs_signed verus_code! {
        use vstd::prelude::*;

        proof fn rhs_signed(a: u8, b: i8) {
            assert(((a as int) + (b as int)) as nat >= 0) by (bit_vector);
        }
    } => Err(err) => assert_vir_error_msg(err, "not supported: nat cast here")
}

// Independence pair for vir/src/bitvector_to_air.rs:1070 atom 2 `matches!(arith_op, ArithOp::Add |...`
test_verify_one_file! {
    #[test] bv_nat_cast_sub verus_code! {
        use vstd::prelude::*;

        proof fn sub_unsigned(a: u8, b: u8) {
            assert(((a as int) - (b as int)) as nat >= 0) by (bit_vector);
        }
    } => Err(err) => assert_vir_error_msg(err, "not supported: nat cast here")
}

// Independence pair for vir/src/expand_errors.rs:107 atom 1 `body.as_ref().is_some_and(|stm| g...`
test_verify_one_file_with_options! {
    #[test] expand_errors_assert_in_atomic_call_body ["--expand-errors"] => verus_code! {
        use vstd::prelude::*;
        use vstd::atomic::*;

        tracked struct Token;

        fn generic_atomic(v: u8)
            atomically (atomic_update) {
                (old: Token) -> (new: Commit<Token>),
                ensures new@ == old,
            },
        {
            try_open_atomic_update!(atomic_update, token => {
                Tracked(Commit(token))
            });
        }

        fn client() {
            generic_atomic(5u8) atomically |update| {
                let tracked t = update(Token);
                let ghost x: int = 2;
                assert(x == 3 && x == 2); // FAILS
            };
        }
    } => Err(err) => assert_one_fails(err)
}

// Independence pair for vir/src/ast_util.rs:167 atom 0 `d1 == d2`
test_verify_one_file! {
    #[test] sig_decor_kind verus_code! {
        use vstd::prelude::*;

        pub trait Tr { type X; type Y; }
        pub trait Tr2 { type X; }
        pub trait Dy { spec fn d(&self) -> int; }
        pub trait Dy2 { spec fn d(&self) -> int; }
        spec fn f(g: &u8, n: nat) -> int
            decreases n
        {
            decreases_by(f_dec);
            if n == 0 { 0 } else { f(g, (n - 1) as nat) }
        }
        #[verifier(decreases_by)]
        proof fn f_dec(g: Box<u8>, n: nat) { }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same parameters")
}

// Independence pair for vir/src/ast_util.rs:163 atom 1 `n_types_equal(ts1, ts2)`
test_verify_one_file! {
    #[test] sig_dyn_args verus_code! {
        use vstd::prelude::*;

        pub trait Tr { type X; type Y; }
        pub trait Tr2 { type X; }
        pub trait Dy { spec fn d(&self) -> int; }
        pub trait Dy2 { spec fn d(&self) -> int; }
        pub trait DyG<T> { spec fn d(&self) -> T; }
        spec fn f(g: Box<dyn DyG<u8>>, n: nat) -> int
            decreases n
        {
            decreases_by(f_dec);
            if n == 0 { 0 } else { f(g, (n - 1) as nat) }
        }
        #[verifier(decreases_by)]
        proof fn f_dec(g: Box<dyn DyG<u16>>, n: nat) { }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same parameters")
}

// Independence pair for vir/src/ast_util.rs:163 atom 0 `path1 == path2`
test_verify_one_file! {
    #[test] sig_dyn_path verus_code! {
        use vstd::prelude::*;

        pub trait Tr { type X; type Y; }
        pub trait Tr2 { type X; }
        pub trait Dy { spec fn d(&self) -> int; }
        pub trait Dy2 { spec fn d(&self) -> int; }
        spec fn f(g: Box<dyn Dy>, n: nat) -> int
            decreases n
        {
            decreases_by(f_dec);
            if n == 0 { 0 } else { f(g, (n - 1) as nat) }
        }
        #[verifier(decreases_by)]
        proof fn f_dec(g: Box<dyn Dy2>, n: nat) { }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same parameters")
}

// Independence pair for vir/src/ast_util.rs:193 atom 0 `n_types_equal(trait_typ_args1, tr...`
test_verify_one_file! {
    #[test] sig_proj_args verus_code! {
        use vstd::prelude::*;

        pub trait Tr { type X; type Y; }
        pub trait Tr2 { type X; }
        pub trait Dy { spec fn d(&self) -> int; }
        pub trait Dy2 { spec fn d(&self) -> int; }
        spec fn f<A: Tr, B: Tr>(g: <A as Tr>::X, n: nat) -> int
            decreases n
        {
            decreases_by(f_dec::<A, B>);
            if n == 0 { 0 } else { f::<A, B>(g, (n - 1) as nat) }
        }
        #[verifier(decreases_by)]
        proof fn f_dec<A: Tr, B: Tr>(g: <B as Tr>::X, n: nat) { }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same parameters")
}

// Independence pair for vir/src/ast_util.rs:193 atom 2 `name1 == name2`
test_verify_one_file! {
    #[test] sig_proj_name verus_code! {
        use vstd::prelude::*;

        pub trait Tr { type X; type Y; }
        pub trait Tr2 { type X; }
        pub trait Dy { spec fn d(&self) -> int; }
        pub trait Dy2 { spec fn d(&self) -> int; }
        spec fn f<A: Tr>(g: <A as Tr>::X, n: nat) -> int
            decreases n
        {
            decreases_by(f_dec::<A>);
            if n == 0 { 0 } else { f::<A>(g, (n - 1) as nat) }
        }
        #[verifier(decreases_by)]
        proof fn f_dec<A: Tr>(g: <A as Tr>::Y, n: nat) { }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same parameters")
}

// Independence pair for vir/src/ast_util.rs:193 atom 1 `trait_path1 == trait_path2`
test_verify_one_file! {
    #[test] sig_proj_trait verus_code! {
        use vstd::prelude::*;

        pub trait Tr { type X; type Y; }
        pub trait Tr2 { type X; }
        pub trait Dy { spec fn d(&self) -> int; }
        pub trait Dy2 { spec fn d(&self) -> int; }
        spec fn f<A: Tr + Tr2>(g: <A as Tr>::X, n: nat) -> int
            decreases n
        {
            decreases_by(f_dec::<A>);
            if n == 0 { 0 } else { f::<A>(g, (n - 1) as nat) }
        }
        #[verifier(decreases_by)]
        proof fn f_dec<A: Tr + Tr2>(g: <A as Tr2>::X, n: nat) { }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same parameters")
}

// Independence pair for vir/src/ast_util.rs:153 atom 0 `n_types_equal(ts1, ts2)`; vir/src/ast_util.rs:236 atom 0 `typs1.len() == typs2.len()`
test_verify_one_file! {
    #[test] sig_specfn_arity verus_code! {
        use vstd::prelude::*;

        pub trait Tr { type X; type Y; }
        pub trait Tr2 { type X; }
        pub trait Dy { spec fn d(&self) -> int; }
        pub trait Dy2 { spec fn d(&self) -> int; }
        spec fn f(g: spec_fn(int) -> int, n: nat) -> int
            decreases n
        {
            decreases_by(f_dec);
            if n == 0 { 0 } else { f(g, (n - 1) as nat) }
        }
        #[verifier(decreases_by)]
        proof fn f_dec(g: spec_fn(int, int) -> int, n: nat) { }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same parameters")
}

// Independence pair for vir/src/ast_util.rs:153 atom 1 `types_equal(t1, t2)`
test_verify_one_file! {
    #[test] sig_specfn_ret verus_code! {
        use vstd::prelude::*;

        pub trait Tr { type X; type Y; }
        pub trait Tr2 { type X; }
        pub trait Dy { spec fn d(&self) -> int; }
        pub trait Dy2 { spec fn d(&self) -> int; }
        spec fn f(g: spec_fn(int) -> int, n: nat) -> int
            decreases n
        {
            decreases_by(f_dec);
            if n == 0 { 0 } else { f(g, (n - 1) as nat) }
        }
        #[verifier(decreases_by)]
        proof fn f_dec(g: spec_fn(int) -> bool, n: nat) { }
    } => Err(err) => assert_vir_error_msg(err, "decreases_by/recommends_by function should have the same parameters")
}

// Independence pair for vir/src/ast_simplify.rs:1262 atom 0 `rename_ok`
test_verify_one_file! {
    #[test] simplify_hygienic_dup_params code! {
        use vstd::prelude::*;
        macro_rules! mk {
            ($y:ident) => {
                verus! {
                    #[verifier::external_body]
                    fn f(x: u8, $y: u8) -> u8 {
                        x.wrapping_mul(10).wrapping_add($y)
                    }
                }
            };
        }
        mk!(x);
        verus! {
        fn test() {
            let r = f(1, 2);
        }
        }
        fn main() {
            let r = f(1, 2);
            assert!(r == 12);
            let r2 = f(9, 0);
            assert!(r2 == 90);
            println!("f(1,2)={} f(9,0)={}", r, r2);
        }
    } => Ok(())
}

// Independence pair for vir/src/sst_util.rs:1124 atom 0 `func.x.params.len() > 0`
test_verify_one_file! {
    #[test] sst_call_requires_fndef verus_code! {
        use vstd::prelude::*;

        fn one(x: u8) requires x > 3 {}
        spec fn flag() -> bool;
        fn zero() requires flag() {}

        fn take<F: Fn(u8)>(f: F) {}
        fn take0<F: Fn()>(f: F) {}

        fn good_one() { take(one); one(5); }
        fn bad_one() { take(one); one(2); } // FAILS
        fn good_zero() requires flag() { take0(zero); zero(); }
        fn bad_zero() { take0(zero); zero(); } // FAILS
        fn good_via_call_requires(y: u8) {
            let f = one;
            if y > 3 { assert(call_requires(f, (y,))); f(y); }
        }
        spec fn gflag<T>() -> bool;
        fn gen0<T>() requires gflag::<T>() {}
        fn good_gen0() requires gflag::<u8>() { take0(gen0::<u8>); gen0::<u8>(); }
        /* FAILS */ fn bad_gen0() requires gflag::<u16>() { take0(gen0::<u8>); gen0::<u8>(); }
    } => Err(err) => assert_fails(err, 3)
}

// Independence pair for vir/src/ast_to_sst_crate.rs:21 atom 0 `!crate::ast_util::is_visible_to(&...`
test_verify_one_file! {
    #[test] sst_crate_private_lemma_in_pub_group verus_code! {
        use vstd::prelude::*;

        mod a {
            use vstd::prelude::*;
            pub uninterp spec fn f(x: int) -> int;
            broadcast axiom fn priv_lemma(x: int) ensures #[trigger] f(x) > 0;
            pub broadcast group g { priv_lemma }
        }
        mod b {
            use vstd::prelude::*;
            use crate::a::*;
            broadcast use crate::a::g;
            proof fn t() { assert(f(3) > 0); } // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// Independence pair for vir/src/sst_vars.rs:203 atom 0 `v1 == v2`
test_verify_one_file! {
    #[test] sst_vars_guard_assign_other_struct code! {
        use vstd::prelude::*;
        verus! {
        pub struct S1 { pub x: u8 }
        pub struct S2 { pub y: u8 }
        pub struct V { pub a: S1, pub b: S2 }

        pub fn f(v: V) -> (r: (u8, u8))
            ensures r.0 == 7, r.1 == v.a.x
        {
            let mut v = v;
            let r = match v.a.x {
                0 if { v.b.y = 7; true } => v.b.y,
                _ => { v.b.y = 7; v.b.y }
            };
            (r, v.a.x)
        }
        } // verus!
        fn main() {
            for x in [0u8, 1, 255] {
                let r = f(V { a: S1 { x }, b: S2 { y: 3 } });
                assert!(r.0 == 7 && r.1 == x);
                println!("x={} -> {:?}", x, r);
            }
        }
    } => Ok(())
}

// Independence pair for vir/src/triggers_auto.rs:501 atom 0 `is_pure1`, atom 1 `is_pure2`
test_verify_one_file! {
    #[test] triggers_auto_exteq_impure verus_code! {
        use vstd::prelude::*;

        uninterp spec fn s(i: int) -> Seq<int>;
        uninterp spec fn q(i: int) -> bool;

        proof fn lhs_impure()
            requires forall|i: int| #![all_triggers] q(i) ==> s(i + 1) =~= s(i),
            ensures q(3) ==> s(4) =~= s(3),
        {
        }

        proof fn rhs_impure()
            requires forall|i: int| #![all_triggers] q(i) ==> s(i) =~= s(i + 1),
            ensures q(3) ==> s(3) =~= s(4),
        {
        }
    } => Ok(())
}

// Independence pair for vir/src/triggers.rs:425 atom 1 `scope_entry.bnd_kind.is_outer_tri...`; vir/src/triggers.rs:441 atom 1 `scope_entry.bnd_kind.is_outer_tri...`
test_verify_one_file! {
    #[test] triggers_height_let verus_code! {
        use vstd::prelude::*;

        pub enum L { Nil, Cons(Box<L>) }
        spec fn p(x: L) -> bool;

        proof fn t1()
            requires forall|x: L| { let k = L::Cons(Box::new(L::Nil)); #[trigger] (decreases_to!(k => L::Nil)) && #[trigger] p(x) },
        {
        }

        proof fn t2()
            requires forall|x: L| { let k = L::Cons(Box::new(L::Nil)); #[trigger] (decreases_to!(k => x)) ==> p(x) },
        {
        }
    } => Ok(_) => ()
}
