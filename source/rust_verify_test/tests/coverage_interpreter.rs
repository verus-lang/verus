// Branch-condition (MC/DC) coverage tests: the assert-by-compute interpreter (vir/src/interpreter.rs).
// Each test's comment names the decisions (file:line) and the conditions (atoms, numbered from 0
// in source order) for which the test supplies an evaluation that no other test supplies, so that
// the condition is shown to independently change the decision's outcome. See
// COVERAGE-UNREACHABLE.md for the conditions that no test can cover.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Independence pair for vir/src/interpreter.rs:475 atom 0 `path_l != path_r`
test_verify_one_file! {
    #[test] interp_choose_ctor_paths verus_code! {
        use vstd::prelude::*;

        pub struct A { pub a: u8 }
        pub struct B { pub b: u8 }
        pub open spec fn idt(x: int) -> int { x }

        proof fn p_ctor() {
            assert((choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && A { a: 1 } == A { a: 1 })
                == (choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && B { b: 1 } == B { b: 1 })) by (compute);
        }
        proof fn n_ctor() {
            assert((choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && A { a: 1 } == A { a: 1 }) // FAILS
                != (choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && B { b: 1 } == B { b: 1 })) by (compute);
        }
    } => Err(err) => assert_one_fails(err)
}

// Independence pair for vir/src/interpreter.rs:333 atoms 0, 1; vir/src/interpreter.rs:336 atoms 0, 1; vir/src/interpreter.rs:545 atom 1
test_verify_one_file! {
    #[test] interp_choose_lambda_binder_types verus_code! {
        use vstd::prelude::*;

        pub struct A { pub a: u8 }
        pub struct B { pub b: u8 }
        pub open spec fn idt(x: int) -> int { x }

        proof fn p_path() {
            assert((choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: A| x) == (|y: A| x)) == (choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: B| x) == (|y: B| x))) by (compute); // FAILS
        }
        proof fn n_path() {
            assert((choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: A| x) == (|y: A| x)) != (choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: B| x) == (|y: B| x))) by (compute); // FAILS
        }
        proof fn p_args() {
            assert((choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: Option<u8>| x) == (|y: Option<u8>| x)) == (choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: Option<u16>| x) == (|y: Option<u16>| x))) by (compute); // FAILS
        }
        proof fn n_args() {
            assert((choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: Option<u8>| x) == (|y: Option<u8>| x)) != (choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: Option<u16>| x) == (|y: Option<u16>| x))) by (compute); // FAILS
        }
        proof fn p_formals() {
            assert((choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: spec_fn(u8) -> int| x) == (|y: spec_fn(u8) -> int| x)) == (choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: spec_fn(u16) -> int| x) == (|y: spec_fn(u16) -> int| x))) by (compute); // FAILS
        }
        proof fn n_formals() {
            assert((choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: spec_fn(u8) -> int| x) == (|y: spec_fn(u8) -> int| x)) != (choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: spec_fn(u16) -> int| x) == (|y: spec_fn(u16) -> int| x))) by (compute); // FAILS
        }
        proof fn p_res() {
            assert((choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: spec_fn(u8) -> int| x) == (|y: spec_fn(u8) -> int| x)) == (choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: spec_fn(u8) -> u8| x) == (|y: spec_fn(u8) -> u8| x))) by (compute); // FAILS
        }
        proof fn n_res() {
            assert((choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: spec_fn(u8) -> int| x) == (|y: spec_fn(u8) -> int| x)) != (choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: spec_fn(u8) -> u8| x) == (|y: spec_fn(u8) -> u8| x))) by (compute); // FAILS
        }
        proof fn p_body() {
            assert((choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: int| 1int) == (|y: int| x)) == (choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: int| 2int) == (|y: int| x))) by (compute); // FAILS
        }
        proof fn n_body() {
            assert((choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: int| 1int) == (|y: int| x)) != (choose|x: int| #![trigger idt(x)] idt(x) == idt(x) && (|y: int| 2int) == (|y: int| x))) by (compute); // FAILS
        }
    } => Err(err) => assert_fails(err, 10)
}

// Independence pair for vir/src/interpreter.rs:492 atom 2 `e_l.syntactic_eq(e_r)?`; vir/src/interpreter.rs:508 atom 1 `e_l.syntactic_eq(e_r)?`
test_verify_one_file! {
    #[test] interp_if_inner verus_code! {
        use vstd::prelude::*;

        spec fn ub(b: bool) -> bool;
        proof fn n_isvariant_if(c: bool) {
            assert(ub(((if c { None::<int> } else { Some(1int) }) is Some) == ((if c { Some(1int) } else { None::<int> }) is Some)) == ub(true)) by (compute); // FAILS
        }
        proof fn n_not_if(c: bool) {
            assert(ub(!(if c { true } else { false }) == !(if c { false } else { true })) == ub(true)) by (compute); // FAILS
        }
        proof fn n_field_if(c: bool) {
            assert(ub((if c { (1int, 2int) } else { (3int, 4int) }).0 == (if c { (5int, 2int) } else { (6int, 4int) }).0) == ub(true)) by (compute); // FAILS
        }
        proof fn t_isvariant_if_same(c: bool) {
            assert(((if c { None::<int> } else { Some(1int) }) is Some) == ((if c { None::<int> } else { Some(1int) }) is Some)) by (compute_only);
        }
    } => Err(err) => assert_fails(err, 3)
}

// Independence pair for vir/src/interpreter.rs:412 atom 0 `acc`, atom 1 `bnd_l.name == bnd_r.name`
test_verify_one_file! {
    #[test] interp_lambda_names verus_code! {
        use vstd::prelude::*;

        spec fn ub(b: bool) -> bool;
        proof fn n_lambda2_names() { assert(ub((|x: int, y: int| x + y) != (|z: int, y: int| z + y)) == ub(true)) by (compute); }
        proof fn n_lambda2_names2() { assert(ub((|x: int, y: int| x + y) != (|x: int, z: int| x + z)) == ub(true)) by (compute); }
        proof fn n_lambda_body() { assert(ub((|x: int| 1int) == (|x: int| 2int)) == ub(true)) by (compute); }
    } => Err(err) => assert_vir_error_msg(err, "Proof by computation included a closure literal that wasn't applied.  This is not yet supported.")
}

// Independence pair for vir/src/interpreter.rs:422 atom 1 `bnd_l.name == bnd_r.name`, atom 2 `bnd_l.a.syntactic_eq(&bnd_r.a)?`
test_verify_one_file! {
    #[test] interp_let_in_quant verus_code! {
        use vstd::prelude::*;

        spec fn ub(b: bool) -> bool;
        spec fn g(x: int, y: int) -> bool;
        proof fn n_let_name() { assert(ub((forall|x: int| #[trigger] g(x, 0) && { let a = x; g(a, 1) }) == (forall|x: int| #[trigger] g(x, 0) && { let b = x; g(b, 1) })) == ub(false)) by (compute); } // FAILS
        proof fn n_let_val() { assert(ub((forall|x: int| #[trigger] g(x, 0) && { let a = 1int; g(a, x) }) == (forall|x: int| #[trigger] g(x, 0) && { let a = 2int; g(a, x) })) == ub(true)) by (compute); } // FAILS
        proof fn n_let_val2() { assert(ub((forall|x: int| #[trigger] g(x, 0) && { let a = 1int; g(a, x) }) != (forall|x: int| #[trigger] g(x, 0) && { let a = 2int; g(a, x) })) == ub(true)) by (compute); } // FAILS
        proof fn t_let_same() { assert((forall|x: int| #[trigger] g(x, 0) && { let a = x; g(a, 1) }) == (forall|x: int| #[trigger] g(x, 0) && { let a = x; g(a, 1) })) by (compute_only); }
        proof fn t_let_same_val() { assert((forall|x: int| #[trigger] g(x, 0) && { let a = 1int; g(a, x) }) == (forall|x: int| #[trigger] g(x, 0) && { let a = 1int; g(a, x) })) by (compute_only); }
    } => Err(err) => assert_fails(err, 3)
}
