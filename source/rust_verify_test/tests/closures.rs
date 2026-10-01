#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        proof fn testfun1() {
            let f = |x: int| x + 1;
            assert(f(10) == 11);
            assert(f(20) == 21);
        }

        proof fn takefun(f: spec_fn(u32, u64) -> bool) -> (b: bool)
            ensures
                b == f(10, 20),
        {
            let b: bool = f(10, 20);
            b
        }

        proof fn testtake() {
            let b: bool = takefun(|x: u32, y: u64| (x as u64) < y);
            assert(b);
        }

        #[verifier(opaque)]
        spec fn apply_to_1(f: spec_fn(u8) -> u8) -> u8 {
            f(1)
        }

        proof fn refine_takefun(f: spec_fn(bool, bool) -> nat) {
            assert(f(true, false) >= 0);
        }

        proof fn test_refine(f: spec_fn(bool, bool) -> nat) {
            refine_takefun(|x: bool, y: bool| 10);
            assert(apply_to_1(|u: u8| 10) >= 0);
        }

        spec fn polytestfun<A>(a: A, f: spec_fn(A, A) -> A) -> A{
            f(a, a)
        }

        proof fn testfun<A>(a: A, b: bool) {
            let aa = polytestfun(a, |x: A, y: A| (if b { x } else { y }));
            assert(a == aa);
        }

        spec fn specf(x: u32, f: spec_fn(u32) -> u32) -> u32 {
            f(f(x))
        }

        proof fn test_specf(p: u32)
            requires
                p < 100,
        {
            let q: u32 = 3;
            assert(specf(10, |z: u32| add(add(add(z, 1), p), q)) == add(18, mul(2, p)));
        }

        proof fn test_specf_inference(p: u32)
            requires
                p < 100,
        {
            let q: u32 = 3;
            assert(specf(10, |z| add(add(add(z, 1), p), q)) == add(18, mul(2, p)));
        }

        proof fn test_refine_inference(f: spec_fn(bool, bool) -> nat) {
            refine_takefun(|x, y| 10);
            assert(apply_to_1(|u| 10) >= 0);
        }

        struct S {
            f: spec_fn(u8) -> u8,
        }

        proof fn test_fnspec_refinement_types(f: spec_fn(u8) -> u8, s: S) {
            let x = f(10);
            assert(x < 300);
            let g = s.f;
            let y = g(10);
            assert(y < 300);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 verus_code! {
        proof fn takefun(f: spec_fn(u32, u64) -> bool) -> bool {
            ensures(|b: bool| b == f(10, 20));

            #[verifier::spec] let b: bool = f(10, 20);
            b
        }

        proof fn testtake() {
            let b: bool = takefun(|x: u32, y: u64| (x as u64) < y);
            assert(!b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 verus_code! {
        spec fn polytestfun<A>(a: A, f: spec_fn(A, A) -> A) -> A{
            f(a, a)
        }

        proof fn testfun<A>(a: A, b: bool) {
            let aa = polytestfun(a, |x: A, y: A| (if b { x } else { y }));
            assert(!equal(a, aa)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails3 verus_code! {
        spec fn specf(x: u32, f: spec_fn(u32) -> u32) -> u32 {
            f(f(x))
        }

        proof fn test_specf(p: u32) {
            let q: u32 = 3;
            assert(specf(10, |z: u32| (z + 1 + p + q) as u32) == 18 + 2 * p); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails4 verus_code! {
        proof fn testfun1() {
            let f = |x: int| x + 1;
            assert(f(10) == 11);
            assert(f(20) == 22); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails5 verus_code! {
        proof fn refine_takefun(f: spec_fn(nat) -> int) {
            assert(f(10) >= 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// Regression tests for #3010.  Lambda bodies are represented over erased AIR
// sorts, but their source SpecFn type must remain part of the function value.
// Otherwise extensional equality at a refinement type can leak facts to values
// outside that refinement and prove false.
test_verify_one_file! {
    #[test] spec_fn_lambda_parameter_type_soundness_3010 verus_code! {
        proof fn unsound() ensures false { // FAILS
            assert((|x: nat| true) =~= (|x: nat| x >= 0));
            assert(!(|x: int| x >= 0)(-1int));
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] spec_fn_lambda_parameter_type_quantifier_soundness_3010 verus_code! {
        proof fn unsound() ensures false {
            let f = |x: int| x >= 0;
            let g = |x: int| true;
            assert forall|p: spec_fn(nat) -> bool, q: spec_fn(nat) -> bool|
                #![trigger p(0nat), q(0nat)]
                (forall|x: nat| #[trigger] p(x) == q(x))
                implies p == q by {
                assert(p =~= q);
            }
            assert(f(0int) && g(0int));
            assert(f == g); // FAILS
            assert(!f(-1int));
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] spec_fn_lambda_parameter_type_valid_3010 verus_code! {
        spec fn identity<A>() -> spec_fn(A) -> A {
            |a: A| a
        }

        proof fn generic<A>(a: A) {
            let f = identity::<A>();
            assert(f(a) == a);
            assert(f =~= (|x: A| x));
        }

        proof fn closures() {
            let f = |x: nat| x >= 0;
            assert(f(0nat));
            assert(f =~= (|x: nat| true));
            assert((|x: int| x >= 0)(-1int) == false);

            let constant = || 7int;
            assert(constant() == 7);
            assert(constant =~= (|| 3int + 4int));

            let add = |x: nat, y: nat| x + y;
            assert(add(2, 3) == 5);
            assert(add =~= (|x: nat, y: nat| y + x));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fn_spec_type verus_code! {
        spec fn stuff(t: spec_fn(int) -> int, x: int) -> int {
            t(x)
        }

        proof fn some_proof() {
            let y = stuff(|x: int| x + 1, 5);
            assert(y == 6);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] return_in_closure verus_code! {
        proof fn p(){
            let _f = |x:int| -> int { return x; };
        }
    } => Err(err) => assert_vir_error_msg(err, "return is not allowed in pure context")
}
