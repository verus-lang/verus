#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

/// Every error is an erasure-check error, and one of them contains `msg` and highlights `text`.
fn assert_erasure_diff(err: TestErr, msg: &str, text: &str) {
    assert!(err.errors.len() > 0);
    assert!(err.errors.iter().all(|e| e.message.starts_with("erasure check:")));
    let highlighted = |e: &Diagnostic| -> Vec<String> {
        e.spans
            .iter()
            .flat_map(|s| s.text.iter())
            .map(|t| t.text[t.highlight_start - 1..t.highlight_end - 1].to_string())
            .collect()
    };
    assert!(
        err.errors
            .iter()
            .any(|e| e.message.contains(msg) && highlighted(e).iter().any(|h| h == text)),
        "no erasure-check error with `{msg}` at `{text}`: {:#?}",
        err.errors.iter().map(|e| (&e.message, highlighted(e))).collect::<Vec<_>>()
    );
}

test_verify_one_file_with_options! {
    #[test] literal_typed_by_ghost_call ["-V check-erasure"] => verus_code! {
        use vstd::prelude::*;
        proof fn lemma_small(x: u64)
            requires x <= 2_000_000_000
            ensures x + x <= 4_000_000_000
        {
        }

        fn double() -> (r: u64)
            ensures r == 4_000_000_000
        {
            let a = 2_000_000_000;
            proof { lemma_small(a); } // only this ghost call types `a` as u64
            (a + a) as u64
        }
    } => Err(err) => assert_erasure_diff(err, "type i32 (compiled) vs u64 (verified)", "2_000_000_000")
}

test_verify_one_file_with_options! {
    #[test] loop_counter_typed_by_ghost_call ["-V check-erasure"] => verus_code! {
        use vstd::prelude::*;
        proof fn check(a: u64)
            requires 1 <= a
        {
        }

        fn test() {
            let mut i = 0;
            let mut x = 0;
            while {
                x = x + 1;
                proof { check(x); }
                i < 10
            }
                invariant
                    i <= 10,
                    x == i,
                decreases 10 - i
            {
                i = i + 1;
            }
        }
    } => Err(err) => assert_erasure_diff(err, "x: i32 (compiled) vs BindingMode(No, Mut) x: u64 (verified)", "x")
}

test_verify_one_file_with_options! {
    #[test] closure_return_typed_by_verus_spec ["-V check-erasure"] => code! {
        use vstd::prelude::*;

        #[verus_spec(r => ensures r == 255)]
        pub fn f() -> u64 {
            // the annotation `r: u8` is the only thing that types the literal
            let c = #[verus_spec(r: u8 => ensures r == 255u8)]
            || 255;
            let v = c();
            v as u64
        }
    } => Err(err) => assert_erasure_diff(err, "type i32 (compiled) vs u8 (verified)", "255")
}

test_verify_one_file_with_options! {
    #[test] ghost_wrapper_name_shadowed ["-V check-erasure"] => verus_code! {
        use vstd::prelude::*;

        // shadows the `Ghost` of the vstd prelude, which the compiled form of `Ghost(e)` names
        pub struct Ghost<T>(core::marker::PhantomData<T>);

        impl<T> Ghost<T> {
            pub fn assume_new_fallback<F>(_f: F) -> u64 { 1 }
        }

        pub trait Val {
            fn val(&self) -> (r: u8) ensures r == self.spec_val();
            spec fn spec_val(&self) -> u8;
        }

        impl Val for vstd::prelude::Ghost<u64> {
            fn val(&self) -> (r: u8) { 0 }
            open spec fn spec_val(&self) -> u8 { 0 }
        }

        impl Val for u64 {
            fn val(&self) -> (r: u8) { 1 }
            open spec fn spec_val(&self) -> u8 { 1 }
        }

        pub fn call() -> (r: u8)
            ensures r == 0,
        {
            Ghost::<u64>(5u64).val()
        }
    } => Err(err) => assert_erasure_diff(err, "(compiled) vs erased-wrapper Ghost<u64> (verified)", "Ghost::<u64>(5u64)")
}

test_verify_one_file_with_options! {
    #[test] break_in_proof_block ["-V check-erasure"] => verus_code! {
        use vstd::prelude::*;
        fn run() -> (r: u64)
            ensures r == 0,
        {
            let mut i: u64 = 0;
            loop
                invariant i == 0,
                ensures i == 0,
                decreases 10 - i,
            {
                proof {
                    if i == 0 {
                        break;
                    }
                }
                i = i + 1;
                if i >= 10 {
                    break;
                }
            }
            i
        }
    } => Err(err) => assert_erasure_diff(err, "is exec control flow in the verified program, but the compiled program has no such node", "break")
}

test_verify_one_file_with_options! {
    #[test] ghost_field_tested_by_exec_match ["-V check-erasure"] => verus_code! {
        use vstd::prelude::*;
        pub struct S {
            pub ghost g: u64,
        }

        fn test() -> (r: u64)
            ensures r == 1,
        {
            let mut s = S { g: 7 };
            proof { s.g = 5; }
            match s {
                S { g: 5 } => 1,
                _ => 0,
            }
        }
    } => Err(err) => assert_erasure_diff(err, "g: ghost(", "match s {")
}

test_verify_one_file_with_options! {
    #[test] no_difference_ghost_code ["-V check-erasure"] => verus_code! {
        use vstd::prelude::*;
        pub struct S {
            pub x: u64,
            pub ghost g: int,
        }

        proof fn lemma(x: u64) ensures x <= u64::MAX {}

        fn f(s: &mut S, Ghost(k): Ghost<int>) -> (r: u64)
            requires old(s).x < 100,
            ensures r == old(s).x + 1,
        {
            let ghost before = s.g;
            proof { lemma(s.x); s.g = k + before; }
            let x = s.x;
            s.x = x + 1;
            assert(s.x == x + 1);
            s.x
        }

        fn g(v: &Vec<u64>) -> (r: u64)
            ensures r <= v.len(),
        {
            let mut n: u64 = 0;
            let mut i: usize = 0;
            while i < v.len()
                invariant i <= v.len(), n <= i,
                decreases v.len() - i,
            {
                if v[i] == 0 {
                    i = i + 1;
                    continue;
                }
                n = n + 1;
                i = i + 1;
            }
            for j in 0..3
                invariant n <= v.len(),
            {
                proof { assert(j < 3); }
            }
            n
        }

        fn h() -> (r: u32)
            ensures r == 7,
        {
            let add = |a: u32| -> (b: u32)
                requires a < 100,
                ensures b == a + 1,
            {
                a + 1
            };
            let c = add(6);
            match Some(c) {
                Some(v) if v > 0 => v,
                _ => 7,
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] no_difference_verus_spec ["-V check-erasure"] => code! {
        use vstd::prelude::*;

        #[verus_spec(r =>
            with Ghost(g): Ghost<u8>
            ensures r == 1
        )]
        pub fn f(x: u8) -> u8 { 1 }

        #[verus_spec(r => ensures r == 1)]
        pub fn call() -> u8 {
            proof_with!{Ghost(0u8)}
            f(7)
        }

        #[verus_spec(r =>
            requires x < 10,
            ensures r == x + 1,
        )]
        pub fn inc(x: u8) -> u8 {
            let c = #[verus_spec(r: u8 => ensures r == 1u8)]
            || 1u8;
            x + c()
        }
    } => Ok(())
}
