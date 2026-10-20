#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] all_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>)
        {
            let mut it = v.into_iter();
            let ghost g = it;
            let v_result = it.all(
                |i: u32| -> (ret: bool)
                    ensures ret == (i < 10)
                {i < 10}
            );
            if v_result {
                // If `all` returned true, every element was below 10.
                assert(forall |i| 0 <= i < v.len() ==> v[i] < 10);
            } else {
                // If `all` returned false, at least one element was >= 10.
                // The witness is the (consumed) element that failed the predicate.
                let ghost idx = g.remaining().len() - it.remaining().len() - 1;
                assert(0 <= idx < v.len() && v[idx] >= 10);
                assert(exists |i| 0 <= i < v.len() && v[i] >= 10);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] any_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>)
        {
            let mut it = v.into_iter();
            let ghost g = it;
            let v_result = it.any(
                |i: u32| -> (ret: bool)
                    ensures ret == (i < 10)
                {i < 10}
            );
            if v_result {
                // If `any` returned true, at least one element was below 10.
                // The witness is the (consumed) element that satisfied the predicate.
                let ghost idx = g.remaining().len() - it.remaining().len() - 1;
                assert(0 <= idx < v.len() && v[idx] < 10);
                assert(exists |i| 0 <= i < v.len() && v[i] < 10);
            } else {
                // If `any` returned false, every element was >= 10.
                assert(forall |i| 0 <= i < v.len() ==> v[i] >= 10);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] chars_next_falls_back_to_iterator_spec verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(s: &str)
            requires
                s@.len() >= 1,
        {
            let mut it = s.chars();
            assert(it.remaining() == s@);
            let r = it.next();
            assert(r == Some(s@[0]));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] collect_works verus_code! {
        use vstd::prelude::*;

        fn test() {
            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().collect();
            assert(v@ == w@);
            let x: Vec<u32> = w.into_iter().rev().collect();
            assert(x@ == seq![4u32, 3, 2, 1]);

            let y: Vec<u32> = vec![1, 2, 3, 4];
            let z: Vec<u32> = y.into_iter().rev().rev().collect();
            assert(z@ == y@);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] filter_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::*;

        fn test() {
            let p = |x: &u32| -> (b: bool)
                ensures b == (*x % 2 == 0)
            { *x % 2 == 0 };

            let v: Vec<u32> = vec![1, 2, 3, 4];
            let mut w: Vec<u32> = Vec::new();

            for x in it: v.into_iter().filter(p)
                invariant
                    w.len() == it.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == it.seq()[i],
            {
                w.push(x);
            }
            assert(w.len() <= 4);
            assert(forall |i| 0 <= i < w.len() ==> w[i] % 2 == 0);
            assert(forall |i| #![auto] 0 <= i < w.len() ==> v@.contains(w[i]));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] find_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>)
        {
            let v_result = v.into_iter().find(
                |i| -> (ret: bool)
                ensures ret == (*i < 10)
                {*i < 10}
            );
            if let Some(i) = v_result {
                assert(i < 10);
                assert(v@.contains(i));
            } else {
                assert(forall |i| 0 <= i < v.len() ==> v[i] >= 10);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] find_map_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>)
        {
            let mut it = v.into_iter();
            let ghost g = it;
            let v_result = it.find_map(
                |x| -> (ret: Option<u32>)
                    ensures ret == if x % 4 == 0 { Some(x / 4) } else { None },
                {
                    if x % 4 == 0 { Some(x / 4) } else { None }
                }
            );
            match v_result {
                Some(r) => {
                    // If `find_map` returned Some, it must have stopped at a valid element.
                    let ghost idx = g.remaining().len() - it.remaining().len() - 1;
                    // find_map stopped at a valid element.
                    assert(0 <= idx < v.len());
                    // That element produced the returned Some value.
                    assert(v[idx] % 4 == 0);
                    assert(r == v[idx] / 4);
                    // Every previous element produced None.
                    assert(forall |j| 0 <= j < idx ==> v[j] % 4 != 0);
                }
                None => {
                    // If `find_map` returned None, every element mapped to None.
                    assert(forall |j| 0 <= j < v.len() ==> v[j] % 4 != 0);
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] map_works verus_code! {
        use vstd::prelude::*;

        fn double_it() {
            let v = vec![1u32, 2, 3, 4];
            let mut w = Vec::new();
            for x in iter: v.iter().map(|x: &u32| -> (y: u32) requires *x < 10, ensures y == x * 2 { *x * 2 })
                invariant
                    w.len() == iter.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == v[i] * 2,
            {
                w.push(x);
            }
            assert(w@ == seq![2u32, 4, 6, 8]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mut_ref_forwarding verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        pub fn next_test<I: Iterator>(i: &mut I)
            requires
                i.obeys_prophetic_iter_laws(),
                i.will_return_none(),
            ensures
                // TODO: The number of operators needed here is unfortunate
                (&(*final(i))).obeys_prophetic_iter_laws(),
                (&(*final(i))).will_return_none(),
        {
            i.next();

        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] position_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test(v: Vec<u32>) {
            let v_result = v.into_iter().position(
                |i| -> (ret: bool)
                ensures ret == (i < 10),
                {i < 10},
            );
            if let Some(index) = v_result {
                assert(index < v.len());
                assert(v@.contains(v[index as int]));
                assert(v[index as int] < 10);
                assert(forall |i: int| 0 <= i < index as int ==> v[i] >= 10);
            } else {
                assert(forall |i: int| 0 <= i < v.len() ==> v[i] >= 10);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] range_works verus_code! {
        use vstd::prelude::*;

        fn test()
        {
            let mut v = vec![];
            for i in iter: 0..4
            invariant
                v.len() == iter.index(),
                iter.index() <= 4,
            {
                assert(i < 4);
                v.push(i);
            }
            assert(v.len() == 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] range_inclusive_works verus_code! {
        use vstd::prelude::*;

        fn test()
        {
            let mut v = vec![];
            for i in iter: 0..=4
            invariant
                v.len() == iter.index(),
                i <= 5,
            {
                assert(i <= 4);
                v.push(i);
            }
            assert(v.len() == 5);
        }
    } => Ok(())
}

const CUSTOM_STEP: &str = code_str! {
    #![feature(step_trait)]
    use vstd::prelude::*;

    verus! {
        #[derive(Clone, Copy, PartialEq, PartialOrd)]
        pub struct S(pub u8);
    }

    // The executable implementation steps normally; its spec model below does not.
    impl core::iter::Step for S {
        fn steps_between(a: &S, b: &S) -> (usize, Option<usize>) {
            if a.0 <= b.0 {
                let n = (b.0 - a.0) as usize;
                (n, Some(n))
            } else {
                (0, None)
            }
        }

        fn forward_checked(a: S, n: usize) -> Option<S> {
            a.0.checked_add(u8::try_from(n).ok()?).map(S)
        }

        fn backward_checked(a: S, n: usize) -> Option<S> {
            a.0.checked_sub(u8::try_from(n).ok()?).map(S)
        }

        fn forward_overflowing(a: S, n: usize) -> (S, bool) {
            (S(a.0.wrapping_add(n as u8)), Self::forward_checked(a, n).is_none())
        }

        fn backward_overflowing(a: S, n: usize) -> (S, bool) {
            (S(a.0.wrapping_sub(n as u8)), Self::backward_checked(a, n).is_none())
        }
    }
};

test_verify_one_file_with_options! {
    #[test] range_custom_step_model ["no-auto-import-verus_builtin"] =>
    FEATURE_PRELUDE.to_string() + CUSTOM_STEP + verus_code_str! {
        use vstd::std_specs::iter::StepSpecImpl;

        // Claiming obeys does not make an incoherent model valid for ranges.
        impl StepSpecImpl for S {
            open spec fn obeys_step_spec() -> bool { true }
            open spec fn spec_steps_between(self, end: Self) -> Option<usize> { Some(1) }
            open spec fn spec_steps_between_int(self, end: Self) -> int { 1 }
            open spec fn spec_forward_checked(self, count: usize) -> Option<Self> { Some(S(7)) }
            open spec fn spec_forward_checked_int(self, count: int) -> Option<Self> { Some(S(7)) }
            open spec fn spec_backward_checked(self, count: usize) -> Option<Self> { None }
            open spec fn spec_backward_checked_int(self, count: int) -> Option<Self> { None }
            open spec fn spec_forward_overflowing(self, count: usize) -> (Self, bool) { (S(7), false) }
            open spec fn spec_backward_overflowing(self, count: usize) -> (Self, bool) { (self, true) }
        }

        fn exclusive()
            ensures false, // FAILS
        {
            let mut r = S(0)..S(1);
            let _ = r.next();
        }

        fn inclusive()
            ensures false, // FAILS
        {
            let mut r = S(0)..=S(1);
            let _ = r.next();
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] range_custom_step_next_not_deterministic ["no-auto-import-verus_builtin"] =>
    FEATURE_PRELUDE.to_string() + code_str! {
        #![feature(step_trait)]
        use std::sync::atomic::{AtomicU64, Ordering};
        use vstd::prelude::*;

        static COUNTER: AtomicU64 = AtomicU64::new(100);

        verus! {
            #[derive(Clone, Copy, PartialEq, PartialOrd)]
            pub struct S(pub u64);

            // No StepSpecImpl: the spec_range_next model must not imply
            // that equal ranges produce equal results for an arbitrary Step type.
            fn two() -> (r: (Option<S>, Option<S>))
                ensures r.0 == r.1, // FAILS
            {
                let mut a = S(0)..S(u64::MAX);
                let mut b = S(0)..S(u64::MAX);
                let _ = a.next();
                let _ = b.next();
                (a.next(), b.next())
            }
        }

        impl core::iter::Step for S {
            fn steps_between(_: &S, _: &S) -> (usize, Option<usize>) { (0, None) }
            fn forward_checked(_: S, _: usize) -> Option<S> {
                Some(S(COUNTER.fetch_add(1, Ordering::SeqCst)))
            }
            fn backward_checked(_: S, _: usize) -> Option<S> { None }
            fn forward_overflowing(a: S, n: usize) -> (S, bool) {
                (Self::forward_checked(a, n).unwrap(), false)
            }
            fn backward_overflowing(a: S, _: usize) -> (S, bool) { (a, true) }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] range_primitive_step_specs code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        macro_rules! check_ranges {
            ($t:ty, $test:ident) => {
                verus! {
                    fn $test() {
                        let mut r = (1 as $t)..(3 as $t);
                        assert(r.obeys_prophetic_iter_laws());
                        assert(r.remaining() =~= seq![1 as $t, 2 as $t]);
                        assert(r.decrease() == Some(2nat));
                        assert(r.peek(0) == Some(1 as $t));
                        let x = r.next();
                        assert(x == Some(1 as $t));
                        assert(r.start == 2 && r.end == 3);
                        let x = r.next();
                        assert(x == Some(2 as $t));
                        let x = r.next();
                        assert(x == None::<$t>);

                        let mut r = (1 as $t)..=(2 as $t);
                        assert(r.obeys_prophetic_iter_laws());
                        assert(r.remaining() =~= seq![1 as $t, 2 as $t]);
                        assert(r.decrease() == Some(2nat));
                        assert(r.peek(0) == Some(1 as $t));
                        let x = r.next();
                        assert(x == Some(1 as $t));
                        let x = r.next();
                        assert(x == Some(2 as $t));
                        assert(r.remaining() =~= Seq::<$t>::empty());
                        let x = r.next();
                        assert(x == None::<$t>);
                    }
                }
            };
        }

        check_ranges!(u8, check_u8);
        check_ranges!(u16, check_u16);
        check_ranges!(u32, check_u32);
        check_ranges!(u64, check_u64);
        check_ranges!(u128, check_u128);
        check_ranges!(usize, check_usize);
        check_ranges!(i8, check_i8);
        check_ranges!(i16, check_i16);
        check_ranges!(i32, check_i32);
        check_ranges!(i64, check_i64);
        check_ranges!(i128, check_i128);
        check_ranges!(isize, check_isize);
    } => Ok(())
}

// Reuse the honest example's type and spec definitions, replacing only its
// executable Step implementation in the negative tests below.
fn custom_step_model_code() -> String {
    let example = include_str!("../../../examples/iterators/custom_step.rs");
    let (model, _) = example.split_once("impl Step for Index").unwrap();
    FEATURE_PRELUDE.to_string() + model + "\n}\n"
}

test_verify_one_file_with_options! {
    #[test] step_overrides_must_obey_model ["no-auto-import-verus_builtin"] =>
    custom_step_model_code() + verus_code_str! {
        impl Step for Index {
            fn steps_between(_start: &Self, _end: &Self) -> (usize, Option<usize>) {
                (0, Some(0)) // FAILS
            }
            fn forward_checked(_start: Self, _count: usize) -> Option<Self> {
                None // FAILS
            }
            fn backward_checked(_start: Self, _count: usize) -> Option<Self> {
                None // FAILS
            }
            fn forward_overflowing(_start: Self, _count: usize) -> (Self, bool) {
                (Index(0), true) // FAILS
            }
            fn backward_overflowing(_start: Self, _count: usize) -> (Self, bool) {
                (Index(0), true) // FAILS
            }
            fn forward(start: Self, _count: usize) -> Self {
                start // FAILS
            }
            fn backward(start: Self, _count: usize) -> Self {
                start // FAILS
            }
            unsafe fn forward_unchecked(start: Self, _count: usize) -> Self {
                start // FAILS
            }
            unsafe fn backward_unchecked(start: Self, _count: usize) -> Self {
                start // FAILS
            }
        }
    } => Err(err) => {
        // Each overflowing override violates both the new complete result
        // model and the existing checked-result/overflow contracts.
        assert_eq!(err.errors.len(), 11);
        for error in err.errors {
            assert!(error.message.contains("postcondition not satisfied"));
            // The failed inherited postcondition has no source text in the
            // imported vstd; inspect the implementation's exit span instead.
            assert!(error.spans.iter().flat_map(|span| &span.text)
                .any(|line| line.text.contains("FAILS")));
        }
    }
}

test_verify_one_file_with_options! {
    #[test] step_overflow_contracts ["no-auto-import-verus_builtin"] =>
    FEATURE_PRELUDE.to_string() + code_str! {
        #![feature(step_trait)]
        use vstd::prelude::*;
        use core::iter::Step;

        verus! {
            fn forward() {
                let _ = <u8 as Step>::forward(255, 1); // FAILS: may panic.
            }
            fn backward() {
                let _ = <u8 as Step>::backward(0, 1); // FAILS: may panic.
            }
            fn forward_unchecked() {
                let _ = unsafe { <u8 as Step>::forward_unchecked(255, 1) }; // FAILS
            }
            fn backward_unchecked() {
                let _ = unsafe { <u8 as Step>::backward_unchecked(0, 1) }; // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] step_wide_counts ["no-auto-import-verus_builtin"] =>
    FEATURE_PRELUDE.to_string() + code_str! {
        #![feature(step_trait)]
        use vstd::prelude::*;
        use core::iter::Step;

        verus! {
            fn composed_counts() {
                // Rust's Step implementations can compose successful steps
                // even when their counts cannot be added in usize.
                let n = usize::MAX;
                let count = n.checked_add(1);
                assert(count == None::<usize>);
                let first = <u128 as Step>::forward_checked(0, n);
                assert(first == Some(n as u128));
                let result = <u128 as Step>::forward_checked(first.unwrap(), 1);
                assert(result == Some((n + 1) as u128));

                let first = <u128 as Step>::backward_checked(u128::MAX, n);
                assert(first == Some((u128::MAX - n) as u128));
                let result = <u128 as Step>::backward_checked(first.unwrap(), 1);
                assert(result == Some((u128::MAX - n - 1) as u128));

                let (unsigned, unsigned_overflow) = <u8 as Step>::forward_overflowing(250, 256);
                let (signed, signed_overflow) = <i8 as Step>::forward_overflowing(-120, 200);
                let (wrapped, wrapped_overflow) = <i8 as Step>::forward_overflowing(-120, 256);
                proof {
                    reveal(vstd::std_specs::range::step_spec_wrapping_value);
                    assert(vstd::std_specs::range::step_spec_wrapping_value(250, 256, 0, 255)
                        == 250) by (compute);
                    assert(vstd::std_specs::range::step_spec_wrapping_value(-120, 256, -128, 127)
                        == -120) by (compute);
                    assert(unsigned == 250 && unsigned_overflow);
                    assert(signed == 80 && !signed_overflow);
                    assert(wrapped == -120 && wrapped_overflow);
                }
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] step_overflowing_must_obey_fold ["no-auto-import-verus_builtin"] => {
        let example = include_str!("../../../examples/iterators/custom_step.rs");
        let (program, _) = example.split_once("pub broadcast proof fn index_step_laws()").unwrap();
        // Both the executable methods and their models return zero on overflow.
        // Their individual postconditions still hold, but repeated forward
        // steps after overflow disagree with one bulk step.
        let program = program.replace("(Index(i), overflow)",
            "(if overflow { Index(0) } else { Index(i) }, overflow)");
        FEATURE_PRELUDE.to_string() + &program + code_str! {
            proof fn rejected_laws() {
                reveal(vstd::std_specs::range::step_spec_wrapping_value);
                assert(vstd::std_specs::range::step_spec_wrapping_value(0, 1, 0, 255)
                    == 1) by (compute);
                let (one, first_overflow) = StepSpec::spec_forward_overflowing(Index(255), 1);
                let (two, bulk_overflow) = StepSpec::spec_forward_overflowing(Index(255), 2);
                let (next, next_overflow) = StepSpec::spec_forward_overflowing(one, 1);
                assert(one == Index(0) && first_overflow);
                assert(two == Index(0) && bulk_overflow);
                assert(next == Index(1) && !next_overflow);
                reveal(step_spec_overflowing_is_well_formed);
                assert(!step_spec_overflowing_is_well_formed::<Index>());
                assert(step_spec_overflowing_is_well_formed::<Index>()); // FAILS
            }
        } + "\n}\n"
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] step_forward_overrides_use_preconditions ["no-auto-import-verus_builtin"] =>
    custom_step_model_code() + verus_code_str! {
        impl Step for Index {
            fn steps_between(start: &Self, end: &Self) -> (usize, Option<usize>) {
                <u8 as Step>::steps_between(&start.0, &end.0)
            }
            fn forward_checked(start: Self, count: usize) -> Option<Self> {
                match <u8 as Step>::forward_checked(start.0, count) {
                    Some(i) => Some(Index(i)),
                    None => None,
                }
            }
            fn backward_checked(start: Self, count: usize) -> Option<Self> {
                match <u8 as Step>::backward_checked(start.0, count) {
                    Some(i) => Some(Index(i)),
                    None => None,
                }
            }
            fn forward_overflowing(start: Self, count: usize) -> (Self, bool) {
                let (i, overflow) = <u8 as Step>::forward_overflowing(start.0, count);
                (Index(i), overflow)
            }
            fn backward_overflowing(start: Self, count: usize) -> (Self, bool) {
                let (i, overflow) = <u8 as Step>::backward_overflowing(start.0, count);
                (Index(i), overflow)
            }

            // The strengthened preconditions justify these unchecked steps.
            fn forward(start: Self, count: usize) -> Self {
                let i = unsafe { <u8 as Step>::forward_unchecked(start.0, count) };
                Index(i)
            }
            fn backward(start: Self, count: usize) -> Self {
                let i = unsafe { <u8 as Step>::backward_unchecked(start.0, count) };
                Index(i)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] skip_works verus_code! {
        use vstd::prelude::*;

        fn test() {
            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().skip(2).collect();
            assert(w@ == seq![3, 4]);


            let v: Vec<u32> = vec![1, 2, 3, 4];
            let mut w: Vec<u32> = Vec::new();

            for x in it: v.into_iter().skip(2)
                invariant
                    w.len() == it.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == it.seq()[i],
            {
                w.push(x);
            }
            assert(w@ == seq![3, 4]);

            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().skip(2).rev().collect();
            assert(w@ == seq![4u32, 3]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] take_works verus_code! {
        use vstd::prelude::*;

        fn test() {
            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().take(2).collect();
            assert(w@ == seq![1, 2]);


            let v: Vec<u32> = vec![1, 2, 3, 4];
            let mut w: Vec<u32> = Vec::new();

            for x in it: v.into_iter().take(3)
                invariant
                    w.len() == it.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == it.seq()[i],
            {
                w.push(x);
            }
            assert(w@ == seq![1, 2, 3]);

            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = v.into_iter().take(2).rev().collect();
            assert(w@ == seq![2u32, 1]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] take_skip verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test<I: Iterator>(v: Vec<u32>, n: usize)
            requires
                n <= v.len(),
        {
            // Creusot:
            //   assert!(iter.take(n).skip(n).next().is_none())
            // Verus:
            let mut r = v.into_iter().take(n).skip(n);
            assert(r.remaining().len() == 0);
            let out = r.next();
            assert(out is None);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] vec_iter_mut_works verus_code! {
        use vstd::prelude::*;

        fn client_for_loop() {
            let mut v: Vec<u32> = vec![1, 2, 3, 4];
            for x in it: v.iter_mut()
                invariant
                    forall |i: int| #![auto] 0 <= i < it.index() ==> *final(it.seq()[i]) == 0,
            {
                *x = 0;
            }
            assert(forall |i: int| 0 <= i < v.len() ==> v[i] == 0);
            assert(v@ == seq![0, 0, 0, 0]);
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] zip_works verus_code! {
        use vstd::prelude::*;

        fn zip_works() {
            let x1 = vec![1u32, 2, 3];
            let x2 = vec![2u32, 4, 6];
            let y1 = vec![2u32, 4, 6];
            let y2 = vec![1u32, 2];
            let z1 = vec![1u32, 2];
            let z2 = vec![2u32, 4, 6, 8, 10];

            let x: Vec<(u32, u32)> = x1.into_iter().zip(x2).collect();
            assert(x@ == seq![(1u32,2u32), (2, 4), (3, 6)]);

            let y: Vec<(u32, u32)> = y1.into_iter().zip(y2).collect();
            assert(y@ == seq![(2u32,1u32), (4, 2)]);

            let z: Vec<(u32, u32)> = z1.into_iter().zip(z2).collect();
            assert(z@ == seq![(1u32,2u32), (2, 4)]);
        }
    } => Ok(())
}
test_verify_one_file! {
    // Adaptors over an iterator without the prophetic laws: the closure must accept every
    // item, since `remaining()` need not describe what `next` yields. An impl that defines
    // `remaining()` as empty while `next` yields 200 used to let `find` call a
    // closure requiring `x < 4` on 200.
    #[test] test_adaptor_requires_without_laws verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpecImpl;
        pub struct It { n: u8 }
        impl Iterator for It {
            type Item = u8;
            fn next(&mut self) -> Option<u8> {
                if self.n == 0 { None } else { self.n = self.n - 1; Some(200) }
            }
        }
        impl IteratorSpecImpl for It {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool { false }
            open spec fn remaining(&self) -> Seq<u8> { Seq::empty() }
            open spec fn will_return_none(&self) -> bool { true }
            open spec fn decrease(&self) -> Option<nat> { None }
            open spec fn peek(&self, index: int) -> Option<u8> { None }
        }
        fn ok(it: It) -> Option<u8> {
            let mut it = it;
            it.find(|x: &u8| *x > 1)
        }
        fn bad(it: It) -> Option<u8> {
            let arr = [0u8; 4];
            let mut it = it;
            it.find(|x: &u8| -> (b: bool) requires *x < 4 { arr[*x as usize] == 0 }) // FAILS
        }
        fn bad_find_map(it: It) -> Option<u8> {
            let arr = [0u8; 4];
            let mut it = it;
            it.find_map(|x: u8| -> (r: Option<u8>) requires x < 4 { Some(arr[x as usize]) }) // FAILS
        }
        fn bad_position(it: It) -> Option<usize> {
            let mut it = it;
            it.position(|x: u8| x > 1) // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}
