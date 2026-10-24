#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] advance_by_and_nth_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test() {
            let mut iter = vec![1u32, 2, 3].into_iter();
            let ghost initial = iter;
            let result = iter.advance_by(0);
            assert(result == Ok(()));
            assert(iter.remaining() == initial.remaining());
            assert(iter.produces() == initial.produces());
            let result = iter.advance_by(1);
            assert(result == Ok(()));
            assert(iter.remaining() =~= seq![2u32, 3]);
            assert(iter.produces() == initial.produces().skip(1));
            let result = iter.nth(0);
            assert(result == Some(2));
            assert(iter.remaining() =~= seq![3u32]);
            assert(iter.produces() == initial.produces().skip(2));
            let result = iter.advance_by(3);
            assert(result is Err && result->Err_0@ == 2);
            assert(iter.remaining().len() == 0);
            assert(iter.produces().len() == 0);

            let mut iter = vec![1u32, 2, 3].into_iter();
            let result = iter.nth(1);
            assert(result == Some(2));
            let result = iter.next();
            assert(result == Some(3));
            let result = iter.nth(usize::MAX);
            assert(result == None);
            assert(iter.produces().len() == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fold_and_for_each_callback_preconditions verus_code! {
        use vstd::prelude::*;

        fn test() {
            let result = Vec::<u32>::new().into_iter().fold(7u32,
                |acc: u32, x: u32| -> u32 requires false, { 0 });
            assert(result == 7);
            let result = vec![1u32].into_iter().fold(7u32,
                |acc: u32, x: u32| -> (ret: u32)
                    requires acc == 7 && x == 1,
                    ensures ret == 8,
                { 8 });
            assert(result == 8);
            vec![1u32].into_iter().for_each(
                |x: u32| requires x == 1, {});
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fold_callback_does_not_require_unreachable_tail verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test<I: Iterator<Item = u32>>(iter: I)
            requires
                iter.obeys_prophetic_iter_laws(),
                iter.remaining() == seq![1u32, 2],
                iter.produces() == seq![false, true],
            ensures
                false,
        {
            assert forall |k: int| 0 < k <= 2 implies
                !(#[trigger] iter.produces().take(k)).all(|p: bool| p) by {
                assert(iter.produces().take(k)[0] == false);
            }
            // The callback rejects the second item, which forward traversal cannot reach.
            let _ = iter.fold(0u32,
                |acc: u32, x: u32| -> (ret: u32)
                    requires x == 1,
                    ensures ret == acc,
                { acc });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] try_fold_callback_does_not_require_unreachable_tail verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        fn test<I: Iterator<Item = u32>>(mut iter: I)
            requires
                iter.obeys_prophetic_iter_laws(),
                iter.remaining() == seq![1u32, 2],
                iter.produces() == seq![false, true],
            ensures
                false,
        {
            assert forall |k: int| 0 < k <= 2 implies
                !(#[trigger] iter.produces().take(k)).all(|p: bool| p) by {
                assert(iter.produces().take(k)[0] == false);
            }
            // The callback rejects the second item, which forward traversal cannot reach.
            let _: Result<u32, u32> = iter.try_fold(0u32,
                |acc: u32, x: u32| -> (ret: Result<u32, u32>)
                    requires x == 1,
                    ensures ret == Ok(acc),
                { Ok(acc) });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] try_fold_short_circuits_and_preserves_tail verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;
        use core::ops::ControlFlow;

        fn test() {
            let mut iter = vec![1u32, 2].into_iter();
            let ghost initial = iter;
            let result = iter.try_fold(7u32,
                |acc: u32, x: u32| -> (ret: Result<u32, u32>)
                    requires acc == 7 && x == 1,
                    ensures ret == Err(9),
                { Err(9) });
            assert(result == Err(9));
            assert(iter.remaining() =~= seq![2u32]);
            assert(iter.produces() == initial.produces().skip(1));
            let next = iter.next();
            assert(next == Some(2));

            let mut iter = Vec::<u32>::new().into_iter();
            let result = iter.try_fold(7u32,
                |acc: u32, x: u32| -> Option<u32> requires false, { None });
            assert(result == Some(7));

            let mut iter = vec![1u32].into_iter();
            let result = iter.try_fold(7u32,
                |acc: u32, x: u32| -> (ret: ControlFlow<u32, u32>)
                    requires acc == 7 && x == 1,
                    ensures ret == ControlFlow::Continue(8),
                { ControlFlow::Continue(8) });
            assert(result == ControlFlow::Continue(8));
            assert(iter.remaining().len() == 0);
            assert(iter.produces().len() == 0);
        }
    } => Ok(())
}

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

// Regression tests for issue #3142.
// The infinite counter from the guide, with an open remaining() so that the
// collect regressions also exercise the prophetic specifications.
const INFINITE_COLLECT_COMMON: &str = verus_code_str! {
    use vstd::modes::tracked_swap;
    use vstd::prelude::*;
    use vstd::proph::ProphecyGhost;
    use vstd::std_specs::iter::*;

    pub struct IterCtr {
        pub count: u64,
        pub len: Tracked<ProphecyGhost<nat>>,
    }

    impl IterCtr {
        fn new() -> Self {
            IterCtr { count: 0, len: Tracked(ProphecyGhost::new()) }
        }
    }

    impl Iterator for IterCtr {
        type Item = u64;

        fn next(&mut self) -> (ret: Option<Self::Item>) {
            proof {
                let tracked mut new = ProphecyGhost::new();
                tracked_swap(&mut new, &mut self.len);
                new.resolve_dependent(&self.len, |x: nat| (x + 1) as nat);
            }
            let ret = self.count;
            if self.count == u64::MAX {
                self.count = 0;
            } else {
                self.count = self.count + 1;
            }
            Some(ret)
        }
    }

    impl IteratorSpecImpl for IterCtr {
        open spec fn obeys_prophetic_iter_laws(&self) -> bool { true }

        #[verifier::prophetic]
        open spec fn remaining(&self) -> Seq<Self::Item> {
            Seq::new(self.len@.value(), |i: int|
                ((i + self.count) % (u64::MAX as int + 1)) as u64)
        }

        #[verifier::prophetic]
        open spec fn produces(&self) -> Seq<bool> {
            Seq::new(self.len@.value(), |i: int| true)
        }
        open spec fn decrease(&self) -> Option<nat> { None }
        open spec fn peek(&self, index: int) -> Option<Self::Item> {
            Some((index % (u64::MAX as int + 1)) as u64)
        }
    }

    pub struct Nothing;

    impl FromIterator<u64> for Nothing {
        fn from_iter<T: IntoIterator<Item = u64>>(iter: T) -> Self {
            let _ = iter.into_iter();
            Nothing
        }
    }

    impl FromIteratorSpecImpl<u64> for Nothing {
        open spec fn from_iter_ensures(remaining: Seq<u64>, produces: Seq<bool>, s: Self) -> bool { true }
    }
};

test_verify_one_file! {
    #[test] collect_without_into_iter_does_not_imply_none
    // Keep the exact early-returning implementation from the issue: it does
    // not even convert its input. The branch's existential contract rejects
    // that implementation, and collect must still not establish false.
    INFINITE_COLLECT_COMMON.replace("let _ = iter.into_iter();", "") + verus_code_str! {
        fn test() {
            let n: Nothing = IterCtr::new().collect();
            assert(false); // FAILS
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(err.errors.iter().any(|e| e.message == "postcondition not satisfied"));
        assert!(err.errors.iter().any(|e| e.message == "assertion failed"));
    }
}

test_verify_one_file! {
    #[test] collect_user_from_iterator_does_not_imply_none
    INFINITE_COLLECT_COMMON.to_string() + verus_code_str! {
        fn test() {
            let it = IterCtr::new();
            let n: Nothing = it.collect();
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] collect_one_next_does_not_imply_none
    INFINITE_COLLECT_COMMON.to_string() + verus_code_str! {
        pub struct One;

        impl FromIterator<u64> for One {
            fn from_iter<T: IntoIterator<Item = u64>>(iter: T) -> Self {
                let mut it = iter.into_iter();
                it.next();
                One
            }
        }

        impl FromIteratorSpecImpl<u64> for One {
            open spec fn from_iter_ensures(remaining: Seq<u64>, produces: Seq<bool>, s: Self) -> bool { true }
        }

        fn test() {
            let n: One = IterCtr::new().collect();
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] collect_adaptors_do_not_imply_none
    INFINITE_COLLECT_COMMON.to_string() + verus_code_str! {
        impl FromIterator<(u64, u64)> for Nothing {
            fn from_iter<T: IntoIterator<Item = (u64, u64)>>(iter: T) -> Self {
                let _ = iter.into_iter();
                Nothing
            }
        }

        impl FromIteratorSpecImpl<(u64, u64)> for Nothing {
            open spec fn from_iter_ensures(remaining: Seq<(u64, u64)>, produces: Seq<bool>, s: Self) -> bool {
                true
            }
        }

        fn skip() {
            let n: Nothing = IterCtr::new().skip(3).collect();
            assert(false); // FAILS
        }

        fn map() {
            let n: Nothing = IterCtr::new().map(|x: u64| -> u64 { x }).collect();
            assert(false); // FAILS
        }

        fn mut_ref() {
            let mut it = IterCtr::new();
            let n: Nothing = (&mut it).collect();
            assert(false); // FAILS
        }

        fn zip() {
            let a = IterCtr::new();
            let b = IterCtr::new();
            let n: Nothing = a.zip(b).collect();
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] collect_vec_of_other_item_type_does_not_imply_none
    INFINITE_COLLECT_COMMON.to_string() + verus_code_str! {
        pub struct Id;

        impl FromIterator<Id> for Vec<u64> {
            fn from_iter<T: IntoIterator<Item = Id>>(iter: T) -> Self {
                let _ = iter.into_iter();
                Vec::new()
            }
        }

        impl FromIteratorSpecImpl<Id> for Vec<u64> {
            open spec fn from_iter_ensures(remaining: Seq<Id>, produces: Seq<bool>, s: Self) -> bool { true }
        }

        fn test() {
            let v: Vec<u64> = IterCtr::new().map(|x: u64| -> Id { Id }).collect();
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] collect_overridden_fold_does_not_imply_none
    // The early-returning override also violates the provided-method contract.
    INFINITE_COLLECT_COMMON.to_string() + verus_code_str! {
        use std::collections::HashSet;

        pub struct FoldCtr { pub inner: IterCtr }

        impl Iterator for FoldCtr {
            type Item = u64;

            fn next(&mut self) -> Option<Self::Item> {
                self.inner.next()
            }

            fn fold<B, F>(self, init: B, f: F) -> B
                where F: FnMut(B, Self::Item) -> B,
            {
                init // FAILS: the override does not fold over the remaining items
            }
        }

        impl IteratorSpecImpl for FoldCtr {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool { true }

            #[verifier::prophetic]
            open spec fn remaining(&self) -> Seq<Self::Item> {
                IteratorSpec::remaining(&self.inner)
            }

            #[verifier::prophetic]
            open spec fn produces(&self) -> Seq<bool> {
                IteratorSpec::produces(&self.inner)
            }
            open spec fn decrease(&self) -> Option<nat> { None }
            open spec fn peek(&self, index: int) -> Option<Self::Item> {
                IteratorSpec::peek(&self.inner, index)
            }
        }

        fn test() {
            let it = FoldCtr { inner: IterCtr::new() };
            let s: HashSet<u64> = it.collect();
            assert(false); // FAILS
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(err.errors.iter().any(|e| e.message.contains("postcondition not satisfied")));
        assert!(err.errors.iter().any(|e| e.message.contains("assertion failed")));
    }
}

test_verify_one_file! {
    #[test] collect_adaptors_are_complete verus_code! {
        use vstd::prelude::*;

        fn mapped_collect() {
            let v: Vec<u64> = vec![1, 2, 3];
            let it = v.into_iter().map(|x: u64| -> (r: u64)
                ensures r == x,
            { x });
            let w: Vec<u64> = it.collect();
            assert(w.len() == 3);
            assert(w@ == seq![1u64, 2, 3]);
        }

        fn filtered_collect() {
            let v: Vec<u64> = vec![1, 2, 3];
            let it = v.into_iter().filter(|x: &u64| -> (r: bool)
                ensures r == true,
            { true });
            let w: Vec<u64> = it.collect();
            reveal_with_fuel(Seq::filter_index, 4);
            assert(w.len() == 3);
        }

        fn mapped_from_iter() {
            let v: Vec<u64> = vec![1, 2, 3];
            let it = v.into_iter().map(|x: u64| -> (r: u64)
                ensures r == x,
            { x });
            let w: Vec<u64> = Vec::from_iter(it);
            assert(w.len() == 3);
            assert(w@ == seq![1u64, 2, 3]);
        }

        fn filtered_from_iter() {
            let v: Vec<u64> = vec![1, 2, 3];
            let it = v.into_iter().filter(|x: &u64| -> (r: bool)
                ensures r == true,
            { true });
            let w: Vec<u64> = Vec::from_iter(it);
            reveal_with_fuel(Seq::filter_index, 4);
            assert(w.len() == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] from_iter_must_establish_claimed_production verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::*;

        pub struct ClaimsToProduce;

        impl FromIterator<u64> for ClaimsToProduce {
            fn from_iter<T: IntoIterator<Item = u64>>(src: T) -> Self {
                let it = src.into_iter();
                ClaimsToProduce // FAILS
            }
        }

        impl FromIteratorSpecImpl<u64> for ClaimsToProduce {
            open spec fn from_iter_ensures(
                remaining: Seq<u64>, produces: Seq<bool>, s: Self,
            ) -> bool {
                produces.len() == remaining.len() && produces.all(|p: bool| p)
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "postcondition not satisfied")
}

test_verify_one_file! {
    #[test] collect_with_early_return_works
    INFINITE_COLLECT_COMMON.to_string() + verus_code_str! {
        fn finite() {
            let n: Nothing = vec![1u64, 2, 3].into_iter().collect();
        }

        fn without_laws<I: Iterator<Item = u64>>(it: I)
            requires
                !it.obeys_prophetic_iter_laws(),
        {
            let n: Nothing = it.collect();
        }

        fn direct_from_iter() {
            // FromIterator itself does not require exhaustion or termination.
            let n = Nothing::from_iter(IterCtr::new());
        }

        fn take_zero() {
            let v: Vec<u64> = IterCtr::new().take(0).collect();
            assert(v@ == Seq::<u64>::empty());
        }
    } => Ok(())
}

// Regression tests for issue #3165.
test_verify_one_file! {
    #[test] from_iter_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::*;

        fn direct() {
            let v = vec![1u8, 2, 3];
            let w: Vec<u8> = Vec::from_iter(v.into_iter());
            assert(w@ == v@);
        }

        fn mut_ref() {
            let v = vec![1u8, 2, 3];
            let mut it = v.into_iter();
            let x: Vec<u8> = Vec::from_iter(&mut it);
            assert(x@ == v@);
        }

        fn zip() {
            let v = vec![1u8, 2, 3];
            let y: Vec<(u8, u8)> = Vec::from_iter(v.into_iter().zip(vec![4u8, 5]));
            assert(y@ == seq![(1u8, 4u8), (2, 5)]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] from_iter_requires_iterator_laws verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::*;

        pub struct It;

        impl Iterator for It {
            type Item = u8;

            fn next(&mut self) -> Option<u8> {
                None
            }
        }

        impl IteratorSpecImpl for It {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool { false }

            #[verifier::prophetic]
            open spec fn remaining(&self) -> Seq<u8> { seq![7u8] }

            #[verifier::prophetic]
            open spec fn produces(&self) -> Seq<bool> { seq![true] }

            open spec fn decrease(&self) -> Option<nat> { None }

            open spec fn peek(&self, index: int) -> Option<u8> { None }
        }

        fn direct() {
            let v: Vec<u8> = Vec::from_iter(It);
            assert(v.len() == 1); // FAILS
        }

        fn mut_ref() {
            let mut it = It;
            let v: Vec<u8> = Vec::from_iter(&mut it);
            assert(v.len() == 1); // FAILS
        }

        fn zip() {
            let w = vec![1u8, 2];
            let v: Vec<(u8, u8)> = Vec::from_iter(w.into_iter().zip(It));
            assert(v.len() == 1); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] from_iter_witness_is_prophetic verus_code! {
        use vstd::prelude::*;
        use vstd::proph::ProphecyGhost;
        use vstd::std_specs::iter::*;

        fn cannot_resolve_from_witness<T: IntoIterator<Item = u8>>(src: T) {
            let tracked p = ProphecyGhost::<nat>::new();
            let result: Vec<u8> = Vec::from_iter(src);
            proof {
                let witness = choose |i: T::IntoIter|
                    call_ensures(T::into_iter, (src,), i)
                    && (i.obeys_prophetic_iter_laws() ==> i.remaining() == result@);
                p.resolve(witness.remaining().len());
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for argument to proof-mode function with tracked parameters")
}

test_verify_one_file! {
    #[test] from_iter_into_iterator_can_vary code! {
        use vstd::prelude::*;
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        verus! {
            pub struct Src;

            fn two() -> (r: (Vec<u64>, Vec<u64>))
                ensures r.0@ == r.1@, // FAILS
            {
                let a: Vec<u64> = Vec::from_iter(Src);
                let b: Vec<u64> = Vec::from_iter(Src);
                (a, b)
            }
        }

        impl IntoIterator for Src {
            type Item = u64;
            type IntoIter = std::vec::IntoIter<u64>;

            fn into_iter(self) -> Self::IntoIter {
                vec![COUNTER.fetch_add(1, Ordering::SeqCst)].into_iter()
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] filter_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

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
    #[test] map_next_back_with_diverging_callback verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::{IteratorSpec, map_iter};

        #[verifier::exec_allows_no_decreases_clause]
        fn diverge() -> u32
            ensures false,
        {
            loop {}
        }

        fn test() {
            let input = vec![0u32, 1, 2];
            let inner = input.into_iter().map(|x: u32| -> (out: u32)
                ensures x > 0 && out == x,
            { if x == 0 { diverge() } else { x } });
            assert forall |i: int| 0 <= i < inner.remaining().len() && inner.produces()[i]
                implies 0 < inner.remaining()[i] < 10 by {
                assert(map_iter(inner).produces()[i]);
            }
            assert(map_iter(inner).produces()[0]);
            assert(!inner.produces()[0]);

            // The stuck slot need not satisfy this callback's precondition.
            let mut iter = inner.map(|x: u32| -> (out: u32)
                requires 0 < x < 10,
                ensures out == x + 10,
            { x + 10 });
            let ghost initial = iter;
            assert(!initial.produces()[0]);
            let back = iter.next_back();
            assert(initial.produces()[2]);
            assert(map_iter(initial).produces()[2]);
            assert(map_iter(inner).produces()[2]);
            assert(back == Some(12));
            assert(iter.produces() == initial.produces().drop_last());
            let back = iter.next_back();
            assert(initial.produces()[1]);
            assert(map_iter(initial).produces()[1]);
            assert(map_iter(inner).produces()[1]);
            assert(back == Some(11));
            assert(iter.remaining().len() == 1);
            assert(iter.produces() =~= seq![false]);
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
                i.produces().all(|p: bool| p),
            ensures
                // TODO: The number of operators needed here is unfortunate
                (&(*final(i))).obeys_prophetic_iter_laws(),
                (&(*final(i))).produces().all(|p: bool| p),
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

        // A StepSpecImpl does not prove anything about the executable Step methods.
        impl StepSpecImpl for S {
            open spec fn spec_is_lt(self, other: Self) -> bool { self.0 < other.0 }
            open spec fn spec_steps_between(self, end: Self) -> Option<usize> { Some(1) }
            open spec fn spec_steps_between_int(self, end: Self) -> int { 1 }
            open spec fn spec_forward_checked(self, count: usize) -> Option<Self> { Some(S(7)) }
            open spec fn spec_forward_checked_int(self, count: int) -> Option<Self> { Some(S(7)) }
            open spec fn spec_backward_checked(self, count: usize) -> Option<Self> { None }
            open spec fn spec_backward_checked_int(self, count: int) -> Option<Self> { None }
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

            // No StepSpecImpl: the uninterpreted spec_range_next must not imply
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
            #[verifier::prophetic]
            open spec fn produces(&self) -> Seq<bool> { Seq::empty() }
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
