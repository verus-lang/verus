#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

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

test_verify_one_file! {
    #[test] collect_works verus_code! {
        use vstd::prelude::*;

        fn test(u: &Vec<u32>)
        {
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
            } else {
                assert(forall |i| 0 <= i < v.len() ==> v[i] >= 10);
            }
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
    #[test] map_can_be_implemented verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::*;

        /* proph util (this should be implementable) */

        pub trait Predicate<T> {
            #[verifier::prophetic]
            spec fn pred(&self, i: int, t: T) -> bool;
        }

        #[verifier::external_body]
        #[verifier::accept_recursive_types(T)]
        #[verifier::accept_recursive_types(Pred)]
        pub tracked struct ProphSeq<T, Pred> { t: T, pred: Pred }

        impl<T, Pred> ProphSeq<T, Pred>
            where Pred: Predicate<T>
        {
            pub uninterp spec fn pred(&self) -> Pred;
            pub uninterp spec fn proph_elem(&self, i: int) -> Option<T>;
            pub uninterp spec fn has_resolved(&self, i: int) -> bool;

            pub axiom fn new(pred: Pred) -> (tracked s: Self)
                ensures
                    s.pred() == pred,
                    forall |i| !s.has_resolved(i);


            pub axiom fn proph_elem_meets_pred(tracked &self)
                ensures forall |i: int| (match #[trigger] self.proph_elem(i) {
                    Some(p) => self.pred().pred(i, p),
                    None => true,
                });

            pub axiom fn resolve(tracked &mut self, i: int, t: T)
                requires
                    !old(self).has_resolved(i),
                    old(self).pred().pred(i, t),
                ensures
                    final(self).pred() == old(self).pred(),
                    forall |j| final(self).proph_elem(j) == old(self).proph_elem(j),
                    forall |j| i != j ==> final(self).has_resolved(j) == old(self).has_resolved(j),
                    final(self).has_resolved(i),
                    final(self).proph_elem(i) == Some(t);
        }


        /* map iterator */
        pub ghost struct MapIteratorPred<Iter, F> {
            iter: Iter,
            f: F,
        }

        impl<Item, Iter, F> Predicate<Item> for MapIteratorPred<Iter, F>
            where
                Iter: Iterator,
                F: FnMut(Iter::Item) -> Item
        {
            #[verifier::prophetic]
            closed spec fn pred(&self, i: int, t: Item) -> bool {
                call_ensures(self.f, (self.iter.remaining()[i],), t)
            }
        }

        #[verifier::reject_recursive_types(Item)]
        pub struct MapIterator<Item, Iter, F>
            where
                Iter: Iterator,
                F: FnMut(Iter::Item) -> Item
        {
            f: F,
            iter: Iter,

            prophs: Tracked<ProphSeq<Item, MapIteratorPred<Iter, F>>>,
            idx: Ghost<int>,
        }

        impl<Item, Iter, F> MapIterator<Item, Iter, F>
            where
                Iter: Iterator,
                F: FnMut(Iter::Item) -> Item
        {
            pub closed spec fn inner(self) -> Iter {
                self.iter
            }

            pub closed spec fn func(self) -> F {
                self.f
            }

            pub closed spec fn the_prophs(self) -> ProphSeq<Item, MapIteratorPred<Iter, F>> {
                self.prophs@
            }

            pub closed spec fn count(self) -> nat {
                self.idx@ as nat
            }

            //#[verifier::type_invariant] // fake this due to &mut limitations
            #[verifier::prophetic]
            pub closed spec fn map_iterator_type_inv(self) -> bool {
                0 <= self.idx@ <= self.prophs@.pred().iter.remaining().len()
                  && self.iter.remaining() =~= self.prophs@.pred().iter.remaining().skip(self.idx@)
                  && self.prophs@.pred().f == self.f
                  && (forall |i| #![auto] 0 <= i < self.iter.remaining().len() ==> call_requires(self.f, (self.iter.remaining()[i], )))
                  && (forall |i: int| self.idx@ <= i < self.idx@ + self.iter.remaining().len() ==> !self.prophs@.has_resolved(i))
                  && self.iter.obeys_prophetic_iter_laws()
            }

            pub fn new(iter: Iter, f: F) -> (s: Self)
                requires
                    iter.obeys_prophetic_iter_laws(),
                    forall |i| #![auto] 0 <= i < iter.remaining().len() ==>
                        call_requires(f, (iter.remaining()[i], ))
                ensures
                    IteratorSpec::remaining(&s).len() <= iter.remaining().len(),
                    forall |i| #![auto] 0 <= i < IteratorSpec::remaining(&s).len() ==>
                        call_ensures(f, (iter.remaining()[i],), IteratorSpec::remaining(&s)[i]),
                    IteratorSpec::will_return_none(&s) ==> iter.will_return_none() && IteratorSpec::remaining(&s).len() == iter.remaining().len(),
                    s.count() == 0,
                    s.inner() == iter,
                    IteratorSpec::decrease(&s) is Some == iter.decrease() is Some,
            {
                let s = Self {
                    f: f,
                    iter: iter,
                    prophs: Tracked(ProphSeq::new(MapIteratorPred {
                        iter: iter,
                        f: f,
                    })),
                    idx: Ghost(0),
                };

                assert(s.map_iterator_type_inv());
                proof {
                    s.prophs.borrow().proph_elem_meets_pred();
                    // PAPER CUT: can't call lemma with prophetic arg
                    broadcast use unwrap_up_to_first_none_len_le;
                    broadcast use unwrap_up_to_first_none_len_le_values;
                }
                s
            }

            #[verifier::prophetic]
            spec fn seq_of_options(&self) -> Seq<Option<Item>> {
                Seq::new(self.iter.remaining().len(), |i| {
                    self.prophs@.proph_elem(self.idx@ + i)
                })
            }
        }

        pub closed spec fn unwrap_up_to_first_none<T>(seq: Seq<Option<T>>) -> Seq<T>
            decreases seq.len()
        {
            if seq.len() == 0 {
                seq![]
            } else if seq[0].is_some() {
                seq![seq[0].unwrap()] + unwrap_up_to_first_none(seq.drop_first())
            } else {
                seq![]
            }
        }

        pub broadcast proof fn unwrap_up_to_first_none_len_le<T>(seq: Seq<Option<T>>)
            ensures #[trigger] unwrap_up_to_first_none(seq).len() <= seq.len(),
                (forall |i| 0 <= i < seq.len() ==> seq[i].is_some()) ==>
                    unwrap_up_to_first_none(seq).len() == seq.len(),
            decreases seq.len()
        {
            if seq.len() != 0 && seq[0].is_some() {
                unwrap_up_to_first_none_len_le(seq.drop_first());
            }
        }

        pub broadcast proof fn unwrap_up_to_first_none_len_le_values<T>(seq: Seq<Option<T>>, i: int)
            requires 0 <= i < unwrap_up_to_first_none(seq).len()
            ensures
                i < seq.len(),
                seq[i].is_some(),
                #[trigger] unwrap_up_to_first_none(seq)[i] == seq[i].unwrap(),
            decreases seq.len()
        {
            if i > 0 {
                unwrap_up_to_first_none_len_le_values(seq.drop_first(), i-1);
            }
        }

        impl<Item, Iter, F> Iterator for MapIterator<Item, Iter, F>
            where
                Iter: Iterator,
                F: FnMut(Iter::Item) -> Item
        {
            type Item = Item;

            fn next(&mut self) -> (ret: Option<Self::Item>)
            {
                assume(self.map_iterator_type_inv());

                match self.iter.next() {
                    None => {
                        assert(self.map_iterator_type_inv());
                        return None;
                    }
                    Some(elem) => {
                        let output = (self.f)(elem);
                        proof {
                            self.prophs.borrow_mut().resolve(self.idx@, output);
                            self.idx@ = self.idx@ + 1;
                        }

                        assert(self.seq_of_options() == old(self).seq_of_options().drop_first());
                        assert(self.map_iterator_type_inv());
                        return Some(output);
                    }
                }
            }
        }

        impl<Item, Iter, F> IteratorSpecImpl for MapIterator<Item, Iter, F>
            where
                Iter: Iterator,
                F: FnMut(Iter::Item) -> Item
        {

            open spec fn obeys_prophetic_iter_laws(&self) -> bool {
                true
            }

            #[verifier::prophetic]
            closed spec fn remaining(&self) -> Seq<Self::Item> {
                unwrap_up_to_first_none(self.seq_of_options())
            }

            #[verifier::prophetic]
            closed spec fn will_return_none(&self) -> bool {
                self.iter.will_return_none()
                  && (forall |i: int| self.idx@ <= i < self.idx@ + self.iter.remaining().len() ==> self.prophs@.proph_elem(i).is_some())
            }

            #[verifier::prophetic]
            open spec fn initial_value_relation(&self, init: &Self) -> bool {
                &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
                &&& self.inner().initial_value_relation(&init.inner())
            }


            closed spec fn decrease(&self) -> Option<nat> {
                self.inner().decrease()
            }


            open spec fn peek(&self, index: int) -> Option<Self::Item> {
                match self.inner().peek(index) {
                    Some(v) => {
                        let x = choose |x| self.func().ensures((v,), x);
                        Some(x)
                    }
                    None => None,
                }
            }
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] iter_mut_can_be_implemented verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::*;

        // Eagerly split a mutable slice into the mutable references to each of its elements, 
        // returned in *reversed* order (so popping the `Vec` yields elements front-to-back).  
        fn split_all<'a, T>(s: &'a mut [T]) -> (refs: Vec<&'a mut T>)
            ensures
                refs@.len() == old(s)@.len(),
                // Current value of each element reference (reversed indexing).
                forall|i: int| #![trigger refs@[i]] 0 <= i < refs@.len() ==>
                    *(refs@[i]) == old(s)@[refs@.len() - 1 - i],
                // The slice's final length matches.
                final(s)@.len() == old(s)@.len(),
                // The prophesied final value of each element reference flows back to the
                // slice's final value (reversed indexing).
                forall|i: int| #![trigger refs@[i]] 0 <= i < refs@.len() ==>
                    *final(refs@[i]) == final(s)@[refs@.len() - 1 - i],
        {
            let ghost n0 = s@.len();
            // Capture the slice's prophesied final value *before* we move `s` into `rest`;
            // afterwards `s` is borrowed and `final(s)` can no longer be named directly.
            let ghost sf: Seq<T> = final(s)@;
            let mut refs: Vec<&'a mut T> = Vec::new();
            let mut rest: &'a mut [T] = s;
            while rest.len() > 0
                invariant
                    rest@.len() + refs@.len() == n0,
                    // `rest` is the not-yet-peeled prefix.
                    forall|i: int| #![trigger rest@[i]] 0 <= i < rest@.len() ==> rest@[i] == old(s)@[i],
                    // Already-peeled references carry the correct current values.
                    forall|i: int| #![trigger refs@[i]] 0 <= i < refs@.len() ==>
                        *(refs@[i]) == old(s)@[n0 - 1 - i],
                    // Telescoping prophecy: the original final value equals the still-to-be
                    // peeled prefix's final value, followed by the finals of the peeled
                    // references (in forward order, hence the reversal).
                    sf == final(rest)@ + Seq::new(
                        refs@.len() as nat,
                        |j: int| *final(refs@[refs@.len() - 1 - j]),
                    ),
                decreases rest.len(),
            {
                let n = rest.len();
                let (head, tail) = rest.split_at_mut(n - 1);
                let last = tail.first_mut().unwrap();
                refs.push(last);
                rest = head;
            }
            refs
        }

        // Mutable iterator over the elements of a `Vec`, modeling `slice::IterMut`.
        // `refs` holds the element references in *reversed* order, so `next` is `pop`.
        struct MyIterMut<'a, T> {
            refs: Vec<&'a mut T>,
        }

        impl<'a, T> MyIterMut<'a, T> {
            /// Non-prophetic count of references still to be returned 
            pub closed spec fn rem_len(&self) -> nat {
                self.refs@.len()
            }

            /// Models `Vec::iter_mut`: borrows the `Vec` for `'a` and produces an iterator
            /// that will hand out a `&'a mut T` for each element, in order.
            pub fn new(v: &'a mut Vec<T>) -> (s: MyIterMut<'a, T>)
                ensures
                    IteratorSpec::remaining(&s).len() == old(v)@.len(),
                    final(v)@.len() == old(v)@.len(),
                    // Each yielded reference initially points at the corresponding element.
                    forall|i: int| #![trigger IteratorSpec::remaining(&s)[i]]
                        0 <= i < old(v)@.len() ==> *(IteratorSpec::remaining(&s)[i]) == old(v)@[i],
                    // ...and its eventual value flows back to the corresponding `Vec` slot.
                    forall|i: int| #![trigger IteratorSpec::remaining(&s)[i]]
                        0 <= i < old(v)@.len() ==> *final(IteratorSpec::remaining(&s)[i]) == final(v)@[i],
                    IteratorSpec::obeys_prophetic_iter_laws(&s),
                    IteratorSpec::will_return_none(&s),
                    IteratorSpec::decrease(&s) is Some,
                    IteratorSpec::initial_value_relation(&s, &s),
            {
                let slice = v.as_mut_slice();
                let refs = split_all(slice);
                MyIterMut { refs }
            }
        }

        impl<'a, T> Iterator for MyIterMut<'a, T> {
            type Item = &'a mut T;

            // Verus checks this `next` against the `IteratorSpec` trait specification.
            fn next(&mut self) -> (r: Option<&'a mut T>) {
                self.refs.pop()
            }
        }

        impl<'a, T> IteratorSpecImpl for MyIterMut<'a, T> {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool {
                true
            }

            // The forward sequence of references still to be returned is the reverse of the
            // (reverse-stored) `refs` vector.
            #[verifier::prophetic]
            closed spec fn remaining(&self) -> Seq<Self::Item> {
                Seq::new(self.refs@.len(), |i: int| self.refs@[self.refs@.len() - 1 - i])
            }

            #[verifier::prophetic]
            closed spec fn will_return_none(&self) -> bool {
                true
            }

            #[verifier::prophetic]
            open spec fn initial_value_relation(&self, init: &Self) -> bool {
                IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
            }

            closed spec fn decrease(&self) -> Option<nat> {
                Some(self.refs@.len() as nat)
            }

            open spec fn peek(&self, index: int) -> Option<Self::Item> {
                None
            }
        }

        /// Bridges the prophetic `remaining()` length to the non-prophetic `rem_len()`,
        /// so loop clients can use `rem_len()` for `decreases` while reasoning about
        /// `remaining()` for correctness.
        broadcast proof fn lemma_rem_len<'a, T>(it: &MyIterMut<'a, T>)
            ensures
                #[trigger] IteratorSpec::remaining(it).len() == it.rem_len(),
        {
        }

        /// Client 1: drive the iterator by hand and overwrite each element, then observe
        /// the updates reflected back in the original `Vec` (the `*x = <const>` shape).
        fn client_set() {
            let mut v: Vec<u32> = vec![10, 20];
            let mut it = MyIterMut::new(&mut v);

            let r0 = it.next().unwrap();
            *r0 = 100;
            let r1 = it.next().unwrap();
            *r1 = 200;

            // After the references resolve and `it`'s borrow of `v` expires, the mutations
            // are visible in `v`.
            assert(v@ == seq![100u32, 200]);
        }

        /// Client 2: read-modify-write through the mutable references (the `*x = x + 1`
        /// shape from the motivating example).
        fn client_increment() {
            let mut v: Vec<u32> = vec![1, 2, 3];
            let mut it = MyIterMut::new(&mut v);

            let r0 = it.next().unwrap();
            *r0 = *r0 + 1;
            let r1 = it.next().unwrap();
            *r1 = *r1 + 1;
            let r2 = it.next().unwrap();
            *r2 = *r2 + 1;

            assert(v@ == seq![2u32, 3, 4]);
        }

        /// Client 3: a general, arbitrary-length `while` loop over `next()` -- the manual
        /// equivalent of `for x in v.iter_mut() { *x = 0; }`.  Proves that every element
        /// of `v` ends up zeroed.
        fn client_loop_general() {
            broadcast use lemma_rem_len;
            broadcast use vstd::seq_lib::group_seq_properties;

            let mut v: Vec<u32> = vec![5u32, 6, 7, 8, 9];
            let blen = v.len();
            let ghost n = v@.len();
            let mut it = MyIterMut::new(&mut v);
            // Prophetic snapshot of the references the iterator will hand out.
            let ghost rem0 = IteratorSpec::remaining(&it);
            let mut k: usize = 0;
            while k < blen
                invariant
                    k <= n,
                    n == rem0.len(),
                    n == blen,
                    it.rem_len() == n - k,
                    IteratorSpec::remaining(&it) == rem0.skip(k as int),
                    IteratorSpec::obeys_prophetic_iter_laws(&it),
                    // Each handed-out reference's eventual value flows back to `v`.
                    forall|j: int| #![trigger rem0[j]] 0 <= j < n ==> *final(rem0[j]) == after_borrow(v)@[j],
                    after_borrow(v)@.len() == n,
                    // Every reference processed so far has been set to 0.
                    forall|j: int| #![trigger rem0[j]] 0 <= j < k ==> *final(rem0[j]) == 0,
                decreases it.rem_len(),
            {
                let ghost k_old = k as int;
                assert(rem0.skip(k_old).len() > 0);
                let x = it.next().unwrap();
                assert(x == rem0[k_old]);
                *x = 0;
                k += 1;
                assert(IteratorSpec::remaining(&it) =~= rem0.skip(k as int));
            }

            // On loop exit k == n, so every reference was set to 0; chain that back to `v`.
            assert forall|j: int| 0 <= j < n implies after_borrow(v)@[j] == 0 by {
                assert(*final(rem0[j]) == 0);
            }
            assert(v@ =~= after_borrow(v)@);
            assert(forall|j: int| 0 <= j < n ==> v@[j] == 0);
        }
    } => Ok(())
}