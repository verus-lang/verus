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
    #[test] vec_iter_mut_works verus_code! {
        use vstd::prelude::*;
        
        fn client_for_loop() {
            let mut v: Vec<u32> = vec![1, 2, 3, 4];
            for x in it: v.iter_mut() 
                invariant
                    // TODO: Ideally we shouldn't need these first two invariants
                    after_borrow(v)@.len() == it.seq().len(),
                    forall |i: int| #![auto] 0 <= i < it.seq().len() ==> *final(it.seq()[i]) == after_borrow(v)@[i],
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
        use vstd::proph::ProphecyGhost;

        pub trait Predicate<T> {
            #[verifier::prophetic]
            spec fn pred(&self, i: int, t: T) -> bool;
        }

        #[verifier::accept_recursive_types(T)]
        pub tracked struct ProphSeq<T, Pred> {
            // A single prophecy for the prophesied value at every index.
            tracked var: ProphecyGhost<spec_fn(int) -> T>,
            // The values of indices that have already been resolved.
            ghost resolved: Map<int, T>,
            // The predicate this sequence is constrained by.
            ghost p: Pred,
        }

        impl<T, Pred> ProphSeq<T, Pred>
            where Pred: Predicate<T>
        {
            pub closed spec fn pred(&self) -> Pred {
                self.p
            }

            #[verifier::prophetic]
            pub closed spec fn proph_elem(&self, i: int) -> Option<T> {
                let v = if self.resolved.dom().contains(i) {
                    self.resolved[i]
                } else {
                    self.var.value()(i)
                };
                if self.p.pred(i, v) {
                    Some(v)
                } else {
                    None
                }
            }

            pub closed spec fn has_resolved(&self, i: int) -> bool {
                self.resolved.dom().contains(i)
            }

            pub proof fn new(pred: Pred) -> (tracked s: Self)
                ensures
                    s.pred() == pred,
                    forall |i| !s.has_resolved(i),
            {
                let tracked var = ProphecyGhost::new();
                ProphSeq { var, resolved: Map::empty(), p: pred }
            }

            pub proof fn proph_elem_meets_pred(tracked &self)
                ensures forall |i: int| (match #[trigger] self.proph_elem(i) {
                    Some(p) => self.pred().pred(i, p),
                    None => true,
                }),
            {
            }

            pub proof fn resolve(tracked &mut self, i: int, t: T)
                requires
                    !old(self).has_resolved(i),
                    old(self).pred().pred(i, t),
                ensures
                    final(self).pred() == old(self).pred(),
                    forall |j| final(self).proph_elem(j) == old(self).proph_elem(j),
                    forall |j| i != j ==> final(self).has_resolved(j) == old(self).has_resolved(j),
                    final(self).has_resolved(i),
                    final(self).proph_elem(i) == Some(t),
            {
                // Peel off coordinate `i`: replace the live prophecy with a fresh one
                // holding the remaining (still prophetic) coordinates, and resolve the
                // old prophecy as a function of the fresh one that pins index `i` to `t`.
                let tracked mut var = ProphecyGhost::new();
                vstd::modes::tracked_swap(&mut var, &mut self.var);
                var.resolve_dependent(
                    &self.var,
                    |g: spec_fn(int) -> T| (|j: int| if j == i { t } else { g(j) }),
                );
                self.resolved = self.resolved.insert(i, t);

                assert forall |j| #[trigger] final(self).proph_elem(j) == old(self).proph_elem(j) by {
                    if j != i && !old(self).resolved.dom().contains(j) {
                        // Unresolved (other) coordinate: old and fresh prophecy agree.
                        assert(old(self).var.value()(j) == final(self).var.value()(j));
                    }
                }
            }
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
                forall|i: int| #![trigger refs@[i]] 0 <= i < refs@.len() ==>
                    *(refs@[i]) == old(s)@[refs@.len() - 1 - i],
                final(s)@.len() == old(s)@.len(),
                forall|i: int| #![trigger refs@[i]] 0 <= i < refs@.len() ==>
                    *final(refs@[i]) == final(s)@[refs@.len() - 1 - i],
        {
            let ghost n0 = s@.len();
            let ghost sf: Seq<T> = final(s)@;
            let mut refs: Vec<&'a mut T> = Vec::new();
            let mut rest: &'a mut [T] = s;
            while rest.len() > 0
                invariant
                    rest@.len() + refs@.len() == n0,
                    forall|i: int| #![trigger rest@[i]] 0 <= i < rest@.len() ==> rest@[i] == old(s)@[i],
                    forall|i: int| #![trigger refs@[i]] 0 <= i < refs@.len() ==>
                        *(refs@[i]) == old(s)@[n0 - 1 - i],
                    sf == final(rest)@ + Seq::new(
                        refs@.len() as nat,
                        |j: int| *final(refs@[refs@.len() - 1 - j]),
                    ),
                decreases rest.len(),
            {
                let (head, tail) = rest.split_at_mut(rest.len() - 1);
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

            fn next(&mut self) -> (r: Option<&'a mut T>) {
                self.refs.pop()
            }
        }

        impl<'a, T> IteratorSpecImpl for MyIterMut<'a, T> {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool {
                true
            }

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

        fn client_set() {
            let mut v: Vec<u32> = vec![10, 20];
            let mut it = MyIterMut::new(&mut v);

            let r0 = it.next().unwrap();
            *r0 = 100;
            let r1 = it.next().unwrap();
            *r1 = 200;

            assert(v@ == seq![100u32, 200]);
        }

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

        fn client_for_loop() {
            let mut v: Vec<u32> = vec![1, 2, 3, 4];
            let mut iter = MyIterMut::new(&mut v);

            for x in it: iter 
                invariant
                    // TODO: Ideally we shouldn't need these first two invariants
                    after_borrow(v)@.len() == it.seq().len(),
                    forall |i: int| #![auto] 0 <= i < it.seq().len() ==> *final(it.seq()[i]) == after_borrow(v)@[i],
                    forall |i: int| #![auto] 0 <= i < it.index() ==> *final(it.seq()[i]) == 0,
            {
                *x = 0;
            }
            assert(forall |i: int| 0 <= i < v.len() ==> v[i] == 0);
            assert(v@ == seq![0, 0, 0, 0]);
        }        
    } => Ok(())
}
