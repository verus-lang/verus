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
    #[test] zip_works verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::zip_iterators;

        fn zip_works() {
            let w = vec![1u32, 2, 3];
            let x = vec![2u32, 4, 6];
            let y = vec![1u32, 2];
            let z = vec![2u32, 4, 6, 8, 10];

            let wx: Vec<(&u32, &u32)> = zip_iterators(w.iter(), x.iter()).collect();
            assert(wx@.unref() == seq![(1u32,2u32), (2, 4), (3, 6)]);

            let xy: Vec<(&u32, &u32)> = zip_iterators(x.iter(), y.iter()).collect();
            assert(xy@.unref() == seq![(2u32,1u32), (4, 2)]);

            let yz: Vec<(&u32, &u32)> = zip_iterators(y.iter(), z.iter()).collect();
            assert(yz@.unref() == seq![(1u32,2u32), (2, 4)]);
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
    #[test] map_works verus_code! {
        use vstd::prelude::*;

        fn double_it() {
            let f = |x: &u32| -> (y: u32) requires *x < 10, ensures y == x * 2 { *x * 2 };
            let v = vec![1u32, 2, 3, 4];
            let mut w = Vec::new();
            for x in iter: v.iter().map(f)
                invariant
                    w.len() == iter.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == iter.seq()[i],
                    // TODO: Fails b/c we can't have a when_used_as_spec version of `map`
                    //forall |i| 0 <= i < w.len() ==> w[i] == v[i] * 2,
            {
                assert(x == iter.seq()[iter.index()]);
                // TODO: Fails b/c we can't have a when_used_as_spec version of `map`
                //assert(x == v[iter.index()] * 2);
                w.push(x);
            }
            assert(w@ == seq![2u32, 4, 6, 8]);
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
    #[test] filter_can_be_implemented verus_code! {
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

        /* filter iterator */
        pub ghost struct FilterIteratorPred<Iter, F> {
            iter: Iter,
            f: F,
        }

        impl<Iter, F> Predicate<bool> for FilterIteratorPred<Iter, F>
            where
                Iter: Iterator,
                F: FnMut(&Iter::Item) -> bool
        {
            #[verifier::prophetic]
            closed spec fn pred(&self, i: int, b: bool) -> bool {
                self.f.ensures((&self.iter.remaining()[i],), b)
            }
        }

        pub struct FilterIterator<Iter, F>
            where
                Iter: Iterator,
                F: FnMut(&Iter::Item) -> bool
        {
            f: F,
            iter: Iter,

            prophs: Tracked<ProphSeq<bool, FilterIteratorPred<Iter, F>>>,
            idx: Ghost<int>,
        }

        impl<Iter, F> FilterIterator<Iter, F>
            where
                Iter: Iterator,
                F: FnMut(&Iter::Item) -> bool
        {
            pub closed spec fn inner(self) -> Iter {
                self.iter
            }

            pub closed spec fn func(self) -> F {
                self.f
            }

            pub closed spec fn the_prophs(self) -> ProphSeq<bool, FilterIteratorPred<Iter, F>> {
                self.prophs@
            }

            pub closed spec fn count(self) -> nat {
                self.idx@ as nat
            }

            //#[verifier::type_invariant] // fake this due to &mut limitations
            #[verifier::prophetic]
            pub closed spec fn filter_iterator_type_inv(self) -> bool {
                0 <= self.idx@ <= self.prophs@.pred().iter.remaining().len()
                && self.iter.remaining() =~= self.prophs@.pred().iter.remaining().skip(self.idx@)
                && self.prophs@.pred().f == self.f
                && (forall |i| #![auto] 0 <= i < self.iter.remaining().len() ==> self.f.requires((&self.iter.remaining()[i], )))
                && (forall |i: int| self.idx@ <= i < self.idx@ + self.iter.remaining().len() ==> !self.prophs@.has_resolved(i))
                && self.iter.obeys_prophetic_iter_laws()
                // We need this to prove termination of our loop in `next()`
                && self.iter.decrease() is Some
            }

            pub fn new(iter: Iter, f: F) -> (s: Self)
                requires
                    iter.obeys_prophetic_iter_laws(),
                    iter.decrease() is Some,
                    forall |i| #![auto] 0 <= i < iter.remaining().len() ==>
                        f.requires((&iter.remaining()[i], ))
                ensures
                    s.keep().len() <= iter.remaining().len(),
                    forall |j| 0 <= j < s.keep().len() ==> f.ensures((&iter.remaining()[j],), #[trigger] s.keep()[j]),
                    IteratorSpec::remaining(&s) == iter.remaining().take(s.keep().len() as int).filter_index(|j: int| s.keep()[j]),
                    IteratorSpec::remaining(&s).len() <= iter.remaining().len(),
                    forall |i| #![trigger IteratorSpec::remaining(&s)[i]] 0 <= i < IteratorSpec::remaining(&s).len() ==>
                        exists |j| 0 <= j < iter.remaining().len()
                            && IteratorSpec::remaining(&s)[i] == #[trigger] iter.remaining()[j]
                            && f.ensures((&iter.remaining()[j],), true),
                    IteratorSpec::will_return_none(&s) ==> iter.will_return_none() && s.keep().len() == iter.remaining().len(),
                    s.count() == 0,
                    s.inner() == iter,
                    IteratorSpec::decrease(&s) is Some == iter.decrease() is Some,
            {
                let s = Self {
                    f: f,
                    iter: iter,
                    prophs: Tracked(ProphSeq::new(FilterIteratorPred {
                        iter: iter,
                        f: f,
                    })),
                    idx: Ghost(0),
                };

                assert(s.filter_iterator_type_inv());
                proof {
                    s.prophs.borrow().proph_elem_meets_pred();
                    // PAPER CUT: can't call lemma with prophetic arg
                    broadcast use unwrap_up_to_first_none_len_le;
                    broadcast use unwrap_up_to_first_none_len_le_values;
                    broadcast use Seq::lemma_filter_index;
                }
                s
            }

            #[verifier::prophetic]
            spec fn seq_of_options(&self) -> Seq<Option<bool>> {
                Seq::new(self.iter.remaining().len(), |i| {
                    self.prophs@.proph_elem(self.idx@ + i)
                })
            }

            #[verifier::prophetic]
            pub closed spec fn keep(self) -> Seq<bool> {
                unwrap_up_to_first_none(self.seq_of_options())
            }

            #[verifier::prophetic]
            closed spec fn spec_remaining(&self) -> Seq<Iter::Item> {
                self.iter.remaining().take(self.keep().len() as int).filter_index(|i| self.keep()[i])
            }

            #[verifier::prophetic]
            closed spec fn spec_will_return_none(&self) -> bool {
                self.iter.will_return_none()
                && (forall |i: int| self.idx@ <= i < self.idx@ + self.iter.remaining().len() ==> self.prophs@.proph_elem(i).is_some())
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

        // Dropping the head element either preserves `remaining()` (if `b == false`, i.e.
        // `f` rejected the head) or pops its first element (if `b == true`).
        proof fn lemma_remaining_step<T>(rem: Seq<T>, opts: Seq<Option<bool>>, b: bool)
            requires
                rem.len() == opts.len(),
                rem.len() > 0,
                opts[0] == Some(b),
            ensures
                ({
                    let keep = unwrap_up_to_first_none(opts);
                    let keep_n = unwrap_up_to_first_none(opts.drop_first());
                    let remaining = rem.take(keep.len() as int).filter_index(|i: int| keep[i]);
                    let remaining_n = rem.drop_first().take(keep_n.len() as int).filter_index(|i: int| keep_n[i]);
                    &&& keep.len() == keep_n.len() + 1
                    &&& b ==> remaining == seq![rem[0]] + remaining_n
                    &&& !b ==> remaining == remaining_n
                }),
        {
            broadcast use unwrap_up_to_first_none_len_le;
            let keep = unwrap_up_to_first_none(opts);
            let keep_n = unwrap_up_to_first_none(opts.drop_first());
            assert(keep == seq![b] + keep_n) by {
                reveal(unwrap_up_to_first_none);
            }
            assert(forall|i: int| 0 <= i < keep_n.len() ==> keep[i + 1] == keep_n[i]);
            let s = rem.take(keep.len() as int);
            let pred = |i: int| keep[i];
            s.lemma_filter_index_head(pred);

            let rem_n = rem.drop_first();
            assert(s.drop_first() =~= rem_n.take(keep_n.len() as int));

            let shifted = |i: int| pred(i + 1);
            let pred_n = |i: int| keep_n[i];
            rem_n.take(keep_n.len() as int).filter_index_ext(shifted, pred_n);
        }

        proof fn lemma_filter_step<Iter, F>(
            h: FilterIterator<Iter, F>,
            n: FilterIterator<Iter, F>,
            b: bool,
        )
            where
                Iter: Iterator,
                F: FnMut(&Iter::Item) -> bool,
            requires
                h.iter.remaining().len() > 0,
                h.prophs@.proph_elem(h.idx@) == Some(b),
                n.idx@ == h.idx@ + 1,
                n.iter.remaining() == h.iter.remaining().drop_first(),
                forall|j: int| n.prophs@.proph_elem(j) == h.prophs@.proph_elem(j),
                n.iter.will_return_none() == h.iter.will_return_none(),
            ensures
                b ==> h.spec_remaining()
                        == seq![h.iter.remaining()[0]] + n.spec_remaining(),
                !b ==> h.spec_remaining() == n.spec_remaining(),
                n.spec_will_return_none() == h.spec_will_return_none(),
        {
            assert(n.seq_of_options() =~= h.seq_of_options().drop_first());
            lemma_remaining_step(h.iter.remaining(), h.seq_of_options(), b);
        }

        impl<Iter, F> Iterator for FilterIterator<Iter, F>
            where
                Iter: Iterator,
                F: FnMut(&Iter::Item) -> bool
        {
            type Item = Iter::Item;

            fn next(&mut self) -> (ret: Option<Self::Item>)
            {
                broadcast use {Seq::lemma_filter_index,unwrap_up_to_first_none_len_le,unwrap_up_to_first_none_len_le_values};
                assume(self.filter_iterator_type_inv());

                loop
                    invariant
                        self.filter_iterator_type_inv(),
                        self.iter.decrease() is Some,
                        old(self).iter.decrease() is Some,
                        self.iter.decrease()->0 <= old(self).iter.decrease()->0,
                        self.idx@ >= old(self).idx@,
                        self.spec_remaining() == old(self).spec_remaining(),
                        self.spec_will_return_none() == old(self).spec_will_return_none(),
                    decreases self.iter.decrease()->0,
                {
                    let ghost h = *self;
                    let item = self.iter.next();
                    match item {
                        None => {
                            assert(self.spec_remaining().len() == 0) by {
                                reveal(Seq::filter_index);
                            }
                            assert(self.filter_iterator_type_inv());
                            return None;
                        }
                        Some(i) => {
                            // The underlying head we just pulled.
                            let keep = (self.f)(&i);
                            proof {
                                self.prophs.borrow_mut().resolve(self.idx@, keep);
                                self.idx@ = self.idx@ + 1;
                            }
                            assert(self.seq_of_options() == h.seq_of_options().drop_first());
                            proof {
                                lemma_filter_step(h, *self, keep);
                            }
                            if keep {
                                assert(old(self).spec_remaining() == seq![i] + self.spec_remaining());
                                assert(old(self).spec_remaining().drop_first() =~= self.spec_remaining());
                                assert(self.filter_iterator_type_inv());
                                return Some(i);
                            } else {
                                assert(self.filter_iterator_type_inv());
                            }
                        }
                    }
                }
            }
        }

        impl<Iter, F> IteratorSpecImpl for FilterIterator<Iter, F>
            where
                Iter: Iterator,
                F: FnMut(&Iter::Item) -> bool
        {

            open spec fn obeys_prophetic_iter_laws(&self) -> bool {
                true
            }

            #[verifier::prophetic]
            closed spec fn remaining(&self) -> Seq<Self::Item> {
                self.spec_remaining()
            }

            #[verifier::prophetic]
            closed spec fn will_return_none(&self) -> bool {
                self.spec_will_return_none()
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
                None
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] take_can_be_implemented verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        struct MyTake<I> {
            iter: I,
            count_remaining: usize,
        }

        impl<I: IteratorSpec> MyTake<I> {
            pub closed spec fn iter(self) -> I {
                self.iter
            }

            pub closed spec fn count(self) -> usize {
                self.count_remaining
            }

            //#[verifier::type_invariant] // fake this (via assert/assume below) due to limitations:
            //  With this as a type invariantVerus won't let us call self.iter.next() unless it's marked no_unwind
            #[verifier::prophetic]
            pub closed spec fn take_inv(self) -> bool {
                self.iter.obeys_prophetic_iter_laws()
            }

            closed spec fn my_take_new(iter: I, n: usize) -> (t: MyTake<I>) {
                MyTake { iter, count_remaining: n }
            }

            #[verifier::when_used_as_spec(my_take_new)]
            fn new(iter: I, n: usize) -> (t: MyTake<I>)
                requires
                    iter.obeys_prophetic_iter_laws(),
                ensures
                    t.remaining() == (if iter.remaining().len() < n { iter.remaining() } else { iter.remaining().take(n as int) }),
                    t.will_return_none() <==> iter.will_return_none() || iter.remaining().len() >= n,
                    t.obeys_prophetic_iter_laws(),
                    // t.iter() == iter,
                    // t.count() == n,
                    t.decrease() is Some,
                    t == Self::my_take_new(iter, n),
            {
                MyTake { iter, count_remaining: n }
            }
        }


        impl<I: Iterator> Iterator for MyTake<I> {
            type Item = <I as Iterator>::Item;

            fn next(&mut self) -> Option<<I as Iterator>::Item> {
                assume(self.take_inv());
                if self.count_remaining != 0 {
                    self.count_remaining -= 1;
                    let r = self.iter.next();
                    assert(self.take_inv());
                    r
                } else {
                    assert(self.take_inv());
                    None
                }
            }
        }

        impl<I: Iterator> vstd::std_specs::iter::IteratorSpecImpl for MyTake<I> {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool {
                true
            }

            #[verifier::prophetic]
            closed spec fn remaining(&self) -> Seq<Self::Item> {
                if self.iter.remaining().len() < self.count_remaining { self.iter.remaining() } else { self.iter.remaining().take(self.count_remaining as int) }
            }

            #[verifier::prophetic]
            closed spec fn will_return_none(&self) -> bool {
                self.iter.will_return_none() || self.iter.remaining().len() >= self.count_remaining
            }

            #[verifier::prophetic]
            open spec fn initial_value_relation(&self, init: &Self) -> bool {
                &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
                &&& self.iter() == init.iter()
                &&& self.iter().initial_value_relation(&init.iter())
                &&& IteratorSpec::remaining(self) == if self.iter().remaining().len() < self.count() { self.iter().remaining() } else { self.iter().remaining().take(self.count() as int) }
            }

            closed spec fn decrease(&self) -> Option<nat> {
                Some(self.count() as nat)
            }

            open spec fn peek(&self, index: int) -> Option<Self::Item> {
                self.iter().peek(index)
            }

        }

        fn take_works() {
            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = MyTake::new(v.into_iter(), 2).collect();
            assert(w@ == seq![1, 2]);

            let v: Vec<u32> = vec![1, 2, 3, 4];
            let mut w: Vec<u32> = Vec::new();
            for x in it: MyTake::new(v.into_iter(), 3)
                invariant
                    w.len() == it.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == it.seq()[i],
                    v@ == seq![1, 2, 3, 4],
            {
                assert(x < 4);
                w.push(x);
            }
            assert(w@ == seq![1, 2, 3]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] skip_can_be_implemented verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpec;

        struct MySkip<I> {
            iter: I,
            n: usize,
            init_n: usize,
        }

        impl<I: IteratorSpec> MySkip<I> {
            pub closed spec fn iter(self) -> I {
                self.iter
            }

            pub closed spec fn init_n(self) -> usize {
                self.init_n
            }

            //#[verifier::type_invariant] // fake this (via assert/assume below) due to limitations:
            //  With this as a type invariantVerus won't let us call self.iter.next() unless it's marked no_unwind
            #[verifier::prophetic]
            pub closed spec fn skip_inv(self) -> bool {
                self.iter.obeys_prophetic_iter_laws()
            }

            spec fn my_skip_new(iter: I, n: usize) -> (t: MySkip<I>) {
                MySkip { iter, n, init_n: n }
            }

            #[verifier::when_used_as_spec(my_skip_new)]
            fn new(iter: I, n: usize) -> (s: MySkip<I>)
                requires
                    iter.obeys_prophetic_iter_laws(),
                ensures
                    s.remaining() == (if iter.remaining().len() < n { seq![] } else { iter.remaining().skip(n as int) }),
                    s.will_return_none() <==> iter.will_return_none(),
                    s.obeys_prophetic_iter_laws(),
                    s.decrease() is Some == iter.decrease() is Some,
                    s == Self::my_skip_new(iter, n),
            {
                let s = MySkip { iter, n, init_n: n };
                assert(s.skip_inv());
                s
            }
        }


        impl<I: Iterator> Iterator for MySkip<I> {
            type Item = <I as Iterator>::Item;

            fn next(&mut self) -> Option<<I as Iterator>::Item> {
                assume(self.skip_inv());

                let ghost snap = self.iter;
                let ghost old_n = self.n as int;

                if self.n > 0 {
                    let mut i: usize = 0;
                    while i < self.n
                        invariant
                            0 <= i <= self.n,
                            self.n == old_n,
                            self.iter.obeys_prophetic_iter_laws(),
                            self.iter.will_return_none() == snap.will_return_none(),
                            self.iter.decrease() is Some == snap.decrease() is Some,
                            snap.decrease() is Some && snap.remaining().len() >= i
                                ==> snap.decrease()->0 >= self.iter.decrease()->0,
                            snap.remaining().len() >= i ==> self.iter.remaining() == snap.remaining().skip(i as int),
                            snap.remaining().len() < i ==> self.iter.remaining().len() == 0,
                        decreases self.n - i,
                    {
                        self.iter.next();
                        i += 1;
                    }
                    self.n = 0;
                }

                let r = self.iter.next();
                assert(self.skip_inv());
                r
            }
        }

        impl<I: Iterator> vstd::std_specs::iter::IteratorSpecImpl for MySkip<I> {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool {
                true
            }

            #[verifier::prophetic]
            closed spec fn remaining(&self) -> Seq<Self::Item> {
                if self.iter.remaining().len() < self.n { seq![] } else { self.iter.remaining().skip(self.n as int) }
            }

            #[verifier::prophetic]
            closed spec fn will_return_none(&self) -> bool {
                self.iter.will_return_none()
            }

            #[verifier::prophetic]
            open spec fn initial_value_relation(&self, init: &Self) -> bool {
                &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
                &&& self.iter() == init.iter()
                &&& self.init_n() == init.init_n()
                &&& self.iter().initial_value_relation(&init.iter())
            }

            closed spec fn decrease(&self) -> Option<nat> {
                self.iter().decrease()
            }

            open spec fn peek(&self, index: int) -> Option<Self::Item> {
                self.iter().peek(self.init_n() + index)
            }

        }

        fn skip_works() {
            let v: Vec<u32> = vec![1, 2, 3, 4];
            let w: Vec<u32> = MySkip::new(v.into_iter(), 2).collect();
            assert(w@ == seq![3, 4]);


            let v: Vec<u32> = vec![1, 2, 3, 4];
            let mut w: Vec<u32> = Vec::new();
            for x in it: MySkip::new(v.into_iter(), 2)
                invariant
                    w.len() == it.index(),
                    forall |i| 0 <= i < w.len() ==> w[i] == it.seq()[i],
                    v@ == seq![1, 2, 3, 4],
            {
                assert(x > 2);
                assert(x == v[2 + it.index()]);
                w.push(x);
            }
            assert(w@ == seq![3, 4]);

            for x in it: MySkip::new(0..4, 2)
                invariant
                    x == it.index() + 2,
            {
                assert(x == it.index() + 2);
            }
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

// TODO: Remove the eager split in favor of a ProphSeq of mutable references
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
