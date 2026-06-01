#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

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
