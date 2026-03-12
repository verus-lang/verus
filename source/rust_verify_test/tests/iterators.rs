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
                    self.pred() == old(self).pred(),
                    forall |j| self.proph_elem(j) == old(self).proph_elem(j),
                    forall |j| i != j ==> self.has_resolved(j) == old(self).has_resolved(j),
                    self.has_resolved(i),
                    self.proph_elem(i) == Some(t);
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
                    IteratorSpec::completes(&s) ==> iter.completes() && IteratorSpec::remaining(&s).len() == iter.remaining().len(),
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
            closed spec fn completes(&self) -> bool {
                self.iter.completes()
                  && (forall |i: int| self.idx@ <= i < self.idx@ + self.iter.remaining().len() ==> self.prophs@.proph_elem(i).is_some())
            }

            #[verifier::prophetic]
            open spec fn initial_value_inv(&self, init: &Self) -> bool {
                &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
                &&& self.inner().initial_value_inv(&init.inner())
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

