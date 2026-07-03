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

            // TODO: We can't call next() here, b/c Verus says we that `core::iter::adapters::skip::impl&%1::next`
            // is not supported, even though it's covered by the trait specification for Iterator
            // let out = r.next();
            // assert(out is None);
        }
    } => Ok(())
}
