#![feature(iter_advance_by)]
#![verifier::loop_isolation(false)]

use core::num::NonZero;
use core::ops::{ControlFlow, FromResidual, Try};
use vstd::prelude::*;
use vstd::std_specs::control_flow::{try_laws, TrySpec};
use vstd::std_specs::iter::{
    fold_post, fold_prefix, fold_requires, try_fold_post, try_fold_prefix, try_fold_requires,
    IteratorSpec,
};

verus! {

proof fn lemma_fold_prefix_empty<A, B, F: FnMut(B, A) -> B>(
    items: Seq<A>,
    produces: Seq<bool>,
    init: B,
    f: F,
)
    ensures
        fold_prefix(items, produces, init, f, seq![init]),
{
}

proof fn lemma_fold_prefix_requires<A, B, F: FnMut(B, A) -> B>(
    items: Seq<A>,
    produces: Seq<bool>,
    init: B,
    f: F,
    bs: Seq<B>,
)
    requires
        fold_requires(items, produces, init, f),
        fold_prefix(items, produces, init, f, bs),
        bs.len() - 1 < items.len(),
        produces.len() == items.len(),
        produces.all(|p: bool| p),
    ensures
        f.requires((bs.last(), items[bs.len() - 1])),
{
}

proof fn lemma_fold_prefix_extend<A, B, F: FnMut(B, A) -> B>(
    items: Seq<A>,
    produces: Seq<bool>,
    init: B,
    f: F,
    bs: Seq<B>,
    next: B,
)
    requires
        fold_prefix(items, produces, init, f, bs),
        bs.len() - 1 < items.len(),
        produces.len() == items.len(),
        produces.all(|p: bool| p),
        f.requires((bs.last(), items[bs.len() - 1])),
        f.ensures((bs.last(), items[bs.len() - 1]), next),
    ensures
        fold_prefix(items, produces, init, f, bs.push(next)),
{
    assert forall|j: int| 0 <= j < bs.len() implies f.requires(
        (bs.push(next)[j], #[trigger] items[j]),
    ) && f.ensures((bs.push(next)[j], items[j]), bs.push(next)[j + 1]) by {
        if j == bs.len() - 1 {
            assert(bs[j] == bs.last());
        }
    }
}

proof fn lemma_try_fold_prefix_empty<A, B, R: Try<Output = B>, F: FnMut(B, A) -> R>(
    items: Seq<A>,
    produces: Seq<bool>,
    init: B,
    f: F,
)
    ensures
        try_fold_prefix(items, produces, init, f, seq![init], Seq::<R>::empty()),
{
}

proof fn lemma_try_fold_prefix_requires<A, B, R: Try<Output = B>, F: FnMut(B, A) -> R>(
    items: Seq<A>,
    produces: Seq<bool>,
    init: B,
    f: F,
    bs: Seq<B>,
    results: Seq<R>,
)
    requires
        try_fold_requires(items, produces, init, f),
        try_fold_prefix(items, produces, init, f, bs, results),
        results.len() < items.len(),
        produces.len() == items.len(),
        produces.all(|p: bool| p),
    ensures
        f.requires((bs.last(), items[results.len() as int])),
{
}

proof fn lemma_try_fold_prefix_extend<A, B, R: Try<Output = B>, F: FnMut(B, A) -> R>(
    items: Seq<A>,
    produces: Seq<bool>,
    init: B,
    f: F,
    bs: Seq<B>,
    results: Seq<R>,
    value: R,
    next: B,
)
    requires
        try_fold_prefix(items, produces, init, f, bs, results),
        results.len() < items.len(),
        produces.len() == items.len(),
        produces.all(|p: bool| p),
        f.requires((bs.last(), items[results.len() as int])),
        f.ensures((bs.last(), items[results.len() as int]), value),
        value.branch_model() == ControlFlow::Continue(next),
    ensures
        try_fold_prefix(items, produces, init, f, bs.push(next), results.push(value)),
{
    assert forall|j: int| 0 <= j < results.len() + 1 implies f.requires(
        (bs.push(next)[j], #[trigger] items[j]),
    ) && f.ensures((bs.push(next)[j], items[j]), results.push(value)[j]) && results.push(
        value,
    )[j].branch_model() == ControlFlow::Continue(bs.push(next)[j + 1]) by {
        if j == results.len() {
            assert(bs[j] == bs.last());
        }
    }
}

// Confirm that all of our provided method specs can be implemented.
// This deliberately simple implementation stores its remaining items directly.
// Every method body is verified against the vstd trait contract; there are no
// assumptions, external bodies, or unchecked type invariants in this example.
pub struct VerifiedIter {
    pub items: Vec<u32>,
}

impl VerifiedIter {
    pub open spec fn production_flags(&self) -> Seq<bool> {
        Seq::new(self.items@.len(), |i: int| true)
    }

    pub fn new(items: Vec<u32>) -> (ret: Self)
        ensures
            ret.remaining() == items@,
    {
        Self { items }
    }

    fn pop_front(&mut self) -> (ret: Option<u32>)
        ensures
            if old(self).items@.len() > 0 {
                ret == Some(old(self).items@[0]) && final(self).items@ == old(
                    self,
                ).items@.drop_first()
            } else {
                ret == None && final(self).items@ == old(self).items@
            },
    {
        if self.items.len() == 0 {
            None
        } else {
            Some(self.items.remove(0))
        }
    }

    fn pop_back(&mut self) -> (ret: Option<u32>)
        ensures
            if old(self).items@.len() > 0 {
                ret == Some(old(self).items@.last()) && final(self).items@ == old(
                    self,
                ).items@.drop_last() && ret == Some(old(self).items@.reverse()[0])
                    && final(self).items@.reverse() == old(self).items@.reverse().drop_first()
            } else {
                ret == None && final(self).items@ == old(self).items@
            },
    {
        let ret = self.items.pop();
        proof {
            if old(self).items@.len() > 0 {
                assert(self.items@.reverse() =~= old(self).items@.reverse().drop_first());
            }
        }
        ret
    }

    fn advance_front(&mut self, n: usize) -> (ret: Result<(), NonZero<usize>>)
        ensures
            ret matches Err(e) ==> 1 <= e@ <= n,
            ret is Ok ==> ret == Ok(()),
            match ret {
                Ok(()) => n <= old(self).items@.len() && final(self).items@ == old(
                    self,
                ).items@[n..],
                Err(e) => old(self).items@.len() < n && e@ == n - old(self).items@.len()
                    && final(self).items@.len() == 0,
            },
    {
        let ghost input = self.items@;
        let mut i = 0usize;
        while i < n
            invariant
                i <= n,
                i <= input.len(),
                self.items@ == input[i as int..],
            decreases n - i,
        {
            match self.pop_front() {
                None => {
                    return Err(NonZero::new(n - i).unwrap());
                },
                Some(_) => {
                    i += 1;
                },
            }
        }
        Ok(())
    }

    fn advance_back(&mut self, n: usize) -> (ret: Result<(), NonZero<usize>>)
        ensures
            ret matches Err(e) ==> 1 <= e@ <= n,
            ret is Ok ==> ret == Ok(()),
            match ret {
                Ok(()) => n <= old(self).items@.len() && final(self).items@ == old(
                    self,
                ).items@[..old(self).items@.len() - n],
                Err(e) => old(self).items@.len() < n && e@ == n - old(self).items@.len()
                    && final(self).items@.len() == 0,
            },
    {
        let ghost input = self.items@;
        let mut i = 0usize;
        while i < n
            invariant
                i <= n,
                i <= input.len(),
                self.items@ == input[..input.len() - i],
            decreases n - i,
        {
            match self.pop_back() {
                None => {
                    return Err(NonZero::new(n - i).unwrap());
                },
                Some(_) => {
                    i += 1;
                },
            }
        }
        Ok(())
    }

    fn for_each_impl<F>(&mut self, f: F) where F: FnMut(u32)
        requires
            forall|j: int| 0 <= j < self.items@.len() ==> f.requires((#[trigger] self.items@[j],)),
        ensures
            forall|j: int|
                #![auto]
                0 <= j < old(self).items@.len() ==> call_ensures(f, (old(self).items@[j],), ()),
    {
        let mut cb = f;
        let ghost input = self.items@;
        while self.items.len() > 0
            invariant
                cb == f,
                self.items@.is_suffix_of(input),
                forall|j: int|
                    #![auto]
                    0 <= j < input.len() - self.items@.len() ==> call_ensures(f, (input[j],), ()),
                forall|j: int| #![auto] 0 <= j < input.len() ==> call_requires(f, (input[j],)),
            decreases self.items.len(),
        {
            let ghost k = input.len() - self.items@.len();
            let x = self.pop_front().unwrap();
            let unit = cb(x);
            match unit {
                () => {},
            }
            proof {
                assert forall|j: int|
                    #![auto]
                    0 <= j < input.len() - self.items@.len() implies call_ensures(
                    f,
                    (input[j],),
                    (),
                ) by {
                    if j == k {
                        assert(x == input[j]);
                    }
                }
            }
        }
    }

    fn fold_impl<B, F>(&mut self, init: B, f: F) -> (ret: B) where F: FnMut(B, u32) -> B
        requires
            fold_requires(self.items@, self.production_flags(), init, f),
        ensures
            fold_post(old(self).items@, old(self).production_flags(), init, f, ret),
    {
        let mut cb = f;
        let ghost input = self.items@;
        let ghost produces = self.production_flags();
        let ghost mut a = seq![init];
        let mut acc = init;
        proof {
            lemma_fold_prefix_empty(input, produces, init, f);
        }
        while self.items.len() > 0
            invariant
                cb == f,
                produces.len() == input.len(),
                produces.all(|p: bool| p),
                fold_requires(input, produces, init, f),
                fold_prefix(input, produces, init, f, a),
                acc == a.last(),
                a.len() - 1 == input.len() - self.items@.len(),
                self.items@ == input[a.len() - 1..],
            decreases self.items.len(),
        {
            let x = self.pop_front().unwrap();
            proof {
                lemma_fold_prefix_requires(input, produces, init, f, a);
            }
            let next = cb(acc, x);
            proof {
                lemma_fold_prefix_extend(input, produces, init, f, a, next);
                a = a.push(next);
            }
            acc = next;
        }
        proof {
            assert(fold_prefix(input, produces, init, f, a));
            assert(fold_post(input, produces, init, f, acc));
        }
        acc
    }

    fn try_fold_impl<B, F, R>(&mut self, init: B, f: F) -> (ret: R) where
        F: FnMut(B, u32) -> R,
        R: Try<Output = B>,

        requires
            try_laws::<R>() ==> try_fold_requires(self.items@, self.production_flags(), init, f),
            !try_laws::<R>() ==> forall|b: B, x: u32| #![auto] call_requires(f, (b, x)),
        ensures
            final(self).items@.is_suffix_of(old(self).items@),
            try_fold_post(
                old(self).items@,
                old(self).production_flags(),
                init,
                f,
                ret,
                old(self).items@.len() - final(self).items@.len(),
                (*final(self)).production_flags(),
            ),
            try_laws::<R>() && ret.branch_model() is Continue ==> final(self).items@.len() == 0,
            try_laws::<R>() && ret.branch_model() is Break ==> final(self).items@.len() < old(
                self,
            ).items@.len(),
    {
        let mut cb = f;
        let ghost input = self.items@;
        let ghost produces = self.production_flags();
        let ghost mut a = seq![init];
        let ghost mut results = Seq::<R>::empty();
        let mut acc = init;
        proof {
            lemma_try_fold_prefix_empty(input, produces, init, f);
        }
        while self.items.len() > 0
            invariant
                cb == f,
                produces.len() == input.len(),
                produces.all(|p: bool| p),
                try_laws::<R>() ==> try_fold_requires(input, produces, init, f),
                !try_laws::<R>() ==> forall|b: B, x: u32| #![auto] call_requires(f, (b, x)),
                try_laws::<R>() ==> try_fold_prefix(input, produces, init, f, a, results),
                acc == a.last(),
                results.len() == input.len() - self.items@.len(),
                a.len() == results.len() + 1,
                self.items@ == input[results.len() as int..],
            decreases self.items.len(),
        {
            let x = self.pop_front().unwrap();
            proof {
                if try_laws::<R>() {
                    lemma_try_fold_prefix_requires(input, produces, init, f, a, results);
                }
            }
            let value = cb(acc, x);
            match value.branch() {
                ControlFlow::Continue(next) => {
                    proof {
                        if try_laws::<R>() {
                            lemma_try_fold_prefix_extend(
                                input,
                                produces,
                                init,
                                f,
                                a,
                                results,
                                value,
                                next,
                            );
                        }
                        a = a.push(next);
                        results = results.push(value);
                    }
                    acc = next;
                },
                ControlFlow::Break(residual) => {
                    let ret = R::from_residual(residual);
                    proof {
                        assert(self.production_flags() =~= produces.skip(results.len() as int + 1));
                        if try_laws::<R>() {
                            assert(value.branch_model() == ControlFlow::Break(residual));
                            assert(ret.branch_model() == ControlFlow::Break(residual));
                            assert(try_fold_prefix(input, produces, init, f, a, results));
                            assert(try_fold_post(
                                input,
                                produces,
                                init,
                                f,
                                ret,
                                results.len() as int + 1,
                                self.production_flags(),
                            ));
                        }
                    }
                    return ret;
                },
            }
        }
        let ret = R::from_output(acc);
        proof {
            assert(self.production_flags() =~= produces.skip(input.len() as int));
            if try_laws::<R>() {
                assert(try_fold_prefix(input, produces, init, f, a, results));
                assert(try_fold_post(
                    input,
                    produces,
                    init,
                    f,
                    ret,
                    input.len() as int,
                    self.production_flags(),
                ));
            }
        }
        ret
    }

    fn rfind_impl<P>(&mut self, predicate: P) -> (ret: Option<u32>) where P: FnMut(&u32) -> bool
        requires
            forall|j: int|
                #![auto]
                0 <= j < self.items@.len() ==> call_requires(predicate, (&self.items@[j],)),
        ensures
            ret matches Some(x) ==> call_ensures(predicate, (&x,), true),
            final(self).items@.is_prefix_of(old(self).items@),
            if ret is None {
                final(self).items@.len() == 0 && forall|j: int|
                    #![auto]
                    0 <= j < old(self).items@.len() ==> call_ensures(
                        predicate,
                        (&old(self).items@[j],),
                        false,
                    )
            } else {
                let k = final(self).items@.len() as int;
                k < old(self).items@.len() && ret == Some(old(self).items@[k]) && forall|j: int|
                    #![auto]
                    k < j < old(self).items@.len() ==> call_ensures(
                        predicate,
                        (&old(self).items@[j],),
                        false,
                    )
            },
    {
        let mut cb = predicate;
        let ghost input = self.items@;
        while self.items.len() > 0
            invariant
                cb == predicate,
                self.items@.is_prefix_of(input),
                forall|j: int|
                    #![auto]
                    0 <= j < input.len() ==> call_requires(predicate, (&input[j],)),
                forall|j: int|
                    #![auto]
                    self.items@.len() <= j < input.len() ==> call_ensures(
                        predicate,
                        (&input[j],),
                        false,
                    ),
            decreases self.items.len(),
        {
            let x = self.pop_back().unwrap();
            if cb(&x) {
                return Some(x);
            }
            proof {
                assert forall|j: int|
                    #![auto]
                    self.items@.len() <= j < input.len() implies call_ensures(
                    predicate,
                    (&input[j],),
                    false,
                ) by {
                    if j == self.items@.len() {
                        assert(input[j] == x);
                    }
                }
            }
        }
        None
    }

    fn rfold_impl<B, F>(&mut self, init: B, f: F) -> (ret: B) where F: FnMut(B, u32) -> B
        requires
            fold_requires(self.items@.reverse(), self.production_flags().reverse(), init, f),
        ensures
            fold_post(
                old(self).items@.reverse(),
                old(self).production_flags().reverse(),
                init,
                f,
                ret,
            ),
    {
        let mut cb = f;
        let ghost input = self.items@.reverse();
        let ghost produces = self.production_flags().reverse();
        let ghost mut a = seq![init];
        let mut acc = init;
        proof {
            lemma_fold_prefix_empty(input, produces, init, f);
        }
        while self.items.len() > 0
            invariant
                cb == f,
                produces.len() == input.len(),
                produces.all(|p: bool| p),
                fold_requires(input, produces, init, f),
                fold_prefix(input, produces, init, f, a),
                acc == a.last(),
                a.len() - 1 == input.len() - self.items@.len(),
                self.items@.reverse() == input[a.len() - 1..],
            decreases self.items.len(),
        {
            let x = self.pop_back().unwrap();
            proof {
                lemma_fold_prefix_requires(input, produces, init, f, a);
            }
            let next = cb(acc, x);
            proof {
                lemma_fold_prefix_extend(input, produces, init, f, a, next);
                a = a.push(next);
            }
            acc = next;
        }
        proof {
            assert(fold_prefix(input, produces, init, f, a));
            assert(fold_post(input, produces, init, f, acc));
        }
        acc
    }

    fn try_rfold_impl<B, F, R>(&mut self, init: B, f: F) -> (ret: R) where
        F: FnMut(B, u32) -> R,
        R: Try<Output = B>,

        requires
            try_laws::<R>() ==> try_fold_requires(
                self.items@.reverse(),
                self.production_flags().reverse(),
                init,
                f,
            ),
            !try_laws::<R>() ==> forall|b: B, x: u32| #![auto] call_requires(f, (b, x)),
        ensures
            final(self).items@.is_prefix_of(old(self).items@),
            try_fold_post(
                old(self).items@.reverse(),
                old(self).production_flags().reverse(),
                init,
                f,
                ret,
                old(self).items@.len() - final(self).items@.len(),
                (*final(self)).production_flags().reverse(),
            ),
            try_laws::<R>() && ret.branch_model() is Continue ==> final(self).items@.len() == 0,
            try_laws::<R>() && ret.branch_model() is Break ==> final(self).items@.len() < old(
                self,
            ).items@.len(),
    {
        let mut cb = f;
        let ghost input = self.items@.reverse();
        let ghost produces = self.production_flags().reverse();
        let ghost original = self.items@;
        let ghost mut a = seq![init];
        let ghost mut results = Seq::<R>::empty();
        let mut acc = init;
        proof {
            lemma_try_fold_prefix_empty(input, produces, init, f);
        }
        while self.items.len() > 0
            invariant
                cb == f,
                produces.len() == input.len(),
                produces.all(|p: bool| p),
                try_laws::<R>() ==> try_fold_requires(input, produces, init, f),
                !try_laws::<R>() ==> forall|b: B, x: u32| #![auto] call_requires(f, (b, x)),
                try_laws::<R>() ==> try_fold_prefix(input, produces, init, f, a, results),
                acc == a.last(),
                results.len() == input.len() - self.items@.len(),
                a.len() == results.len() + 1,
                self.items@.reverse() == input[results.len() as int..],
                self.items@ == original[..original.len() - results.len()],
            decreases self.items.len(),
        {
            let x = self.pop_back().unwrap();
            proof {
                if try_laws::<R>() {
                    lemma_try_fold_prefix_requires(input, produces, init, f, a, results);
                }
            }
            let value = cb(acc, x);
            match value.branch() {
                ControlFlow::Continue(next) => {
                    proof {
                        if try_laws::<R>() {
                            lemma_try_fold_prefix_extend(
                                input,
                                produces,
                                init,
                                f,
                                a,
                                results,
                                value,
                                next,
                            );
                        }
                        a = a.push(next);
                        results = results.push(value);
                    }
                    acc = next;
                },
                ControlFlow::Break(residual) => {
                    let ret = R::from_residual(residual);
                    proof {
                        assert(self.production_flags().reverse() =~= produces.skip(
                            results.len() as int + 1,
                        ));
                        if try_laws::<R>() {
                            assert(value.branch_model() == ControlFlow::Break(residual));
                            assert(ret.branch_model() == ControlFlow::Break(residual));
                            assert(try_fold_prefix(input, produces, init, f, a, results));
                            assert(try_fold_post(
                                input,
                                produces,
                                init,
                                f,
                                ret,
                                results.len() as int + 1,
                                self.production_flags().reverse(),
                            ));
                        }
                    }
                    return ret;
                },
            }
        }
        let ret = R::from_output(acc);
        proof {
            assert(self.production_flags().reverse() =~= produces.skip(input.len() as int));
            if try_laws::<R>() {
                assert(try_fold_prefix(input, produces, init, f, a, results));
                assert(try_fold_post(
                    input,
                    produces,
                    init,
                    f,
                    ret,
                    input.len() as int,
                    self.production_flags().reverse(),
                ));
            }
        }
        ret
    }
}

impl vstd::std_specs::iter::IteratorSpecImpl for VerifiedIter {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    open spec fn remaining(&self) -> Seq<u32> {
        self.items@
    }

    open spec fn produces(&self) -> Seq<bool> {
        self.production_flags()
    }

    open spec fn decrease(&self) -> Option<nat> {
        Some(self.items@.len())
    }

    open spec fn peek(&self, index: int) -> Option<u32> {
        if 0 <= index < self.items@.len() {
            Some(self.items@[index])
        } else {
            None
        }
    }
}

impl vstd::std_specs::iter::DoubleEndedIteratorSpecImpl for VerifiedIter {
    open spec fn peek_back(&self, index: int) -> Option<u32> {
        if 0 <= index < self.items@.len() {
            Some(self.items@[self.items@.len() - index - 1])
        } else {
            None
        }
    }
}

impl Iterator for VerifiedIter {
    type Item = u32;

    fn next(&mut self) -> Option<u32> {
        self.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.items.len();
        (len, Some(len))
    }

    fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        self.advance_front(n)
    }

    fn nth(&mut self, n: usize) -> Option<u32> {
        match self.advance_front(n) {
            Ok(()) => self.pop_front(),
            Err(_) => None,
        }
    }

    fn for_each<F>(mut self, f: F) where F: FnMut(u32) {
        self.for_each_impl(f)
    }

    fn fold<B, F>(mut self, init: B, f: F) -> B where F: FnMut(B, u32) -> B {
        self.fold_impl(init, f)
    }

    fn try_fold<B, F, R>(&mut self, init: B, f: F) -> R where
        F: FnMut(B, u32) -> R,
        R: Try<Output = B>,
     {
        self.try_fold_impl(init, f)
    }
}

impl DoubleEndedIterator for VerifiedIter {
    fn next_back(&mut self) -> Option<u32> {
        self.pop_back()
    }

    fn advance_back_by(&mut self, n: usize) -> Result<(), NonZero<usize>> {
        self.advance_back(n)
    }

    fn nth_back(&mut self, n: usize) -> Option<u32> {
        match self.advance_back(n) {
            Ok(()) => self.pop_back(),
            Err(_) => None,
        }
    }

    fn rfind<P>(&mut self, predicate: P) -> Option<u32> where P: FnMut(&u32) -> bool {
        self.rfind_impl(predicate)
    }

    fn rfold<B, F>(mut self, init: B, f: F) -> B where F: FnMut(B, u32) -> B {
        self.rfold_impl(init, f)
    }

    fn try_rfold<B, F, R>(&mut self, init: B, f: F) -> R where
        F: FnMut(B, u32) -> R,
        R: Try<Output = B>,
     {
        self.try_rfold_impl(init, f)
    }
}

} // verus!
fn main() {}
