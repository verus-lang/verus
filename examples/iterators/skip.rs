use vstd::prelude::*;
use vstd::std_specs::iter::{IteratorSpec, DoubleEndedIteratorSpec, ExactSizeIteratorSpec};

verus! {

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

    fn new(iter: I, n: usize) -> (s: MySkip<I>)
        ensures
            s.init_n() == n,
            s.iter() == iter,
            iter.obeys_prophetic_iter_laws() ==> s.remaining()
                == (if iter.remaining().len() < n { seq![] } else { iter.remaining()[n..] }),
            iter.obeys_prophetic_iter_laws() ==> s.produces()
                == (if iter.remaining().len() < n { seq![] } else { iter.produces()[n..] }),
            s.obeys_prophetic_iter_laws() == iter.obeys_prophetic_iter_laws(),
            s.decrease() is Some == iter.decrease() is Some,
    {
        let s = MySkip { iter, n, init_n: n };
        s
    }
}


impl<I: Iterator> Iterator for MySkip<I> {
    type Item = <I as Iterator>::Item;

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (lower, upper) = self.iter.size_hint();
        let upper = match upper {
            Some(n) => Some(n.saturating_sub(self.n)),
            None => None,
        };
        (lower.saturating_sub(self.n), upper)
    }

    fn next(&mut self) -> Option<<I as Iterator>::Item> {
        let ghost snap = self.iter;
        let ghost old_n = self.n as int;

        if self.n > 0 {
            let mut i: usize = 0;
            while i < self.n
                invariant
                    0 <= i <= self.n,
                    self.n == old_n,
                    self.iter.obeys_prophetic_iter_laws() == snap.obeys_prophetic_iter_laws(),
                    snap.obeys_prophetic_iter_laws() && snap.remaining().len() >= i ==>
                        self.iter.produces() == snap.produces()[i..],
                    snap.obeys_prophetic_iter_laws() && snap.remaining().len() < i ==>
                        self.iter.produces().len() == 0,
                    snap.obeys_prophetic_iter_laws() && i > 0 ==> snap.produces().len() == snap.remaining().len(),
                    snap.obeys_prophetic_iter_laws() ==> self.iter.decrease() is Some == snap.decrease() is Some,
                    snap.obeys_prophetic_iter_laws() && snap.decrease() is Some && snap.remaining().len() >= i
                        ==> snap.decrease()->0 >= self.iter.decrease()->0,
                    snap.obeys_prophetic_iter_laws() && snap.remaining().len() >= i ==> self.iter.remaining() == snap.remaining()[i..],
                    snap.obeys_prophetic_iter_laws() && snap.remaining().len() < i ==> self.iter.remaining().len() == 0,
                decreases self.n - i,
            {
                self.iter.next();
                i += 1;
            }
            self.n = 0;
        }

        let r = self.iter.next();
        r
    }
}

impl<I: Iterator> vstd::std_specs::iter::IteratorSpecImpl for MySkip<I> {
    closed spec fn obeys_prophetic_iter_laws(&self) -> bool {
        self.iter.obeys_prophetic_iter_laws()
    }

    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Self::Item> {
        if self.iter.remaining().len() < self.n { seq![] } else { self.iter.remaining()[self.n..] }
    }

    #[verifier::prophetic]
    closed spec fn produces(&self) -> Seq<bool> {
        if self.iter.remaining().len() < self.n { seq![] } else { self.iter.produces()[self.n..] }
    }

    closed spec fn decrease(&self) -> Option<nat> {
        self.iter().decrease()
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        self.iter().peek(self.init_n() + index)
    }
}

impl<I: DoubleEndedIterator + ExactSizeIterator> DoubleEndedIterator for MySkip<I> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.iter.len() > self.n {
            self.iter.next_back()
        } else {
            None
        }
    }
}

impl<I: DoubleEndedIterator + ExactSizeIterator>
    vstd::std_specs::iter::DoubleEndedIteratorSpecImpl for MySkip<I>
{
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        self.iter().peek_back(index)
    }
}

impl<I: ExactSizeIterator> ExactSizeIterator for MySkip<I> {
    fn len(&self) -> usize {
        self.iter.len().saturating_sub(self.n)
    }
}

impl<I: ExactSizeIterator> vstd::std_specs::iter::ExactSizeIteratorSpecImpl for MySkip<I> {
    closed spec fn exact_len(&self) -> usize {
        if self.iter.exact_len() > self.n {
            (self.iter.exact_len() - self.n) as usize
        } else {
            0
        }
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

fn skip_from_both_ends() {
    let input = vec![1u32, 2, 3, 4, 5];
    let mut iter = MySkip::new(input.into_iter(), 2);
    let len = iter.len();
    assert(len == 3);
    let back = iter.next_back();
    assert(back == Some(5));
    let len = iter.len();
    assert(len == 2);
    let front = iter.next();
    assert(front == Some(3));
    let len = iter.len();
    assert(len == 1);
    let back = iter.next_back();
    assert(back == Some(4));
    let len = iter.len();
    assert(len == 0);
    let back = iter.next_back();
    assert(back == None);
    let front = iter.next();
    assert(front == None);

    let mut all_skipped = MySkip::new(vec![1u32, 2].into_iter(), 2);
    let len = all_skipped.len();
    assert(len == 0);
    let back = all_skipped.next_back();
    assert(back == None);
    let front = all_skipped.next();
    assert(front == None);

    let mut short = MySkip::new(vec![1u32, 2].into_iter(), 5);
    let len = short.len();
    assert(len == 0);
    let back = short.next_back();
    assert(back == None);
    let front = short.next();
    assert(front == None);
}

}
