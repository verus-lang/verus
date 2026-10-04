use vstd::prelude::*;
use vstd::std_specs::iter::IteratorSpec;

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

    //#[verifier::type_invariant] // fake this (via assert/assume below) due to limitations:
    //  With this as a type invariantVerus won't let us call self.iter.next() unless it's marked no_unwind
    #[verifier::prophetic]
    pub closed spec fn skip_inv(self) -> bool {
        self.iter.obeys_prophetic_iter_laws()
    }

    fn new(iter: I, n: usize) -> (s: MySkip<I>)
        requires
            iter.obeys_prophetic_iter_laws(),
        ensures
            s.init_n() == n,
            s.iter() == iter,
            s.remaining() == (if iter.remaining().len() < n { seq![] } else { iter.remaining()[n..] }),
            s.will_return_none() <==> iter.will_return_none(),
            s.obeys_prophetic_iter_laws(),
            s.decrease() is Some == iter.decrease() is Some,
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
                    snap.remaining().len() >= i ==> self.iter.remaining() == snap.remaining()[i..],
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
        if self.iter.remaining().len() < self.n { seq![] } else { self.iter.remaining()[self.n..] }
    }

    #[verifier::prophetic]
    closed spec fn will_return_none(&self) -> bool {
        self.iter.will_return_none()
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

}
