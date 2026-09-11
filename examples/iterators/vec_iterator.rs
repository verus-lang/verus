use vstd::prelude::*;
use vstd::std_specs::iter::{
    DoubleEndedIteratorSpecImpl, ExactSizeIteratorSpecImpl, IteratorSpec, IteratorSpecImpl,
};

verus! {

pub struct MyVecIterator<'a, T> {
    values: &'a Vec<T>,
    front: usize,
    back: usize,
}

impl<'a, T> MyVecIterator<'a, T> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        self.front <= self.back <= self.values.len()
    }
}

impl<'a, T> MyVecIterator<'a, T> {
    pub closed spec fn exact_len_spec(&self) -> usize {
        (self.back - self.front) as usize
    }

    pub closed spec fn peek_front(&self, index: int) -> Option<&'a T> {
        if 0 <= index < self.back - self.front {
            Some(&self.values@[self.front + index])
        } else {
            None
        }
    }

    pub closed spec fn peek_back(&self, index: int) -> Option<&'a T> {
        if 0 <= index < self.back - self.front {
            Some(&self.values@[self.back - index - 1])
        } else {
            None
        }
    }

    fn new(values: &'a Vec<T>) -> (iter: Self)
        ensures
            IteratorSpec::remaining(&iter) == values@.as_ref(),
            iter.exact_len_spec() == values.len(),
    {
        let back = values.len();
        MyVecIterator { values, front: 0, back }
    }
}

impl<'a, T> Iterator for MyVecIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        proof { use_type_invariant(&*self); }
        if self.front < self.back {
            let front = self.front;
            self.front = self.front + 1;
            Some(&self.values[front])
        } else {
            None
        }
    }
}

impl<'a, T> IteratorSpecImpl for MyVecIterator<'a, T> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    closed spec fn remaining(&self) -> Seq<Self::Item> {
        self.values@.subrange(self.front as int, self.back as int).as_ref()
    }

    closed spec fn will_return_none(&self) -> bool {
        true
    }

    closed spec fn decrease(&self) -> Option<nat> {
        Some((self.back - self.front) as nat)
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        self.peek_front(index)
    }
}

impl<'a, T> ExactSizeIteratorSpecImpl for MyVecIterator<'a, T> {
    open spec fn exact_len(&self) -> usize {
        self.exact_len_spec()
    }
}

impl<'a, T> ExactSizeIterator for MyVecIterator<'a, T> {
    fn len(&self) -> usize {
        proof { use_type_invariant(self); }
        self.back - self.front
    }
}

impl<'a, T> DoubleEndedIterator for MyVecIterator<'a, T> {
    fn next_back(&mut self) -> (ret: Option<Self::Item>) {
        proof { use_type_invariant(&*self); }
        if self.front < self.back {
            self.back = self.back - 1;
            Some(&self.values[self.back])
        } else {
            None
        }
    }
}

impl<'a, T> DoubleEndedIteratorSpecImpl for MyVecIterator<'a, T> {
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        self.peek_back(index)
    }
}

fn test_my_vec_iterator() {
    let values = vec![10u64, 20u64, 30u64, 40u64];
    let mut iter = MyVecIterator::new(&values);

    let len = iter.len();
    assert(len == 4);
    let next = iter.next();
    assert(next == Some(&10));
    let len = iter.len();
    assert(len == 3);
    let next = iter.next_back();
    assert(next == Some(&40));
    let len = iter.len();
    assert(len == 2);
    let next = iter.next_back();
    assert(next == Some(&30));
    let next = iter.next();
    assert(next == Some(&20));
    let len = iter.len();
    assert(len == 0);
    let next = iter.next();
    assert(next is None);
    let next = iter.next_back();
    assert(next is None);
}

} // verus!

fn main() {}