use std::collections::VecDeque;
use vstd::pervasive::runtime_assert;
#[allow(unused_imports)]
use vstd::std_specs::vecdeque::*;
use vstd::prelude::*;

verus! {

fn vec_deque_test()
{
    broadcast use group_vec_dequeue_axioms;
    
    let mut v1: VecDeque<u32> = VecDeque::<u32>::new();
    let mut v2: VecDeque<u32> = VecDeque::<u32>::new();
    v1.push_back(3);
    v1.push_back(4);
    let front = v1.pop_front();
    runtime_assert(front.is_some());
    runtime_assert(front.unwrap() == 3);
    assert(v1@ == seq![4u32]);

    v2.push_back(5);
    assert(v2.len() == 1);
    v2.push_back(7);
    assert(v2@.len() == 2);
    v2.insert(1, 6);
    assert(v2@ == seq![5u32, 6u32, 7u32]);

    v1.append(&mut v2);
    assert(v2@.len() == 0);
    assert(v1@.len() == 4);
    assert(v1@ == seq![4u32, 5u32, 6u32, 7u32]);
    v1.remove(2);
    assert(v1@ == seq![4u32, 5u32, 7u32]);
    
    let mut x = v1.pop_front();
    runtime_assert(x.is_some());
    runtime_assert(x.unwrap() == 4);
    x = v1.pop_front();
    runtime_assert(x.is_some());
    runtime_assert(x.unwrap() == 5);
    x = v1.pop_front();
    runtime_assert(x.is_some());
    runtime_assert(x.unwrap() == 7);
    x = v1.pop_front();
    runtime_assert(x.is_none());

    v1.push_back(10);
    v1.push_back(11);
    assert(v1@ == seq![10u32, 11u32]);
    for x in it: v1.iter()
        invariant
            it.elements == seq![10u32, 11u32],
    {
    }

    /*
    let mut i: usize = 0;
    for x in v1.iter()
        invariant
            i == it.pos,
            it.elements == seq![10u32, 11u32],
            v1@ == seq![10u32, 11u32],
            i + it@.len() == v1@.len(),
    {
        assert(x > 9);
        assert(x < 12);
        i = i + 1;
    }
    */
}

} // verus!
