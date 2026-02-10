use vstd::prelude::*;
use vstd::std_specs::iter::IteratorSpecImpl;

verus! {

#[verifier::exec_allows_no_decreases_clause]
fn test_loop() {
    let mut n: u64 = 0;
    let mut iter: std::ops::Range<u64> = (0..10).into_iter();
    loop
        invariant
            iter.start <= 10,
            iter.end == 10,
            n == iter.start * 3,
        ensures
            iter.start == 10,
    {
        if let Some(x) = iter.next() {
            assert(x < 10);
            assert(x == iter.start - 1);
            n += 3;
        } else {
            break;
        }
    }
    assert(iter.start == 10);
    assert(n == 30);
}

//fn test_loop() {
//    let mut n: u64 = 0;
//    let mut end = 10;
//    for x in iter: 0..end
//        invariant
//            n == x * 3,
//            end == 10,
//    {
//        assert(x < 10);
//        assert(x == iter.index@);
//        n += 3;
//    }
//    assert(n == 30);
//}

//fn test_loop_fail() {
//    let mut n: u64 = 0;
//    let mut end = 10;
////    let r = 0..end;
////    let i = ::core::iter::IntoIterator::into_iter(r);
////    let v = ::vstd::std_specs::iter::VerusForLoopWrapper::new(i, Ghost(Some(&i)));
////    assert(v.init@ == Some(&::core::iter::IntoIterator::into_iter(0..end)));
////
////    let mut i = 5;
////    loop 
////        invariant 
////            v.init@ == Some(&::core::iter::IntoIterator::into_iter(0..end)),
////        decreases i
////    {
////        assume(false);
////        i -= 1;
////    }
//
//    //#[verifier::loop_isolation(false)]
//    for x in iter: 0..end
//        invariant
//            n == iter.index@ * 3,
//            end == 10,
//    {
//        assert(x < 10); // FAILS
//        n += 3;
//        end = end + 0; // causes end to be non-constant, so loop needs more invariants
//    }
//}


//fn non_spec() {}
//
//fn test_loop_modes_transient_state() {
//    let mut n: u64 = 0;
//    let mut end = 10;
//    // test Typing::snapshot_transient_state
//    for x in iter: 0..({let z = end; non_spec(); z})
//        invariant
//            n == x * 3,
//            end == 10,
//    {
//        n += 3;
//        end = end + 0; // causes end to be non-constant
//    }
//}
//
//        fn test_loop(n: u32) -> (v: Vec<u32>)
//            ensures
//                v.len() == n,
//                forall|i: int| 0 <= i < n ==> v[i] == i,
//        {
//            let mut v: Vec<u32> = Vec::new();
//            for i in iter: 0..n
//                invariant
//                    v.len() == iter.index@,
//                    forall |i| 0 <= i < v.len() ==> v[i] == iter.seq()[i],
//            {
//                v.push(i);
//            }
//            v
//        }
//
//        fn test_loop_fail(n: u32) -> (v: Vec<u32>)
//            ensures
//                v.len() == n,
//                forall|i: int| 0 <= i < n ==> v[i] == i,
//        {
//            let mut v: Vec<u32> = Vec::new();
//            for i in iter: 0..n
//                invariant
//                    v.len() == iter.index@,
//                    forall |i| 0 <= i < v.len() ==> v[i] == iter.seq()[i],
//            {
//                v.push(0);
//            }
//            v
//        }

/*
fn non_spec() {}

fn test_loop_modes_transient_state() {
    let mut n: u64 = 0;
    let mut end = 10;
    // test Typing::snapshot_transient_state
    for x in iter: 0..({let z = end; non_spec(); z})
        invariant
            n == x * 3,
            end == 10,
    {
        n += 3;
        end = end + 0; // causes end to be non-constant
    }
}


fn exec_for_loop() {
    let mut n: u64 = 0;
    for x in iter: 0..10
        invariant n == iter.index@ * 3,
    {
        n += 3;
    }
    assert(n == 30);
}

fn exec_for_loop2() {
    let mut n: u64 = 0;
    for x in y: 0..10
        invariant 
            n == x * 3,
    {
        n += 3;
    }
    assert(n == 30);
}


fn a() {
    let mut i: i8 = 0;
    for x in 0..10
        invariant i == x * 3,
        decreases 10 - x
    {
        i += 3;
    }
}

fn test_basic() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = Vec::new();

    for x in y: v 
        invariant
            w.len() as int == y.index@,
            //forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i],
            forall |i| 0 <= i < w.len() ==> w[i] == v[i],
    {
        w.push(x);
    }
    assert(w.len() == v.len());
    assert(w@ == v@);
}

/*
fn all_positive(v: &Vec<u8>) -> (b: bool)
    ensures
        b <==> (forall|i: int| 0 <= i < v.len() ==> v[i] > 0),
{
    let mut b: bool = true;

    for x in iter: v
        invariant
            b <==> (forall|i: int| 0 <= i < iter.index@ ==> v[i] > 0),
    {
        b = b && *x > 0;
    }
    b
}
*/

fn test() {
    let mut v1: Vec<u32> = Vec::new();
    let mut v2: Vec<u32> = Vec::new();
    v1.push(3);
    v1.push(4);
    assert(v1@ == seq![3u32, 4u32]);

    v2.push(5);
    assert(v2.len() == 1);
    v2.push(7);
    assert(v2@.len() == 2);
    v2.insert(1, 6);
    assert(v2@ == seq![5u32, 6u32, 7u32]);

    v1.append(&mut v2);
    assert(v2@.len() == 0);
    assert(v1@.len() == 5);
    assert(v1@ == seq![3u32, 4u32, 5u32, 6u32, 7u32]);
    v1.remove(2);
    assert(v1@ == seq![3u32, 4u32, 6u32, 7u32]);

    v1.push(8u32);
    v1.push(9u32);
    assert(v1@ == seq![3u32, 4u32, 6u32, 7u32, 8u32, 9u32]);

    v1.swap_remove(5);
    assert(v1@ == seq![3u32, 4u32, 6u32, 7u32, 8u32]);

    let mut i: usize = 0;
    for x in it: v1
        invariant
            i == it.index@,
            it.seq() == seq![3u32, 4u32, 6u32, 7u32, 8u32],
    {
        assert(x > 2);
        assert(x < 10);
        i = i + 1;
    }
}

spec fn sum_u8(s: Seq<u8>) -> nat 
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (sum_u8(s.drop_last()) + s.last()) as nat
    }
}

proof fn sum_u8_monotonic(s: Seq<u8>, i: int, j: int)
    requires
        0 <= i <= j < s.len(),
    ensures 
        sum_u8(s.take(i)) <= sum_u8(s.take(j)),
    decreases j - i,
{
    if i == j {
    } else {
        sum_u8_monotonic(s, i, j - 1);
        assert(sum_u8(s.take(i)) <= sum_u8(s.take(j - 1)));
        assert(sum_u8(s.take(j - 1)) <= sum_u8(s.take(j))) by {
            assert(s.take(j).drop_last() == s.take(j - 1)); // OBSERVE
        }
    }
}

proof fn sum_u8_monotonic_forall()
    ensures 
        forall |s: Seq<u8>, i, j| #![auto]
            0 <= i <= j < s.len() ==>
            sum_u8(s.take(i)) <= sum_u8(s.take(j)),
{
    assert forall |s: Seq<u8>, i, j| #![auto] 0 <= i <= j < s.len() implies sum_u8(s.take(i)) <= sum_u8(s.take(j)) by {
        sum_u8_monotonic(s, i, j);
    }
}

// Test user-supplied break
fn for_loop_test_skip(v: Vec<u8>) {
    let mut sum: u8 = 0;

    for x in y: v 
      invariant_except_break
         sum == sum_u8(v@.take(y.index@))
      ensures
          (y.index@ == y.seq().len() && sum == sum_u8(y.seq().take(y.index@))) || 
              (sum == u8::MAX && sum_u8(v@.take(y.index@)) > u8::MAX),
    {
        assert(v@.take(y.index@ + 1).drop_last() == v@.take(y.index@ as int)); // OBSERVE
        if x <= u8::MAX - sum {
            sum += x;
        } else {
            sum = u8::MAX;
            break;
        }
    }
    
    // Prove that we accomplished our goal
    assert(v@.take(v@.len() as int) == v@); // OBSERVE
    proof {
        // PAPER CUT: Can't call a lemma on the prophetic sequence
        sum_u8_monotonic_forall();
    }
    assert(sum == sum_u8(v@) || (sum == u8::MAX && sum_u8(v@) > u8::MAX));
}
/*
struct NoTerminate {
    x: u64,
}

impl Iterator for NoTerminate {
    type Item = u64;

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        Some(self.x)
    }
}

impl IteratorSpecImpl for NoTerminate {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool { false }

    open spec fn seq(&self) -> Seq<Self::Item> {
        Seq::empty()
    }

    open spec fn completes(&self) -> bool {
        true
    }

    open spec fn decrease(&self) -> Option<nat> {
        None
    }

    open spec fn initial_value_inv(&self, init: Option<&Self>) -> bool {
        true
    }
}


#[verifier::exec_allows_no_decreases_clause]
fn test_no_termination(n: NoTerminate) {
    let mut w: Vec<u64> = Vec::new();

    for x in y: n 
        invariant
            true,
            //w.len() as int == y.index@,
    {
        //w.push(x);
    }
}
*/
*/
}

fn main() {}
