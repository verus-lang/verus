use vstd::prelude::*;
use vstd::std_specs::iter::IteratorSpecImpl;

verus! {
/*
fn test_basic() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = Vec::new();

    for x in y: v 
        invariant
            w.len() as int == y.index@,
            forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i],
            //forall |i| 0 <= i < w.len() ==> w[i] == v[i],
    {
        w.push(x);
    }
    assert(w.len() == v.len());
    assert(w@ == v@);
}
*/

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
        assert(sum == sum_u8(v@.take(y.index@)));
        assert(0 <= y.index@ < v.len());
        assert(v@.take(y.index@ + 1).drop_last() == v@.take(y.index@ as int)); // OBSERVE
        if x <= u8::MAX - sum {
            sum += x;
        } else {
            sum = u8::MAX;
            break;
        }
    }
    
//    assert(y.seq() == v@.map_values(|e:u8| &e)); // OBSERVE
//    assert(y.seq() == y.seq().take(y.seq().len() as int)); // OBSERVE
//    proof {
//        // PAPER CUT: Can't call a lemma on the prophetic sequence
//        sum_u8_monotonic_forall();
//    }
//    assert(sum == sum_u8(v@.map_values(|e:u8| &e)) || 
//            (sum == u8::MAX && sum_u8(v@.map_values(|e:u8| &e)) > u8::MAX));
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

}

fn main() {}
