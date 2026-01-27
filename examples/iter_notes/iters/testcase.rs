use vstd::prelude::*;
use vstd::std_specs::iter::IteratorSpecImpl;

verus! {

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


/*
 * Verus complains: loop invariants with 'loop_isolation(false)' cannot be invariant_except_break or ensures
 *
fn test_no_loop_isolation() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = Vec::new();

    #[verifier::loop_isolation(false)]
    for x in y: v 
        invariant
            w.len() as int == y.index@,
            forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i],
    {
        w.push(x);
    }
    assert(w.len() == v.len());
    assert(w@ == v@);

}


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


fn test_no_termination(n: NoTerminate) {
    let mut w: Vec<u64> = Vec::new();

    //#[verifier::exec_allows_no_decreases_clause]
    for x in y: n 
        invariant
            w.len() as int == y.index@,
    {
        w.push(x);
    }
}
*/
}

fn main() {}
