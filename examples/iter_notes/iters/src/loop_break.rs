use std::{io::Take, iter::{self, Skip}, path::Iter};
use vstd::prelude::*;
use crate::prophetic_iters::decreases_fix::*;
use crate::prophetic_iters::iterator_traits::*;

verus!{

broadcast use group_decrease_axioms;

#[verifier::exec_allows_no_decreases_clause]
fn for_loop_test_vec() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = vec![];

    let i = vec_iter(&v);

    let mut count: u128 = 0;
    // Verus will desugar this: 
    // for x in y: v 
    //     invariant
    //         w.len() == y.index,
    //         forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i],
    //         count == w.len() <= u64::MAX,
    // {
    //     w.push(x);
    //     count += 1;
    // }
    //
    // Into:
    let iter = VerusForLoopIterator::new(vec_iter(&v));
    let Ghost(VERUS_old_snap) = iter.snapshot;
    #[allow(non_snake_case)]
    let VERUS_loop_result = match iter {
        mut y => {
            loop
                invariant_except_break
                    y.iter.decrease() is Some,
                invariant
                    // Internal invariants that assist the user
                    0 <= y.index@ <= y.snapshot@.seq().len(),

                    // Internal invariants that help maintain the other internal invariants
                    y.snapshot == VERUS_old_snap,
                    
                    // Previously: y.iter.seq() =~= y.seq().skip(y.index@),
                    y.iter.seq().len() == y.seq().len() - y.index@,
                    forall |i| 0 <= i < y.iter.seq().len() ==> #[trigger] y.iter.seq()[i] == y.seq()[y.index@ + i],

                    (y.iter.completes() ==> y.snapshot@.completes()),

                    ({ 
                      // Grab the next val for (possible) use in inv
                      let x = if y.index@ < y.snapshot@.seq().len() { y.snapshot@.seq()[y.index@] } else { arbitrary() };

                      w.len() == y.index &&
                      (forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i]) &&
                      count == w.len() <= u64::MAX
                    }),
                ensures
                    // REVIEW: This works, but only if we don't allow `break`s inside a for loop.
                    //         It appears that may be the case, although the error messages are confusing.
                    y.snapshot@.completes(),        // AUTO
                    y.index == y.snapshot@.seq().len(), // AUTO
                decreases
                    y.iter.decrease(),
            {
                #[allow(non_snake_case)]
                let mut VERUS_loop_next;
                match y.iter.next() {
                    Some(VERUS_loop_val) => VERUS_loop_next = VERUS_loop_val,
                    None => {
                        break
                    }
                }
                proof {
                    y.index@ = y.index@ + 1;
                }
                let x = VERUS_loop_next;
                let () = {
                    // body
                    w.push(*x);
                    count += 1;
                };
            }
        }
    };

    // Make sure our invariant was useful
    assert(w@.len() == v@.len());
    assert(w@ == v@);
    assert(count == v.len());
}


} // verus!
