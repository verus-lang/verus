use std::{io::Take, iter::{self, Skip}, path::Iter};
use vstd::prelude::*;
use crate::prophetic_iters::decreases_fix::*;
use crate::prophetic_iters::iterator_traits::*;

verus!{

broadcast use group_decrease_axioms;

/// Example of what our desugaring will look like when the user
/// has added #[verifier::exec_allows_no_decreases_clause]

#[verifier::exec_allows_no_decreases_clause]
fn for_loop_test_vec() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = vec![];

    let i = vec_iter(&v);

    let mut count: u128 = 0;
    // Verus will desugar this: 
    // #[verifier::exec_allows_no_decreases_clause]
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
    let init = Ghost(Some(&vec_iter_spec(&v)));
    let iter = VerusForLoopIterator::new(vec_iter(&v), init);
    let Ghost(VERUS_old_snap) = iter.snapshot;
    #[allow(non_snake_case)]
    let VERUS_loop_result = match iter {
        mut y => {
            loop
                // Removed when the user adds #[verifier::exec_allows_no_decreases_clause]
                // invariant_except_break
                //     y.iter.decrease() is Some,
                invariant
                    y.snapshot == VERUS_old_snap,
                    y.init == Ghost(Some(&vec_iter_spec(&v))),
                    y.wf(),
                    ({ 
                      // Grab the next val for (possible) use in inv
                      let x = if y.index@ < y.seq().len() { y.seq()[y.index@] } else { arbitrary() };

                      w.len() == y.index &&
                      (forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i]) &&
                      count == w.len() <= u64::MAX
                    }),
                ensures
                    // REVIEW: This works, but only if we don't allow `break`s inside a for loop.
                    //         It appears that may be the case, although the error messages are confusing.
                    y.snapshot@.completes(),        // AUTO
                    y.index == y.seq().len(), // AUTO
                // Removed when the user adds #[verifier::exec_allows_no_decreases_clause]
                // decreases
                //     y.iter.decrease(),
            {
                #[allow(non_snake_case)]
                let mut VERUS_loop_next;
                match y.next() {
                    Some(VERUS_loop_val) => VERUS_loop_next = VERUS_loop_val,
                    None => {
                        break
                    }
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