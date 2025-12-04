use std::{io::Take, iter::{self, Skip}, path::Iter};
use vstd::prelude::*;
use crate::prophetic_iters::decreases_fix::*;
use crate::prophetic_iters::iterator_traits::*;

verus!{

broadcast use group_decrease_axioms;

fn for_loop_test_vec() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = vec![];

    let i = vec_iter(&v);

    let mut count: u128 = 0;
    // Verus will desugar this: 
    //
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
                invariant_except_break
                    y.iter.decrease() is Some,
                invariant
                    y.wf(VERUS_old_snap, init@),
                    ({ 
                      // Grab the next val for (possible) use in inv
                      let x = if y.index@ < y.seq().len() { y.seq()[y.index@] } else { arbitrary() };

                      // User inv 1
                      w.len() == y.index &&
                      (forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i]) &&

                      // User inv 2
                      w.len() == y.index &&
                      (forall |i| 0 <= i < w.len() ==> w[i] == v[i]) &&


                      count == w.len() <= u64::MAX
                    }),
                ensures
                    // REVIEW: This works, but only if we don't allow `break`s inside a for loop.
                    //         It appears that may be the case, although the error messages are confusing.
                    y.snapshot@.completes(),        // AUTO
                    y.index == y.seq().len(), // AUTO
                decreases
                    y.iter.decrease(),
            {
                let ghost old_y = y;
                #[allow(non_snake_case)]
                let mut VERUS_loop_next;
                match y.next(Ghost(VERUS_old_snap), init) {
                    Some(VERUS_loop_val) => VERUS_loop_next = VERUS_loop_val,
                    None => {
                        break
                    }
                }
                let x = VERUS_loop_next;
                let () = {
                    // body
                    assert(w.len() == y.index@ - 1);
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

/*
fn for_loop_test_map() {
    let f = |i: &u8| -> (out: u8)
        requires i < 255,
        ensures out == i + 1,
        {
            *i + 1
        };
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = vec![];

    let i = vec_iter(&v);
    let iter= MapIterator::new(i, f);
    assert(forall |i| 0 <= i < iter.seq().len() ==> iter.seq()[i] < 10);


    // Verus will desugar this: 
    //
    // for x in y: m
    //     invariant
    //         w.len() == y.index,
    //         forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i]),
    // {
    //     w.push(x);
    // }
    //
    // Into:
    #[allow(non_snake_case)]
    //let VERUS_iter_expr = v;
    // let result =  match IntoIterator::into_iter(VERUS_iter_expr) {...
    let iter = VerusForLoopIterator::new(iter);
    let Ghost(VERUS_old_snap) = iter.snapshot;
    #[allow(non_snake_case)]
    let VERUS_loop_result = match iter {
        mut y => {
            loop
                invariant_except_break
                    y.iter.decrease() is Some,
                invariant
                    y.wf(VERUS_old_snap),
                    
                    // User invariants
                    ({ 
                      // Grab the next val for (possible) use in inv
                      let x = if y.index@ < y.seq().len() { y.seq()[y.index@] } else { arbitrary() };

                    // inv
                    //w@ == y.seq().take(y.index@) 
                    w.len() == y.index
                    && (forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i])

                    && (forall |i| 0 <= i < y.seq().len() ==> y.seq()[i] < 8)
                    && (y.index@ < y.seq().len() ==> x < 8)
                    }),
                ensures
                    y.snapshot@.completes(),        // AUTO
                    y.index == y.seq().len(), // AUTO
                decreases
                    y.iter.decrease(),
            {
                #[allow(non_snake_case)]
                let mut VERUS_loop_next;
                match y.next(Ghost(VERUS_old_snap)) {
                    Some(VERUS_loop_val) => {
                        VERUS_loop_next = VERUS_loop_val
                    }
                    None => {
                        break
                    }
                }
                let x = VERUS_loop_next;
                let () = {
                    // body
                    assert(x < 8);
                    w.push(x);
                };
            }
        }
    };
    // Make sure our invariant was useful
    assert(w@ == v@.map_values(|i:u8| (i + 1) as u8));
}

fn for_loop_test_take() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = vec![];

    let i = vec_iter(&v);
    let iter = TakeIterator::new(i, 3);

    // Verus will desugar this: 
    //
    // for x in y: m
    //     invariant
    //         &&& w.len() == y.index
    //         &&& forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i]
    // {
    //     w.push(*x);
    // }
    //
    // Into:
    //#[allow(non_snake_case)]
    //let VERUS_iter_expr = v;
    let iter = VerusForLoopIterator::new(iter);
    let Ghost(VERUS_old_snap) = iter.snapshot;
    #[allow(non_snake_case)]
    // let result =  match IntoIterator::into_iter(VERUS_iter_expr) {...
    let VERUS_loop_result = match iter {
        mut y => {
            loop
                invariant_except_break
                    y.iter.decrease() is Some,
                invariant
                    y.wf(VERUS_old_snap),
                    ({ 
                      // Grab the next val for (possible) use in inv
                      let x = if y.index@ < y.seq().len() { y.seq()[y.index@] } else { arbitrary() };

                      // inv
                      &&& w.len() == y.index
                      &&& forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i]
                    }),
                ensures
                    y.snapshot@.completes(),        // AUTO
                    y.index == y.seq().len(), // AUTO
                decreases
                    y.iter.decrease(),
            {
                #[allow(non_snake_case)]
                let mut VERUS_loop_next;
                match y.next(Ghost(VERUS_old_snap)) {
                    Some(VERUS_loop_val) => {
                        VERUS_loop_next = VERUS_loop_val
                    }
                    None => {
                        break
                    }
                }
                let x = VERUS_loop_next;
                let () = {
                    // body
                    w.push(*x);
                };
            }
        }
    };

    // Make sure our invariant was useful
    assert(w@ == v@.take(3));
}

fn for_loop_test_skip() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = vec![];

    let i = vec_iter(&v);
    let ghost old_i = i;
    let iter = SkipIterator::new(i, 3);
    // Verus will desugar this: 
    //
    // for x in y: m
    //     invariant
    //        &&& w.len() == y.index
    //        &&& forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i]
    // {
    //     w.push(*x);
    // }
    //
    // Into:
    let iter = VerusForLoopIterator::new(iter);
    let Ghost(VERUS_old_snap) = iter.snapshot;
    #[allow(non_snake_case)]
    //let VERUS_iter_expr = v;
    #[allow(non_snake_case)]
    // let result =  match IntoIterator::into_iter(VERUS_iter_expr) {...
    let VERUS_loop_result = match iter {
        mut y => {
            loop
                invariant_except_break
                    y.iter.decrease() is Some,
                invariant
                    y.wf(VERUS_old_snap),
                    ({ 
                      // Grab the next val for (possible) use in inv
                      let x = if y.index@ < y.seq().len() { y.seq()[y.index@] } else { arbitrary() };

                      // inv
                      &&& w.len() == y.index
                      &&& forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i]
                    }),
                ensures
                    y.snapshot@.completes(),        // AUTO
                    y.index == y.seq().len(), // AUTO
                decreases
                    y.iter.decrease()
            {
                #[allow(non_snake_case)]
                let mut VERUS_loop_next;
                match y.next(Ghost(VERUS_old_snap)) {
                    Some(VERUS_loop_val) => {
                        VERUS_loop_next = VERUS_loop_val
                    }
                    None => {
                        break
                    }
                }
                let x = VERUS_loop_next;
                let () = {
                    // body
                    w.push(*x);
                };
                // assert(y.decrease() is Some);
            }
        }
    };

    // Make sure our invariant was useful
    assert(w@ == v@.skip(3));
}

fn for_loop_test_rev() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = vec![];

    let i = vec_iter(&v);
    let ghost old_i = i;
    let iter = ReverseIterator::new(i);
    // Verus will desugar this: 
    //
    // for x in y: m
    //     invariant
    //        &&& w.len() == y.index
    //        &&& forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i]
    // {
    //     w.push(*x);
    // }
    //
    // Into:
    let iter = VerusForLoopIterator::new(iter);
    let Ghost(VERUS_old_snap) = iter.snapshot;
    #[allow(non_snake_case)]
    let VERUS_loop_result = match iter {
        mut y => {
            loop
                invariant_except_break
                    y.iter.decrease() is Some,
                invariant
                    y.wf(VERUS_old_snap),
                    ({ 
                      // Grab the next val for (possible) use in inv
                      let x = if y.index@ < y.seq().len() { y.seq()[y.index@] } else { arbitrary() };

                      // inv
                      &&& w.len() == y.index
                      &&& forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i]
                    }),
                ensures
                    y.snapshot@.completes(),        // AUTO
                    y.index == y.seq().len(), // AUTO
                decreases
                    y.iter.decrease(),
            {
                #[allow(non_snake_case)]
                let mut VERUS_loop_next;
                match y.next(Ghost(VERUS_old_snap)) {
                    Some(VERUS_loop_val) => {
                        VERUS_loop_next = VERUS_loop_val
                    }
                    None => {
                        break
                    }
                }
                let x = VERUS_loop_next;
                let () = {
                    // body
                    w.push(*x);
                };
            }
        }
    };

    // Make sure our invariant was useful
    assert(w@ == v@.reverse());
}

fn for_loop_test_double_rev() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = vec![];

    let i = vec_iter(&v);
    let ghost old_i = i;
    let iter = ReverseIterator::new(ReverseIterator::new(i));
    // Verus will desugar this: 
    //
    // for x in y: m
    //     invariant
    //        &&& w.len() == y.index
    //        &&& forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i]
    // {
    //     w.push(*x);
    // }
    //
    // Into:
    let iter = VerusForLoopIterator::new(iter);
    let Ghost(VERUS_old_snap) = iter.snapshot;
    #[allow(non_snake_case)]
    let VERUS_loop_result = match iter {
        mut y => {
            loop
                invariant_except_break
                    y.iter.decrease() is Some,
                invariant
                    y.wf(VERUS_old_snap),
                    ({ 
                      // Grab the next val for (possible) use in inv
                      let x = if y.index@ < y.seq().len() { y.seq()[y.index@] } else { arbitrary() };

                      // inv
                      &&& w.len() == y.index
                      &&& forall |i| 0 <= i < w.len() ==> w[i] == y.seq()[i]
                    }),
                ensures
                    y.snapshot@.completes(),        // AUTO
                    y.index == y.seq().len(), // AUTO
                decreases
                    y.iter.decrease(),
            {
                #[allow(non_snake_case)]
                let mut VERUS_loop_next;
                match y.next(Ghost(VERUS_old_snap)) {
                    Some(VERUS_loop_val) => {
                        VERUS_loop_next = VERUS_loop_val
                    }
                    None => {
                        break
                    }
                }
                let x = VERUS_loop_next;
                let () = {
                    // body
                    w.push(*x);
                };
            }
        }
    };

    // Make sure our invariant was useful
    assert(w@ == v@);
}
*/
} // verus!
