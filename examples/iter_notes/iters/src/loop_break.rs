use std::{io::Take, iter::{self, Skip}, path::Iter};
use vstd::prelude::*;
use crate::prophetic_iters::decreases_fix::*;
use crate::prophetic_iters::iterator_traits::*;

verus!{

broadcast use group_decrease_axioms;

spec fn sum_u8(s: Seq<&u8>) -> nat 
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (sum_u8(s.drop_last()) + *s.last()) as nat
    }
}

proof fn sum_u8_monotonic(s: Seq<&u8>, i: int, j: int)
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
        forall |s: Seq<&u8>, i, j| #![auto]
            0 <= i <= j < s.len() ==>
            sum_u8(s.take(i)) <= sum_u8(s.take(j)),
{
    assert forall |s: Seq<&u8>, i, j| #![auto] 0 <= i <= j < s.len() implies sum_u8(s.take(i)) <= sum_u8(s.take(j)) by {
        sum_u8_monotonic(s, i, j);
    }
}

// Can't write an ensures clause or an invariant_except_break clause on a for loop
// fn existing_version(v: Vec<u8>) {
//     let mut sum: u8 = 0;
//     let mut i: usize = 0;

//     for x in iter: v 
//         //invariant_except_break
//         invariant
//             i == iter.pos,
//             0 <= i <= v.len(),
//             sum == sum_u8(v@.take(i as int)),
//         ensures
//             sum == sum_u8(v@.take(i as int)) || (sum == 0xff && sum_u8(v@.take(i as int)) > u8::MAX),
//     {
//         let ghost old_iter = iter;
//         if x <= u8::MAX - sum {
//             sum += x;
//             assert(x == v@[i as int]);
//         } else {
//             sum = u8::MAX;
//             break;
//         }
//         i += 1;
//         assert(v@.take(i as int).drop_last() == v@.take(i - 1 as int));
//     }
// }

fn existing_version(v: Vec<&u8>) {
    let mut sum: u8 = 0;
    let mut i: usize = 0;

    while i < v.len()
        invariant_except_break
            0 <= i <= v.len(),
            sum == sum_u8(v@.take(i as int)),
        ensures
            sum == sum_u8(v@.take(i as int)) || (sum == u8::MAX && sum_u8(v@.take(i as int)) > u8::MAX),
        decreases
            v.len() - i,
    {
        let x = v[i];
        i += 1;
        assert(v@.take(i as int).drop_last() == v@.take(i - 1 as int)); // OBSERVE
        if *x <= u8::MAX - sum {
            sum += *x;
        } else {
            sum = u8::MAX;
            break;
        }
    }
}

fn for_loop_test_skip(v: Vec<u8>) {

    let mut sum: u8 = 0;

    // Verus will desugar this: 
    // for x in y: v 
    //     invariant_except_break
    //         sum == sum_u8(v@.take(y.index@))
    //      ensures
    //         sum == sum_u8(v@.take(y.index@)) || 
    //            (sum == u8::MAX && sum_u8(v@.take(y.index@)) > u8::MAX),
    // {
    //     assert(v@.take(y.index@).drop_last() == v@.take(y.index@ - 1 as int)); // OBSERVE
    //     if x <= u8::MAX - sum {
    //         sum += x;
    //     } else {
    //         sum = u8::MAX;
    //         break;
    //     }
    // }
    //
    // Into:
    let iter = VerusForLoopIterator::new(vec_iter(&v));
    assert(iter.seq().len() == v.len());
    assert(iter.seq().map_values(|e: &u8| *e) == v@);
    let Ghost(VERUS_old_snap) = iter.snapshot;
    #[allow(non_snake_case)]
    let VERUS_loop_result = match iter {
        mut y => {
            loop
                invariant_except_break
                    y.iter.decrease() is Some,
                    // User invariant_except_break
                    sum == sum_u8(y.seq().take(y.index@))
                invariant
                    y.wf(VERUS_old_snap),
                    ({ 
                      // Grab the next val for (possible) use in inv
                      let x = if y.index@ < y.seq().len() { y.seq()[y.index@] } else { arbitrary() };
                      true
                    }),
                ensures
                    // TODO: Automatically omit these when the for loop contains a break?
                    // y.snapshot@.completes(),        // AUTO
                    // y.index == y.seq().len(), // AUTO
                    
                    // User ensures 
                    // sum == sum_u8(y.seq()) || 
                    //     (sum == u8::MAX && sum_u8(y.seq()) > u8::MAX),
                    (y.index@ == y.seq().len() && sum == sum_u8(y.seq().take(y.index@))) || 
                        (sum == u8::MAX && sum_u8(y.seq().take(y.index@)) > u8::MAX),
                decreases
                    y.iter.decrease(),
            {
                #[allow(non_snake_case)]
                let mut VERUS_loop_next;
                match y.next(Ghost(VERUS_old_snap)) {
                    Some(VERUS_loop_val) => VERUS_loop_next = VERUS_loop_val,
                    None => {
                        break
                    }
                }
                let x = VERUS_loop_next;
                let () = {
                    // body
                    assert(y.seq().take(y.index@).drop_last() == y.seq().take(y.index@ - 1 as int)); // OBSERVE
                    if *x <= u8::MAX - sum {
                        sum += *x;
                    } else {
                        sum = u8::MAX;
                    // assert(sum_u8(y.seq().take(y.index@)) > u8::MAX);
                    // assert(sum_u8(y.seq()) > u8::MAX) by {
                    //     // PAPER CUT: Can't call a lemma on the prophetic sequence
                    //     //sum_u8_monotonic(y.seq(), y.index@, y.seq().len() as int);
                    //     sum_u8_monotonic_forall();
                    // }

                        break;
                    }
                };
            }
        }
    };

    assert(iter.seq() == v@.map_values(|e:u8| &e)); // OBSERVE
    assert(iter.seq() == iter.seq().take(iter.seq().len() as int)); // OBSERVE
    //assert(sum == sum_u8(v@.map_values(|e:u8| &e)) || sum == u8::MAX);
    proof {
        sum_u8_monotonic_forall();
    }
    assert(sum == sum_u8(v@.map_values(|e:u8| &e)) || 
            (sum == u8::MAX && sum_u8(v@.map_values(|e:u8| &e)) > u8::MAX));

}


} // verus!
