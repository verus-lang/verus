use vstd::prelude::*;

verus! {
 
uninterp spec fn is_decrease<A>(from: A, to: A) -> bool;

broadcast axiom fn is_decrease_decreases<A>(from: A, to: A)
    ensures
        #[trigger] is_decrease(from, to) <==> decreases_to!(from => to);

broadcast axiom fn is_decrease_int(from: int, to: int)
    ensures
        #[trigger] is_decrease(from, to) <==> 0 <= to < from,
;

trait I {

    type Decrease;

    spec fn decrease(&self) -> Self::Decrease;

    fn next(&mut self) -> (b: bool)
//        decreases
//            old(self).decrease()
        ensures
            //b ==> decreases_to!(old(self).decrease() => self.decrease()),
            b ==> is_decrease(old(self).decrease(), self.decrease()),
    ;
}

struct Count {
    count: u32,
}


impl I for Count {

    type Decrease = u32;

    spec fn decrease(&self) -> Self::Decrease {
        self.count
    }

    fn next(&mut self) -> (b: bool) {
        broadcast use {is_decrease_decreases, is_decrease_int};
        if self.count > 0 {
            self.count = self.count - 1;
//            proof {
//                is_decrease_int(old(self).count as int, self.count as int);
//            }
            assert(is_decrease(old(self).count as int, self.count as int));
            assert(is_decrease(old(self).count, self.count));
            return true;
        } else {
            return false;
        }
    }
}

fn test() {

    let mut c = Count { count: 3 };

    while c.count > 0 
        decreases 
            c.decrease()
    {
        broadcast use {is_decrease_decreases, is_decrease_int};
        let ghost old_c = c;
        let b = c.next();
        assert(b ==> is_decrease(old_c.count as int, c.count as int));
        proof {
            is_decrease_decreases(old_c.count as int, c.count as int);
        }
        assert(b ==> decreases_to!(old_c.count as int => c.count as int));
        if !b {
            break;
        }
    }
}

/*
spec fn triangle(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}

proof fn triangle_is_monotonic(i: nat, j: nat)
    ensures
        i <= j ==> triangle(i) <= triangle(j),
    decreases j,
{
    // We prove the statement `i <= j ==> triangle(i) <= triangle(j)`
    // by induction on `j`.

    if j == 0 {
        // The base case (`j == 0`) is trivial since it's only
        // necessary to reason about when `i` and `j` are both 0.
        // So no proof lines are needed for this case.
    }
    else {
        // In the induction step, we can assume the statement is true
        // for `j - 1`. In Verus, we can get that fact into scope with
        // a recursive call substituting `j - 1` for `j`.

        triangle_is_monotonic(i, (j - 1) as nat);

        // Once we know it's true for `j - 1`, the rest of the proof
        // is trivial.
    }
}

fn for_loop_triangle(n: u32) -> (sum: u32)
    requires
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        sum == triangle(n as nat),
{
    let mut sum: u32 = 0;
    for idx in iter: 0..n
//        invariant
//            true,
//        invariant_except_break
//            sum == triangle(idx as nat),
//            triangle(n as nat) < 0x1_0000_0000,
    {
        assert(sum + idx + 1 < 0x1_0000_0000) by {
            triangle_is_monotonic((idx + 1) as nat, n as nat);
        }
        sum = sum + idx + 1;
        if sum > 0 {
            break;
        }
    }
    sum
}
*/

fn main() {
    assert(1 == 0 + 1);
}

} // verus!
