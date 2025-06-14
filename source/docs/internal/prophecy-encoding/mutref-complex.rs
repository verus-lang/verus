use builtin::*;
use builtin_macros::verus;

verus! {

fn one_or_the_other(which: bool) {
    let mut a: i32 = 0;
    let mut b: i32 = 0;
    let x = &'x mut a; // x ≘ {x_cur: 0, x_fut: ?}  ,  assume(a == x_fut)   |   ɸ = { a: blocked }
    let y = &'y mut b; // y ≘ {y_cur: 0, y_fut: ?}  ,  assume(b == y_fut)
    assert(a as int <= i32::MAX); // still (maybe) reasonable
    let mut c: &'z mut = reborrow(which, &mut a, &mut b); // c ≘ {c_cur: _, c_fut: _} == if which {r_cur: x_cur, r_fut: x_fut} else {r_cur: y_cur, r_fut: y_fut}
    *c = 5; // c_cur: 5
    resolve(c); // assume(c_cur == c_fut)
                // --> if (which) { a == 5 && b == 0 } else { a == 0 && b == 5 }
    assert(which  ==> a == 5 && b == 0);
    assert(!which ==> a == 0 && b == 5);
}

fn reborrow(which: bool, x: &mut i32, y: &mut i32) -> (r: &mut i32)
// x ≘ {x_cur: 0, x_fut: ?}  ,  assume(a == x_fut)
// y ≘ {y_cur: 0, y_fut: ?}  ,  assume(b == y_fut)
    ensures
        *r == if which { old(x) } else { old(y) },
        on_expiry(r) == if which { on_expiry(x) } else { on_expiry(y) },

// r ≘ if which {r_cur: x_cur, r_fut: x_fut} else {r_cur: y_cur, r_fut: y_fut}
{
    if which { x } else { y }
}

} // verus!
