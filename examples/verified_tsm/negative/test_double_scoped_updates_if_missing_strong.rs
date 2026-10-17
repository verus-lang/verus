// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
verus! {

verified_state_machine_model!{ X {

            fields {
                pub m: IMap<int, int>,

                pub a: int,
                pub b: int,
            }

            transition!{
                tr(x: bool, y: bool, z: bool, w: bool, v: bool) {
                    if x {
                        require w;
                        update m[0] = 10;
                    } else {
                        assert y by { assume(false); };
                        update a = 99;
                    }

                    assert z by { assume(false); };

                    if v {
                        update b = 11;
                    } else {
                        update m[1] = 11;
                    }
                }
            }
        }}

spec fn tr_weak(
    pre: X::State,
    post: X::State,
    x: bool,
    y: bool,
    z: bool,
    w: bool,
    v: bool,
) -> bool {
    (x ==> w) && ((!x ==> y) ==> (
    // TODO this should probably be under the `z ==>`
    (x ==> post.a == pre.a) && (!x ==> post.a == 99) && (z ==> ((v ==> post.b == 11) && (!v
        ==> post.b == pre.b) && (if x {
        if v {
            post.m =~= pre.m.insert(0, 10)
        } else {
            post.m =~= pre.m.insert(0, 10).insert(1, 11)
        }
    } else {
        if v {
            post.m =~= pre.m
        } else {
            post.m =~= pre.m.insert(1, 11)
        }
    })))))
}

proof fn test(pre: X::State, post: X::State, x: bool, y: bool, z: bool, w: bool, v: bool)
    ensures
        X::State::tr(pre, post, x, y, z, w, v) <==> tr_weak(pre, post, x, y, z, w, v),
{
}

spec fn tr_strong(
    pre: X::State,
    post: X::State,
    x: bool,
    y: bool,
    z: bool,
    w: bool,
    v: bool,
) -> bool {
    (x ==> w) && (!x ==> y) && z && (x ==> post.a == pre.a) && (!x ==> post.a == 99) && (v
        ==> post.b == 11) && (!v ==> post.b == pre.b) && (if x {
        if v {
            post.m =~= pre.m.insert(0, 10)
        } else {
            post.m =~= pre.m.insert(0, 10).insert(1, 11)
        }
    } else {
        if v {
            post.m =~= pre.m
        } else {
            post.m =~= pre.m.insert(1, 11)
        }
    })
}

proof fn test2(pre: X::State, post: X::State, x: bool, y: bool, z: bool, w: bool, v: bool)
    ensures
        X::State::tr_strong(pre, post, x, y, z, w, v) <==> tr_strong(pre, post, x, y, z, w, v),
{
    if X::State::tr_strong(pre, post, x, y, z, w, v) {
        assert(tr_strong(pre, post, x, y, z, w, v));
    }
    if tr_strong(pre, post, x, y, z, w, v) {
        assert(X::State::tr_strong(pre, post, x, y, z, w, v));
    }
}

fn main() {
    proof {
        let pre = X::State { m: IMap::empty(), a: 1int, b: 2int };
        let post = X::take_step::tr(pre, false, false, true, false, false);
    }
}

} // verus!
