// no-cheating: off --- keeps the trusted original's `by { assume(false); }` proofs of its asserts
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
                tr(r#__tsm_checked_take_step_tr: Option<int>, y: bool, z: bool, w: bool, v: Option<int>) {
                    match r#__tsm_checked_take_step_tr {
                        Option::Some(x1) => {
                            require w;
                            update m[0] = x1;
                        }
                        Option::None => {
                            assert y by { assume(false); };
                            update a = 99;
                        }
                    }

                    assert z by { assume(false); };

                    match v {
                        Option::Some(v1) => {
                            update b = v1;
                        }
                        Option::None => {
                            update m[1] = 11;
                        }
                    }
                }
            }
        }}

spec fn tr_weak(
    pre: X::State,
    post: X::State,
    r#__tsm_checked_take_step_tr: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
) -> bool {
    (r#__tsm_checked_take_step_tr is Some ==> w) && ((!(r#__tsm_checked_take_step_tr is Some) ==> y)
        ==> (
    // TODO this should probably be under the `z ==>`
    (r#__tsm_checked_take_step_tr is Some ==> post.a == pre.a) && (!(
    r#__tsm_checked_take_step_tr is Some) ==> post.a == 99) && (z ==> ((v is Some ==> post.b
        == v->0) && (!(v is Some) ==> post.b == pre.b) && (if r#__tsm_checked_take_step_tr is Some {
        if v is Some {
            post.m =~= pre.m.insert(0, r#__tsm_checked_take_step_tr->0)
        } else {
            post.m =~= pre.m.insert(0, r#__tsm_checked_take_step_tr->0).insert(1, 11)
        }
    } else {
        if v is Some {
            post.m =~= pre.m
        } else {
            post.m =~= pre.m.insert(1, 11)
        }
    })))))
}

proof fn test(
    pre: X::State,
    post: X::State,
    r#__tsm_checked_take_step_tr: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
)
    ensures
        X::State::tr(pre, post, r#__tsm_checked_take_step_tr, y, z, w, v) <==> tr_weak(
            pre,
            post,
            r#__tsm_checked_take_step_tr,
            y,
            z,
            w,
            v,
        ),
{
}

spec fn tr_strong(
    pre: X::State,
    post: X::State,
    r#__tsm_checked_take_step_tr: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
) -> bool {
    (r#__tsm_checked_take_step_tr is Some ==> w) && (!(r#__tsm_checked_take_step_tr is Some) ==> y)
        && z && (r#__tsm_checked_take_step_tr is Some ==> post.a == pre.a) && (!(
    r#__tsm_checked_take_step_tr is Some) ==> post.a == 99) && (v is Some ==> post.b == v->0) && (!(
    v is Some) ==> post.b == pre.b) && (if r#__tsm_checked_take_step_tr is Some {
        if v is Some {
            post.m =~= pre.m.insert(0, r#__tsm_checked_take_step_tr->0)
        } else {
            post.m =~= pre.m.insert(0, r#__tsm_checked_take_step_tr->0).insert(1, 11)
        }
    } else {
        if v is Some {
            post.m =~= pre.m
        } else {
            post.m =~= pre.m.insert(1, 11)
        }
    })
}

proof fn test2(
    pre: X::State,
    post: X::State,
    r#__tsm_checked_take_step_tr: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
)
    ensures
        X::State::tr_strong(pre, post, r#__tsm_checked_take_step_tr, y, z, w, v) <==> tr_strong(
            pre,
            post,
            r#__tsm_checked_take_step_tr,
            y,
            z,
            w,
            v,
        ),
{
    if X::State::tr_strong(pre, post, r#__tsm_checked_take_step_tr, y, z, w, v) {
        assert(tr_strong(pre, post, r#__tsm_checked_take_step_tr, y, z, w, v));
    }
    if tr_strong(pre, post, r#__tsm_checked_take_step_tr, y, z, w, v) {
        assert(X::State::tr_strong(pre, post, r#__tsm_checked_take_step_tr, y, z, w, v));
    }
}

spec fn tr_enabled(
    pre: X::State,
    r#__tsm_checked_take_step_tr: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
) -> bool {
    r#__tsm_checked_take_step_tr is Some ==> w
}

proof fn test3(
    pre: X::State,
    r#__tsm_checked_take_step_tr: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
)
    ensures
        X::State::tr_enabled(pre, r#__tsm_checked_take_step_tr, y, z, w, v) <==> tr_enabled(
            pre,
            r#__tsm_checked_take_step_tr,
            y,
            z,
            w,
            v,
        ),
{
}

proof fn test_take_step(
    pre: X::State,
    r#__tsm_checked_take_step_tr: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
)
    requires
        X::State::tr_enabled_strong(pre, r#__tsm_checked_take_step_tr, y, z, w, v),
        pre.invariant(),
{
    let post = X::take_step::tr(pre, r#__tsm_checked_take_step_tr, y, z, w, v);
    assert(X::State::tr(pre, post, r#__tsm_checked_take_step_tr, y, z, w, v));
}

fn main() {
    proof {
        let pre = X::State { m: IMap::empty(), a: 0int, b: 0int };
        test_take_step(pre, Some(17int), false, true, true, Some(23int));
        let post = X::take_step::tr(pre, None, true, true, false, None);
        assert(X::State::tr_strong(pre, post, None, true, true, false, None));
        assert(post.invariant());
    }
}

} // verus!
