//! Complete scoped-update case: exact weak model and a strengthened resource companion.
//! Original assertion proof overrides are omitted from the pure model, which emits no safety theorem.
//! checked_take_step certifies the weak mathematical relation only, including when assertions are false.
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::imap::*;
use vstd::prelude::*;
use vstd::resource::exclusive::ExclusiveRA;
verus! {

verified_state_machine_model!{ X {

            fields {
                pub m: IMap<int, int>,

                pub a: int,
                pub b: int,
            }

            transition!{
                tr(x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>) {
                    match x {
                        Option::Some(x1) => {
                            require w;
                            update m[0] = x1;
                        }
                        Option::None => {
                            assert y;
                            update a = 99;
                        }
                    }

                    assert z;

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
    x: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
) -> bool {
    (x is Some ==> w) && ((!(x is Some) ==> y) ==> (
    // TODO this should probably be under the `z ==>`
    (x is Some ==> post.a == pre.a) && (!(x is Some) ==> post.a == 99) && (z ==> ((v is Some
        ==> post.b == v->0) && (!(v is Some) ==> post.b == pre.b) && (if x is Some {
        if v is Some {
            post.m =~= pre.m.insert(0, x->0)
        } else {
            post.m =~= pre.m.insert(0, x->0).insert(1, 11)
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
    x: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
)
    ensures
        X::State::tr(pre, post, x, y, z, w, v) <==> tr_weak(pre, post, x, y, z, w, v),
{
}

spec fn tr_strong(
    pre: X::State,
    post: X::State,
    x: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
) -> bool {
    (x is Some ==> w) && (!(x is Some) ==> y) && z && (x is Some ==> post.a == pre.a) && (!(
    x is Some) ==> post.a == 99) && (v is Some ==> post.b == v->0) && (!(v is Some) ==> post.b
        == pre.b) && (if x is Some {
        if v is Some {
            post.m =~= pre.m.insert(0, x->0)
        } else {
            post.m =~= pre.m.insert(0, x->0).insert(1, 11)
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
    x: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
)
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

spec fn tr_enabled(
    pre: X::State,
    x: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
) -> bool {
    x is Some ==> w
}

proof fn test3(pre: X::State, x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>)
    ensures
        X::State::tr_enabled(pre, x, y, z, w, v) <==> tr_enabled(pre, x, y, z, w, v),
{
}

proof fn test_take_step(pre: X::State, x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>)
    requires
        x is Some ==> w,
{
    let post = checked_take_step(pre, x, y, z, w, v);
    assert(X::State::tr(pre, post, x, y, z, w, v));
}

// This produces a mathematical next state only; it certifies no resource update.
pub open spec fn chosen_next(pre: X::State, x: Option<int>, v: Option<int>) -> X::State {
    let intermediate = match x {
        Some(value) => pre.m.insert(0int, value),
        None => pre.m,
    };
    X::State {
        m: match v {
            Some(_) => intermediate,
            None => intermediate.insert(1int, 11int),
        },
        a: if x is Some {
            pre.a
        } else {
            99
        },
        b: match v {
            Some(value) => value,
            None => pre.b,
        },
    }
}

pub proof fn checked_take_step(
    pre: X::State,
    x: Option<int>,
    y: bool,
    z: bool,
    w: bool,
    v: Option<int>,
) -> (post: X::State)
    requires
        X::State::tr_enabled(pre, x, y, z, w, v),
    ensures
        X::State::tr(pre, post, x, y, z, w, v),
        post == chosen_next(pre, x, v),
{
    let post = chosen_next(pre, x, v);
    assert(tr_weak(pre, post, x, y, z, w, v));
    test(pre, post, x, y, z, w, v);
    post
}

verified_tokenized_state_machine!{
    #[verified_raw_tokens]
 SafeX {

            fields {
                #[sharding(variable)] pub m: IMap<int, int>,

                #[sharding(variable)] pub a: int,
                #[sharding(variable)] pub b: int,
            }

            init! {initialize() {init m=IMap::empty();init a=0;init b=0;} }
            transition!{
                tr(x: Option<int>, y: bool, assertion_z: bool, w: bool, v: Option<int>) {
                    require x is Some || y;
                    require assertion_z;
                    match x {
                        Option::Some(x1) => {
                            require w;
                            update m[0] = x1;
                        }
                        Option::None => {
                            assert y;
                            update a = 99;
                        }
                    }

                    assert assertion_z;

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

pub proof fn weak_model_clients() {
    let pre = X::State { m: IMap::empty(), a: 1, b: 2 };
    test_take_step(pre, Some(17), false, false, true, Some(23));
    test_take_step(pre, None, false, false, false, None);
    let post = checked_take_step(pre, Some(17), false, false, true, Some(23));
    assert(X::State::tr(pre, post, Some(17), false, false, true, Some(23)));
    assert(!X::State::tr_strong(pre, post, Some(17), false, false, true, Some(23)));
}

pub proof fn checked_resource_clients() {
    let tracked token = SafeX::Protocol::initialize();
    let tracked token = SafeX::Protocol::tr(token, Some(17), false, true, true, Some(23));
    assert(token.fragment().m == Some(ExclusiveRA::Exclusive(IMap::empty().insert(0int, 17int))));
    assert(token.fragment().a == Some(ExclusiveRA::Exclusive(0int)));
    assert(token.fragment().b == Some(ExclusiveRA::Exclusive(23int)));
    let tracked token = SafeX::Protocol::tr(token, None, true, true, false, None);
    assert(token.fragment().m == Some(
        ExclusiveRA::Exclusive(IMap::empty().insert(0int, 17int).insert(1int, 11int)),
    ));
    assert(token.fragment().a == Some(ExclusiveRA::Exclusive(99int)));
    assert_imaps_equal!(IMap::<int,int>::empty().insert(0int,17int).insert(1int,11int)
        .insert(0int,31int).insert(1int,11int),
        IMap::<int,int>::empty().insert(0int,31int).insert(1int,11int));
    let tracked token = SafeX::Protocol::tr(token, Some(31), false, true, true, None);
    assert(token.fragment().m == Some(
        ExclusiveRA::Exclusive(IMap::empty().insert(0int, 31int).insert(1int, 11int)),
    ));
    let tracked token = SafeX::Protocol::tr(token, None, true, true, false, Some(42));
    assert(token.fragment().b == Some(ExclusiveRA::Exclusive(42int)));
}

pub fn demonstration() {
    proof {
        weak_model_clients();
        checked_resource_clients();
    }
}

} // verus!
fn main() {
    demonstration();
}
