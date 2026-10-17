//! Complete extracted substantial state-machine test; reference relations retained.
#![allow(unused_imports)]
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::{CountRA, Token};
use vstd::{imap::*, map::*, modes::*, multiset::*, pervasive::*, set::*};
verus! {

pub ghost enum Foo {
    Bar(int),
    Qax(int),
    Duck(int),
}

} // verus!
verified_state_machine_model! { X {
    fields {
        pub x: int,
        pub y: int,
        pub z: int,
    }

    init!{
        initialize(x: int, y: int, z: int, foo: Foo) {
            init x = x;
            init y = y;
            require(y <= z);
            match foo {
                Foo::Bar(a) => { init z = z; }
                Foo::Qax(b) => { init z = z + 1; }
                Foo::Duck(d) => { init z = z + 2; }
            }
        }
    }

    transition!{
        tr1(foo: Foo, c: bool) {
            match foo {
                Foo::Bar(a) => { update z = pre.z + 1; }
                Foo::Qax(b) if b == 20 => { assert(pre.y <= pre.z); }
                Foo::Duck(d) => { assert(foo is Duck); }
                _ => { }
            }
            require(c);
        }
    }

    #[invariant]
    pub fn the_inv(self) -> bool { self.y <= self.z }

    #[inductive(initialize)]
    fn init_inductive(post: Self, x: int, y: int, z: int, foo: Foo) { }

    #[inductive(tr1)]
    fn tr1_inductive(pre: Self, post: Self, foo: Foo, c: bool) { }
}}

verus! {

spec fn rel_init(post: X::State, x: int, y: int, z: int, foo: Foo) -> bool {
    &&& post.x == x
    &&& post.y == y
    &&& y <= z
    &&& match foo {
        Foo::Bar(a) => { post.z == z },
        Foo::Qax(b) => { post.z == z + 1 },
        Foo::Duck(d) => { post.z == z + 2 },
    }
}

spec fn rel_tr1(pre: X::State, post: X::State, foo: Foo, c: bool) -> bool {
    &&& (match foo {
        Foo::Bar(a) => { post.z == pre.z + 1 },
        Foo::Qax(b) if b == 20 => { pre.y <= pre.z ==> post.z == pre.z },
        Foo::Duck(d) => { post.z == pre.z },
        _ => { post.z == pre.z },
    })
    &&& ((match foo {
        Foo::Bar(a) => { true },
        Foo::Qax(b) if b == 20 => { pre.y <= pre.z },
        Foo::Duck(d) => { true },
        _ => { true },
    }) ==> {
        &&& c
        &&& pre.x == post.x
        &&& pre.y == post.y
    })
}

spec fn rel_tr1_strong(pre: X::State, post: X::State, foo: Foo, c: bool) -> bool {
    &&& (match foo {
        Foo::Bar(a) => { post.z == pre.z + 1 },
        Foo::Qax(b) if b == 20 => { post.z == pre.z && pre.y <= pre.z },
        Foo::Duck(d) => { post.z == pre.z },
        _ => { post.z == pre.z },
    })
    &&& (c && pre.x == post.x && pre.y == post.y)
}

proof fn correct_init(post: X::State, x: int, y: int, z: int, foo: Foo) {
    requires(X::State::initialize(post, x, y, z, foo));
    ensures(rel_init(post, x, y, z, foo));
}

proof fn rev_init(post: X::State, x: int, y: int, z: int, foo: Foo) {
    requires(rel_init(post, x, y, z, foo));
    ensures(X::State::initialize(post, x, y, z, foo));
}

proof fn correct_tr1(pre: X::State, post: X::State, foo: Foo, c: bool) {
    requires(X::State::tr1(pre, post, foo, c));
    ensures(rel_tr1(pre, post, foo, c));
}

proof fn rev_tr1(pre: X::State, post: X::State, foo: Foo, c: bool) {
    requires(rel_tr1(pre, post, foo, c));
    ensures(X::State::tr1(pre, post, foo, c));
}

proof fn correct_tr1_strong(pre: X::State, post: X::State, foo: Foo, c: bool) {
    requires(X::State::tr1_strong(pre, post, foo, c));
    ensures(rel_tr1_strong(pre, post, foo, c));
}

proof fn rev_tr1_strong(pre: X::State, post: X::State, foo: Foo, c: bool) {
    requires(rel_tr1_strong(pre, post, foo, c));
    ensures(X::State::tr1_strong(pre, post, foo, c));
}

} // verus!
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 SafeX {
    fields {
        #[sharding(variable)] pub x: int,
        #[sharding(variable)] pub y: int,
        #[sharding(variable)] pub z: int,
    }

    init!{
        initialize(x: int, y: int, z: int, foo: Foo) {
            init x = x;
            init y = y;
            require(y <= z);
            match foo {
                Foo::Bar(a) => { init z = z; }
                Foo::Qax(b) => { init z = z + 1; }
                Foo::Duck(d) => { init z = z + 2; }
            }
        }
    }

    transition!{
        tr1(foo: Foo, c: bool) {
            match foo {
                Foo::Bar(a) => { update z = pre.z + 1; }
                Foo::Qax(b) if b == 20 => { assert(pre.y <= pre.z); }
                Foo::Duck(d) => { assert(foo is Duck); }
                _ => { }
            }
            require(c);
        }
    }

    #[invariant]
    pub fn the_inv(self) -> bool { self.y <= self.z }

    #[inductive(initialize)]
    fn init_inductive(post: Self, x: int, y: int, z: int, foo: Foo) { }

    #[inductive(tr1)]
    fn tr1_inductive(pre: Self, post: Self, foo: Foo, c: bool) { }
}}

verus! {

pub proof fn resource_matches() {
    let tracked token = SafeX::Protocol::initialize(0, 1, 2, Foo::Bar(0));
    assert(token.fragment().z == Some(ExclusiveRA::Exclusive(2)));
    let tracked token = SafeX::Protocol::tr1(token, Foo::Bar(0), true);
    assert(token.fragment().z == Some(ExclusiveRA::Exclusive(3)));
    let tracked token = SafeX::Protocol::tr1(token, Foo::Qax(20), true);
    let tracked token = SafeX::Protocol::tr1(token, Foo::Qax(21), true);
    let tracked token = SafeX::Protocol::tr1(token, Foo::Duck(0), true);
    assert(token.fragment().z == Some(ExclusiveRA::Exclusive(3)));
    let tracked qax = SafeX::Protocol::initialize(0, 1, 2, Foo::Qax(0));
    assert(qax.fragment().z == Some(ExclusiveRA::Exclusive(3)));
    let tracked duck = SafeX::Protocol::initialize(0, 1, 2, Foo::Duck(0));
    assert(duck.fragment().z == Some(ExclusiveRA::Exclusive(4)));
}

pub fn demonstration() {
    proof {
        resource_matches();
    }
}

} // verus!
fn main() {
    demonstration();
}
