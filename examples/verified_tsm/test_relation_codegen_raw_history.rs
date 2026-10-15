//! Complete extracted substantial state-machine test; reference relations retained.
#![allow(unused_imports)]
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::{CountRA, Token};
use vstd::{imap::*, map::*, modes::*, multiset::*, pervasive::*, set::*};
verified_state_machine_model! { X {
    fields {
        pub x: int,
        pub y: int,
        pub z: int,
    }

    init!{
        initialize(x: int, y: int, z: int) {
            init x = x;
            init y = y;
            require(y <= z);
            if x == y {
                init z = z;
            } else {
                init z = z + 1;
            }
        }
    }

    transition!{
        tr1(b: bool, c: bool) {
            require(b);
            assert(pre.y <= pre.z);
            require(c);
            update z = pre.z + 1;
        }
    }

    transition!{
        tr2(b: bool, c: bool) {
            if b {
                update z = pre.z + 1;
            } else {
                assert(pre.y <= pre.z);
            }
            require(c);
        }
    }

    transition!{
        tr3(b: bool, c: bool) {
            if b {
                assert(pre.y <= pre.z);
            } else {
                let j = pre.z + 1;
                update z = j;
            }
            require(c);
        }
    }

    #[invariant]
    pub fn the_inv(self) -> bool { self.y <= self.z }

    #[inductive(initialize)]
    fn init_inductive(post: Self, x: int, y: int, z: int) { }

    #[inductive(tr1)]
    fn tr1_inductive(pre: Self, post: Self, b: bool, c: bool) { }

    #[inductive(tr2)]
    fn tr2_inductive(pre: Self, post: Self, b: bool, c: bool) { }

    #[inductive(tr3)]
    fn tr3_inductive(pre: Self, post: Self, b: bool, c: bool) { }

}}

verus! {

spec fn rel_init(post: X::State, x: int, y: int, z: int) -> bool {
    post.x == x && post.y == y && y <= z && if x == y {
        post.z == z
    } else {
        post.z == z + 1
    }
}

spec fn rel_tr1(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
    &&& b
    &&& pre.y <= pre.z ==> {
        &&& c
        &&& post.z == pre.z + 1
        &&& post.x == pre.x
        &&& post.y == pre.y
    }
}

spec fn rel_tr1_strong(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
    &&& b
    &&& pre.y <= pre.z && {
        &&& c
        &&& post.z == pre.z + 1
        &&& post.x == pre.x
        &&& post.y == pre.y
    }
}

spec fn rel_tr2(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
    &&& (if b {
        post.z == pre.z + 1
    } else {
        pre.y <= pre.z ==> post.z == pre.z
    })
    &&& (!b ==> pre.y <= pre.z) ==> {
        &&& c
        &&& pre.x == post.x
        &&& pre.y == post.y
    }
}

spec fn rel_tr2_strong(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
    &&& (if b {
        post.z == pre.z + 1
    } else {
        post.z == pre.z
    })
    &&& (!b ==> pre.y <= pre.z) && {
        &&& c
        &&& pre.x == post.x
        &&& pre.y == post.y
    }
}

spec fn rel_tr3(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
    &&& (if !b {
        post.z == pre.z + 1
    } else {
        pre.y <= pre.z ==> post.z == pre.z
    })
    &&& (b ==> pre.y <= pre.z) ==> {
        &&& c
        &&& pre.x == post.x
        &&& pre.y == post.y
    }
}

spec fn rel_tr3_strong(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
    &&& (if !b {
        post.z == pre.z + 1
    } else {
        post.z == pre.z
    })
    &&& (b ==> pre.y <= pre.z) && {
        &&& c
        &&& pre.x == post.x
        &&& pre.y == post.y
    }
}

proof fn correct_init(post: X::State, x: int, y: int, z: int) {
    requires(X::State::initialize(post, x, y, z));
    ensures(rel_init(post, x, y, z));
}

proof fn rev_init(post: X::State, x: int, y: int, z: int) {
    requires(rel_init(post, x, y, z));
    ensures(X::State::initialize(post, x, y, z));
}

proof fn correct_tr1(pre: X::State, post: X::State, b: bool, c: bool) {
    requires(X::State::tr1(pre, post, b, c));
    ensures(rel_tr1(pre, post, b, c));
}

proof fn rev_tr1(pre: X::State, post: X::State, b: bool, c: bool) {
    requires(rel_tr1(pre, post, b, c));
    ensures(X::State::tr1(pre, post, b, c));
}

proof fn correct_tr1_strong(pre: X::State, post: X::State, b: bool, c: bool) {
    requires(X::State::tr1_strong(pre, post, b, c));
    ensures(rel_tr1_strong(pre, post, b, c));
}

proof fn rev_tr1_strong(pre: X::State, post: X::State, b: bool, c: bool) {
    requires(rel_tr1_strong(pre, post, b, c));
    ensures(X::State::tr1_strong(pre, post, b, c));
}

proof fn correct_tr2(pre: X::State, post: X::State, b: bool, c: bool) {
    requires(X::State::tr2(pre, post, b, c));
    ensures(rel_tr2(pre, post, b, c));
}

proof fn rev_tr2(pre: X::State, post: X::State, b: bool, c: bool) {
    requires(rel_tr2(pre, post, b, c));
    ensures(X::State::tr2(pre, post, b, c));
}

proof fn correct_tr2_strong(pre: X::State, post: X::State, b: bool, c: bool) {
    requires(X::State::tr2_strong(pre, post, b, c));
    ensures(rel_tr2_strong(pre, post, b, c));
}

proof fn rev_tr2_strong(pre: X::State, post: X::State, b: bool, c: bool) {
    requires(rel_tr2_strong(pre, post, b, c));
    ensures(X::State::tr2_strong(pre, post, b, c));
}

proof fn correct_tr3(pre: X::State, post: X::State, b: bool, c: bool) {
    requires(X::State::tr3(pre, post, b, c));
    ensures(rel_tr3(pre, post, b, c));
}

proof fn rev_tr3(pre: X::State, post: X::State, b: bool, c: bool) {
    requires(rel_tr3(pre, post, b, c));
    ensures(X::State::tr3(pre, post, b, c));
}

proof fn correct_tr3_strong(pre: X::State, post: X::State, b: bool, c: bool) {
    requires(X::State::tr3_strong(pre, post, b, c));
    ensures(rel_tr3_strong(pre, post, b, c));
}

proof fn rev_tr3_strong(pre: X::State, post: X::State, b: bool, c: bool) {
    requires(rel_tr3_strong(pre, post, b, c));
    ensures(X::State::tr3_strong(pre, post, b, c));
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
        initialize(x: int, y: int, z: int) {
            init x = x;
            init y = y;
            require(y <= z);
            if x == y {
                init z = z;
            } else {
                init z = z + 1;
            }
        }
    }

    transition!{
        tr1(b: bool, c: bool) {
            require(b);
            assert(pre.y <= pre.z);
            require(c);
            update z = pre.z + 1;
        }
    }

    transition!{
        tr2(b: bool, c: bool) {
            if b {
                update z = pre.z + 1;
            } else {
                assert(pre.y <= pre.z);
            }
            require(c);
        }
    }

    transition!{
        tr3(b: bool, c: bool) {
            if b {
                assert(pre.y <= pre.z);
            } else {
                let j = pre.z + 1;
                update z = j;
            }
            require(c);
        }
    }

    #[invariant]
    pub fn the_inv(self) -> bool { self.y <= self.z }

    #[inductive(initialize)]
    fn init_inductive(post: Self, x: int, y: int, z: int) { }

    #[inductive(tr1)]
    fn tr1_inductive(pre: Self, post: Self, b: bool, c: bool) { }

    #[inductive(tr2)]
    fn tr2_inductive(pre: Self, post: Self, b: bool, c: bool) { }

    #[inductive(tr3)]
    fn tr3_inductive(pre: Self, post: Self, b: bool, c: bool) { }

}}

verus! {

pub proof fn resource_branches() {
    let tracked token = SafeX::Protocol::initialize(0, 1, 2);
    assert(token.fragment().z == Some(ExclusiveRA::Exclusive(3)));
    let tracked token = SafeX::Protocol::tr1(token, true, true);
    assert(token.fragment().z == Some(ExclusiveRA::Exclusive(4)));
    let tracked token = SafeX::Protocol::tr2(token, true, true);
    assert(token.fragment().z == Some(ExclusiveRA::Exclusive(5)));
    let tracked token = SafeX::Protocol::tr2(token, false, true);
    assert(token.fragment().z == Some(ExclusiveRA::Exclusive(5)));
    let tracked token = SafeX::Protocol::tr3(token, true, true);
    assert(token.fragment().z == Some(ExclusiveRA::Exclusive(5)));
    let tracked token = SafeX::Protocol::tr3(token, false, true);
    assert(token.fragment().z == Some(ExclusiveRA::Exclusive(6)));
    let tracked equal = SafeX::Protocol::initialize(1, 1, 2);
    assert(equal.fragment().z == Some(ExclusiveRA::Exclusive(2)));
}

pub fn demonstration() {
    proof {
        resource_branches();
    }
}

} // verus!
fn main() {
    demonstration();
}
