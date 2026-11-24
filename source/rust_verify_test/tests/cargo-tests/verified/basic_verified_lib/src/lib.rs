use vstd::prelude::*;
use vstd::atomic::*;

verus! {

// Library function for use in verified and unverified functions
pub fn double(x: u16) -> (z: u32)
    ensures z == x * 2,
{
    x as u32 + x as u32
}

pub trait OpaqueTrait { }

struct OpaqueHidden;

impl OpaqueTrait for OpaqueHidden { }

pub fn opaque_hidden() -> impl OpaqueTrait {
    OpaqueHidden
}

// Some corner cases that have been problematic for cargo-verus in the past

trait Trait: View {}

impl<T: View> Trait for Option<T> {}

fn test(f: spec_fn(nat) -> nat) {}

mod IsNotRegressionIssue1573 {
    enum Test {
        A,
        B,
    }

    spec fn is_not_a(t: Test) -> bool {
        t !is A
    }

    spec fn is_a(t: Test) -> bool {
        t is A
    }
}

// Simple logically atomic library function

pub tracked struct Token {
    pub value: u32,
}

pub fn logatom_function()
    atomically (au) {
        type PredType,
        (x: Token) -> (y: Commit<Token>),
        ensures y@ == x,
    }
{
    try_open_atomic_update!(au, token => {
        Tracked(Commit(token))
    });
}

} // verus!
