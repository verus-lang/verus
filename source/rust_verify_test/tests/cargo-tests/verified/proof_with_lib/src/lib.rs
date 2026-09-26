use vstd::prelude::*;

// The free-function counterpart is exported through crate metadata.
#[verus_spec(ret =>
    with Tracked(expected): Tracked<u8>
    requires x == expected,
    ensures ret == !b,
)]
pub fn negate(b: bool, x: u8) -> bool {
    !b
}

#[verus_verify]
pub struct Counter(pub u8);

// The inherent counterpart remains in the same implementation.
#[verus_verify]
impl Counter {
    #[verus_spec(ret =>
        with Tracked(step): Tracked<u8> -> next: Tracked<u8>
        requires step == 1u8,
        ensures ret == 7u8, next@ == step,
    )]
    pub fn bump(&self) -> u8 {
        proof_with!{|= Tracked(step)}
        7
    }
}

// Trait counterparts and their implementations are exported through a companion trait.
#[verus_verify]
pub trait Doubler {
    #[verus_spec(ret =>
        with Ghost(g): Ghost<u64>
        requires g < 100, a < 100,
        ensures ret == a + a,
    )]
    fn double(&self, a: u64) -> u64;
}

#[verus_verify]
pub struct Twice;

#[verus_verify]
impl Doubler for Twice {
    #[verus_spec(with Ghost(g): Ghost<u64>)]
    fn double(&self, a: u64) -> u64 {
        a + a
    }
}

// The inherent method deliberately shadows the trait method for cross-crate lookup coverage.
#[verus_verify]
pub struct Shadowed;

#[verus_verify]
impl Doubler for Shadowed {
    #[verus_spec(with Ghost(g): Ghost<u64>)]
    fn double(&self, a: u64) -> u64 {
        a + a
    }
}

#[verus_verify]
impl Shadowed {
    #[verus_spec(ret =>
        with Ghost(g): Ghost<u64>
        requires g < 100, a < 100,
        ensures ret == a + 1,
    )]
    pub fn double(&self, a: u64) -> u64 {
        a + 1
    }
}
