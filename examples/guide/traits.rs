// rust_verify/tests/example.rs expect-success
use vstd::prelude::*;

verus! {

// ANCHOR: basic_trait
trait Compressor {
    fn compress(&self, input: u64) -> (output: u64)
        ensures output <= input;
}
// ANCHOR_END: basic_trait

// ANCHOR: impl_extends
struct HalfCompressor;

impl Compressor for HalfCompressor {
    // The trait's `ensures output <= input` is automatically inherited.
    // We additionally specify the exact return value.
    fn compress(&self, input: u64) -> (output: u64)
        ensures output == input / 2,
    {
        input / 2
    }
}
// ANCHOR_END: impl_extends

// ANCHOR: dispatch
fn compress_generic<C: Compressor>(c: &C, x: u64) {
    let r = c.compress(x);
    assert(r <= x); // OK: trait-level ensures holds for every C
}

fn compress_concrete(c: &HalfCompressor, x: u64) {
    let r = c.compress(x);
    assert(r <= x);      // From the trait ensures
    assert(r == x / 2);  // From HalfCompressor's stronger ensures (statically resolved)
}
// ANCHOR_END: dispatch

// ANCHOR: requires_ensures
trait Bounded {
    fn clamp(&self, val: u64, lo: u64, hi: u64) -> (result: u64)
        requires lo <= hi,
        ensures lo <= result <= hi;
}
// ANCHOR_END: requires_ensures

// ANCHOR: requires_ensures_impl
struct Saturate;

impl Bounded for Saturate {
    // Inherits: requires lo <= hi, ensures lo <= result <= hi
    // Adds: the exact formula for result
    fn clamp(&self, val: u64, lo: u64, hi: u64) -> (result: u64)
        ensures result == if val < lo { lo } else if val > hi { hi } else { val },
    {
        if val < lo { lo } else if val > hi { hi } else { val }
    }
}
// ANCHOR_END: requires_ensures_impl

// ANCHOR: spec_trait
trait Distance {
    spec fn dist(&self, other: &Self) -> nat;

    fn distance(&self, other: &Self) -> (d: u64)
        ensures
            d as nat == self.dist(other),
    ;

    proof fn valid_distance_metric()
        ensures
            forall |x: &Self, y| x.dist(y) == y.dist(x),
            forall |x: &Self, y| x.dist(y) == 0 <==> x == y,
            forall |x: &Self, y, z| x.dist(y) <= x.dist(z) + z.dist(y),
        ;
}
// ANCHOR_END: spec_trait

// ANCHOR: spec_trait_impl
struct P {
    u: u64
}

impl Distance for P {
    spec fn dist(&self, other: &Self) -> nat {
        vstd::math::abs(self.u - other.u)
    }

    fn distance(&self, other: &Self) -> u64 {
        if self.u > other.u {
            self.u - other.u
        } else {
            other.u - self.u
        }
    }

    proof fn valid_distance_metric() 
    {
    }
}
// ANCHOR_END: spec_trait_impl

// ANCHOR: view_impl
struct Stack {
    data: Vec<u64>,
}

impl View for Stack {
    type V = Seq<u64>;

    closed spec fn view(&self) -> Seq<u64> {
        self.data@
    }
}

impl Stack {
    fn push(&mut self, val: u64)
        ensures final(self)@ == old(self)@.push(val),
    {
        self.data.push(val);
    }

    fn is_empty(&self) -> (result: bool)
        ensures result <==> self@.len() == 0,
    {
        self.data.len() == 0
    }
}
// ANCHOR_END: view_impl

// ANCHOR: default_ensures
trait Reducer {
    // Every implementation must satisfy: output <= input.
    // The default implementation additionally satisfies: output == input / 2.
    fn halve(&self, input: u64) -> (output: u64)
        ensures output <= input,
        default_ensures output == input / 2,
    {
        input / 2
    }
}
// ANCHOR_END: default_ensures

// ANCHOR: default_ensures_impls
struct DefaultReducer;

impl Reducer for DefaultReducer {
    // No override: inherits the default implementation and its default_ensures.
}

struct ThirdReducer;

impl Reducer for ThirdReducer {
    // Overrides with a different strategy.  Only the trait `ensures` (output <= input)
    // applies to callers who don't statically know the type.
    fn halve(&self, input: u64) -> (output: u64)
        ensures output == input / 3,
    {
        input / 3
    }
}
// ANCHOR_END: default_ensures_impls

// ANCHOR: default_ensures_callers
fn call_generic<H: Reducer>(h: &H, x: u64) {
    let r = h.halve(x);
    assert(r <= x);        // From trait ensures — always available
    // assert(r == x / 2); // Would FAIL: not known for arbitrary H
}

fn call_default(h: &DefaultReducer, x: u64) {
    let r = h.halve(x);
    assert(r <= x);     // From trait ensures
    assert(r == x / 2); // From default_ensures (DefaultReducer uses the default impl)
}

fn call_override(h: &ThirdReducer, x: u64) {
    let r = h.halve(x);
    assert(r <= x);        // From trait ensures
    assert(r == x / 3);    // From ThirdReducer's own ensures
    // assert(r == x / 2); // Would FAIL: ThirdReducer overrides, no default_ensures
}
// ANCHOR_END: default_ensures_callers

} // verus!
