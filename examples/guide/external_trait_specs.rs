#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use verus_builtin_macros::*;

// ANCHOR: basic_trait
// Suppose we have an external trait (e.g., from a Rust library crate):
#[verifier::external]
trait Formatter {
    fn format_value(&self, x: u64) -> u64;
}
// ANCHOR_END: basic_trait

verus! {

// ANCHOR: basic_spec
// We can add specifications to it using external_trait_specification:
#[verifier::external_trait_specification]
trait ExFormatter {
    // This associated type names the trait being specified:
    type ExternalTraitSpecificationFor: Formatter;

    fn format_value(&self, x: u64) -> (result: u64)
        ensures
            result >= x;
}
// ANCHOR_END: basic_spec

// ANCHOR: basic_use
// Now verified code can use the trait with its specification:
fn use_formatter<F: Formatter>(f: &F, val: u64) -> (result: u64)
    ensures
        result >= val,
{
    f.format_value(val)
}
// ANCHOR_END: basic_use

} // verus!

// ANCHOR: extension_trait
// Suppose we have another external trait:
#[verifier::external]
trait Hasher {
    fn finish(&self) -> u64;
    fn write(&mut self, bytes: &[u8]);
}
// ANCHOR_END: extension_trait

verus! {

// ANCHOR: extension_spec
// external_trait_extension adds spec helper functions to a trait.
// The syntax is: #[verifier::external_trait_extension(SpecTrait via SpecImplTrait)]
//   - SpecTrait: the name for spec-mode functions on the trait
//   - SpecImplTrait: the trait that concrete types implement

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(HasherSpec via HasherSpecImpl)]
trait ExHasher {
    type ExternalTraitSpecificationFor: Hasher;

    // A spec helper function (not part of the original trait):
    spec fn spec_finish(&self) -> u64;

    fn finish(&self) -> (result: u64)
        ensures
            result == self.spec_finish();

    fn write(&mut self, bytes: &[u8]);
}
// ANCHOR_END: extension_spec

// ANCHOR: extension_impl
// Concrete types implement SpecImplTrait to define the spec helpers:
struct MyHasher { value: u64 }

impl Hasher for MyHasher {
    #[verifier::external_body]
    fn finish(&self) -> u64 { self.value }
    #[verifier::external_body]
    fn write(&mut self, bytes: &[u8]) { }
}

impl HasherSpecImpl for MyHasher {
    spec fn spec_finish(&self) -> u64 {
        self.value
    }
}

fn test_hasher(h: &MyHasher) {
    let v = h.finish();
    assert(v == h.value);
}
// ANCHOR_END: extension_impl

} // verus!

fn main() {}
