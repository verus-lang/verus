#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use verus_builtin_macros::*;

// ANCHOR: basic_trait
#[verifier::external]
trait Encoder {
    fn encode_value(&self, x: u64) -> u64;
}
// ANCHOR_END: basic_trait

verus! {

// ANCHOR: basic_spec
#[verifier::external_trait_specification]
trait ExEncoder {
    // This associated type names the trait being specified:
    type ExternalTraitSpecificationFor: Encoder;

    fn encode_value(&self, x: u64) -> (result: u64)
        ensures
            result >= x;
}
// ANCHOR_END: basic_spec

// ANCHOR: basic_use
fn use_encoder<E: Encoder>(f: &E, val: u64) -> (result: u64)
    ensures
        result >= val,
{
    f.encode_value(val)
}
// ANCHOR_END: basic_use

} // verus!

// ANCHOR: extension_trait
#[verifier::external]
trait Hasher {
    fn finish(&self) -> u64;
    fn write(&mut self, bytes: &[u8]);
}
// ANCHOR_END: extension_trait

verus! {

// ANCHOR: extension_spec
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(SummarizerSpec via SummarizerSpecImpl)]
trait ExSummarizer {
    type ExternalTraitSpecificationFor: Summarizer;

    // A spec helper function (not part of the original trait):
    spec fn spec_summary(&self) -> u64;

    fn summary(&self) -> (result: u64)
        ensures
            result == self.spec_summary();
}
// ANCHOR_END: extension_spec

// ANCHOR: extension_impl
struct MyCustomStruct { value: u64 }

// Implement the concrete external Summarizer trait
impl Summarizer for MyCustomStruct {
    fn summary(&self) -> u64 {
        // Prove that our overly complicated implementation satisfies the spec_summary
        assert(self.value & 0xffff_ffff_ffff_ffff == self.value) by (bit_vector);
        self.value & 0xffff_ffff_ffff_ffff
    }
}

// Implement the additional spec functions
impl SummarizerSpecImpl for MyCustomStruct {
    spec fn spec_summary(&self) -> u64 {
        self.value
    }
}

fn test_hasher(h: &MyCustomStruct) {
    let v = h.summary();
    assert(v == h.value);
}
// ANCHOR_END: extension_impl

} // verus!

fn main() {}
