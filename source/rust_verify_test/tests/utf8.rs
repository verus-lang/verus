#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// The length fact (encode_utf8(a + b).len() == encode_utf8(a).len() +
// encode_utf8(b).len()) doesn't need its own lemma - it's a free corollary
// of encode_utf8_concat's full sequence equality, via Seq's own
// additive-length property.
test_verify_one_file! {
    #[test] test_encode_utf8_concat_length_is_a_free_corollary verus_code! {
        use vstd::prelude::*;
        use vstd::utf8::encode_utf8;

        proof fn test(a: Seq<char>, b: Seq<char>) {
            broadcast use vstd::utf8::group_utf8_lib;

            assert(encode_utf8(a + b).len() == encode_utf8(a).len() + encode_utf8(b).len());
        }
    } => Ok(())
}
