#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_char_is_whitespace verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = ' '.is_whitespace();
            assert(a);
            let b = '\u{3000}'.is_whitespace(); // IDEOGRAPHIC SPACE
            assert(b);
            let c = 'a'.is_whitespace();
            assert(!c);
            let d = '\u{2010}'.is_whitespace(); // HYPHEN, not whitespace
            assert(!d);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_whitespace_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'a'.is_whitespace();
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// The length fact (encode_utf8(a + b).len() == encode_utf8(a).len() +
// encode_utf8(b).len()) doesn't need its own lemma - it's a free corollary
// of lemma_encode_utf8_concat's full sequence equality, via Seq's own
// additive-length property.
test_verify_one_file! {
    #[test] test_encode_utf8_concat_length_is_a_free_corollary verus_code! {
        use vstd::prelude::*;
        use vstd::utf8::{encode_utf8, lemma_encode_utf8_concat};

        proof fn test(a: Seq<char>, b: Seq<char>) {
            lemma_encode_utf8_concat(a, b);
            assert(encode_utf8(a + b).len() == encode_utf8(a).len() + encode_utf8(b).len());
        }
    } => Ok(())
}
