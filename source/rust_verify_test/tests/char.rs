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

test_verify_one_file! {
    #[test] test_char_len_utf8 verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'a'.len_utf8(); // ASCII, U+0061
            assert(a == 1);
            let b = '\u{a3}'.len_utf8(); // £, U+00A3
            assert(b == 2);
            let c = '\u{20ac}'.len_utf8(); // €, U+20AC
            assert(c == 3);
            let d = '\u{1f600}'.len_utf8(); // 😀, U+1F600
            assert(d == 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_len_utf8_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'a'.len_utf8();
            assert(a == 2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// #[verifier::allow_in_spec] lets these be called directly in spec position, not just
// through an exec `let` first - the tests above don't exercise that.
test_verify_one_file! {
    #[test] test_char_len_utf8_allow_in_spec verus_code! {
        use vstd::prelude::*;

        proof fn test() {
            assert('a'.len_utf8() == 1); // ASCII, U+0061
            assert('\u{a3}'.len_utf8() == 2); // £, U+00A3
            assert('\u{20ac}'.len_utf8() == 3); // €, U+20AC
            assert('\u{1f600}'.len_utf8() == 4); // 😀, U+1F600
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_whitespace_allow_in_spec verus_code! {
        use vstd::prelude::*;

        proof fn test() {
            assert(' '.is_whitespace());
            assert('\u{3000}'.is_whitespace()); // IDEOGRAPHIC SPACE
            assert(!'a'.is_whitespace());
            assert(!'\u{2010}'.is_whitespace()); // HYPHEN, not whitespace
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] typ_invariant_issue2876 verus_code! {
        fn foo(c: &mut char)
            ensures
                *final(c) as u32 == 'A' as u32,
        {
            *c = 'A';
        }

        fn test_foo() {
            let mut c = 'a';
            foo(&mut c);

            assert(0 <= c as int);
            assert(c <= 0x10ffff);
            assert(c <= 0xD7FF || c >= 0xE000);
        }
    } => Ok(())
}
