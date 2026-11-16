#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] u8_ascii_classes verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::ascii::*;

        fn test_digit() {
            assert(b'7'.is_ascii_digit());
            assert(!b'a'.is_ascii_digit());
            assert(b'a'.is_ascii_hexdigit());
            assert(b'F'.is_ascii_hexdigit());
            assert(!b'g'.is_ascii_hexdigit());
            let d = b'5'.is_ascii_digit();
            assert(d);
        }

        fn digit_value(b: u8) -> (r: u8)
            requires b.is_ascii_digit(),
            ensures r < 10,
        {
            b - b'0'
        }

        fn test_parse(b: u8) -> (r: Option<u8>)
            ensures r.is_some() ==> r.unwrap() < 10,
        {
            if b.is_ascii_digit() {
                Some(b - b'0')
            } else {
                None
            }
        }

        fn test_alnum(b: u8)
            requires b.is_ascii_alphanumeric(),
        {
            assert(b.is_ascii_alphabetic() || b.is_ascii_digit());
            assert(b.is_ascii());
            assert(b.is_ascii_graphic());
            assert(!b.is_ascii_punctuation());
            assert(!b.is_ascii_whitespace());
            assert(!b.is_ascii_control());
        }

        fn test_classes() {
            assert(b'Q'.is_ascii_uppercase());
            assert(!b'q'.is_ascii_uppercase());
            assert(b'q'.is_ascii_lowercase());
            assert(b'!'.is_ascii_punctuation());
            assert(b' '.is_ascii_whitespace());
            assert(!0x0Bu8.is_ascii_whitespace());
            assert(0x7Fu8.is_ascii_control());
            assert(!0x80u8.is_ascii());
            assert(u8_is_ascii_digit(b'0'));
        }

        fn test_no_unwind(b: u8)
            no_unwind
        {
            let _ = b.is_ascii();
            let _ = b.is_ascii_digit();
            let _ = b.is_ascii_hexdigit();
            let _ = b.is_ascii_alphanumeric();
            let _ = b.is_ascii_alphabetic();
            let _ = b.is_ascii_uppercase();
            let _ = b.is_ascii_lowercase();
            let _ = b.is_ascii_punctuation();
            let _ = b.is_ascii_graphic();
            let _ = b.is_ascii_whitespace();
            let _ = b.is_ascii_control();
        }

        fn test_wrong() {
            assert(b'x'.is_ascii_hexdigit()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] u8_ascii_case verus_code! {
        use vstd::prelude::*;

        fn test_values() {
            let u = b'a'.to_ascii_uppercase();
            assert(u == b'A');
            let l = b'Z'.to_ascii_lowercase();
            assert(l == b'z');
            let same = b'3'.to_ascii_uppercase();
            assert(same == b'3');
            let hi = 0xE9u8.to_ascii_uppercase();
            assert(hi == 0xE9u8);
        }

        fn test_round_trip(b: u8)
            requires b.is_ascii_lowercase(),
        {
            let u = b.to_ascii_uppercase();
            assert(u.is_ascii_uppercase());
            let l = u.to_ascii_lowercase();
            assert(l == b);
        }

        fn test_eq_ignore_case() {
            let e = b'k'.eq_ignore_ascii_case(&b'K');
            assert(e);
            let n = b'k'.eq_ignore_ascii_case(&b'L');
            assert(!n);
        }

        fn test_make(b: u8) {
            let mut x = b;
            x.make_ascii_lowercase();
            assert(!x.is_ascii_uppercase());
            let mut y = b'm';
            y.make_ascii_uppercase();
            assert(y == b'M');
        }

        fn test_no_unwind(b: u8)
            no_unwind
        {
            let _ = b.to_ascii_uppercase();
            let _ = b.to_ascii_lowercase();
            let _ = b.eq_ignore_ascii_case(&b);
            let mut c = b;
            c.make_ascii_uppercase();
            c.make_ascii_lowercase();
        }

        fn test_wrong() {
            let u = b'a'.to_ascii_lowercase();
            assert(u == b'A'); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
