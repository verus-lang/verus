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

test_verify_one_file! {
    #[test] test_char_is_ascii verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('\u{0}'.is_ascii());
            assert('A'.is_ascii());
            assert('~'.is_ascii());
            assert('\u{7F}'.is_ascii());

            assert(!'\u{80}'.is_ascii());
            assert(!'\u{00E9}'.is_ascii()); // é
            assert(!'\u{1f600}'.is_ascii()); // 😀, U+1F600
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('\u{80}'.is_ascii()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_to_ascii_uppercase verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('a'.to_ascii_uppercase() == 'A');
            assert('z'.to_ascii_uppercase() == 'Z');
            assert('m'.to_ascii_uppercase() == 'M');
            assert('A'.to_ascii_uppercase() == 'A');
            assert('Z'.to_ascii_uppercase() == 'Z');
            assert('0'.to_ascii_uppercase() == '0');
            assert('@'.to_ascii_uppercase() == '@');
            assert('\u{00e9}'.to_ascii_uppercase() == '\u{00e9}'); // é, non-ASCII
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_to_ascii_uppercase_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('a'.to_ascii_uppercase() == 'a'); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_to_ascii_lowercase verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('A'.to_ascii_lowercase() == 'a');
            assert('Z'.to_ascii_lowercase() == 'z');
            assert('M'.to_ascii_lowercase() == 'm');
            assert('a'.to_ascii_lowercase() == 'a');
            assert('z'.to_ascii_lowercase() == 'z');
            assert('0'.to_ascii_lowercase() == '0');
            assert('@'.to_ascii_lowercase() == '@');
            assert('\u{00C9}'.to_ascii_lowercase() == '\u{00C9}'); // É, non-ASCII
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_to_ascii_lowercase_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('A'.to_ascii_lowercase() == 'A'); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_eq_ignore_ascii_case verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'A'.eq_ignore_ascii_case(&'a');
            assert(a);
            let b = 'Z'.eq_ignore_ascii_case(&'z');
            assert(b);
            let c = 'm'.eq_ignore_ascii_case(&'M');
            assert(c);
            let d = 'A'.eq_ignore_ascii_case(&'A');
            assert(d);
            let e = '0'.eq_ignore_ascii_case(&'0');
            assert(e);
            let f = '@'.eq_ignore_ascii_case(&'@');
            assert(f);
            let g = 'A'.eq_ignore_ascii_case(&'B');
            assert(!g);
            let h = 'a'.eq_ignore_ascii_case(&'b');
            assert(!h);
            let i = '0'.eq_ignore_ascii_case(&'1');
            assert(!i);
            let j = '\u{00C9}'.eq_ignore_ascii_case(&'\u{00E9}'); // É vs é
            assert(!j);
            let k = '\u{00E9}'.eq_ignore_ascii_case(&'\u{00E9}');
            assert(k);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_eq_ignore_ascii_case_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'A'.eq_ignore_ascii_case(&'B');
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_make_ascii_uppercase verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut a = 'a';
            a.make_ascii_uppercase();
            assert(a == 'A');
            let mut b = 'z';
            b.make_ascii_uppercase();
            assert(b == 'Z');
            let mut c = 'm';
            c.make_ascii_uppercase();
            assert(c == 'M');
            let mut d = 'A';
            d.make_ascii_uppercase();
            assert(d == 'A');
            let mut e = '0';
            e.make_ascii_uppercase();
            assert(e == '0');
            let mut f = '@';
            f.make_ascii_uppercase();
            assert(f == '@');
            let mut g = '\u{00e9}'; // é, non-ASCII
            g.make_ascii_uppercase();
            assert(g == '\u{00e9}');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_make_ascii_uppercase_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut a = 'a';
            a.make_ascii_uppercase();
            assert(a == 'a'); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_make_ascii_lowercase verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut a = 'A';
            a.make_ascii_lowercase();
            assert(a == 'a');
            let mut b = 'Z';
            b.make_ascii_lowercase();
            assert(b == 'z');
            let mut c = 'M';
            c.make_ascii_lowercase();
            assert(c == 'm');
            let mut d = 'a';
            d.make_ascii_lowercase();
            assert(d == 'a');
            let mut e = '0';
            e.make_ascii_lowercase();
            assert(e == '0');
            let mut f = '@';
            f.make_ascii_lowercase();
            assert(f == '@');
            let mut g = '\u{00C9}'; // É, non-ASCII
            g.make_ascii_lowercase();
            assert(g == '\u{00C9}');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_make_ascii_lowercase_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut a = 'A';
            a.make_ascii_lowercase();
            assert(a == 'A'); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_alphabetic verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('A'.is_ascii_alphabetic());
            assert('Z'.is_ascii_alphabetic());
            assert('a'.is_ascii_alphabetic());
            assert('z'.is_ascii_alphabetic());
            assert(!'@'.is_ascii_alphabetic()); // before 'A'
            assert(!'['.is_ascii_alphabetic()); // after 'Z'
            assert(!'`'.is_ascii_alphabetic()); // before 'a'
            assert(!'{'.is_ascii_alphabetic()); // after 'z'
            assert(!'0'.is_ascii_alphabetic());
            assert(!'\u{00e9}'.is_ascii_alphabetic()); // é, alphabetic but non-ASCII
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_alphabetic_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('0'.is_ascii_alphabetic()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_uppercase verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('A'.is_ascii_uppercase());
            assert('Z'.is_ascii_uppercase());
            assert(!'@'.is_ascii_uppercase()); // before 'A'
            assert(!'['.is_ascii_uppercase()); // after 'Z'
            assert(!'a'.is_ascii_uppercase());
            assert(!'0'.is_ascii_uppercase());
            assert(!'\u{00c9}'.is_ascii_uppercase()); // É, uppercase but non-ASCII
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_uppercase_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('a'.is_ascii_uppercase()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_lowercase verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('a'.is_ascii_lowercase());
            assert('z'.is_ascii_lowercase());
            assert(!'`'.is_ascii_lowercase()); // before 'a'
            assert(!'{'.is_ascii_lowercase()); // after 'z'
            assert(!'A'.is_ascii_lowercase());
            assert(!'0'.is_ascii_lowercase());
            assert(!'\u{00e9}'.is_ascii_lowercase()); // é, lowercase but non-ASCII
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_lowercase_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('A'.is_ascii_lowercase()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_alphanumeric verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('A'.is_ascii_alphanumeric());
            assert('Z'.is_ascii_alphanumeric());
            assert('a'.is_ascii_alphanumeric());
            assert('z'.is_ascii_alphanumeric());
            assert('0'.is_ascii_alphanumeric());
            assert('9'.is_ascii_alphanumeric());
            assert(!'@'.is_ascii_alphanumeric()); // before 'A'
            assert(!'['.is_ascii_alphanumeric()); // after 'Z'
            assert(!'`'.is_ascii_alphanumeric()); // before 'a'
            assert(!'{'.is_ascii_alphanumeric()); // after 'z'
            assert(!'/'.is_ascii_alphanumeric()); // before '0'
            assert(!':'.is_ascii_alphanumeric()); // after '9'

            assert(!'\u{00e9}'.is_ascii_alphanumeric()); // é, non-ASCII alphabetic
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_alphanumeric_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('@'.is_ascii_alphanumeric()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_digit verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('0'.is_ascii_digit());
            assert('9'.is_ascii_digit());

            assert(!'/'.is_ascii_digit()); // before '0'
            assert(!':'.is_ascii_digit()); // after '9'

            assert(!'A'.is_ascii_digit());
            assert(!'\u{0660}'.is_ascii_digit()); // Arabic-Indic digit zero, non-ASCII
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_digit_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('A'.is_ascii_digit()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_hexdigit verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('0'.is_ascii_hexdigit());
            assert('9'.is_ascii_hexdigit());
            assert('A'.is_ascii_hexdigit());
            assert('F'.is_ascii_hexdigit());
            assert('a'.is_ascii_hexdigit());
            assert('f'.is_ascii_hexdigit());
            assert(!'/'.is_ascii_hexdigit());
            assert(!':'.is_ascii_hexdigit());
            assert(!'G'.is_ascii_hexdigit());
            assert(!'g'.is_ascii_hexdigit());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_hexdigit_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('G'.is_ascii_hexdigit()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_punctuation verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('!'.is_ascii_punctuation());
            assert('/'.is_ascii_punctuation());
            assert(':'.is_ascii_punctuation());
            assert('@'.is_ascii_punctuation());
            assert('['.is_ascii_punctuation());
            assert('`'.is_ascii_punctuation());
            assert('{'.is_ascii_punctuation());
            assert('~'.is_ascii_punctuation());
            assert(!' '.is_ascii_punctuation());
            assert(!'0'.is_ascii_punctuation());
            assert(!'A'.is_ascii_punctuation());
            assert(!'a'.is_ascii_punctuation());
            assert(!'\u{7f}'.is_ascii_punctuation());
            assert(!'\u{00a1}'.is_ascii_punctuation()); // ¡, non-ASCII
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_punctuation_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('A'.is_ascii_punctuation()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_graphic verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('!'.is_ascii_graphic());
            assert('~'.is_ascii_graphic());
            assert('A'.is_ascii_graphic());
            assert('0'.is_ascii_graphic());
            assert(!' '.is_ascii_graphic());
            assert(!'\u{7f}'.is_ascii_graphic());
            assert(!'\n'.is_ascii_graphic());
            assert(!'\u{00e9}'.is_ascii_graphic()); // é, non-ASCII
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_graphic_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert(' '.is_ascii_graphic()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_whitespace verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('\u{9}'.is_ascii_whitespace()); // TAB
            assert('\u{A}'.is_ascii_whitespace()); // LF
            assert('\u{C}'.is_ascii_whitespace()); // FF
            assert('\u{D}'.is_ascii_whitespace()); // CR
            assert(' '.is_ascii_whitespace()); // SPACE
            assert(!'\u{B}'.is_ascii_whitespace()); // VERTICAL TAB
            assert(!'A'.is_ascii_whitespace());
            assert(!'\u{3000}'.is_ascii_whitespace()); // IDEOGRAPHIC SPACE
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_whitespace_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('\u{B}'.is_ascii_whitespace()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_control verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert('\u{0}'.is_ascii_control()); // NUL
            assert('\u{1F}'.is_ascii_control()); // UNIT SEPARATOR
            assert('\u{7F}'.is_ascii_control()); // DELETE
            assert(!' '.is_ascii_control());
            assert(!'~'.is_ascii_control());
            assert(!'\u{80}'.is_ascii_control());
            assert(!'\u{85}'.is_ascii_control()); // Unicode control, but non-ASCII
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_control_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            assert(' '.is_ascii_control()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
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

test_verify_one_file! {
    #[test] char_ord verus_code! {
        use vstd::prelude::*;
        use core::cmp::Ordering;

        fn test(a: char, b: char) {
            let m = a.max(b);
            assert(m >= a && m >= b && (m == a || m == b));
            let n = a.min(b);
            assert(n <= a && n <= b && (n == a || n == b));
            let o = a.cmp(&b);
            assert(o == Ordering::Less <==> a < b);
            let c = 'x'.clamp('a', 'f');
            assert(c == 'f');
        }

        fn test_fails(a: char, b: char) {
            let m = a.max(b);
            assert(m == a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
