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
            let a = '\u{0}'.is_ascii();
            assert(a);
            let b = 'A'.is_ascii();
            assert(b);
            let c = '~'.is_ascii();
            assert(c);
            let d = '\u{7F}'.is_ascii();
            assert(d);

            let e = '\u{80}'.is_ascii();
            assert(!e);
            let f = '\u{00E9}'.is_ascii(); // é
            assert(!f);
            let g = '\u{1f600}'.is_ascii(); // 😀, U+1F600
            assert(!g);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = '\u{80}'.is_ascii();
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_to_ascii_uppercase verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'a'.to_ascii_uppercase();
            assert(a == 'A');
            let b = 'z'.to_ascii_uppercase();
            assert(b == 'Z');
            let c = 'm'.to_ascii_uppercase();
            assert(c == 'M');
            let d = 'A'.to_ascii_uppercase();
            assert(d == 'A');
            let e = 'Z'.to_ascii_uppercase();
            assert(e == 'Z');
            let f = '0'.to_ascii_uppercase();
            assert(f == '0');
            let g = '@'.to_ascii_uppercase();
            assert(g == '@');
            let h = '\u{00e9}'.to_ascii_uppercase(); // é, non-ASCII
            assert(h == '\u{00e9}');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_to_ascii_uppercase_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'a'.to_ascii_uppercase();
            assert(a == 'a'); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_to_ascii_lowercase verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'A'.to_ascii_lowercase();
            assert(a == 'a');
            let b = 'Z'.to_ascii_lowercase();
            assert(b == 'z');
            let c = 'M'.to_ascii_lowercase();
            assert(c == 'm');
            let d = 'a'.to_ascii_lowercase();
            assert(d == 'a');
            let e = 'z'.to_ascii_lowercase();
            assert(e == 'z');
            let f = '0'.to_ascii_lowercase();
            assert(f == '0');
            let g = '@'.to_ascii_lowercase();
            assert(g == '@');
            let h = '\u{00C9}'.to_ascii_lowercase(); // É, non-ASCII
            assert(h == '\u{00C9}');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_to_ascii_lowercase_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'A'.to_ascii_lowercase();
            assert(a == 'A'); // FAILS
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
        // broadcast use vstd::std_specs::char::lemma_to_ascii_uppercase;
        use vstd::std_specs::char::to_ascii_uppercase;

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
            let a = 'A'.is_ascii_alphabetic();
            assert(a);
            let b = 'Z'.is_ascii_alphabetic();
            assert(b);
            let c = 'a'.is_ascii_alphabetic();
            assert(c);
            let d = 'z'.is_ascii_alphabetic();
            assert(d);
            let e = '@'.is_ascii_alphabetic(); // before 'A'
            assert(!e);
            let f = '['.is_ascii_alphabetic(); // after 'Z'
            assert(!f);
            let g = '`'.is_ascii_alphabetic(); // before 'a'
            assert(!g);
            let h = '{'.is_ascii_alphabetic(); // after 'z'
            assert(!h);
            let i = '0'.is_ascii_alphabetic();
            assert(!i);
            let j = '\u{00e9}'.is_ascii_alphabetic(); // é, alphabetic but non-ASCII
            assert(!j);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_alphabetic_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = '0'.is_ascii_alphabetic();
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_uppercase verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'A'.is_ascii_uppercase();
            assert(a);
            let b = 'Z'.is_ascii_uppercase();
            assert(b);
            let c = '@'.is_ascii_uppercase(); // before 'A'
            assert(!c);
            let d = '['.is_ascii_uppercase(); // after 'Z'
            assert(!d);
            let e = 'a'.is_ascii_uppercase();
            assert(!e);
            let f = '0'.is_ascii_uppercase();
            assert(!f);
            let g = '\u{00c9}'.is_ascii_uppercase(); // É, uppercase but non-ASCII
            assert(!g);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_uppercase_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'a'.is_ascii_uppercase();
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_lowercase verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'a'.is_ascii_lowercase();
            assert(a);
            let b = 'z'.is_ascii_lowercase();
            assert(b);
            let c = '`'.is_ascii_lowercase(); // before 'a'
            assert(!c);
            let d = '{'.is_ascii_lowercase(); // after 'z'
            assert(!d);
            let e = 'A'.is_ascii_lowercase();
            assert(!e);
            let f = '0'.is_ascii_lowercase();
            assert(!f);
            let g = '\u{00e9}'.is_ascii_lowercase(); // é, lowercase but non-ASCII
            assert(!g);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_lowercase_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'A'.is_ascii_lowercase();
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_alphanumeric verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'A'.is_ascii_alphanumeric();
            assert(a);
            let b = 'Z'.is_ascii_alphanumeric();
            assert(b);
            let c = 'a'.is_ascii_alphanumeric();
            assert(c);
            let d = 'z'.is_ascii_alphanumeric();
            assert(d);
            let e = '0'.is_ascii_alphanumeric();
            assert(e);
            let f = '9'.is_ascii_alphanumeric();
            assert(f);
            let g = '@'.is_ascii_alphanumeric(); // before 'A'
            assert(!g);
            let h = '['.is_ascii_alphanumeric(); // after 'Z'
            assert(!h);
            let i = '`'.is_ascii_alphanumeric(); // before 'a'
            assert(!i);
            let j = '{'.is_ascii_alphanumeric(); // after 'z'
            assert(!j);
            let k = '/'.is_ascii_alphanumeric(); // before '0'
            assert(!k);
            let l = ':'.is_ascii_alphanumeric(); // after '9'
            assert(!l);

            let m = '\u{00e9}'.is_ascii_alphanumeric(); // é, non-ASCII alphabetic
            assert(!m);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_alphanumeric_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = '@'.is_ascii_alphanumeric();
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_digit verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = '0'.is_ascii_digit();
            assert(a);
            let b = '9'.is_ascii_digit();
            assert(b);

            let c = '/'.is_ascii_digit(); // before '0'
            assert(!c);
            let d = ':'.is_ascii_digit(); // after '9'
            assert(!d);

            let e = 'A'.is_ascii_digit();
            assert(!e);
            let f = '\u{0660}'.is_ascii_digit(); // Arabic-Indic digit zero, non-ASCII
            assert(!f);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_digit_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'A'.is_ascii_digit();
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_hexdigit verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = '0'.is_ascii_hexdigit();
            assert(a);
            let b = '9'.is_ascii_hexdigit();
            assert(b);
            let c = 'A'.is_ascii_hexdigit();
            assert(c);
            let d = 'F'.is_ascii_hexdigit();
            assert(d);
            let e = 'a'.is_ascii_hexdigit();
            assert(e);
            let f = 'f'.is_ascii_hexdigit();
            assert(f);
            let g = '/'.is_ascii_hexdigit();
            assert(!g);
            let h = ':'.is_ascii_hexdigit();
            assert(!h);
            let i = 'G'.is_ascii_hexdigit();
            assert(!i);
            let j = 'g'.is_ascii_hexdigit();
            assert(!j);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_hexdigit_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'G'.is_ascii_hexdigit();
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_punctuation verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = '!'.is_ascii_punctuation();
            assert(a);
            let b = '/'.is_ascii_punctuation();
            assert(b);
            let c = ':'.is_ascii_punctuation();
            assert(c);
            let d = '@'.is_ascii_punctuation();
            assert(d);
            let e = '['.is_ascii_punctuation();
            assert(e);
            let f = '`'.is_ascii_punctuation();
            assert(f);
            let g = '{'.is_ascii_punctuation();
            assert(g);
            let h = '~'.is_ascii_punctuation();
            assert(h);
            let i = ' '.is_ascii_punctuation();
            assert(!i);
            let j = '0'.is_ascii_punctuation();
            assert(!j);
            let k = 'A'.is_ascii_punctuation();
            assert(!k);
            let l = 'a'.is_ascii_punctuation();
            assert(!l);
            let m = '\u{7f}'.is_ascii_punctuation();
            assert(!m);
            let n = '\u{00a1}'.is_ascii_punctuation(); // ¡, non-ASCII
            assert(!n);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_punctuation_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = 'A'.is_ascii_punctuation();
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_graphic verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = '!'.is_ascii_graphic();
            assert(a);
            let b = '~'.is_ascii_graphic();
            assert(b);
            let c = 'A'.is_ascii_graphic();
            assert(c);
            let d = '0'.is_ascii_graphic();
            assert(d);
            let e = ' '.is_ascii_graphic();
            assert(!e);
            let f = '\u{7f}'.is_ascii_graphic();
            assert(!f);
            let g = '\n'.is_ascii_graphic();
            assert(!g);
            let h = '\u{00e9}'.is_ascii_graphic(); // é, non-ASCII
            assert(!h);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_graphic_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = ' '.is_ascii_graphic();
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_whitespace verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = '\u{9}'.is_ascii_whitespace(); // TAB
            assert(a);
            let b = '\u{A}'.is_ascii_whitespace(); // LF
            assert(b);
            let c = '\u{C}'.is_ascii_whitespace(); // FF
            assert(c);
            let d = '\u{D}'.is_ascii_whitespace(); // CR
            assert(d);
            let e = ' '.is_ascii_whitespace(); // SPACE
            assert(e);
            let f = '\u{B}'.is_ascii_whitespace(); // VERTICAL TAB
            assert(!f);
            let g = 'A'.is_ascii_whitespace();
            assert(!g);
            let h = '\u{3000}'.is_ascii_whitespace(); // IDEOGRAPHIC SPACE
            assert(!h);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_whitespace_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = '\u{B}'.is_ascii_whitespace();
            assert(a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_is_ascii_control verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = '\u{0}'.is_ascii_control(); // NUL
            assert(a);
            let b = '\u{1F}'.is_ascii_control(); // UNIT SEPARATOR
            assert(b);
            let c = '\u{7F}'.is_ascii_control(); // DELETE
            assert(c);
            let d = ' '.is_ascii_control();
            assert(!d);
            let e = '~'.is_ascii_control();
            assert(!e);
            let f = '\u{80}'.is_ascii_control();
            assert(!f);
            let g = '\u{85}'.is_ascii_control(); // Unicode control, but non-ASCII
            assert(!g);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_is_ascii_control_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let a = ' '.is_ascii_control();
            assert(a); // FAILS
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
