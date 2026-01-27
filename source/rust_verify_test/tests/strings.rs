#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_pass_is_ascii verus_code! {
    #[allow(unused_imports)]
    use vstd::string::*;

    fn str_is_ascii_passes() {
        let x = ("Hello World");
        proof {
            reveal_strlit("Hello World");
        }
        assert(x.is_ascii());
    }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails_is_ascii verus_code! {
        use vstd::string::*;
        fn str_is_ascii_fails() {
            let x = ("à");
            proof {
                reveal_strlit("à");
            }
            assert(x.is_ascii()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_pass_get_char verus_code! {
        use vstd::string::*;
        fn get_char() {
            let x = ("hello world");
            proof {
                reveal_strlit("hello world");
            }
            assert(x@.len() == 11);
            let val = x.get_char(0);
            assert('h' === val);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fail_get_char verus_code! {
        use vstd::string::*;
        fn get_char_fails() {
            let x = ("hello world");
            let val = x.get_char(0); // FAILS
            assert(val === 'h'); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_passes_len verus_code! {
        use vstd::string::*;

        pub fn len_passes() {
            let x = ("abcdef");
            proof {
                reveal_strlit("abcdef");
            }
            assert(x@.len() === 6);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails_len verus_code! {
        use vstd::string::*;

        pub fn len_fails() {
            let x = ("abcdef");
            proof {
                reveal_strlit("abcdef");
            }
            assert(x@.len() == 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_passes_substring verus_code! {
        use vstd::string::*;
        fn test_substring_passes<'a>() -> (ret: &'a str)
            ensures
                ret@.subrange(0,5) =~= ("Hello")@
        {
            proof {
                reveal_strlit("Hello");
                reveal_strlit("Hello World");
            }
            ("Hello World")

        }

        fn test_substring_passes2<'a>() -> (ret: &'a str)
            ensures
                ret@.subrange(0,5) =~= ("Hello")@
        {
            let x = ("Hello World");

            proof {
                reveal_strlit("Hello");
                reveal_strlit("Hello World");
            }

            x.substring_ascii(0,5)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails_substring verus_code! {
        use vstd::string::*;
        fn test_substring_fails<'a>() -> (ret: &'a str)
            ensures
                ret@.subrange(0,5) =~= ("Hello")@ // FAILS
        {
            proof {
                reveal_strlit("Hello");
                reveal_strlit("Gello World");
            }
            ("Gello World")
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_passes_multi verus_code! {
        use vstd::string::*;

        fn test_multi_passes() {
            let a = ("a");
            let a_clone = ("a");
            let b = ("b");
            let c = ("c");
            let abc = ("abc");
            let cba = ("cba");
            let abc_clone = ("abc");

            proof {
                reveal_strlit("a");
                reveal_strlit("b");
                reveal_strlit("c");
                reveal_strlit("d");
                reveal_strlit("abc");
                reveal_strlit("cba");
            }

            let a0 = a.get_char(0);
            let a0_clone = a_clone.get_char(0);
            let b0 = a.get_char(0);
            let c0 = a.get_char(0);

            assert(a !== b);
            assert(b !== c);
            assert(a === a);
            assert(a0_clone === a0);

            assert(a@ =~= abc@.subrange(0,1));
            assert(b@ =~= abc@.subrange(1,2));
            assert(c@ =~= abc@.subrange(2,3));

            assert(cba !== abc);
            assert(abc === abc_clone);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails_multi verus_code! {
        use vstd::string::*;
        const x: &'static str = "Hello World";
        const y: &'static str = "Gello World";
        const z: &'static str = "Insert string here";

        fn test_multi_fails1() {
            assert(x@.len() === 11); // FAILS
        }

        fn test_multi_fails2() {
            assert(x@.len() !== 11) // FAILS
        }

        fn test_multi_fails3() {
            assert(x === y); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_reveal_strlit_invalid_1 verus_code! {
        use vstd::string::*;
        fn test() {
            proof {
                reveal_strlit(12u32);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "string literal expected")
}

test_verify_one_file! {
    #[test] test_reveal_strlit_invalid_2 verus_code! {
        use vstd::string::*;
        fn test() {
            proof {
                reveal_strlit("a", "a");
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "this function takes 1 argument but 2 arguments were supplied")
}

test_verify_one_file! {
    #[test] test_string_1_pass verus_code! {
        use vstd::string::*;
        fn test() {
            let a = String::from_str(("A"));
            proof {
                reveal_strlit("A");
            }
            assert(a@ === ("A")@);
            assert(a.is_ascii());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_1_fail verus_code! {
        use vstd::string::*;
        fn test() {
            let a = String::from_str(("A"));
            proof {
                reveal_strlit("A");
            }
            assert(a@ === ("B")@); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_strlit_neq verus_code! {
        use vstd::string::*;
        const x: &'static str = "Hello World";
        const y: &'static str = "Gello World";
        fn test() {
            assert(x !== y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_strlit_neq_soundness verus_code! {
        use vstd::string::*;
        const x: &'static str = "Hello World";
        const y: &'static str = "Gello World";
        fn test() {
            assert(x !== y);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_passes verus_code! {
        fn test_char_passes() {
            let c = 'c';
            assert(c == 'c');
        }
        fn test_char_passes1() {
            let c = 'c';
            assert(c != 'b');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_fails verus_code! {
        fn test_char_fails() {
            let c = 'c';
            assert(c == 'a'); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_unicode_passes verus_code! {
        fn test_char_unicode_passes() {
            let a = '💩';
            assert(a == '💩');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_len_return_passes verus_code! {
        use vstd::string::*;
        fn test_len_return_passes<'a>() -> (ret: usize)
            ensures
                ret == 4
        {
            proof {
                reveal_strlit("abcd");
            }
            ("abcd").unicode_len()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_get_unicode_passes verus_code! {
        use vstd::string::*;
        fn test_get_unicode_passes() {
            let x = ("Hello");
            proof {
                reveal_strlit("Hello");
            }
            let x0: char = x.get_char(0);
            assert(x0 == 'H');
        }
        fn test_get_unicode_non_ascii_passes() {
            let emoji_with_str = ("💩");
            proof {
                reveal_strlit("💩");
            }
            let p = emoji_with_str.get_char(0);
            assert(p == '💩');
        }
        fn test_get_unicode_non_ascii_passes1() {
            let emoji_with_str = ("abcdef💩");
            proof {
                reveal_strlit("abcdef💩");
            }
            let p = emoji_with_str.get_char(0);
            assert(p == 'a');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_unicode_substring_passes verus_code! {
        use vstd::string::*;
        fn test_substring_passes() {
            proof {
                reveal_strlit("01234💩");
                reveal_strlit("012");
                reveal_strlit("34💩");
            }
            let x = ("01234💩");
            assert(x@.len() == 6);

            let x0 = x.substring_char(0,3);
            assert(x0@ =~= ("012")@);

            let x1 = x.substring_char(3,6);
            assert(x1@ =~= ("34💩")@);

        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_unicode_mixed_chars verus_code! {
        use vstd::string::*;
        proof fn test() {
            let a = ("è ❤️");
            reveal_strlit("è ❤️");
            assert(a@[0] === 'è');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_2_pass verus_code! {
        use vstd::string::*;
        fn test() {
            let a = String::from_str(("ABC"));
            proof {
                reveal_strlit("ABC");
            }
            let b = a.as_str().substring_ascii(1, 2);
            proof {
                reveal_strlit("B");
            }
            assert(b@ =~= ("B")@);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_2_fail verus_code! {
        use vstd::string::*;
        fn test() {
            let a = String::from_str(("ABC"));
            proof {
                reveal_strlit("ABC");
            }
            let b = a.as_str().substring_ascii(2, 3);
            proof {
                reveal_strlit("B");
                reveal_strlit("C");
            }
            assert(b@ =~= ("C")@);
            assert(b@ === ("B")@); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_string_is_ascii_roundtrip verus_code! {
        use vstd::string::*;
        fn test() {
            let a = ("ABC");
            let b = a.to_owned();
            let c = b.as_str();
            proof {
                reveal_strlit("ABC");
            }
            assert(a@ =~= c@);
            assert(a.is_ascii());
            assert(b.is_ascii());
            assert(c.is_ascii());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ascii_handling_passes verus_code! {
        use vstd::string::*;
        fn test_get_ascii_passes() {
            proof {
                reveal_strlit("Hello World");
            }
            let x = ("Hello World");

            let x0 = x.get_ascii(0);
            assert(x0 === 72);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ascii_ascii_handling_fails verus_code! {
        use vstd::string::*;
        fn test_get_ascii_fails() {
            proof {
                reveal_strlit("Hèllo World");
            }

            let y = ("Hèllo World");
            let y0 = y.get_ascii(0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_conversion_passes verus_code! {
        use vstd::string::*;

        fn test_char_conversion_passes() {
            let c = 'c';
            let d = c as u8;
            // ascii value
            assert(d === 99);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_char_conversion_fails verus_code! {
        use vstd::string::*;
        fn test_char_conversion_fails() {
            let z = 'ž';
            let d = z as u8;
            assert(d == 382); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_char_conversion_u32 verus_code! {
        use vstd::string::*;
        fn test() {
            let z = 'ž';
            let d = z as u32;
            assert(d == 382);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_strslice_get verus_code! {
        use vstd::string::*;
        fn test_strslice_get_passes<'a>(x: &'a str) -> (ret: u8)
            requires
                x.is_ascii(),
                x@.len() > 10
        {
            let x0 = x.get_char(0);
            x0 as u8
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_strslice_as_bytes_passes verus_code! {
        use vstd::view::*;
        use vstd::string::*;
        use vstd::prelude::*;
        fn test_strslice_as_bytes<'a>(x: &'a str) -> (ret: Vec<u8>)
            requires
                x.is_ascii(),
                x@.len() > 10
            ensures
                ret@.len() > 10
        {
            x.as_bytes_vec()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_strslice_as_bytes_fails verus_code! {
        use vstd::view::*;
        use vstd::string::*;
        use vstd::prelude::*;

        fn test_strslice_as_bytes_fails<'a>(x: &'a str) -> (ret: Vec<u8>)
            requires
                x@.len() > 10
            ensures
                ret@.len() > 10
        {
            x.as_bytes() // FAILS
        }

    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_append_1 verus_code! {
        use vstd::view::*;
        use vstd::string::*;
        use vstd::prelude::*;

        fn foo() -> (ret: String)
            ensures ret@ === ("hello world")@
        {
            proof {
                reveal_strlit("hello world");
                reveal_strlit("hello ");
                reveal_strlit("world");
            }

            let mut s = ("hello ").to_owned();
            s.append(("world"));
            assert(s@ =~= ("hello world")@);
            s
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] test_append_2 verus_code! {
        use vstd::view::*;
        use vstd::string::*;
        use vstd::prelude::*;

        fn foo() -> (ret: String)
            ensures ret@ !== ("hello worlds")@
        {
            proof {
                reveal_strlit("hello worlds");
                reveal_strlit("hello ");
                reveal_strlit("world");
            }

            let mut s = ("hello ").to_owned();
            s.append(("world"));
            assert(s@ !~= ("hello worlds")@);
            s
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] test_concat_1 verus_code! {
        use vstd::view::*;
        use vstd::string::*;
        use vstd::prelude::*;

        fn foo() -> (ret: String)
            ensures ret@ === ("hello world")@
        {
            proof {
                reveal_strlit("hello world");
                reveal_strlit("hello ");
                reveal_strlit("world");
            }

            let s1 = ("hello ").to_owned();
            let s = s1.concat(("world"));
            assert(s@ =~= ("hello world")@);
            s
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] test_concat_2 verus_code! {
        use vstd::view::*;
        use vstd::string::*;
        use vstd::prelude::*;

        fn foo() -> (ret: String)
            ensures ret@ !== ("hello worlds")@
        {
            proof {
                reveal_strlit("hello worlds");
                reveal_strlit("hello ");
                reveal_strlit("world");
            }

            let s1 = ("hello ").to_owned();
            let s = s1.concat(("world"));
            assert(s@ !~= ("hello worlds")@);
            s
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] char_clipping_and_ranges verus_code! {
        fn test_char_to_u32(c: char) {
            let i = c as u32;
            assert((0 <= i && i <= 0xD7FF) || (0xE000 <= i && i <= 0x10FFFF));
        }
        fn test_char_to_u32_fail(c: char) {
            let i = c as u32;
            assert(i != 0); // FAILS
        }
        fn test_char_to_u32_fail2(c: char) {
            let i = c as u32;
            assert(i != 0xD7FF); // FAILS
        }
        fn test_char_to_u32_fail3(c: char) {
            let i = c as u32;
            assert(i != 0xE000); // FAILS
        }
        fn test_char_to_u32_fail4(c: char) {
            let i = c as u32;
            assert(i != 0x10FFFF); // FAILS
        }

        proof fn test_char_to_int(c: char) {
            let i = c as int;
            assert((0 <= i && i <= 0xD7ff) || (0xE000 <= i && i <= 0x10FFFF));
        }
        proof fn test_char_to_int_fail(c: char) {
            let i = c as int;
            assert(i != 0); // FAILS
        }
        proof fn test_char_to_int_fail2(c: char) {
            let i = c as int;
            assert(i != 0xD7FF); // FAILS
        }
        proof fn test_char_to_int_fail3(c: char) {
            let i = c as int;
            assert(i != 0xE000); // FAILS
        }
        proof fn test_char_to_int_fail4(c: char) {
            let i = c as int;
            assert(i != 0x10FFFF); // FAILS
        }

        fn test_ineq(a: char, b: char) {
            let bool1 = a <= b;
            let bool2 = (a as u32) <= (b as u32);
            assert(bool1 == bool2);
        }

        proof fn test_ineq_pf(a: char, b: char) {
            let bool1 = a <= b;
            let bool2 = (a as u32) <= (b as u32);
            assert(bool1 == bool2);
        }

        fn test_cast_u8_to_char(x: u8) {
            let c = x as char;
            assert('\0' <= c && c <= (255 as char));
            assert(0 <= c && c <= 255);
        }
        fn test_cast_u8_to_char_fail(x: u8) {
            let c = x as char;
            assert(c != 255); // FAILS
        }

        // Casting any int type to char is not supported in normal Rust (which only allows u8 -> char)
        // But it's ok in spec code
        proof fn test_cast_u32_to_char(x: u32) {
            let c = x as char;
            assert((0 <= c && c <= 0xD7FF) || (0xE000 <= c && c <= 0x10FFFF));
        }
        proof fn test_cast_u32_to_char_fails(x: u32) {
            let c = x as char;
            assert(c == x); // FAILS
        }

        proof fn test_cast_i32_to_char(x: i32) {
            let c = x as char;
            assert((0 <= c && c <= 0xD7FF) || (0xE000 <= c && c <= 0x10FFFF));
        }
        proof fn test_cast_i32_to_char_fails(x: i32) {
            let c = x as char;
            assert(c == x); // FAILS
        }

        proof fn test_cast_int_to_char(x: int) {
            let c = x as char;
            assert((0 <= c && c <= 0xD7FF) || (0xE000 <= c && c <= 0x10FFFF));
            assert(((0 <= x && x <= 0xD7FF) || (0xE000 <= x && x <= 0x10FFFF)) ==> c == x);
        }
        proof fn test_cast_int_to_char_fails(x: int) {
            let c = x as char;
            assert(c == x); // FAILS
        }
        proof fn test_cast_int_to_char_fails2(x: int) {
            let c = x as char;
            assert(c != 0); // FAILS
        }
        proof fn test_cast_int_to_char_fails3(x: int) {
            let c = x as char;
            assert(c != 0xD7FF); // FAILS
        }
        proof fn test_cast_int_to_char_fails4(x: int) {
            let c = x as char;
            assert(c != 0xE000); // FAILS
        }
        proof fn test_cast_int_to_char_fails5(x: int) {
            let c = x as char;
            assert(c != 0x10FFFF); // FAILS
        }
        proof fn test_cast_int_to_char_fails6(x: int) {
            let c = x as char;
            assert(x == 0xD800 ==> c == x); // FAILS
        }
        proof fn test_cast_int_to_char_fails7(x: int) {
            let c = x as char;
            assert(x == 0xDFFF ==> c == x); // FAILS
        }
        proof fn test_cast_int_to_char_fails8(x: int) {
            let c = x as char;
            assert(x == 0x110000 ==> c == x); // FAILS
        }

        spec fn char_range_match(c: char) -> bool {
            match c {
                '\0' ..= '\u{D7FF}' => false,
                '\u{E000}' ..= '\u{10FFFF}' => true,
            }
        }

        proof fn test_char_range_match(c: char) {
            let x = char_range_match(c);
            assert(x ==> c >= 0xDEEE);
        }
    } => Err(err) => assert_fails(err, 19)
}

test_verify_one_file! {
    #[test] test_reveal_empty_string_issue1240 verus_code! {
        use vstd::*;
        use vstd::string::*;

        pub fn test() {
            proof { reveal_strlit(""); }
            let mut res = String::from_str("");
            assert(res@ =~= seq![]);
        }

        pub fn test2() {
            proof { reveal_strlit(""); }
            let mut res = String::from_str("");
            assert(res@ =~= seq![]);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_chars_iterator verus_code! {
        use vstd::*;
        use vstd::prelude::*;

        #[verifier::loop_isolation(false)]
        fn test() {
            let s = "abca";
            proof {
                reveal_strlit("abca");
            }
            let mut chars_it = s.chars();
            let mut num_as = 0usize;
            let ghost is_a = |c: char| c == 'a';
            for c in it: chars_it
                invariant num_as == it@.filter(is_a).len()
            {
                reveal(Seq::filter);
                let ghost prev_chars = it.chars.take(it.pos);
                let ghost next_chars = it.chars.take(it.pos + 1);
                assert(next_chars =~= prev_chars + seq![c]);
                if c == 'a' {
                    assert(seq![c].filter(is_a) =~= seq![c]);
                    num_as += 1;
                } else {
                    assert(seq![c].drop_last().filter(is_a) =~= Seq::<char>::empty());
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_deref verus_code! {
        use vstd::prelude::*;
        use vstd::string::*;

        fn test_string_deref() {
            let s: String = String::from_str("hello");
            proof {
                reveal_strlit("hello");
            }

            let slice: &str = &s;
            assert(slice@ == s@);
            assert(slice.is_ascii() == s.is_ascii());
        }
    } => Ok(())
}
