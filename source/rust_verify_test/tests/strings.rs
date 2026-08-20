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
            assert('h' == val);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fail_get_char verus_code! {
        use vstd::string::*;
        fn get_char_fails() {
            let x = ("hello world");
            let val = x.get_char(0); // FAILS
            assert(val == 'h'); // FAILS
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
            assert(x@.len() == 6);
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

            assert(a != b);
            assert(b != c);
            assert(a == a);
            assert(a0_clone == a0);

            assert(a@ =~= abc@.subrange(0,1));
            assert(b@ =~= abc@.subrange(1,2));
            assert(c@ =~= abc@.subrange(2,3));

            assert(cba != abc);
            assert(abc == abc_clone);
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
            assert(x@.len() == 11); // FAILS
        }

        fn test_multi_fails2() {
            assert(x@.len() != 11) // FAILS
        }

        fn test_multi_fails3() {
            assert(x == y); // FAILS
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
            assert(a@ == ("A")@);
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
            assert(a@ == ("B")@); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_strlit_neq verus_code! {
        use vstd::string::*;
        const x: &'static str = "Hello World";
        const y: &'static str = "Gello World";
        fn test() {
            assert(x != y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_strlit_neq_soundness verus_code! {
        use vstd::string::*;
        const x: &'static str = "Hello World";
        const y: &'static str = "Gello World";
        fn test() {
            assert(x != y);
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
            assert(a@[0] == 'è');
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
            assert(b@ == ("B")@); // FAILS
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
            assert(x0 == 72);
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
            assert(d == 99);
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
            ensures ret@ == ("hello world")@
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
            ensures ret@ != ("hello worlds")@
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
            ensures ret@ == ("hello world")@
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
            ensures ret@ != ("hello worlds")@
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
                invariant num_as == it.seq().take(it.index()).filter(is_a).len()
            {
                reveal(Seq::filter);
                let ghost prev_chars = it.seq().take(it.index());
                let ghost next_chars = it.seq().take(it.index() + 1);
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

test_verify_one_file! {
    #[test] test_string_push_pop verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut s = String::new();
            assert(s@ == Seq::<char>::empty());
            s.push('a');
            s.push('b');
            assert(s@ == seq!['a', 'b']);
            let popped = s.pop();
            assert(popped == Some('b'));
            assert(s@ == seq!['a']);
            let popped2 = s.pop();
            assert(popped2 == Some('a'));
            assert(s@ == Seq::<char>::empty());
            let popped3 = s.pop();
            assert(popped3 is None);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_push_pop_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut s = String::new();
            s.push('a');
            let popped = s.pop();
            assert(popped == Some('b')); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_string_push_str verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut s = String::new();
            s.push('a');
            s.push_str("bc");
            proof {
                reveal_strlit("bc");
            }
            assert(s@ == seq!['a', 'b', 'c']);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_push_str_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut s = String::new();
            s.push_str("bc");
            proof {
                reveal_strlit("bc");
            }
            assert(s@ == seq!['b']); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_string_is_empty_and_clear verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut s = String::new();
            let empty0 = s.is_empty();
            assert(empty0);
            s.push('a');
            let empty1 = s.is_empty();
            assert(!empty1);
            s.clear();
            let empty2 = s.is_empty();
            assert(empty2);
            assert(s@ == Seq::<char>::empty());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_is_empty_and_clear_fails verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut s = String::new();
            s.push('a');
            s.clear();
            let empty = s.is_empty();
            assert(!empty); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_str_pattern_wrappers_pass verus_code! {
        use vstd::string::*;
        use vstd::seq::*;

        fn test_pattern_wrappers_concrete() {
            proof {
                reveal_strlit("hello world");
                reveal_strlit("hello");
                reveal_strlit("world");
                reveal_strlit("lo wo");
                reveal_strlit("xyz");
                assert("hello world"@ =~= seq!['h', 'e', 'l', 'l', 'o', ' ', 'w', 'o', 'r', 'l', 'd']);
                assert("hello"@ =~= seq!['h', 'e', 'l', 'l', 'o']);
                assert("world"@ =~= seq!['w', 'o', 'r', 'l', 'd']);
                assert("xyz"@ =~= seq!['x', 'y', 'z']);
                assert("hello world"@.subrange(0, 5) =~= seq!['h', 'e', 'l', 'l', 'o']);
                assert("hello world"@.subrange(6, 11) =~= seq!['w', 'o', 'r', 'l', 'd']);
                assert("hello world"@.subrange(3, 3 + "lo wo"@.len() as int) =~= "lo wo"@);
            }
            let r1 = str_starts_with_str("hello world", "hello");
            assert(r1);
            let r2 = str_starts_with_str("hello world", "xyz");
            assert(!r2);
            let r3 = str_ends_with_str("hello world", "world");
            assert(r3);
            let r4 = str_ends_with_str("hello world", "xyz");
            assert(!r4);
            let r5 = str_ends_with_char("hello world", 'd');
            assert(r5);
            let r6 = str_ends_with_char("hello world", 'x');
            assert(!r6);
            let r7 = str_contains_str("hello world", "lo wo");
            assert(r7);
            let r8 = str_contains_str("hello world", "xyz");
            assert(!r8);
        }

        // `&[char]` matches by set membership of a single char, not by
        // sequence - e.g. `['h', 'x']` matches because 'h' is in the set,
        // same as `['e', 'h']` would.
        fn test_chars_pattern_wrappers_concrete() {
            proof {
                reveal_strlit("hello world");
                assert("hello world"@[2] == 'l');
            }
            let starts_pat: [char; 2] = ['h', 'x'];
            let r9 = str_starts_with_chars("hello world", &starts_pat);
            assert(r9);
            let no_match_pat: [char; 2] = ['x', 'y'];
            let r10 = str_starts_with_chars("hello world", &no_match_pat);
            assert(!r10);
            let ends_pat: [char; 2] = ['d', 'x'];
            let r11 = str_ends_with_chars("hello world", &ends_pat);
            assert(r11);
            let contains_pat: [char; 2] = ['z', 'l'];
            let r12 = str_contains_chars("hello world", &contains_pat);
            assert(r12);
            let r13 = str_contains_chars("hello world", &no_match_pat);
            assert(!r13);
        }

        // A closure Pattern - the predicate is given as an ordinary Verus
        // closure with an explicit `ensures`, which is what lets Verus
        // reason precisely about its result at the call site.
        fn test_pred_pattern_wrappers_concrete() {
            proof {
                reveal_strlit("hello world");
                assert("hello world"@[2] == 'l');
            }
            let r18 = str_contains_pred(
                "hello world",
                |c: char| -> (b: bool) ensures b == (c == 'l') { c == 'l' },
            );
            assert(r18);
            let r19 = str_contains_pred(
                "hello world",
                |c: char| -> (b: bool) ensures b == (c == 'z') { c == 'z' },
            );
            assert(!r19);
            let r14 = str_starts_with_pred(
                "hello world",
                |c: char| -> (b: bool) ensures b == (c == 'h') { c == 'h' },
            );
            assert(r14);
            let r15 = str_starts_with_pred(
                "hello world",
                |c: char| -> (b: bool) ensures b == (c == 'x') { c == 'x' },
            );
            assert(!r15);
            let r16 = str_ends_with_pred(
                "hello world",
                |c: char| -> (b: bool) ensures b == (c == 'd') { c == 'd' },
            );
            assert(r16);
            let r17 = str_ends_with_pred(
                "hello world",
                |c: char| -> (b: bool) ensures b == (c == 'x') { c == 'x' },
            );
            assert(!r17);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_str_pattern_wrappers_fail verus_code! {
        use vstd::string::*;
        use vstd::seq::*;

        fn test_pattern_wrappers_wrong() {
            proof {
                reveal_strlit("hello world");
                reveal_strlit("hello");
                assert("hello world"@.subrange(0, 5) =~= seq!['h', 'e', 'l', 'l', 'o']);
            }
            let r = str_starts_with_str("hello world", "hello");
            assert(!r); // FAILS
        }

        fn test_chars_pattern_wrapper_wrong() {
            proof {
                reveal_strlit("hello world");
            }
            let pat: [char; 2] = ['h', 'x'];
            let r = str_starts_with_chars("hello world", &pat);
            assert(!r); // FAILS
        }

        fn test_pred_pattern_wrapper_wrong() {
            proof {
                reveal_strlit("hello world");
            }
            let r = str_starts_with_pred(
                "hello world",
                |c: char| -> (b: bool) ensures b == (c == 'h') { c == 'h' },
            );
            assert(!r); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_str_find_wrappers_pass verus_code! {
        use vstd::string::*;
        use vstd::seq::*;
        use vstd::utf8::{encode_scalar, encode_utf8};
        use vstd::pervasive::FnWithRequiresEnsures;

        proof fn lemma_bitand_7f(v: u32)
            requires v <= 0x7F,
            ensures (v & 0x7F) as u8 == v as u8,
        {
            assert((v & 0x7F) as u8 == v as u8) by (bit_vector)
                requires v <= 0x7F;
        }

        proof fn lemma_ascii_char_encode_scalar(c: char)
            requires
                c as u32 <= 0x7F,
            ensures
                encode_scalar(c as u32).len() == 1,
                encode_scalar(c as u32)[0] == c as u8,
        {
            let v = c as u32;
            lemma_bitand_7f(v);
            assert(v as u8 == c as u8);
        }

        fn test_find_str() {
            proof {
                reveal_strlit("hello world");
                reveal_strlit("world");
                reveal_strlit("xyz");
            }
            let r1 = str_find_str("hello world", "world");
            assert(r1 is Some) by {
                broadcast use vstd::string::is_ascii_spec_bytes;
                assert("hello world".is_ascii());
                assert("world".is_ascii());
                assert("hello world"@ =~= seq!['h', 'e', 'l', 'l', 'o', ' ', 'w', 'o', 'r', 'l', 'd']);
                assert("world"@ =~= seq!['w', 'o', 'r', 'l', 'd']);
                assert("hello world".spec_bytes() =~= Seq::new(11, |i| "hello world"@.index(i) as u8));
                assert("world".spec_bytes() =~= Seq::new(5, |i| "world"@.index(i) as u8));
                assert("hello world".spec_bytes().subrange(6, 6 + "world".spec_bytes().len() as int) =~= "world".spec_bytes());
            };
            // The wrapper's own postcondition already ties the returned offset back
            // to a real match - no need to independently re-derive its exact value.
            assert("hello world".spec_bytes().subrange(
                r1.unwrap() as int,
                r1.unwrap() as int + "world".spec_bytes().len() as int,
            ) =~= "world".spec_bytes());

            let r2 = str_find_str("hello world", "xyz");
            assert(r2 is None) by {
                broadcast use vstd::string::is_ascii_spec_bytes;
                assert("hello world".is_ascii());
                assert("xyz".is_ascii());
                let haystack = "hello world".spec_bytes();
                let needle = "xyz".spec_bytes();
                assert("hello world"@ =~= seq!['h', 'e', 'l', 'l', 'o', ' ', 'w', 'o', 'r', 'l', 'd']);
                assert("xyz"@ =~= seq!['x', 'y', 'z']);
                assert(haystack =~= Seq::new(11, |i| "hello world"@.index(i) as u8));
                assert(needle =~= Seq::new(3, |i| "xyz"@.index(i) as u8));
                assert forall|j: int| 0 <= j <= 8 implies !(#[trigger] haystack.subrange(j, j + 3) =~= needle) by {
                    assert(haystack[j] != needle[0]) by { assert("hello world"@.index(j) != 'x'); }
                    lemma_first_byte_mismatch_not_a_match(haystack, needle, j);
                }
            };
        }

        fn test_rfind_str() {
            proof {
                reveal_strlit("hello world hello");
                reveal_strlit("hello");
            }
            let r = str_rfind_str("hello world hello", "hello");
            assert(r is Some) by {
                broadcast use vstd::string::is_ascii_spec_bytes;
                assert("hello world hello".is_ascii());
                assert("hello".is_ascii());
                assert("hello world hello"@ =~= seq!['h','e','l','l','o',' ','w','o','r','l','d',' ','h','e','l','l','o']);
                assert("hello"@ =~= seq!['h', 'e', 'l', 'l', 'o']);
                assert("hello world hello".spec_bytes() =~= Seq::new(17, |i| "hello world hello"@.index(i) as u8));
                assert("hello".spec_bytes() =~= Seq::new(5, |i| "hello"@.index(i) as u8));
                assert("hello world hello".spec_bytes().subrange(12, 12 + "hello".spec_bytes().len() as int) =~= "hello".spec_bytes());
            };
            // The wrapper's own postcondition already ties the returned offset back
            // to a real match - no need to independently re-derive its exact value.
            assert("hello world hello".spec_bytes().subrange(
                r.unwrap() as int,
                r.unwrap() as int + "hello".spec_bytes().len() as int,
            ) =~= "hello".spec_bytes());
        }

        fn test_find_char() {
            proof {
                reveal_strlit("hello world");
                lemma_ascii_char_encode_scalar('o');
            }
            let r1 = str_find_char("hello world", 'o');
            assert(r1 is Some) by {
                broadcast use vstd::string::is_ascii_spec_bytes;
                lemma_ascii_char_encode_scalar('o');
                assert("hello world".is_ascii());
                assert("hello world"@ =~= seq!['h', 'e', 'l', 'l', 'o', ' ', 'w', 'o', 'r', 'l', 'd']);
                assert("hello world".spec_bytes() =~= Seq::new(11, |i| "hello world"@.index(i) as u8));
                assert("hello world".spec_bytes().subrange(4, 4 + encode_scalar('o' as u32).len() as int)
                    =~= encode_scalar('o' as u32));
            };
            // The wrapper's own postcondition already ties the returned offset back
            // to a real match - no need to independently re-derive its exact value.
            assert("hello world".spec_bytes().subrange(
                r1.unwrap() as int,
                r1.unwrap() as int + encode_scalar('o' as u32).len() as int,
            ) =~= encode_scalar('o' as u32));
        }

        fn test_rfind_char() {
            proof {
                reveal_strlit("hello world");
                lemma_ascii_char_encode_scalar('o');
            }
            let r1 = str_rfind_char("hello world", 'o');
            assert(r1 is Some) by {
                broadcast use vstd::string::is_ascii_spec_bytes;
                lemma_ascii_char_encode_scalar('o');
                assert("hello world".is_ascii());
                assert("hello world"@ =~= seq!['h', 'e', 'l', 'l', 'o', ' ', 'w', 'o', 'r', 'l', 'd']);
                assert("hello world".spec_bytes() =~= Seq::new(11, |i| "hello world"@.index(i) as u8));
                assert("hello world".spec_bytes().subrange(7, 7 + encode_scalar('o' as u32).len() as int)
                    =~= encode_scalar('o' as u32));
            };
            // The wrapper's own postcondition already ties the returned offset back
            // to a real match - no need to independently re-derive its exact value.
            assert("hello world".spec_bytes().subrange(
                r1.unwrap() as int,
                r1.unwrap() as int + encode_scalar('o' as u32).len() as int,
            ) =~= encode_scalar('o' as u32));
        }

        fn test_find_pred() {
            proof {
                reveal_strlit("hello world");
                assert("hello world"@[4] == 'o');
            }
            let pred = |c: char| -> (b: bool) ensures b == (c == 'o') { c == 'o' };
            let r1 = str_find_pred("hello world", pred);
            assert(r1 is Some);
            // The postcondition's own witness already ties the returned offset back
            // to a real matching character - no need to pin down its exact value.
            assert(exists|i: int|
                0 <= i < 11 && pred.ensures((#[trigger] "hello world"@[i],), true)
                    && r1.unwrap() as int == encode_utf8("hello world"@.subrange(0, i)).len());

            let r2 = str_find_pred(
                "hello world",
                |c: char| -> (b: bool) ensures b == (c == 'z') { c == 'z' },
            );
            assert(r2 is None);
        }

        fn test_rfind_pred() {
            proof {
                reveal_strlit("hello world");
                assert("hello world"@[4] == 'o');
                assert("hello world"@[7] == 'o');
            }
            let pred = |c: char| -> (b: bool) ensures b == (c == 'o') { c == 'o' };
            let r1 = str_rfind_pred("hello world", pred);
            assert(r1 is Some);
            // The postcondition's own witness already ties the returned offset back
            // to a real matching character - no need to pin down its exact value.
            assert(exists|i: int|
                0 <= i < 11 && pred.ensures((#[trigger] "hello world"@[i],), true)
                    && r1.unwrap() as int == encode_utf8("hello world"@.subrange(0, i)).len());

            let r2 = str_rfind_pred(
                "hello world",
                |c: char| -> (b: bool) ensures b == (c == 'z') { c == 'z' },
            );
            assert(r2 is None);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_str_find_wrappers_fail verus_code! {
        use vstd::string::*;

        fn test_find_str_wrong() {
            proof {
                reveal_strlit("hello world");
                reveal_strlit("world");
            }
            let r = str_find_str("hello world", "world");
            assert(r is None); // FAILS
        }

        fn test_find_pred_wrong() {
            proof {
                reveal_strlit("hello world");
            }
            let r = str_find_pred(
                "hello world",
                |c: char| -> (b: bool) ensures b == (c == 'o') { c == 'o' },
            );
            assert(r is None); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}
