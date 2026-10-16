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
                ret@[0..5] =~= ("Hello")@
        {
            proof {
                reveal_strlit("Hello");
                reveal_strlit("Hello World");
            }
            ("Hello World")

        }

        fn test_substring_passes2<'a>() -> (ret: &'a str)
            ensures
                ret@[0..5] =~= ("Hello")@
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
                ret@[0..5] =~= ("Hello")@ // FAILS
        {
            proof {
                reveal_strlit("Hello");
                reveal_strlit("Gello World");
            }
            ("Gello World")
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_str_index_ranges ["no-auto-import-verus_builtin"] => code! {
        #![cfg_attr(verus_keep_ghost, feature(slice_index_methods))]

        use verus_builtin::*;
        use verus_builtin_macros::*;

        verus! {
        use core::ops::{Bound, Index};
        use core::slice::SliceIndex;
        use vstd::prelude::*;
        use vstd::seq::lemma_seq_subrange_len;
        use vstd::string::StringSliceAdditionalSpecFns;
        use vstd::utf8::*;

        broadcast use group_utf8_lib;

        // @zero-to-nat points out: This `assume_specification` is for
        // testing purposes only; we shouldn't use it in real code. We
        // can't have a verified `str::as_bytes_mut` because we don't
        // have a way of ensuring the UTF8 invariant is enforced on
        // final(b), so uses of this function could easily create a
        // str which violates the invariant. In vstd, we assume that
        // the UTF8 invariant always holds, because the View of a str
        // is Seq<char> instead of Seq<u8>.
        pub assume_specification[ str::as_bytes_mut ](s: &mut str) -> (b: &mut [u8])
            ensures
                b@ == old(s).spec_bytes(),
                final(b)@ == final(s).spec_bytes(),
        ;

        fn overwrite_2(s: &mut str)
            requires
                s.spec_bytes().len() == 2,
            ensures
                final(s).spec_bytes() == seq![b'x', b'y'],
        {
            unsafe {
                let bytes = s.as_bytes_mut();
                bytes[0] = b'x';
                bytes[1] = b'y';
            }
        }

        fn overwrite_3(s: &mut str)
            requires
                s.spec_bytes().len() == 3,
            ensures
                final(s).spec_bytes() == seq![b'x', b'y', b'z'],
        {
            unsafe {
                let bytes = s.as_bytes_mut();
                bytes[0] = b'x';
                bytes[1] = b'y';
                bytes[2] = b'z';
            }
        }

        fn overwrite_4(s: &mut str)
            requires
                s.spec_bytes().len() == 4,
            ensures
                final(s).spec_bytes() == seq![b'w', b'x', b'y', b'z'],
        {
            unsafe {
                let bytes = s.as_bytes_mut();
                bytes[0] = b'w';
                bytes[1] = b'x';
                bytes[2] = b'y';
                bytes[3] = b'z';
            }
        }

        fn overwrite_5(s: &mut str)
            requires
                s.spec_bytes().len() == 5,
            ensures
                final(s).spec_bytes() == seq![b'v', b'w', b'x', b'y', b'z'],
        {
            unsafe {
                let bytes = s.as_bytes_mut();
                bytes[0] = b'v';
                bytes[1] = b'w';
                bytes[2] = b'x';
                bytes[3] = b'y';
                bytes[4] = b'z';
            }
        }

        fn bound_pair(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
                s.is_char_boundary(2),
                s.is_char_boundary(4),
        {
            let _: &str = &s[(Bound::Excluded(1), Bound::Included(3))];
            let _: &str = &s[(Bound::Unbounded, Bound::Unbounded)];
        }

        fn range(s: &mut str)
            requires
                s.len() == 5,
                s.is_char_boundary(1),
                s.is_char_boundary(3),
        {
            let _: &str = &s[1..3];
            let _: &str = s.index(1..3);
            let r: &str = (1..3).index(s);
            assert(r.spec_bytes() == s.spec_bytes()[1..3]);

            let ghost old_s = s.spec_bytes();
            let r: &mut str = (1..3).index_mut(s);
            assert(r.spec_bytes() == old_s[1..3]);
            overwrite_2(r);
            assert(s.spec_bytes()[0..1] == old_s[0..1]);
            assert(s.spec_bytes()[1..3] == seq![b'x', b'y']);
            assert(s.spec_bytes()[3..5] == old_s[3..5]);
        }

        fn range_from(s: &mut str)
            requires
                valid_utf8(s.spec_bytes()),
                s.spec_bytes().len() == 5,
                s.is_char_boundary(2),
        {
            let _: &str = &s[2..];
            let r: &str = (2..).index(s);
            assert(r.spec_bytes() == s.spec_bytes()[2..]);

            let ghost old_s = s.spec_bytes();
            let r: &mut str = (2..).index_mut(s);
            assert(r.spec_bytes() == old_s[2..]);
            proof {
                lemma_seq_subrange_len(old_s, 2, old_s.len() as int);
            }
            assert(r.spec_bytes().len() == 3);
            overwrite_3(r);
            assert(s.spec_bytes()[0..2] == old_s[0..2]);
            assert(s.spec_bytes()[2..5] == seq![b'x', b'y', b'z']);
        }

        fn range_full(s: &mut str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
                s.spec_bytes().len() == 5,
        {
            let _: &str = &s[..];
            let r: &str = (..).index(s);
            assert(r.spec_bytes() == s.spec_bytes());

            let ghost old_s = s.spec_bytes();
            let r: &mut str = (..).index_mut(s);
            assert(r.spec_bytes() == old_s);
            assert(r.spec_bytes().len() == 5);
            overwrite_5(r);
            assert(s.spec_bytes() == seq![b'v', b'w', b'x', b'y', b'z']);
        }

        fn range_inclusive(s: &mut str)
            requires
                s.len() == 5,
                s.is_char_boundary(1),
                s.is_char_boundary(4),
        {
            let _: &str = &s[1..=3];
            let r: &str = (1..=3).index(s);
            assert(r.spec_bytes() == s.spec_bytes()[1..4]);

            let ghost old_s = s.spec_bytes();
            let r: &mut str = (1..=3).index_mut(s);
            assert(r.spec_bytes() == old_s[1..4]);
            overwrite_3(r);
            assert(s.spec_bytes()[0..1] == old_s[0..1]);
            assert(s.spec_bytes()[1..4] == seq![b'x', b'y', b'z']);
            assert(s.spec_bytes()[4..5] == old_s[4..5]);
        }

        fn range_to(s: &mut str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
                s.is_char_boundary(4),
        {
            let _: &str = &s[..4];
            let r: &str = (..4).index(s);
            assert(r.spec_bytes() == s.spec_bytes()[0..4]);

            let ghost old_s = s.spec_bytes();
            let r: &mut str = (..4).index_mut(s);
            assert(r.spec_bytes() == old_s[0..4]);
            overwrite_4(r);
            assert(s.spec_bytes()[0..4] == seq![b'w', b'x', b'y', b'z']);
            assert(s.spec_bytes()[4..5] == old_s[4..5]);
        }

        fn range_to_inclusive(s: &mut str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
                s.is_char_boundary(4),
        {
            let _: &str = &s[..=3];
            let r: &str = (..=3).index(s);
            assert(r.spec_bytes() == s.spec_bytes()[0..4]);

            let ghost old_s = s.spec_bytes();
            let r: &mut str = (..=3).index_mut(s);
            assert(r.spec_bytes() == old_s[0..4]);
            overwrite_4(r);
            assert(s.spec_bytes()[0..4] == seq![b'w', b'x', b'y', b'z']);
            assert(s.spec_bytes()[4..5] == old_s[4..5]);
        }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_str_index_ranges_fail verus_code! {
        use core::ops::Bound;
        use vstd::prelude::*;
        use vstd::string::StringSliceAdditionalSpecFns;
        use vstd::utf8::*;

        broadcast use group_utf8_lib;

        fn bound_pair_end_out_of_bounds(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
        {
            let _ = &s[(Bound::Unbounded, Bound::Included(5))]; // FAILS
        }

        fn bound_pair_start_not_char_boundary(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
                !s.is_char_boundary(2),
                s.is_char_boundary(4),
        {
            let _ = &s[(Bound::Excluded(1), Bound::Included(3))]; // FAILS
        }

        fn range_start_after_end(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
                s.is_char_boundary(1),
                s.is_char_boundary(3),
        {
            let _ = &s[3..1]; // FAILS
        }

        fn range_end_out_of_bounds(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
        {
            let _ = &s[3..7]; // FAILS
        }

        fn range_start_not_char_boundary(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
                !s.is_char_boundary(1),
                s.is_char_boundary(3),
        {
            let _ = &s[1..3]; // FAILS
        }

        fn range_end_not_char_boundary(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
                s.is_char_boundary(1),
                !s.is_char_boundary(3),
        {
            let _ = &s[1..3]; // FAILS
        }

        fn range_from_out_of_bounds(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
        {
            let _ = &s[7..]; // FAILS
        }

        fn range_from_not_char_boundary(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
                !s.is_char_boundary(2),
        {
            let _ = &s[2..]; // FAILS
        }

        fn range_inclusive_end_out_of_bounds(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
        {
            let _ = &s[1..=5]; // FAILS
        }

        fn range_inclusive_end_not_char_boundary(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
                s.is_char_boundary(1),
                !s.is_char_boundary(4),
        {
            let _ = &s[1..=3]; // FAILS
        }

        fn range_to_out_of_bounds(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
        {
            let _ = &s[..7]; // FAILS
        }

        fn range_to_not_char_boundary(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
                !s.is_char_boundary(4),
        {
            let _ = &s[..4]; // FAILS
        }

        fn range_to_inclusive_out_of_bounds(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
        {
            let _ = &s[..=5]; // FAILS
        }

        fn range_to_inclusive_not_char_boundary(s: &str)
            requires
                valid_utf8(s.spec_bytes()),
                s.len() == 5,
                !s.is_char_boundary(4),
        {
            let _ = &s[..=3]; // FAILS
        }
    } => Err(err) => assert_fails(err, 14)
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

            assert(a@ =~= abc@[0..1]);
            assert(b@ =~= abc@[1..2]);
            assert(c@ =~= abc@[2..3]);

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
                invariant num_as == it.seq()[..it.index()].filter(is_a).len()
            {
                reveal(Seq::filter);
                let ghost prev_chars = it.seq()[..it.index()];
                let ghost next_chars = it.seq()[..it.index() + 1];
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
    #[test]
    str_equality_uses_view verus_code! {
        use vstd::prelude::*;

        struct TextSource;

        uninterp spec fn modeled_text(source: &TextSource) -> Seq<char>;

        #[verifier::external_body]
        fn get_text<'a>(source: &'a TextSource) -> (result: &'a str)
            ensures
                result@ == modeled_text(source),
        {
            "hello world"
        }

        spec fn is_hello(source: &TextSource) -> bool {
            modeled_text(source) == "hello world"@
        }

        fn check(source: &TextSource) -> (result: bool)
            ensures
                result == is_hello(source),
        {
            get_text(source) == "hello world"
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_strlit_view_id_literal_disequality verus_code! {
        use vstd::prelude::*;

        broadcast use vstd::string::axiom_new_strlit_view_id;

        proof fn same_length() {
            assert("hello"@ != "world"@);
        }

        proof fn prefix() {
            assert("hello"@ != "helloworld"@);
        }

        proof fn same_literal_stays_equal() {
            assert("hello"@ == "hello"@);
        }

        proof fn map_keys() {
            let m = Map::<Seq<char>, int>::empty()
                .insert("hello"@, 1)
                .insert("world"@, 2);
            assert(m["hello"@] == 1);
            assert(m.remove("hello"@)["world"@] == 2);
        }

        proof fn empty_string() {
            assert(""@ != "hello"@);
        }

        proof fn unicode() {
            assert("héllo"@ != "hello"@);
        }

        // the axiom coexists with reveal_strlit content facts
        proof fn with_reveal() {
            reveal_strlit("hello");
            assert("hello"@.len() == 5);
            assert("hello"@ != "world"@);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_strlit_view_id_no_spurious_disequality verus_code! {
        use vstd::prelude::*;

        broadcast use vstd::string::group_string_axioms;

        proof fn p() {
            assert("hello"@ != "hello"@); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_str_pattern_char_and_str verus_code! {
        use vstd::prelude::*;
        use vstd::string::{PatternSpec, StringExecFns, StringSliceAdditionalSpecFns};

        fn test() {
            proof {
                reveal_strlit("héllo");
                reveal_strlit("hé");
                reveal_strlit("lo");
                reveal_strlit("él");
                assert("héllo"@ =~= seq!['h', 'é', 'l', 'l', 'o']);
                assert("héllo"@.subrange(0, 2) =~= "hé"@);
                assert("héllo"@.subrange(3, 5) =~= "lo"@);
                assert("héllo"@.subrange(1, 3) =~= "él"@);
            }
            // A positive match needs its witness; a non-match doesn't.
            assert("hé".matches_at("héllo"@, 0, 2));
            let r = "héllo".starts_with("hé");
            assert(r);
            assert("lo".matches_at("héllo"@, 3, 5));
            let r = "héllo".ends_with("lo");
            assert(r);
            assert("él".matches_at("héllo"@, 1, 3));
            let r = "héllo".contains("él");
            assert(r);
            assert('é'.matches_at("héllo"@, 1, 2));
            let r = "héllo".contains('é');
            assert(r);
            let r = "héllo".starts_with('é');
            assert(!r);
            let r = "héllo".contains('z');
            assert(!r);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_str_pattern_other_impls verus_code! {
        use vstd::prelude::*;
        use vstd::string::{PatternSpec, StringExecFns, StringSliceAdditionalSpecFns};

        fn test() {
            proof {
                reveal_strlit("héllo");
                reveal_strlit("ll");
                assert("héllo"@ =~= seq!['h', 'é', 'l', 'l', 'o']);
                assert("héllo"@.subrange(2, 4) =~= "ll"@);
            }
            let arr = ['x', 'h'];
            assert(arr.matches_at("héllo"@, 0, 1));
            let r = "héllo".starts_with(arr);
            assert(r);
            let arr_ref = &['o', 'z'];
            assert((&arr_ref).matches_at("héllo"@, 4, 5));
            let r = "héllo".ends_with(arr_ref);
            assert(r);
            let slice: &[char] = &['z', 'é'];
            assert(slice.matches_at("héllo"@, 1, 2));
            let r = "héllo".contains(slice);
            assert(r);
            let slice: &[char] = &['z', 'q'];
            let r = "héllo".contains(slice);
            assert(!r);
            let pat: &&str = &"ll";
            assert((&pat).matches_at("héllo"@, 2, 4));
            let r = "héllo".contains(pat);
            assert(r);
            let owned = String::from_str("ll");
            let owned_ref = &owned;
            assert((&owned_ref).matches_at("héllo"@, 2, 4));
            let r = "héllo".contains(owned_ref);
            assert(r);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_str_pattern_closure verus_code! {
        use vstd::prelude::*;
        use vstd::string::{PatternSpec, StringExecFns, StringSliceAdditionalSpecFns};

        fn test() {
            proof {
                reveal_strlit("héllo");
                assert("héllo"@ =~= seq!['h', 'é', 'l', 'l', 'o']);
            }
            let is_l = |c: char| -> (b: bool) ensures b == (c == 'l') { c == 'l' };
            // `is_l.ensures(('l',), true)` is only known from an actual call.
            let _ = is_l('l');
            assert(is_l.matches_at("héllo"@, 2, 3));
            let r = "héllo".contains(is_l);
            assert(r);
            let is_z = |c: char| -> (b: bool) ensures b == (c == 'z') { c == 'z' };
            let r = "héllo".contains(is_z);
            assert(!r);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_closure_pattern_requires_false_not_obeyed verus_code! {
        use vstd::prelude::*;
        use vstd::string::{PatternSpec, StringExecFns, StringSliceAdditionalSpecFns};

        fn test() {
            let pred = |_c: char| -> (b: bool)
                requires false
                ensures !b
            { true };
            assert(pred.obeys_pattern_spec()); // FAILS
            let res = "a".starts_with(pred);
            // Wrong at runtime: provable only because the failed assert above is assumed.
            assert(!res);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_str_find_rfind_byte_offsets verus_code! {
        use vstd::prelude::*;
        use vstd::string::{PatternSpec, StringSliceAdditionalSpecFns};
        use vstd::utf8::{encode_scalar, encode_utf8};

        // UTF-8 bytes of "héllo" ('é' is two bytes), 'l', and 'z'.
        proof fn lemma_hello_bytes()
            ensures
                "héllo".spec_bytes() =~= seq![0x68u8, 0xC3, 0xA9, 0x6C, 0x6C, 0x6F],
                encode_scalar('l' as u32) =~= seq![0x6Cu8],
                encode_scalar('z' as u32) =~= seq![0x7Au8],
        {
            reveal_strlit("héllo");
            assert("héllo"@ =~= seq!['h', 'é', 'l', 'l', 'o']);
            assert((0x68u32 & 0x7F) as u8 == 0x68u8 && (0x6Cu32 & 0x7F) as u8 == 0x6Cu8
                && (0x6Fu32 & 0x7F) as u8 == 0x6Fu8 && (0x7Au32 & 0x7F) as u8 == 0x7Au8
                && (0xC0u8 | ((0xE9u32 >> 6) & 0x1F) as u8) == 0xC3u8
                && (0x80u8 | (0xE9u32 & 0x3F) as u8) == 0xA9u8) by (bit_vector);
            reveal_with_fuel(encode_utf8, 6);
        }

        // A one-byte pattern match pins down the byte at its start.
        proof fn lemma_one_byte_match(bytes: Seq<u8>, start: int, end: int, b: u8)
            requires
                0 <= start <= end <= bytes.len(),
                bytes.subrange(start, end) =~= seq![b],
            ensures
                end == start + 1,
                bytes[start] == b,
        {
            assert(seq![b].len() == 1 && seq![b][0] == b);
            assert(bytes.subrange(start, end)[0] == bytes[start]);
        }

        fn test() {
            proof { lemma_hello_bytes(); }
            let ghost bytes = "héllo".spec_bytes();
            // The first 'l' is at byte 3 (char index 2), the last at byte 4.
            let r = "héllo".find('l');
            assert(r == Some(3usize)) by {
                assert('l'.matches_at_bytes(bytes, 3, 4));
                let i = r->0 as int;
                let end = choose|end: int| i <= end <= bytes.len() && 'l'.matches_at_bytes(bytes, i, end);
                lemma_one_byte_match(bytes, i, end, 0x6C);
            }
            let r = "héllo".rfind('l');
            assert(r == Some(4usize)) by {
                assert('l'.matches_at_bytes(bytes, 4, 5));
                let i = r->0 as int;
                let end = choose|end: int| i <= end <= bytes.len() && 'l'.matches_at_bytes(bytes, i, end);
                lemma_one_byte_match(bytes, i, end, 0x6C);
            }
            // The empty pattern matches at byte 0 first and at the end last.
            proof { reveal_strlit(""); }
            let r = "héllo".find("");
            assert(r == Some(0usize)) by {
                assert("".matches_at_bytes(bytes, 0, 0));
            }
            let r = "héllo".rfind("");
            assert(r == Some(6usize)) by {
                assert("".matches_at_bytes(bytes, 6, 6));
            }
            let r = "héllo".find('z');
            assert(r is None) by {
                if r is Some {
                    let i = r->0 as int;
                    let end = choose|end: int| i <= end <= bytes.len() && 'z'.matches_at_bytes(bytes, i, end);
                    lemma_one_byte_match(bytes, i, end, 0x7A);
                }
            }
        }
    } => Ok(())
}

// A caller generic over the closure can recover per-char facts in both directions.
test_verify_one_file_with_options! {
    #[test] generic_starts_with_matches_wrapper ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use vstd::string::PatternSpec;

        fn generic_starts_with_pred<F: FnMut(char) -> bool>(s: &str, pred: F) -> (res: bool)
            requires
                pred.obeys_pattern_spec(),
            ensures
                s@.len() == 0 ==> !res,
                s@.len() > 0 ==> (res == pred.ensures((s@[0],), true)),
        {
            let res = s.starts_with(pred);
            proof {
                if s@.len() > 0 {
                    assert(pred.matches_at(s@, 0, 1) == pred.ensures((s@[0],), true));
                }
            }
            res
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] generic_ends_with_matches_wrapper ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use vstd::string::PatternSpec;

        fn generic_ends_with_pred<F: FnMut(char) -> bool>(s: &str, pred: F) -> (res: bool)
            requires
                pred.obeys_pattern_spec(),
            ensures
                s@.len() == 0 ==> !res,
                s@.len() > 0 ==> (res == pred.ensures((s@[s@.len() - 1],), true)),
        {
            let res = s.ends_with(pred);
            proof {
                if s@.len() > 0 {
                    let last = s@.len() - 1;
                    assert(pred.matches_at(s@, last, last + 1) == pred.ensures((s@[last],), true));
                }
            }
            res
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] generic_contains_matches_wrapper ["vstd"] => verus_code! {
        use vstd::prelude::*;
        use vstd::string::PatternSpec;

        fn generic_contains_pred<F: FnMut(char) -> bool>(s: &str, pred: F) -> (res: bool)
            requires
                pred.obeys_pattern_spec(),
            ensures
                res == exists|i: int| 0 <= i < s@.len() && pred.ensures((#[trigger] s@[i],), true),
        {
            let res = s.contains(pred);
            proof {
                if !res {
                    assert forall|i: int| 0 <= i < s@.len() implies !pred.ensures(
                        (#[trigger] s@[i],),
                        true,
                    ) by {
                        assert(!pred.matches_at(s@, i, i + 1));
                    };
                }
            }
            res
        }
    } => Ok(())
}
