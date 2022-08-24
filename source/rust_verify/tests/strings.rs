#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_pass_is_ascii verus_code! {
    #[allow(unused_imports)]
    use pervasive::string::*;

    fn str_is_ascii_passes() {
        let x = new_strlit("Hello World");
        proof {
            reveal_strlit("Hello World");
        }
        assert(x.is_ascii());
    }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails_is_ascii verus_code! {
        use pervasive::string::*;
        fn str_is_ascii_fails() {
            let x = new_strlit("à");
            proof {
                reveal_strlit("à");
            }
            assert(x.is_ascii()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_pass_get_char verus_code! {
        use pervasive::string::*;
        fn get_char() {
            let x = new_strlit("hello world");
            proof {
                reveal_strlit("hello world");
            }
            assert(x.bytes().len() == 11);
            let val = x.get_char(0);
            let h_u8 = 104;
            assert(h_u8 === val);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fail_get_char verus_code! {
        use pervasive::string::*;
        fn get_char_fails() {
            let x = new_strlit("hello world");
            let val = x.get_char(0);
            assert(val == 104); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_passes_len verus_code! {
        use pervasive::string::*;

        pub fn len_passes() {
            let x = new_strlit("abcdef");
            proof {
                reveal_strlit("abcdef");
            }
            assert(x.bytes().len() === 6);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails_len verus_code! {
        use pervasive::string::*;

        pub fn len_fails() {
            let x = new_strlit("abcdef");
            proof {
                reveal_strlit("abcdef");
            }
            assert(x.bytes().len() == 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_passes_substring verus_code! {
        use pervasive::string::*;
        fn test_substring_passes<'a>() -> (ret: StrSlice<'a>)
            ensures
                ret.bytes().subrange(0,5).ext_equal(new_strlit("Hello").bytes())

        {
            proof {
                reveal_strlit("Hello");
                reveal_strlit("Hello World");
            }
            new_strlit("Hello World")

        }

        fn test_substring_passes2<'a>() -> (ret: StrSlice<'a>)
            ensures
                ret.bytes().subrange(0,5).ext_equal(new_strlit("Hello").bytes())
        {
            let x = new_strlit("Hello World");

            proof {
                reveal_strlit("Hello");
                reveal_strlit("Hello World");
            }

            x.substring(0,5)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails_substring verus_code! {
        use pervasive::string::*;
        fn test_substring_fails<'a>() -> (ret: StrSlice<'a>)
            ensures
                ret.bytes().subrange(0,5).ext_equal(new_strlit("Hello").bytes()) // FAILS
        {
            proof {
                reveal_strlit("Hello");
                reveal_strlit("Gello World");
            }
            new_strlit("Gello World")
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_passes_multi verus_code! {
        use pervasive::string::*;

        fn test_multi_passes() {
            let a = new_strlit("a");
            let a_clone = new_strlit("a");
            let b = new_strlit("b");
            let c = new_strlit("c");
            let abc = new_strlit("abc");
            let cba = new_strlit("cba");
            let abc_clone = new_strlit("abc");

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

            assert(a.bytes().ext_equal(abc.bytes().subrange(0,1)));
            assert(b.bytes().ext_equal(abc.bytes().subrange(1,2)));
            assert(c.bytes().ext_equal(abc.bytes().subrange(2,3)));

            assert(cba !== abc);
            assert(abc === abc_clone);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_fails_multi verus_code! {
        use pervasive::string::*;
        const x: StrSlice<'static> = new_strlit("Hello World");
        const y: StrSlice<'static> = new_strlit("Gello World");
        const z: StrSlice<'static> = new_strlit("Insert string here");

        fn test_multi_fails1() {
            assert(x.bytes().len() === 11); // FAILS
        }

        fn test_multi_fails2() {
            assert(x.bytes().len() !== 11) // FAILS
        }

        fn test_multi_fails3() {
            assert(x === y); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_new_strlit_invalid verus_code! {
        use pervasive::string::*;
        const x: StrSlice<'static> = new_strlit(12);
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_reveal_strlit_invalid_1 verus_code! {
        use pervasive::string::*;
        fn test() {
            reveal_strlit(12);
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] test_reveal_strlit_invalid_2 verus_code! {
        use pervasive::string::*;
        fn test() {
            reveal_strlit("a", "a");
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_string_1_pass verus_code! {
        use pervasive::string::*;
        fn test() {
            let a = String::from_str(new_strlit("A"));
            reveal_strlit("A");
            assert(a.bytes() === new_strlit("A").bytes());
            assert(a.is_ascii());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_1_fail verus_code! {
        use pervasive::string::*;
        fn test() {
            let a = String::from_str(new_strlit("A"));
            reveal_strlit("A");
            assert(a.bytes() === new_strlit("B").bytes()); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_strlit_neq verus_code! {
        use pervasive::string::*;
        const x: StrSlice<'static> = new_strlit("Hello World");
        const y: StrSlice<'static> = new_strlit("Gello World");
        fn test() {
            assert(x !== y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_strlit_neq_soundness verus_code! {
        use pervasive::string::*;
        const x: StrSlice<'static> = new_strlit("Hello World");
        const y: StrSlice<'static> = new_strlit("Gello World");
        fn test() {
            assert(x !== y);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
