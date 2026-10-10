#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_auto_reveal_strlit_invalid_boolean verus_code! {
        #[verifier::auto_reveal_strlit(typo)]
        proof fn test() {}
    } => Err(err) => assert_vir_error_msg(err, "unrecognized verifier attribute")
}

test_verify_one_file! {
    #[test] test_auto_reveal_strlit_extra_argument verus_code! {
        #[verifier::auto_reveal_strlit(true, typo)]
        proof fn test() {}
    } => Err(err) => assert_vir_error_msg(err, "unrecognized verifier attribute")
}

test_verify_one_file! {
    #[test] test_invalid_expression_setting verus_code! {
        proof fn test() {
            let s = #[verifier::auto_reveal_strlit(true, false)] "abc";
        }
    } => Err(err) => assert_vir_error_msg(err, "unrecognized verifier attribute")
}

test_verify_one_file! {
    #[test] test_auto_reveal_bare_attributes verus_code! {
        use vstd::prelude::*;

        #[verifier::auto_reveal_strlit]
        #[verifier::auto_reveal_byteslit]
        proof fn test() {
            assert("abc"@[1] == 'b');
            assert(b"def"@[1] == b'e');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_auto_reveal_both verus_code! {
        use vstd::prelude::*;

        #[verifier::auto_reveal_strlit(true)]
        #[verifier::auto_reveal_byteslit(true)]
        proof fn test() {
            assert("abc"@[1] == 'b');
            assert(b"def"@[1] == b'e');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_auto_reveal_independent_false verus_code! {
        use vstd::prelude::*;

        #[verifier::auto_reveal_strlit(false)]
        #[verifier::auto_reveal_byteslit(true)]
        proof fn strings_disabled() {
            assert(b"abc"@[1] == b'b');
            assert("def"@[1] == 'e'); // FAILS
        }

        #[verifier::auto_reveal_strlit(true)]
        #[verifier::auto_reveal_byteslit(false)]
        proof fn bytes_disabled() {
            assert("ghi"@[1] == 'h');
            assert(b"jkl"@[1] == b'k'); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_auto_reveal_strlit verus_code! {
        use vstd::prelude::*;

        spec fn combine(str1: Seq<char>, str2: Seq<char>) -> Seq<char> {
            str1 + " "@ + str2
        }

        #[verifier::auto_reveal_strlit(true)]
        proof fn check_hello_world(str1: Seq<char>, str2: Seq<char>)
            requires
                str1 =~= "hello"@,
                str2 =~= "world"@,
            ensures
                combine(str1, str2) =~= "hello world"@,
        {
            assert(str1 + " "@ + str2 == "hello world"@);
        }

        spec fn has_prefix(string: Seq<char>, prefix: Seq<char>) -> bool
        {
            string.len() >= prefix.len()
                && string.subrange(0, prefix.len() as int) == prefix
        }

        #[verifier::auto_reveal_strlit(true)]
        proof fn check_prefix_abc(string: Seq<char>)
            requires
                has_prefix(string, "abc"@),
        {
            assert(string.subrange(0, 2) == "ab"@);
        }

        #[verifier::auto_reveal_strlit(true)]
        proof fn function_query(input: Seq<char>)
            requires input == "abc"@,
            ensures input.len() == 3,
        {
            assert(input[1] == 'b');
        }

        #[verifier::auto_reveal_strlit(true)]
        fn isolated_loop_query(n: u64) {
            let mut i = 0u64;
            while i < n
                invariant i <= n,
                decreases n - i,
            {
                assert("hello"@.len() == 5);
                assert("hello"@[0] == 'h');
                i += 1;
            }
        }

        #[verifier::auto_reveal_strlit(true)]
        proof fn nonlinear_query() {
            assert(("abc"@.len() as int) * ("abc"@.len() as int) == 9)
                by (nonlinear_arith);
        }

        #[verifier::opaque]
        #[verifier::auto_reveal_strlit(true)]
        spec fn prefix() -> Seq<char> {
            "text/"@
        }

        proof fn caller(tail: Seq<char>) {
            reveal(prefix);
            assert(prefix().len() == 5);
            assert("text/"@[4] == '/');
            let input = prefix() + tail;
            assert(input.subrange(5, input.len() as int) =~= tail);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_auto_reveal_strlit_fails verus_code! {
        use vstd::prelude::*;

        proof fn function_query(input: Seq<char>)
            requires input == "abc"@,
        {
            assert(input[1] == 'b'); // FAILS
        }

        fn isolated_loop_query(n: u64) {
            let mut i = 0u64;
            while i < n
                invariant i <= n,
                decreases n - i,
            {
                assert("hello"@.len() == 5); // FAILS
                i += 1;
            }
        }

        proof fn nonlinear_query() {
            assert(("abc"@.len() as int) * ("abc"@.len() as int) == 9) // FAILS
                by (nonlinear_arith);
        }

        #[verifier::opaque]
        #[verifier::auto_reveal_strlit(true)]
        spec fn prefix() -> Seq<char> { "text/"@ }
        proof fn definition_stays_hidden() {
            assert(prefix().len() == 5); // FAILS
        }
        proof fn literal_stays_hidden() {
            assert("text/"@.len() == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file! {
    #[test] test_auto_reveal_byteslit verus_code! {
        use vstd::prelude::*;

        spec fn combine(first: Seq<u8>, second: Seq<u8>) -> Seq<u8> {
            first + b" "@ + second
        }

        #[verifier::auto_reveal_byteslit(true)]
        proof fn check_hello_world(first: Seq<u8>, second: Seq<u8>)
            requires
                first =~= b"hello"@,
                second =~= b"world"@,
            ensures
                combine(first, second) =~= b"hello world"@,
        {
            assert(first + b" "@ + second == b"hello world"@);
        }

        spec fn has_prefix(bytes: Seq<u8>, prefix: Seq<u8>) -> bool {
            bytes.len() >= prefix.len()
                && bytes.subrange(0, prefix.len() as int) == prefix
        }

        #[verifier::auto_reveal_byteslit(true)]
        proof fn check_prefix_ab(bytes: Seq<u8>)
            requires
                has_prefix(bytes, b"abc"@),
        {
            // Relate two different literals: knowing their lengths is not enough.
            assert(bytes.subrange(0, 2) == b"ab"@);
        }

        #[verifier::auto_reveal_byteslit(true)]
        proof fn check_masked_pattern(pattern: Seq<u8>, mask: Seq<u8>)
            requires
                pattern =~= b"\x89\x00HTML"@,
                mask =~= b"\xFF\x00\xDF\xDF\xDF\xDF"@,
        {
            assert(pattern.len() == mask.len());

            assert forall|i: int| #![trigger pattern[i]]
                0 <= i < pattern.len()
                implies (pattern[i] & mask[i]) == pattern[i]
            by {
                let p = pattern[i];
                let m = mask[i];
                assert((p & m) == p) by (bit_vector)
                    requires
                        m == 0xFFu8
                        || (m == 0x00u8 && p == 0x00u8)
                        || (m == 0xDFu8 && 0x40u8 <= p && p < 0x60u8),
                ;
            }
        }

        #[verifier::auto_reveal_byteslit(true)]
        proof fn function_query(input: Seq<u8>)
            requires input == b"abc"@,
            ensures input[1] == b'b',
        {
            assert(input[0] == b'a');
        }

        #[verifier::auto_reveal_byteslit(true)]
        fn isolated_loop_query(n: u64) {
            let mut i = 0u64;
            while i < n
                invariant i <= n,
                decreases n - i,
            {
                assert(b"hello"@[0] == b'h');
                assert(b"\x00\xFF"@[1] == 255u8);
                i += 1;
            }
        }

        #[verifier::auto_reveal_byteslit(true)]
        proof fn nonlinear_query() {
            assert((b"\x03"@[0] as int) * (b"\x03"@[0] as int) == 9)
                by (nonlinear_arith);
        }

        #[verifier::opaque]
        #[verifier::auto_reveal_byteslit(true)]
        spec fn prefix() -> Seq<u8> {
            b"text/"@
        }

        proof fn caller(tail: Seq<u8>) {
            reveal(prefix);
            assert(prefix()[0] == b't');
            assert(b"text/"@[4] == b'/');
            let input = prefix() + tail;
            assert(input.subrange(5, input.len() as int) =~= tail);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_auto_reveal_byteslit_fails verus_code! {
        use vstd::prelude::*;

        proof fn function_query(input: Seq<u8>)
            requires input == b"abc"@,
        {
            assert(input[0] == b'a'); // FAILS
        }

        fn isolated_loop_query(n: u64) {
            let mut i = 0u64;
            while i < n
                invariant i <= n,
                decreases n - i,
            {
                assert(b"hello"@[0] == b'h'); // FAILS
                i += 1;
            }
        }

        proof fn nonlinear_query() {
            assert((b"\x03"@[0] as int) * (b"\x03"@[0] as int) == 9) // FAILS
                by (nonlinear_arith);
        }

        #[verifier::opaque]
        #[verifier::auto_reveal_byteslit(true)]
        spec fn prefix() -> Seq<u8> { b"text/"@ }
        proof fn definition_stays_hidden() {
            assert(prefix() =~= seq![b't', b'e', b'x', b't', b'/']); // FAILS
        }
        proof fn literal_stays_hidden() {
            assert(b"text/"@[4] == b'/'); // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] test_crate_inheritance ["no-auto-import-verus_builtin"] => code! {
        #![verifier::auto_reveal_strlit]
        #![verifier::auto_reveal_byteslit]
        use vstd::prelude::*;
        verus! {
            proof fn test() {
                assert("abc"@[1] == 'b');
                assert(b"def"@[1] == b'e');
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_module_inheritance verus_code! {
        #[verifier::auto_reveal_strlit(true)]
        #[verifier::auto_reveal_byteslit(true)]
        mod enabled {
            use vstd::prelude::*;

            proof fn contracts(s: Seq<char>, b: Seq<u8>)
                requires s == "abc"@, b == b"def"@,
                ensures s[1] == 'b', b[1] == b'e',
            {}

            mod nested {
                use vstd::prelude::*;

                fn executable() {
                    let s = "ghi";
                    let b = b"jkl";
                    assert(s@[1] == 'h');
                    assert(b@[1] == b'k');
                }
            }

            #[verifier::auto_reveal_strlit(false)]
            #[verifier::auto_reveal_byteslit(false)]
            mod disabled {
                use vstd::prelude::*;

                #[verifier::auto_reveal_strlit]
                #[verifier::auto_reveal_byteslit]
                proof fn reenabled() {
                    assert("mno"@[1] == 'n');
                    assert(b"pqr"@[1] == b'q');
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_module_and_function_overrides verus_code! {
        #[verifier::auto_reveal_strlit]
        #[verifier::auto_reveal_byteslit]
        mod enabled {
            use vstd::prelude::*;

            #[verifier::auto_reveal_strlit(false)]
            proof fn strings_disabled() {
                assert(b"abc"@[1] == b'b');
                assert("def"@[1] == 'e'); // FAILS
            }

            #[verifier::auto_reveal_byteslit(false)]
            proof fn bytes_disabled() {
                assert("ghi"@[1] == 'h');
                assert(b"jkl"@[1] == b'k'); // FAILS
            }

            #[verifier::auto_reveal_strlit(false)]
            #[verifier::auto_reveal_byteslit(false)]
            mod disabled {
                use vstd::prelude::*;

                proof fn strings() {
                    assert("mno"@[1] == 'n'); // FAILS
                }

                proof fn bytes() {
                    assert(b"pqr"@[1] == b'q'); // FAILS
                }
            }
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] test_expression_and_block_enable verus_code! {
        use vstd::prelude::*;

        proof fn test() {
            #[verifier::auto_reveal_strlit]
            #[verifier::auto_reveal_byteslit]
            {
                assert("abc"@[1] == 'b');
                assert(b"def"@[1] == b'e');

                #[verifier::auto_reveal_strlit(false)]
                #[verifier::auto_reveal_byteslit(false)]
                {
                    let s = #[verifier::auto_reveal_strlit(true)] "ghi";
                    let b = #[verifier::auto_reveal_byteslit(true)] b"jkl";
                    assert(s@[1] == 'h');
                    assert(b@[1] == b'k');
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_expression_and_block_disable verus_code! {
        use vstd::prelude::*;

        #[verifier::auto_reveal_strlit]
        #[verifier::auto_reveal_byteslit]
        proof fn block_strings() {
            #[verifier::auto_reveal_strlit(false)]
            {
                assert(b"abc"@[1] == b'b');
                assert("def"@[1] == 'e'); // FAILS
            }
        }

        #[verifier::auto_reveal_strlit]
        #[verifier::auto_reveal_byteslit]
        proof fn block_bytes() {
            #[verifier::auto_reveal_byteslit(false)]
            {
                assert("ghi"@[1] == 'h');
                assert(b"jkl"@[1] == b'k'); // FAILS
            }
        }

        #[verifier::auto_reveal_strlit]
        proof fn literal_string() {
            let s = #[verifier::auto_reveal_strlit(false)] "mno";
            assert(s@[1] == 'n'); // FAILS
        }

        #[verifier::auto_reveal_byteslit]
        proof fn literal_bytes() {
            let b = #[verifier::auto_reveal_byteslit(false)] b"pqr";
            assert(b@[1] == b'q'); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] test_closest_marker verus_code! {
        #[verifier::auto_reveal_strlit(true)]
        #[verifier::auto_reveal_byteslit(true)]
        mod enabled {
            use vstd::prelude::*;

            // Module true -> function false -> block true -> block false -> literal true.
            #[verifier::auto_reveal_strlit(false)]
            #[verifier::auto_reveal_byteslit(false)]
            proof fn closest_true() {
                #[verifier::auto_reveal_strlit(true)]
                #[verifier::auto_reveal_byteslit(true)]
                {
                    assert("mno"@[1] == 'n');
                    assert(b"pqr"@[1] == b'q');

                    #[verifier::auto_reveal_strlit(false)]
                    #[verifier::auto_reveal_byteslit(false)]
                    {
                        let s = #[verifier::auto_reveal_strlit(true)] "abc";
                        let b = #[verifier::auto_reveal_byteslit(true)] b"def";
                        assert(s@[1] == 'b');
                        assert(b@[1] == b'e');
                    }
                }
            }

            // Without a literal-level override, the innermost block's false wins.
            // Use distinct literals so an enabled occurrence cannot supply their facts.
            #[verifier::auto_reveal_strlit(false)]
            proof fn closest_false_string() {
                #[verifier::auto_reveal_strlit(true)]
                {
                    #[verifier::auto_reveal_strlit(false)]
                    {
                        assert("ghi"@[1] == 'h'); // FAILS
                    }
                }
            }

            #[verifier::auto_reveal_byteslit(false)]
            proof fn closest_false_bytes() {
                #[verifier::auto_reveal_byteslit(true)]
                {
                    #[verifier::auto_reveal_byteslit(false)]
                    {
                        assert(b"jkl"@[1] == b'k'); // FAILS
                    }
                }
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_inherited_queries verus_code! {
        mod enabled {
            #![verifier::auto_reveal_strlit]
            #![verifier::auto_reveal_byteslit]
            use vstd::prelude::*;

            fn loops(n: u64) {
                let mut i = 0;
                while i < n
                    invariant i <= n,
                    decreases n - i,
                {
                    assert("abc"@[1] == 'b');
                    assert(b"def"@[1] == b'e');
                    i += 1;
                }
            }

            proof fn nonlinear() {
                assert("abc"@.len() * "abc"@.len() == 9) by (nonlinear_arith);
                assert((b"\x03"@[0] as int) * (b"\x03"@[0] as int) == 9)
                    by (nonlinear_arith);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_scope_does_not_leak verus_code! {
        use vstd::prelude::*;

        #[verifier::auto_reveal_strlit]
        #[verifier::auto_reveal_byteslit]
        proof fn enabled() {
            assert("abc"@[1] == 'b');
            assert(b"def"@[1] == b'e');
        }

        proof fn sibling_string() {
            assert("abc"@[1] == 'b'); // FAILS
        }

        proof fn sibling_bytes() {
            assert(b"def"@[1] == b'e'); // FAILS
        }

        proof fn block_string() {
            #[verifier::auto_reveal_strlit]
            { assert("ghi"@[1] == 'h'); }
            assert("jkl"@[1] == 'k'); // FAILS
        }

        proof fn block_bytes() {
            #[verifier::auto_reveal_byteslit]
            { assert(b"mno"@[1] == b'n'); }
            assert(b"pqr"@[1] == b'q'); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] test_opaque_and_closed_specs verus_code! {
        use vstd::prelude::*;

        #[verifier::auto_reveal_strlit]
        #[verifier::auto_reveal_byteslit]
        mod definitions {
            use vstd::prelude::*;

            #[verifier::opaque]
            pub open spec fn string() -> Seq<char> { "abc"@ }

            #[verifier::opaque]
            pub open spec fn bytes() -> Seq<u8> { b"def"@ }

            pub closed spec fn hidden_string() -> Seq<char> { "ghi"@ }
            pub closed spec fn hidden_bytes() -> Seq<u8> { b"jkl"@ }
        }

        proof fn revealed() {
            reveal(definitions::string);
            reveal(definitions::bytes);
            assert(definitions::string()[1] == 'b');
            assert(definitions::bytes()[1] == b'e');
        }

        proof fn opaque_string() {
            assert(definitions::string()[1] == 'b'); // FAILS
        }

        proof fn opaque_bytes() {
            assert(definitions::bytes()[1] == b'e'); // FAILS
        }

        proof fn opaque_string_literal() {
            assert("abc"@[1] == 'b'); // FAILS
        }

        proof fn opaque_bytes_literal() {
            assert(b"def"@[1] == b'e'); // FAILS
        }

        proof fn closed_string_literal() {
            let s = definitions::hidden_string();
            assert("ghi"@[1] == 'h'); // FAILS
        }

        proof fn closed_bytes_literal() {
            let b = definitions::hidden_bytes();
            assert(b"jkl"@[1] == b'k'); // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file! {
    #[test] test_literal_lowering verus_code! {
        use vstd::prelude::*;

        #[verifier::auto_reveal_strlit]
        #[verifier::auto_reveal_byteslit]
        fn test() {
            let f = || {
                let s = "abc";
                let b = b"def";
                assert(s@[1] == 'b');
                assert(b@[1] == b'e');
            };
            f();
            let s = "ghi";
            match s {
                "ghi" => { assert(s@[1] == 'h'); }
                _ => {}
            }
            proof {
                reveal_strlit("jkl");
                reveal_byteslit(b"mno");
                assert("jkl"@[1] == 'k');
                assert(b"mno"@[1] == b'n');
            }
        }
    } => Ok(())
}

// Attributes on compound expressions and closure expressions.

test_verify_one_file! {
    #[test] test_expression_call_enable verus_code! {
        use vstd::prelude::*;

        spec fn identity<A>(x: A) -> A { x }

        proof fn test() {
            let s = #[verifier::auto_reveal_strlit] identity("abc"@);
            let b = #[verifier::auto_reveal_byteslit] identity(b"def"@);
            assert(s[1] == 'b');
            assert(b[1] == b'e');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_expression_call_disable verus_code! {
        use vstd::prelude::*;

        spec fn identity<A>(x: A) -> A { x }

        #[verifier::auto_reveal_strlit]
        proof fn strings() {
            let s = #[verifier::auto_reveal_strlit(false)] identity("abc"@);
            assert(s[1] == 'b'); // FAILS
        }

        #[verifier::auto_reveal_byteslit]
        proof fn bytes() {
            let b = #[verifier::auto_reveal_byteslit(false)] identity(b"def"@);
            assert(b[1] == b'e'); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_expression_exec_closure_enable verus_code! {
        use vstd::prelude::*;

        fn test() {
            let f = #[verifier::auto_reveal_strlit]
                #[verifier::auto_reveal_byteslit] || {
                    assert("abc"@[1] == 'b');
                    assert(b"def"@[1] == b'e');
                };
            f();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_expression_exec_closure_disable verus_code! {
        use vstd::prelude::*;

        #[verifier::auto_reveal_strlit]
        #[verifier::auto_reveal_byteslit]
        fn strings() {
            let f = #[verifier::auto_reveal_strlit(false)] || {
                assert(b"abc"@[1] == b'b');
                assert("def"@[1] == 'e'); // FAILS
            };
            f();
        }

        #[verifier::auto_reveal_strlit]
        #[verifier::auto_reveal_byteslit]
        fn bytes() {
            let f = #[verifier::auto_reveal_byteslit(false)] || {
                assert("ghi"@[1] == 'h');
                assert(b"jkl"@[1] == b'k'); // FAILS
            };
            f();
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_expression_spec_closure_enable verus_code! {
        use vstd::prelude::*;

        proof fn test() {
            let s = #[verifier::auto_reveal_strlit] |i: int| "abc"@[i];
            let b = #[verifier::auto_reveal_byteslit] |i: int| b"def"@[i];
            assert(s(1) == 'b');
            assert(b(1) == b'e');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_expression_spec_closure_disable verus_code! {
        use vstd::prelude::*;

        #[verifier::auto_reveal_strlit]
        proof fn strings() {
            let s = #[verifier::auto_reveal_strlit(false)] |i: int| "abc"@[i];
            assert(s(1) == 'b'); // FAILS
        }

        #[verifier::auto_reveal_byteslit]
        proof fn bytes() {
            let b = #[verifier::auto_reveal_byteslit(false)] |i: int| b"def"@[i];
            assert(b(1) == b'e'); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_expression_nested_closure_override verus_code! {
        use vstd::prelude::*;

        fn test() {
            let outer = #[verifier::auto_reveal_strlit]
                #[verifier::auto_reveal_byteslit] || {
                    assert("abc"@[1] == 'b');
                    assert(b"def"@[1] == b'e');
                    let inner = #[verifier::auto_reveal_strlit(false)]
                        #[verifier::auto_reveal_byteslit(false)] || {
                            let s = #[verifier::auto_reveal_strlit] "ghi";
                            let b = #[verifier::auto_reveal_byteslit] b"jkl";
                            assert(s@[1] == 'h');
                            assert(b@[1] == b'k');
                        };
                    inner();
                };
            outer();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_expression_closure_call_site_is_not_definition_scope verus_code! {
        use vstd::prelude::*;

        fn strings() {
            let f = || {
                assert("abc"@[1] == 'b'); // FAILS
            };
            #[verifier::auto_reveal_strlit]
            f();
        }

        fn bytes() {
            let f = || {
                assert(b"def"@[1] == b'e'); // FAILS
            };
            #[verifier::auto_reveal_byteslit]
            f();
        }
    } => Err(err) => assert_fails(err, 2)
}
