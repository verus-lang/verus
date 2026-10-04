#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] byte_string_opaque_without_reveal verus_code! {
        use vstd::prelude::*;

        fn test() {
            let bytes: &'static [u8; 4] = b"RIFF";

            // The array length is part of the type.
            assert(bytes@.len() == 4);

            // The contents remain opaque until reveal_byteslit is called.
            assert(bytes@[0] == b'R'); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] byte_string_reveal_contents verus_code! {
        use vstd::prelude::*;

        const ICON_PATTERN: &'static [u8; 4] =
            b"\x00\x00\x02\x00";

        fn direct_array_reference() {
            proof {
                reveal_byteslit(b"RIFF");
            }

            let bytes: &'static [u8; 4] = b"RIFF";

            assert(bytes@.len() == 4);
            assert(bytes@ =~= seq![b'R', b'I', b'F', b'F']);
        }

        fn direct_slice_reference() {
            proof {
                reveal_byteslit(b"\x00\x00\x02\x00");
            }

            // Exercises local coercion from &[u8; 4] to &[u8].
            let bytes: &'static [u8] = b"\x00\x00\x02\x00";

            assert(bytes@.len() == 4);
            assert(bytes@ =~= seq![0u8, 0u8, 2u8, 0u8]);
        }

        fn constant_array_reference() {
            proof {
                reveal_byteslit(b"\x00\x00\x02\x00");
            }

            assert(ICON_PATTERN@.len() == 4);
            assert(ICON_PATTERN@ =~= seq![0u8, 0u8, 2u8, 0u8]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] byte_string_reveal_soundness verus_code! {
        use vstd::prelude::*;

        fn wrong_byte() {
            proof {
                reveal_byteslit(b"RIFF");
            }

            let bytes: &'static [u8] = b"RIFF";
            assert(bytes@[1] == b'X'); // FAILS
        }

        fn wrong_length() {
            proof {
                reveal_byteslit(b"\x00\x00\x02\x00");
            }

            let bytes: &'static [u8] = b"\x00\x00\x02\x00";
            assert(bytes@.len() == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] byte_string_distinct_same_length verus_code! {
        const X: &'static [u8; 3] = b"ABC";
        const Y: &'static [u8; 3] = b"XYZ";

        fn test() {
            // No reveal: this depends on opaque literal identity/injectivity.
            assert(!(X === Y));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] byte_string_same_literal_equal verus_code! {
        const X: &'static [u8; 3] = b"ABC";
        const Y: &'static [u8; 3] = b"ABC";

        fn test() {
            assert(X === Y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] reveal_byteslit_requires_literal verus_code! {
        use vstd::prelude::*;

        fn test() {
            proof {
                reveal_byteslit(12u32);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "byte-string literal expected")
}

test_verify_one_file! {
    #[test] reveal_byteslit_requires_one_argument verus_code! {
        use vstd::prelude::*;

        fn test() {
            proof {
                reveal_byteslit(b"a", b"b");
            }
        }
    } => Err(err) => assert_rust_error_msg(
        err,
        "this function takes 1 argument but 2 arguments were supplied",
    )
}

test_verify_one_file! {
    #[test] reveal_byteslit_requires_proof_mode verus_code! {
        use vstd::prelude::*;

        fn test() {
            reveal_byteslit(b"ABC");
        }
    } => Err(err) => assert_vir_error_msg(
        err,
        "cannot use reveal_byteslit in exec mode",
    )
}

test_verify_one_file! {
    #[test] byte_string_edge_cases verus_code! {
        use vstd::prelude::*;

        fn empty() {
            proof {
                reveal_byteslit(b"");
            }

            let bytes: &'static [u8] = b"";
            assert(bytes@ =~= seq![]);
        }

        fn raw() {
            proof {
                reveal_byteslit(br"RIFF");
            }

            let bytes: &'static [u8] = br"RIFF";
            assert(bytes@ =~= seq![b'R', b'I', b'F', b'F']);
        }

        fn non_utf8() {
            proof {
                reveal_byteslit(b"\x00\x80\xfe\xff");
            }

            let bytes: &'static [u8] = b"\x00\x80\xfe\xff";
            assert(bytes@ =~= seq![0u8, 128u8, 254u8, 255u8]);
        }

        fn escapes() {
            proof {
                reveal_byteslit(b"\n\r\t\\\"");
            }

            let bytes: &'static [u8] = b"\n\r\t\\\"";
            assert(bytes@ =~= seq![b'\n', b'\r', b'\t', b'\\', b'"']);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] byte_string_in_struct verus_code! {
        use vstd::prelude::*;

        struct ByteMatcher {
            pattern: &'static [u8],
            mask: &'static [u8],
            leading_ignore: &'static [u8],
        }

        fn image_x_icon() {
            proof {
                reveal_byteslit(b"\x00\x00\x01\x00");
                reveal_byteslit(b"\xff\xff\xff\xff");
                reveal_byteslit(b"");
            }

            let matcher = ByteMatcher {
                pattern: b"\x00\x00\x01\x00",
                mask: b"\xff\xff\xff\xff",
                leading_ignore: b"",
            };

            assert(matcher.pattern@ =~= seq![0u8, 0u8, 1u8, 0u8]);
            assert(matcher.mask@ =~= seq![255u8, 255u8, 255u8, 255u8]);
            assert(matcher.leading_ignore@ =~= seq![]);
        }

        fn video_avi() {
            proof {
                reveal_byteslit(b"RIFF\x00\x00\x00\x00AVI ");
                reveal_byteslit(
                    b"\xff\xff\xff\xff\x00\x00\x00\x00\xff\xff\xff\xff"
                );
                reveal_byteslit(b"");
            }

            let matcher = ByteMatcher {
                pattern: b"RIFF\x00\x00\x00\x00AVI ",
                mask: b"\xff\xff\xff\xff\x00\x00\x00\x00\xff\xff\xff\xff",
                leading_ignore: b"",
            };

            assert(matcher.pattern@.len() == 12);
            assert(matcher.mask@.len() == 12);
            assert(matcher.pattern@[0] == b'R');
            assert(matcher.pattern@[4] == 0u8);
            assert(matcher.pattern@[8] == b'A');
            assert(matcher.pattern@[11] == b' ');
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test]
    byte_string_equality_uses_view verus_code! {
        use vstd::prelude::*;

        struct ByteSource;

        uninterp spec fn modeled_bytes(source: &ByteSource) -> Seq<u8>;

        #[verifier::external_body]
        fn get_bytes<'a>(source: &'a ByteSource) -> (result: &'a [u8])
            ensures
                result@ == modeled_bytes(source),
        {
            b"hello world"
        }

        spec fn is_hello(source: &ByteSource) -> bool {
            modeled_bytes(source) =~= b"hello world"@
        }

        fn check(source: &ByteSource) -> (result: bool)
            ensures
                result == is_hello(source),
        {
            get_bytes(source) == b"hello world"
        }
    } => Ok(())
}
