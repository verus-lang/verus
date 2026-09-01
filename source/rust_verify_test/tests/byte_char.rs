#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] byte_char_literals verus_code! {
        const ZERO: u8 = b'\x00';
        const SPACE: u8 = b' ';
        const GREATER_THAN: u8 = b'>';
        const MAX: u8 = b'\xff';

        proof fn values() {
            assert(b'\x00' == 0u8);
            assert(b' ' == 0x20u8);
            assert(b'>' == 0x3eu8);
            assert(b'\xff' == 255u8);

            assert(ZERO == 0u8);
            assert(SPACE == 0x20u8);
            assert(GREATER_THAN == 0x3eu8);
            assert(MAX == 255u8);
        }

        fn is_separator(d: u8) -> (result: bool)
            ensures
                result == (d == 0x20u8 || d == 0x3eu8),
        {
            d == b' ' || d == b'>'
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] byte_char_set_literal_0 verus_code! {
        use vstd::set::*;

        proof fn empty() {
            let s1: Set<u8> = set![];
            let s2: Set<u8> = set![];
            assert(s1 =~= s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] byte_char_set_literal_1 verus_code! {
        use vstd::set::*;

        proof fn singleton() {
            let s1: Set<u8> = set![b' '];
            let s2: Set<u8> = set![0x20u8];
            assert(s1 =~= s2);
        }

        proof fn escaped_singleton() {
            let s1: Set<u8> = set![b'\xff'];
            let s2: Set<u8> = set![255u8];
            assert(s1 =~= s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] byte_char_set_literal_2 verus_code! {
        use vstd::set::*;

        proof fn two_elements() {
            let s1: Set<u8> = set![b' ', b'>'];
            let s2: Set<u8> = set![b'>', b' '];

            assert(s1 =~= s2);
            assert(s1.contains(0x20u8));
            assert(s1.contains(0x3eu8));
        }

        proof fn comma_at_end() {
            let s1: Set<u8> = set![b' ', b'>',];
            let s2: Set<u8> = set![b'>', b' ',];
            assert(s1 =~= s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] byte_char_seq_literals verus_code! {
        use vstd::seq::*;

        proof fn ascii() {
            let s: Seq<u8> = seq![b'R', b'I', b'F', b'F'];

            assert(s.len() == 4);
            assert(s.index(0) == 0x52u8);
            assert(s.index(1) == 0x49u8);
            assert(s.index(2) == 0x46u8);
            assert(s.index(3) == 0x46u8);
        }

        proof fn escaped() {
            let s: Seq<u8> = seq![b'\x00', b' ', b'>', b'\xff'];

            assert(s.index(0) == 0u8);
            assert(s.index(1) == 0x20u8);
            assert(s.index(2) == 0x3eu8);
            assert(s.index(3) == 255u8);
        }

        proof fn comma_at_end() {
            let s: Seq<u8> = seq![b'R', b'I', b'F', b'F',];
            assert(s.len() == 4);
            assert(s.index(2) == 0x46u8);
        }
    } => Ok(())
}
