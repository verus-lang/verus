#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] signed_saturating verus_code! {
        use vstd::prelude::*;

        fn test_i8() {
            let a = 100i8.saturating_add(100);
            assert(a == i8::MAX);
            let b = (-100i8).saturating_add(-100);
            assert(b == i8::MIN);
            let c = 5i8.saturating_add(-7);
            assert(c == -2);
            let d = (-100i8).saturating_sub(100);
            assert(d == i8::MIN);
            let e = 100i8.saturating_sub(-100);
            assert(e == i8::MAX);
            let f = 5i8.saturating_sub(7);
            assert(f == -2);
        }

        fn test_generic_widths(a: i16, b: i32, c: i64, d: i128, e: isize) {
            let x = a.saturating_add(a);
            assert(i16::MIN <= 2 * a <= i16::MAX ==> x == 2 * a);
            let y = b.saturating_sub(b);
            assert(y == 0);
            let z = c.saturating_add(0);
            assert(z == c);
            let w = d.saturating_sub(1);
            assert(d > i128::MIN ==> w == d - 1);
            assert(d == i128::MIN ==> w == i128::MIN);
            let v = e.saturating_add(1);
            assert(e < isize::MAX ==> v == e + 1);
        }

        spec fn spec_sat(x: i32, y: i32) -> i32 {
            x.saturating_add(y)
        }

        proof fn test_spec() {
            assert(spec_sat(i32::MAX, 1) == i32::MAX);
            assert(spec_sat(-3i32, 2i32) == -1i32);
        }

        fn test_no_unwind(a: i8, b: i64)
            no_unwind
        {
            let _ = a.saturating_add(a);
            let _ = a.saturating_sub(a);
            let _ = b.saturating_add(b);
            let _ = b.saturating_sub(b);
        }

        fn test_wrong() {
            let a = 100i8.saturating_add(100);
            assert(a == 200 - 256); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] be_bytes verus_code! {
        use vstd::prelude::*;
        use vstd::bytes::*;

        fn test_round_trip(w: u16, x: u32, y: u64) {
            proof {
                lemma_auto_spec_u16_to_from_be_bytes();
                lemma_auto_spec_u32_to_from_be_bytes();
                lemma_auto_spec_u64_to_from_be_bytes();
            }
            let bw = w.to_be_bytes();
            let bx = x.to_be_bytes();
            let by = y.to_be_bytes();
            assert(bw@ == spec_u16_to_be_bytes(w));
            assert(spec_u16_to_be_bytes(w).len() == 2);
            assert(spec_u32_to_be_bytes(x).len() == 4);
            assert(spec_u64_to_be_bytes(y).len() == 8);
            let w2 = u16::from_be_bytes(bw);
            let x2 = u32::from_be_bytes(bx);
            let y2 = u64::from_be_bytes(by);
            assert(w2 == w);
            assert(x2 == x);
            assert(y2 == y);
        }

        fn test_value_u32() {
            let b: [u8; 4] = [0x01, 0x02, 0x03, 0x04];
            let x = u32::from_be_bytes(b);
            proof {
                lemma_spec_u32_be_bytes_def(0, b@);
                let (s0, s1, s2, s3) = (b@[0] as u32, b@[1] as u32, b@[2] as u32, b@[3] as u32);
                assert(s0 << 24 | s1 << 16 | s2 << 8 | s3 == 0x0102_0304u32) by (bit_vector)
                    requires s0 == 0x01u32 && s1 == 0x02u32 && s2 == 0x03u32 && s3 == 0x04u32;
            }
            assert(x == 0x0102_0304u32);
        }

        fn test_value_u16() {
            let b = 0xabcdu16.to_be_bytes();
            proof {
                lemma_spec_u16_be_bytes_def(0xabcdu16, seq![0u8, 0u8]);
                let x = 0xabcdu16;
                assert(((x >> 8) & 0xff) as u8 == 0xabu8 && (x & 0xff) as u8 == 0xcdu8)
                    by (bit_vector) requires x == 0xabcdu16;
            }
            assert(b[0] == 0xab);
            assert(b[1] == 0xcd);
        }

        fn test_value_u16_from() {
            let b: [u8; 2] = [0x01, 0x02];
            let x = u16::from_be_bytes(b);
            proof {
                lemma_spec_u16_be_bytes_def(0, b@);
                let (s0, s1) = (b@[0] as u16, b@[1] as u16);
                assert(s0 << 8 | s1 == 0x0102u16) by (bit_vector) requires s0 == 1u16 && s1 == 2u16;
            }
            assert(x == 0x0102u16);
        }

        fn test_le(w: u16, x: u32, y: u64) {
            proof {
                lemma_auto_spec_u16_to_from_le_bytes();
                lemma_auto_spec_u32_to_from_le_bytes();
                lemma_auto_spec_u64_to_from_le_bytes();
            }
            let bw = w.to_le_bytes();
            let bx = x.to_le_bytes();
            let by = y.to_le_bytes();
            assert(spec_u16_to_le_bytes(w).len() == 2);
            assert(spec_u32_to_le_bytes(x).len() == 4);
            let w2 = u16::from_le_bytes(bw);
            let x2 = u32::from_le_bytes(bx);
            let y2 = u64::from_le_bytes(by);
            assert(w2 == w);
            assert(x2 == x);
            assert(y2 == y);
        }

        fn test_u8(v: u8) {
            let b = v.to_be_bytes();
            assert(b[0] == v);
            let l = v.to_le_bytes();
            assert(l[0] == v);
            let v2 = u8::from_be_bytes(b);
            assert(v2 == v);
        }

        fn test_no_unwind(v: u8, w: u16, x: u32, y: u64, b2: [u8; 2], b4: [u8; 4], b8: [u8; 8])
            no_unwind
        {
            let _ = v.to_be_bytes();
            let _ = v.to_le_bytes();
            let _ = w.to_be_bytes();
            let _ = w.to_le_bytes();
            let _ = x.to_be_bytes();
            let _ = x.to_le_bytes();
            let _ = y.to_be_bytes();
            let _ = y.to_le_bytes();
            let _ = u8::from_be_bytes([v]);
            let _ = u16::from_be_bytes(b2);
            let _ = u32::from_be_bytes(b4);
            let _ = u64::from_be_bytes(b8);
        }

        fn test_wrong() {
            let b: [u8; 4] = [0x01, 0x02, 0x03, 0x04];
            let x = u32::from_be_bytes(b);
            proof {
                lemma_spec_u32_be_bytes_def(0, b@);
                let (s0, s1, s2, s3) = (b@[0] as u32, b@[1] as u32, b@[2] as u32, b@[3] as u32);
                assert(s0 << 24 | s1 << 16 | s2 << 8 | s3 == 0x0102_0304u32) by (bit_vector)
                    requires s0 == 0x01u32 && s1 == 0x02u32 && s2 == 0x03u32 && s3 == 0x04u32;
            }
            assert(x == 0x0403_0201u32); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
