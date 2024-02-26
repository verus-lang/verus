#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// All these tests are marked as #[ignore] unless Verus is compiled with `--features singular`
test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    simple_1 verus_code! {
        proof fn test(x: int, y: int, z:int, m:int) by(integer_ring)
          requires (x-y) % m == 0
          ensures (x*z- y*z) % m == 0
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    simple_2 verus_code! {
        proof fn test(x: int, y: int, z:int) by(integer_ring)
            ensures
                (x+y+z)*(x+y+z) == x*x + y*y + z*z + 2*(x*y + y*z + z*x)
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    mont_mul_1 verus_code! {
        proof fn test(a:int, s:int, R:int, M:int, RR:int, R_INV:int) by(integer_ring)
            requires
                (a * R - RR * s) % M == 0,
                (R_INV * R - 1) % M == 0,
                (RR - R * R % M) == 0,
            ensures
                (a - s*R) % M == 0
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    mont_mul_2 verus_code! {
        proof fn test(p2_full: int, BASE: int, ui: int, m0: int, m0d: int, p1_lh: int, p1_full: int) by(integer_ring)
            requires
                p2_full == ui * m0 + p1_lh,
                (p1_full - p1_lh) % BASE == 0,
                (m0d * m0 - (BASE-1)) % BASE == 0,
                (ui - p1_full * m0d) % BASE == 0,
            ensures
                p2_full % BASE == 0
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    wide_mul verus_code! {
        proof fn test (
            B: int,
            p0: int, p1: int, p2: int, p3: int,
            p4: int, p5: int, p6: int, p7: int,
            p8: int, p9: int, p10: int, p11: int,
            p12: int, p13: int, p14: int, p15: int,
            x: int, x_0: int, x_1: int, x_2: int, x_3: int,
            y: int, y_0: int, y_1: int,y_2: int, y_3: int) by(integer_ring)

            requires
                x == x_0 + x_1 * B + x_2 * B * B + x_3 * B * B * B,
                y == y_0 + y_1 * B + y_2 * B * B + y_3 * B * B * B,
                p0 == x_0 * y_0,
                p1 == x_1 * y_0,
                p2 == x_0 * y_1,
                p3 == x_2 * y_0,
                p4 == x_1 * y_1,
                p5 == x_0 * y_2,
                p6 == x_3 * y_0,
                p7 == x_2 * y_1,
                p8 == x_1 * y_2,
                p9 == x_0 * y_3,
                p10 == x_3 * y_1,
                p11 == x_2 * y_2,
                p12 == x_1 * y_3,
                p13 == x_3 * y_2,
                p14 == x_2 * y_3,
                p15 == x_3 * y_3,
            ensures
                x * y == p0 + (p1 + p2) * B + (p3 + p4 + p5) * B * B + (p6 + p7 + p8 + p9) * B * B * B + (p10 + p11 + p12) * B * B * B * B + (p13 + p14) * B * B * B * B * B + p15 * B * B * B * B * B * B

        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    uninterpreted_function verus_code! {
        spec fn square(a:int) -> int{
            a*a
        }
        spec fn quad(a:int) -> int{
            a*a*a*a
        }
        proof fn test(x:int, y:int, m:int) by(integer_ring)
            requires
                (square(x) - square(y)) % m == 0,
                square(x) == x*x,
                square(y) == y*y,
                quad(x) == x*x*x*x,
                quad(y) == y*y*y*y,
            ensures (quad(x) - quad(y)) % m == 0
        {}
    } => Ok(())
}

// Failing test cases
test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    simple_fail_1 verus_code! {
        proof fn test(x: int, y: int, z:int, m:int) by(integer_ring)
            requires
                (x-y) % m == 0
            ensures (x*z + y*z) % m == 0 //FAILS
        {}
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    simple_fail_2 verus_code! {
        proof fn test(x: int, y: int, z:int) by(integer_ring)
            ensures
                (x+y+z)*(x+y+z) == x*x + y*y + z + 2*(x*y + y*z + z*x) // FAILS
        {}
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    wide_mul_fail verus_code! {
        proof fn test(
            B: int,
            p0: int, p1: int, p2: int, p3: int,
            p4: int, p5: int, p6: int, p7: int,
            p8: int, p9: int, p10: int, p11: int,
            p12: int, p13: int, p14: int, p15: int,
            x: int, x_0: int, x_1: int, x_2: int, x_3: int,
            y: int, y_0: int, y_1: int,y_2: int, y_3: int) by(integer_ring)

            requires
                x == x_0 + x_1 * B + x_2 * B * B + x_3 * B * B * B,
                y == y_0 + y_1 * B + y_2 * B * B + y_3 * B * B * B,
                p0 == x_0 * y_0,
                p1 == x_1 * y_0,
                p2 == x_0 * y_1,
                p3 == x_2 * y_0,
                p4 == x_1 * y_1,
                p5 == x_0 * y_2,
                p6 == x_3 * y_0,
                p7 == x_2 * y_2,   // originally  p7 == x_2 * y_1
                p8 == x_1 * y_2,
                p9 == x_0 * y_3,
                p10 == x_3 * y_1,
                p11 == x_2 * y_2,
                p12 == x_1 * y_3,
                p13 == x_3 * y_2,
                p14 == x_2 * y_3,
                p15 == x_3 * y_3,
            ensures x * y == p0 + (p1 + p2) * B + (p3 + p4 + p5) * B * B + (p6 + p7 + p8 + p9) * B * B * B + (p10 + p11 + p12) * B * B * B * B + (p13 + p14) * B * B * B * B * B + p15 * B * B * B * B * B * B // FAILS
        {}
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    type_fail verus_code! {
        proof fn test(x: u32, y: u32, z:u32, m:int) by(integer_ring) // FAILS (not supported)
            requires
              (x-y) % m == 0
            ensures
              (x*z - y*z) % m == 0
        {}
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    reserved_keyword verus_code! {
        proof fn test(singular_tmp_1 : int, y: int, z:int, m:int) by(integer_ring)
            requires (singular_tmp_1 - y) % m == 0
            ensures (singular_tmp_1 * z- y*z) % m == 0
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    div_by_zero_fail verus_code! {
        proof fn may_div_zero(x : int) by(integer_ring)
            ensures x % x == 0
        {}

        proof fn div_by_zero_fails() {
            let a = 0int;
            may_div_zero(a);
            assert(a % a == 0); // FAILS , `x` shouldn't be zero
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    mul_mod_noop verus_code! {
        pub proof fn test(x: int, y: int, m: int) by(integer_ring)
            ensures
                ((x % m) * y) % m == (x * y) % m,
                (x * (y % m)) % m == (x * y) % m,
                ((x % m) * (y % m)) % m == (x * y) % m
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    mul_mod_noop_fail_1 verus_code! {
        pub proof fn test(x: int, y: int, m: int) by(integer_ring)
            ensures
                ((x % m) * y) % m == (x * y) % m,
                ((x % m) * (y % m)) % m == (x) % m, // FAILS
                (x * (y % m)) % m == (x * y) % m
        {}
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    mul_mod_noop_fail_2 verus_code! {
        pub proof fn test(x: int, y: int, m: int) by(integer_ring)
            ensures
                ((x % m) * y) % m == (x * y) % m,
                ((x % m) * (y % m)) % m == (x) % m, // FAILS
                (x * (y % m)) % m == (x) % m // also FAILS (but should not report this, since we stop at the first failure)
        {}
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    neq_not_supported verus_code! {
        proof fn test(x: int, y: int, z:int, m:int) by(integer_ring)
            requires (x-y) % m != 0  //FAILS (not supported)
            ensures (x*z + y*z) % m == 0
        {}
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    gt_not_supported verus_code! {
        proof fn test(x: int, y: int, z:int, m:int) by(integer_ring)
            requires (x-y) % m > 0  //FAILS (not supported)
            ensures (x*z + y*z) % m == 0
        {}
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test]
    #[cfg_attr(not(feature = "singular"), ignore)]
    lt_not_supported verus_code! {
        proof fn test(x: int, y: int, z:int, m:int) by(integer_ring)
            requires (x-y) % m == 0
            ensures (x*z + y*z) % m < 0 //FAILS (not supported)
        {}
    } => Err(err) => assert_one_fails(err)
}
