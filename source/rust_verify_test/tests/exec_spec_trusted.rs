// Tests for additional features in the exec_spec_trusted! macro. These tests only check that the code compiles.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    #[allow(unused_imports)] use vstd::prelude::*;
    #[allow(unused_imports)] use vstd::contrib::exec_spec::*;
};

test_verify_one_file_with_options! {
    // Test quantifiers with multiple variables
    #[test] test_exec_spec_trusted_multivar_quant ["--compile"] => IMPORTS.to_string() + verus_code_str! {
        exec_spec_trusted! {
            spec fn spec_five(x1: u8, x2: u8, x3: u8, x4: u8, x5: u8) -> bool {
                x1 == x2 && x3 != x4 && x3 != x5 && x5 != x2
            }

            spec fn test_five_forall() -> bool {
                forall |x1: u8, x2: u8, x3: u8, x4: u8, x5: u8| 0 <= x1 < 10 && 0 <= x2 < 10 && 0 <= x3 < 10 && 0 <= x4 < 10 && 0 <= x5 < 10 ==> spec_five(x1, x2, x3, x4, x5)
            }

            spec fn test_five_exists() -> bool {
                exists |x1: u8, x2: u8, x3: u8, x4: u8, x5: u8| 0 <= x1 < 10 && 0 <= x2 < 10 && 0 <= x3 < 10 && 0 <= x4 < 10 && 0 <= x5 < 10 && spec_five(x1, x2, x3, x4, x5)
            }

            spec fn test_vec_vec_forall(v: Seq<Seq<u8>>) -> bool {
                forall |i: usize, j: usize| 0 <= i < v.len() && 0 <= j < v[i as int].len() ==> v[i as int][j as int] != 0
            }

            spec fn test_vec_vec_exists(v: Seq<Seq<u8>>) -> bool {
                exists |i: usize, j: usize| 0 <= i < v.len() && 0 <= j < v[i as int].len() && v[i as int][j as int] != 0
            }

            spec fn test_diff_bounds_forall() -> bool {
                forall |i: usize, j: usize| #![trigger i + j] 0 <= i < 2 && 5 <= j < 7 ==> i + j <= 2 * j
            }

            spec fn test_diff_bounds_exists() -> bool {
                exists |i: usize, j: usize| #![trigger i + j] 0 <= i < 2 && 5 <= j < 7 && 2 * j < i + j
            }

            spec fn test_diff_bounds_four_forall() -> bool {
                forall |i1: u8, i2: u8, i3: u8, i4: u8| #![trigger i1 + i2 + i3 + i4] 1 <= i1 < 2 && 2 <= i2 < 3 && 3 <= i3 < 4 && 4 <= i4 < 5 ==> i1 + i2 + i3 + i4 != 10
            }

            spec fn test_diff_bounds_four_exists() -> bool {
                exists |i1: u8, i2: u8, i3: u8, i4: u8| #![trigger i1 + i2 + i3 + i4] 1 <= i1 < 2 && 2 <= i2 < 3 && 3 <= i3 < 4 && 4 <= i4 < 5 && i1 + i2 + i3 + i4 == 10
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // Test quantifiers over char
    #[test] test_exec_spec_trusted_char_quant ["--compile"] => IMPORTS.to_string() + verus_code_str! {
        exec_spec_trusted! {
            spec fn forall_char_le_le() -> bool {
                forall |c: char| #![trigger c as u32] 'A' <= c <= 'Z' ==> c != '!'
            }

            spec fn forall_char_lt_le() -> bool {
                forall |c: char| #![trigger c as u32] 'A' < c <= 'Z' ==> c != '!'
            }

            spec fn forall_char_le_lt() -> bool {
                forall |c: char| #![trigger c as u32] 'A' <= c < 'Z' ==> c != '!'
            }

            spec fn forall_char_lt_lt() -> bool {
                forall |c: char| #![trigger c as u32] 'A' < c < 'Z' ==> c != '!'
            }

            spec fn exists_char_le_le() -> bool {
                exists |c: char| #![trigger c as u32] 'A' <= c <= 'Z' && c == 'K'
            }

            spec fn exists_char_lt_le() -> bool {
                exists |c: char| #![trigger c as u32] 'A' < c <= 'Z' && c == 'K'
            }

            spec fn exists_char_le_lt() -> bool {
                exists |c: char| #![trigger c as u32] 'A' <= c < 'Z' && c == 'K'
            }

            spec fn exists_char_lt_lt() -> bool {
                exists |c: char| #![trigger c as u32] 'A' < c < 'Z' && c == 'K'
            }
        }
    } => Ok(())
}
