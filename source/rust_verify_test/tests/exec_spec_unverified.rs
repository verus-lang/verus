// Tests for additional features in the exec_spec_unverified! macro.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    #[allow(unused_imports)] use vstd::prelude::*;
    #[allow(unused_imports)] use vstd::contrib::exec_spec::*;
};

test_verify_one_file! {
    // Test quantifiers with multiple variables
    #[test] test_exec_spec_unverified_multivar_quant IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
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

test_verify_one_file! {
    // Test quantifiers over char
    #[test] test_exec_spec_unverified_char_quant IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
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

test_verify_one_file! {
    // Test using exec_spec_verified! and exec_spec_unverified! macros together
    #[test] test_exec_spec_mixed_modes IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct X {
                a: u32,
                b: bool
            }

            spec fn x_test1(x1: X, x2: X) -> bool {
                x1 == x2 && !x1.b
            }
        }

        exec_spec_unverified! {
            spec fn forall_char_le_le() -> bool {
                forall |c: char| #![trigger c as u32] 'A' <= c <= 'Z' ==> c != '!'
            }

            spec fn x_test2(x: X) -> u32 {
                x.a
            }

            spec fn x_test3(x1: X, x2: X) -> bool {
                x_test1(x1, x2)
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Test ensuring that specification is generated on code compiled from exec_spec_unverified!
    #[test] test_exec_spec_unverified_spec IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            spec fn test1() -> bool {
                true
            }
        }

        exec_spec_unverified! {
            spec fn test2() -> bool {
                true
            }
        }

        fn exc() {
            let res1 = exec_test1();
            assert(res1);

            let res2 = exec_test2();
            assert(res2);
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests a basic inherent impl with a `&self` method in unverified mode.
    #[test] test_exec_spec_unverified_impl_basic IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            struct Point {
                x: u32,
                y: u32,
            }

            impl Point {
                spec fn get_x(&self) -> u32 {
                    self.x
                }

                spec fn sum(&self) -> u32
                    recommends self.x + self.y <= u32::MAX
                {
                    (self.x + self.y) as u32
                }
            }
        }

        fn sanity_check() {
            let p = ExecPoint { x: 3, y: 4 };
            let xv = p.exec_get_x();
            assert(xv == 3);
            let s = p.exec_sum();
            if s == 7 {
                assert(p.x + p.y == 7);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests an impl on an enum with `&self` methods over multiple variants in unverified mode.
    #[test] test_exec_spec_unverified_impl_enum IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            enum Shape {
                Circle(u32),
                Rect { w: u32, h: u32 },
                Unit,
            }

            impl Shape {
                spec fn is_unit(&self) -> bool {
                    match self {
                        Shape::Unit => true,
                        _ => false,
                    }
                }

                spec fn describe(&self) -> SpecString {
                    match self {
                        Shape::Circle(_) => "circle"@,
                        Shape::Rect { .. } => "rect"@,
                        Shape::Unit => "unit"@,
                    }
                }
            }
        }

        fn sanity_check() {
            let c = ExecShape::Circle(5);
            let u = ExecShape::Unit;
            let c_is = c.exec_is_unit();
            let u_is = u.exec_is_unit();
            assert(!c_is);
            assert(u_is);
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests impl methods with additional parameters beyond the receiver in unverified mode.
    #[test] test_exec_spec_unverified_impl_method_args IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            struct Counter {
                count: u32,
            }

            impl Counter {
                spec fn plus(&self, n: u32) -> u32
                    recommends self.count + n <= u32::MAX
                {
                    (self.count + n) as u32
                }

                spec fn between(&self, lo: u32, hi: u32) -> bool {
                    lo <= self.count && self.count <= hi
                }
            }
        }

        fn sanity_check() {
            let c = ExecCounter { count: 10 };
            let b = c.exec_between(0, 20);
            if b {
                assert(0 <= c.count && c.count <= 20);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests impls used across both verified and unverified modules.
    #[test] test_exec_spec_unverified_impl_mixed_modes IMPORTS.to_string() + verus_code_str! {
        exec_spec_verified! {
            struct Pair(u32, u32);

            impl Pair {
                spec fn ordered(&self) -> bool {
                    self.0 <= self.1
                }
            }
        }

        exec_spec_unverified! {
            spec fn pair_eq_ordered(p: Pair) -> bool {
                p.ordered()
            }
        }

        fn sanity_check() {
            let p = ExecPair(2, 5);
            let o = p.exec_ordered();
            let r = exec_pair_eq_ordered(&p);
            assert(o == r);
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests an unverified impl using a quantifier in the method body.
    #[test] test_exec_spec_unverified_impl_quant IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            struct Bag {
                items: Seq<u8>,
            }

            impl Bag {
                spec fn all_nonzero(&self) -> bool {
                    forall |i: usize| 0 <= i < self.items.len() ==> self.items[i as int] != 0
                }
            }
        }

        fn sanity_check() {
            let b = ExecBag { items: vec![1, 2, 3] };
            let _ = b.exec_all_nonzero();
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Tests that trait impls are still rejected in unverified mode.
    #[test] test_exec_spec_unverified_impl_trait_rejected IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            struct S {
                x: u32,
            }

            trait T {
                spec fn f(&self) -> u32;
            }

            impl T for S {
                spec fn f(&self) -> u32 {
                    self.x
                }
            }
        }
    } => Err(_)
}
