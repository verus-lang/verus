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
    /// Tests that the postcondition of an associated fn (no receiver) refers to `T::f`,
    /// not to a module-level spec fn of the same name.
    #[test] test_exec_spec_unverified_impl_assoc_fn_shadowed IMPORTS.to_string() + verus_code_str! {
        spec fn mk(x: u8) -> u8 { 0 }

        exec_spec_unverified! {
            pub struct Foo { pub a: u8 }

            impl Foo {
                spec fn mk(x: u8) -> u8 {
                    x
                }
            }
        }

        fn test_ok() {
            let r = ExecFoo::exec_mk(5);
            assert(r == Foo::mk(5));
            assert(r == 5);
        }

        fn test_fail() {
            let r = ExecFoo::exec_mk(5);
            assert(r == 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    /// Tests that the postcondition of a `&self` method refers to the inherent method `T::f`,
    /// not to a by-value trait method `f(self)` that method-call syntax would prefer.
    #[test] test_exec_spec_unverified_impl_method_shadowed_by_trait IMPORTS.to_string() + verus_code_str! {
        trait Tr {
            spec fn get(self) -> u8;
        }

        impl Tr for Foo {
            spec fn get(self) -> u8 { 0 }
        }

        exec_spec_unverified! {
            pub struct Foo { pub a: u8 }

            impl Foo {
                spec fn get(&self) -> u8 {
                    self.a
                }
            }
        }

        fn test_ok() {
            let f = ExecFoo { a: 5 };
            let r = f.exec_get();
            assert(r == 5);
        }

        fn test_fail() {
            let f = ExecFoo { a: 5 };
            let r = f.exec_get();
            assert(r == 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    /// Tests that `Self` in the clauses of an impl method refers to the spec type.
    #[test] test_exec_spec_unverified_impl_self_in_clauses IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            struct Foo { a: u8 }

            impl Foo {
                spec fn small(x: u8) -> bool {
                    x < 100
                }

                spec fn inc(x: u8) -> u8
                    recommends Self::small(x)
                {
                    (x + 1) as u8
                }
            }
        }

        fn test() {
            let r = ExecFoo::exec_inc(5);
            assert(r == 6);
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

test_verify_one_file! {
    #[test] test_exec_spec_unverified_misc_forms IMPORTS.to_string() + verus_code_str! {
        use vstd::raw_ptr::MemContents;

        exec_spec_unverified! {
            enum E {
                A(u32),
                B { x: u32 },
            }

            spec fn guarded(x: Option<u32>) -> u32 {
                match x {
                    Some(v) if v > 3 => v,
                    _ => 0,
                }
            }

            spec fn arrow(e: E) -> u32
                recommends e is A,
            {
                e->A_0
            }

            spec fn ext_eq(a: Seq<u8>, b: Seq<u8>) -> bool {
                a =~= b
            }

            spec fn is_a(e: E) -> bool {
                is_variant(e, "A")
            }

            spec fn wrap(a: u8, b: u8) -> u8 {
                sub(add(a, b), mul(a, b))
            }

            spec fn init_value(m: MemContents<u32>) -> u32
                recommends m is Init,
            {
                m.value()
            }

            spec fn ok_val(r: Result<u32, bool>) -> u32
                recommends r is Ok,
            {
                r->Ok_0
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    /// Explicit discriminants carry over to the exec enum, so the trusted
    /// `exec_disc` agrees with `disc` at run time.
    #[test] test_exec_spec_unverified_enum_discriminant IMPORTS.to_string() + verus_code_str! {
        exec_spec_unverified! {
            #[derive(Clone, Copy)]
            pub enum E {
                A = 10,
                B = 20,
                C,
            }

            spec fn disc(e: E) -> u8 {
                e as u8
            }
        }

        fn test() {
            assert(disc(E::B) == 20);
            // the exec enum must have the same discriminants as the spec enum
            let b = ExecE::B as u8;
            assert(b == 20);
            let c = ExecE::C as u8;
            assert(c == 21);
        }
    } => Ok(())
}

/// Runs compiled quantifiers whose bounds are at the edge of the quantified type.
/// The loop bounds must not be computed as `upper + 1` / `lower + 1`, which would
/// wrap around (or panic) and make the trusted `exec_*` disagree with its spec.
#[test]
fn test_exec_spec_unverified_quant_bounds_overflow_runtime() {
    let source = code_str! {
        use vstd::prelude::*;
        use vstd::contrib::exec_spec::*;

        verus! {

        exec_spec_unverified! {
            spec fn is_seven(x: u8) -> bool {
                x == 7
            }

            spec fn has_seven(n: u8) -> bool {
                exists |x: u8| 0 <= x <= n && is_seven(x)
            }

            spec fn eq_u8(x: u8, y: u8) -> bool {
                x == y
            }

            spec fn always(x: u8) -> bool {
                true
            }

            spec fn count_le_le(lo: u8, hi: u8) -> bool {
                exists |x: u8| lo <= x <= hi && eq_u8(x, hi)
            }

            spec fn all_lt_le(lo: u8, hi: u8) -> bool {
                forall |x: u8| lo < x <= hi ==> !always(x)
            }

            spec fn any_lt_lt(lo: u8, hi: u8) -> bool {
                exists |x: u8| lo < x < hi && always(x)
            }

            spec fn is_i8_max(x: i8) -> bool {
                x == 127
            }

            spec fn any_i8_le_le(lo: i8, hi: i8) -> bool {
                exists |x: i8| lo <= x <= hi && is_i8_max(x)
            }

            spec fn any_char_le_le(lo: char, hi: char) -> bool {
                exists |c: char| #![trigger c as u32] lo <= c <= hi && c == hi
            }

            spec fn any_char_lt_le(lo: char, hi: char) -> bool {
                exists |c: char| #![trigger c as u32] lo < c <= hi && true
            }

            spec fn not_x(c: char) -> bool {
                c != 'x'
            }

            spec fn none_x_surrogates() -> bool {
                forall |c: char| '\u{D000}' <= c < '\u{E000}' ==> not_x(c)
            }

            spec fn both_255(x: u8, y: u8) -> bool {
                x == 255 && y == 255
            }

            spec fn any_pair(n: u8) -> bool {
                exists |x: u8, y: u8| 0 <= x <= n && x <= y <= n && both_255(x, y)
            }
        }

        } // verus!

        fn main() {
            assert!(exec_has_seven(255));
            assert!(exec_has_seven(7));
            assert!(!exec_has_seven(6));

            assert!(exec_count_le_le(0, 255));
            assert!(exec_count_le_le(255, 255));
            assert!(!exec_count_le_le(255, 254));

            // empty range: 255 < x <= 255
            assert!(exec_all_lt_le(255, 255));
            assert!(!exec_all_lt_le(254, 255));

            // empty ranges must stay empty, nonempty ones nonempty
            assert!(!exec_any_lt_lt(255, 10));
            assert!(!exec_any_lt_lt(0, 1));
            assert!(!exec_any_lt_lt(254, 255));
            assert!(exec_any_lt_lt(253, 255));

            assert!(exec_any_i8_le_le(-128, 127));
            assert!(!exec_any_i8_le_le(-128, 126));

            assert!(exec_any_char_le_le('\u{10FF00}', '\u{10FFFF}'));
            assert!(exec_any_char_le_le('\u{D700}', '\u{E000}'));
            assert!(!exec_any_char_lt_le('\u{10FFFF}', '\u{10FFFF}'));
            assert!(exec_any_char_lt_le('\u{D7FF}', '\u{E000}'));
            assert!(exec_none_x_surrogates());

            assert!(exec_any_pair(255));
            assert!(!exec_any_pair(254));
        }
    };
    let tempdir = tempfile::tempdir().unwrap();
    let entry_file = tempdir.path().join("quant_bounds.rs");
    std::fs::write(&entry_file, format!("{FEATURE_PRELUDE}\n{USE_PRELUDE}\n{source}")).unwrap();
    let output = run_verus_raw(&["--compile", entry_file.to_str().unwrap()], tempdir.path());
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let binary =
        tempdir.path().join(if cfg!(windows) { "quant_bounds.exe" } else { "quant_bounds" });
    let output = std::process::Command::new(binary).output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
}
