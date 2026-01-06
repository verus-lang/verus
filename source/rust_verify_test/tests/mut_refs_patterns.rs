#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] basic_match_mut_ref ["new-mut-ref"] => verus_code! {
        enum Option<T> { Some(T), None }
        use crate::Option::Some;
        use crate::Option::None;

        struct Foo(u64);

        fn test_foo(o: Foo, orig: Foo) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            match o_ref {
                Foo(i) => {
                    assert(orig == Foo(*i));

                    *i = 20;
                }
            }

            assert(o === Foo(20));
        }

        fn test_foo_fails(o: Foo, orig: Foo) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            match o_ref {
                Foo(i) => {
                    *i = 20;
                }
            }

            assert(false); // FAILS
        }

        fn test_opt(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            match o_ref {
                Some(i) => {
                    assert(orig == Some(*i));

                    *i = 20;
                }
                None => {
                }
            }

            assert(orig is None ==> o is None);
            assert(orig is Some ==> o === Some(20));
        }

        fn test_opt_fails1(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            match o_ref {
                Some(i) => {
                    assert(orig == Some(*i));

                    *i = 20;
                }
                None => {
                }
            }

            assert(orig is None ==> o is None);
            assert(orig is Some ==> o === Some(20));

            assert(o is Some); // FAILS
            assert(o is None); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] basic_let_stmt_mut_ref ["new-mut-ref"] => verus_code! {
        struct Foo(u64);

        fn test_foo(o: Foo, orig: Foo) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            let Foo(i) = o_ref;
            assert(orig == Foo(*i));
            *i = 20;

            assert(o === Foo(20));
        }

        fn test_foo_fails(o: Foo, orig: Foo) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            let Foo(i) = o_ref;
            *i = 20;

            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] match_on_a_field_place_via_dot ["new-mut-ref"] => verus_code! {
        enum Option<T> { Some(T), None }
        use crate::Option::Some;
        use crate::Option::None;

        fn test_opt(cond: bool) {
            let mut x = 3;

            let mut o = if cond {
                Some(&mut x)
            } else {
                None
            };

            let mut y = 4;

            let pair = (o, &mut y);

            match pair.0 {
                Some(i) => {
                    assert(cond);
                    assert(*i == 3);
                    *i = 20;
                }
                None => {
                    assert(!cond);
                }
            }

            if cond {
                assert(x == 20);
                assert(y == 4);
            } else {
                assert(x == 3);
                assert(y == 4);
            }
        }

        fn test_opt_fails(cond: bool) {
            let mut x = 3;

            let mut o = if cond {
                Some(&mut x)
            } else {
                None
            };

            let mut y = 4;

            let pair = (o, &mut y);

            match pair.0 {
                Some(i) => {
                    assert(cond);
                    assert(*i == 3);
                    *i = 20;
                }
                None => {
                    assert(!cond);
                }
            }

            if cond {
                assert(x == 20);
                assert(y == 4);
                assert(false); // FAILS
            } else {
                assert(x == 3);
                assert(y == 4);
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] match_on_a_field_via_underscore ["new-mut-ref"] => verus_code! {
        enum Option<T> { Some(T), None }
        use crate::Option::Some;
        use crate::Option::None;

        fn test_opt(cond: bool) {
            let mut x = 3;

            let mut o = if cond {
                Some(&mut x)
            } else {
                None
            };

            let mut y = 4;

            let pair = (o, &mut y);

            match pair {
                (Some(i), _) => {
                    assert(cond);
                    assert(*i == 3);
                    *i = 20;
                }
                (None, _) => {
                    assert(!cond);
                }
            }

            if cond {
                assert(x == 20);
                assert(y == 4);
            } else {
                assert(x == 3);
                assert(y == 4);
            }
        }

        fn test_opt_fails(cond: bool) {
            let mut x = 3;

            let mut o = if cond {
                Some(&mut x)
            } else {
                None
            };

            let mut y = 4;

            let pair = (o, &mut y);

            match pair {
                (Some(i), _) => {
                    assert(cond);
                    assert(*i == 3);
                    *i = 20;
                }
                (None, _) => {
                    assert(!cond);
                }
            }

            if cond {
                assert(x == 20);
                assert(y == 4);
                assert(false); // FAILS
            } else {
                assert(x == 3);
                assert(y == 4);
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] let_decl_on_a_field_place ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 0;
            let mut pair = (20, 30);
            let big_pair = (&mut x, &mut pair);

            let (ref1, ref2) = big_pair.1;

            *ref1 = 100;
            *ref2 = 200;

            assert(x == 0);
            assert(pair === (100, 200));
        }

        fn test2() {
            let mut x = 0;
            let mut pair = (20, 30);
            let big_pair = (&mut x, &mut pair);

            let (_, (ref1, ref2)) = big_pair;

            *ref1 = 100;
            *ref2 = 200;

            assert(x == 0);
            assert(pair === (100, 200));
        }

        fn test_fails() {
            let mut x = 0;
            let mut pair = (20, 30);
            let big_pair = (&mut x, &mut pair);

            let (ref1, ref2) = big_pair.1;

            *ref1 = 100;
            *ref2 = 200;

            assert(x == 0);
            assert(pair === (100, 200));
            assert(false); // FAILS
        }

        fn test2_fails() {
            let mut x = 0;
            let mut pair = (20, 30);
            let big_pair = (&mut x, &mut pair);

            let (_, (ref1, ref2)) = big_pair;

            *ref1 = 100;
            *ref2 = 200;

            assert(x == 0);
            assert(pair === (100, 200));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] match_explicit_ref_mut_binding ["new-mut-ref"] => verus_code! {
        enum Option<T> { Some(T), None }
        use crate::Option::Some;
        use crate::Option::None;

        fn test_explicit_ref_mut(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            match o {
                Some(ref mut i) => {
                    assert(orig == Some(*i));

                    *i = 20;
                }
                None => {
                }
            }

            assert(orig is None ==> o is None);
            assert(orig is Some ==> o === Some(20));
        }

        fn test_explicit_ref_mut_fails(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            match o {
                Some(ref mut i) => {
                    assert(orig == Some(*i));

                    *i = 20;
                }
                None => {
                }
            }

            assert(orig is None ==> o is None);
            assert(orig is Some ==> o === Some(20));

            assert(o is Some); // FAILS
            assert(o is None); // FAILS
        }

        fn test_explicit_redundant_ref_mut(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            match o_ref {
                // The ref mut here doesn't have any effect because o_ref is already a mutable borrow
                Some(ref mut i) => {
                    assert(orig == Some(*i));

                    *i = 20;
                }
                None => {
                }
            }

            assert(orig is None ==> o is None);
            assert(orig is Some ==> o === Some(20));
        }

        fn test_explicit_redundant_ref_mut_fails(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            match o_ref {
                // The ref mut here doesn't have any effect because o_ref is already a mutable borrow
                Some(ref mut i) => {
                    assert(orig == Some(*i));

                    *i = 20;
                }
                None => {
                }
            }

            assert(orig is None ==> o is None);
            assert(orig is Some ==> o === Some(20));

            assert(o is Some); // FAILS
            assert(o is None); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] let_explicit_ref_mut_binding ["new-mut-ref"] => verus_code! {
        enum Foo<T> { Some(T) }
        use crate::Foo::Some;

        fn test_explicit_ref_mut(o: Foo<u64>, orig: Foo<u64>) {
            assume(orig == o);

            let mut o = o;
            let Some(ref mut i) = o;
            assert(orig == Some(*i));
            *i = 20;

            assert(o === Some(20));
        }

        fn test_explicit_redundant_ref_mut(o: Foo<u64>, orig: Foo<u64>) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            let Some(ref mut i) = o_ref;
            assert(orig == Some(*i));
            *i = 20;

            assert(o === Some(20));
        }

        fn test_explicit_ref_mut_fails(o: Foo<u64>, orig: Foo<u64>) {
            assume(orig == o);

            let mut o = o;
            let Some(ref mut i) = o;
            assert(orig == Some(*i));
            *i = 20;

            assert(o === Some(20));
            assert(false); // FAILS
        }

        fn test_explicit_redundant_ref_mut_fails(o: Foo<u64>, orig: Foo<u64>) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            let Some(ref mut i) = o_ref;
            assert(orig == Some(*i));
            *i = 20;

            assert(o === Some(20));
            assert(false); // FAILS
        }

    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] ref_mut_inside_immut_ref ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;
        fn ref_mut(o: Option<u64>, orig: Option<u64>) {
            let mut o = o;
            let mut o_ref = &o;
            match o_ref {
                Some(ref mut i) => {
                }
                None => {
                }
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `o_ref.0` as mutable, as it is behind a `&` reference")
}

test_verify_one_file_with_options! {
    #[test] ref_mut_inside_immut_ref_no_lifetime ["new-mut-ref", "--no-lifetime"] => verus_code! {
        use vstd::prelude::*;
        fn ref_mut(o: Option<u64>, orig: Option<u64>) {
            let mut o = o;
            let mut o_ref = &o;
            match o_ref {
                Some(ref mut i) => {
                }
                None => {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot borrow this place as mutable, as it is behind a `&` reference")
}

test_verify_one_file_with_options! {
    #[test] ref_mut_inside_at_binder ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_copy_with_ref_mut_binder_in_subpat(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;

            // You could imagine this being supported (i.e., by copying `opt` before
            // taking the mut-ref to i) but it's a lifetime error.
            // If Rust ever supports this, need to make sure we handle it in the right order.
            match o {
                opt @ Some(ref mut i) => {
                    assert(orig == Some(*i));
                    assert(opt == orig);

                    *i = 20;
                }
                None => {
                }
            }

            assert(o === match orig {
                Some(x) => Some(20),
                None => None,
            });
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot use `o` because it was mutably borrowed")
}

test_verify_one_file_with_options! {
    #[test] match_complex_mut_ref_combos ["new-mut-ref"] => verus_code! {
        enum Option<T> { Some(T), None }
        use crate::Option::Some;
        use crate::Option::None;

        fn test_mut_mut(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            let mut o_ref_ref = &mut o_ref;
            match o_ref {
                Option::Some(i) => {
                    assert(orig == Option::Some(*i));

                    *i = 20;
                }
                Option::None => {
                }
            }

            assert(orig is None ==> o is None);
            assert(orig is Some ==> o === Option::Some(20));
        }

        fn test_mut_mut_fails(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            let mut o_ref_ref = &mut o_ref;
            match o_ref {
                Some(i) => {
                    assert(orig == Some(*i));

                    *i = 20;
                }
                None => {
                }
            }

            assert(orig is None ==> o is None);
            assert(orig is Some ==> o === Some(20));

            assert(o is Some); // FAILS
            assert(o is None); // FAILS
        }

        fn test_ref_mut_binder_copy_in_subpat(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            match o {
                ref mut opt @ Some(i) => {
                    assert(orig == Some(i));
                    assert(*opt == orig);

                    *opt = None;
                }
                None => {
                }
            }

            assert(o is None);
        }


        fn test_ref_mut_binder_copy_in_subpat_fails(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            match o {
                ref mut opt @ Some(i) => {
                    assert(orig == Some(i));
                    assert(*opt == orig);

                    *opt = None;
                }
                None => {
                }
            }

            assert(o is None);

            assert(orig is None); // FAILS
            assert(orig is Some); // FAILS
        }

        fn test_ref_mut_binder_copy_in_subpat_nested(o: Option<Option<u64>>, orig: Option<Option<u64>>)
            requires (match o {
                Some(Some(x)) => x < 5,
                _ => true,
            })
        {
            assume(orig == o);

            let mut o = o;
            match o {
                Some(ref mut opt @ Some(i)) => {
                    *opt = Some(i + 1);
                }
                Some(ref mut opt @ None) => {
                    *opt = Some(0);
                }
                None => {
                }
            }

            assert(o === match orig {
                Some(Some(x)) => Some(Some((x+1) as u64)),
                Some(None) => Some(Some(0)),
                None => None,
            });
        }

        fn test_ref_mut_binder_copy_in_subpat_nested_fails(o: Option<Option<u64>>, orig: Option<Option<u64>>)
            requires (match o {
                Some(Some(x)) => x < 5,
                _ => true,
            })
        {
            assume(orig == o);

            let mut o = o;
            match o {
                Some(ref mut opt @ Some(i)) => {
                    *opt = Some(i + 1);
                }
                Some(ref mut opt @ None) => {
                    *opt = Some(0);
                }
                None => {
                }
            }

            assert(o === match orig {
                Some(Some(x)) => Some(Some((x+1) as u64)),
                Some(None) => Some(Some(0)),
                None => None,
            });
            assert(orig is Some); // FAILS
            assert(false); // FAILS
        }

        fn test_ref_mut_binder_copy_in_subpat_nested_fails2(o: Option<Option<u64>>, orig: Option<Option<u64>>)
            requires (match o {
                Some(Some(x)) => x < 5,
                _ => true,
            })
        {
            assume(orig == o);

            let mut o = o;
            match o {
                Some(ref mut opt @ Some(i)) => {
                    *opt = Some(i + 1);
                }
                Some(ref mut opt @ None) => {
                    *opt = Some(0);
                }
                None => {
                }
            }

            assert(o === match orig {
                Some(Some(x)) => Some(Some((x+1) as u64)),
                Some(None) => Some(Some(0)),
                None => None,
            });

            assert(match orig { Some(x) => x is None, None => true }); // FAILS
            assert(match orig { Some(x) => x is Some, None => true }); // FAILS
        }
    } => Err(err) => assert_fails(err, 8)
}

test_verify_one_file_with_options! {
    #[test] complex_nesting_enum_1_variant ["new-mut-ref"] => verus_code! {
        enum BigEnum1<'a, 'b, 'c> {
            A((&'a mut (u64, &'b mut u64), &'c mut u64)),
        }

        fn test_big_enum1() {
            let mut x = 0;
            let mut y = 1;
            let mut z = 2;

            let x_ref = &mut x;
            let mut pair = (4, x_ref);
            let pair_ref = &mut pair;

            let y_ref = &mut y;
            let mut big_pair = (pair_ref, y_ref);

            let z_ref = &mut z;

            let bg = BigEnum1::A(big_pair);

            let mut o = bg;
            match o {
                BigEnum1::A(((r_pair_0, rx), ry)) => {
                    assert(*r_pair_0 == 4);
                    assert(**rx == 0);
                    assert(*ry == 1);

                    assert(has_resolved(o->A_0.0.1)); // TODO(new_mut_ref): better triggering

                    *r_pair_0 = 20;
                    assert(mut_ref_future(r_pair_0) == pair.0);
                    **rx = 21;
                    *ry = 22;
                }
            }

            assert(pair.0 == 20);
            assert(x == 21);
            assert(y == 22);
        }

        fn test_big_enum1_with_mut_ref() {
            let mut x = 0;
            let mut y = 1;
            let mut z = 2;

            let x_ref = &mut x;
            let mut pair = (4, x_ref);
            let pair_ref = &mut pair;

            let y_ref = &mut y;
            let mut big_pair = (pair_ref, y_ref);

            let z_ref = &mut z;

            let bg = BigEnum1::A(big_pair);

            // mostly the same as previous case, but with a &mut ref at the top
            let mut o = bg;
            let mut o_ref = &mut o;
            match o_ref {
                BigEnum1::A(((r_pair_0, rx), ry)) => {
                    assert(*r_pair_0 == 4);
                    assert(**rx == 0);
                    assert(**ry == 1);

                    assert(has_resolved(o->A_0.0.1)); // TODO(new_mut_ref): better triggering
                    assert(has_resolved(o->A_0.1));

                    *r_pair_0 = 20;
                    **rx = 21;
                    **ry = 22;

                    assert(has_resolved(r_pair_0));
                }
            }

            assert(pair.0 == 20);
            assert(x == 21);
            assert(y == 22);
        }

        fn test_big_enum1_fails() {
            let mut x = 0;
            let mut y = 1;
            let mut z = 2;

            let x_ref = &mut x;
            let mut pair = (4, x_ref);
            let pair_ref = &mut pair;

            let y_ref = &mut y;
            let mut big_pair = (pair_ref, y_ref);

            let z_ref = &mut z;

            let bg = BigEnum1::A(big_pair);

            let mut o = bg;
            match o {
                BigEnum1::A(((r_pair_0, rx), ry)) => {
                    assert(*r_pair_0 == 4);
                    assert(**rx == 0);
                    assert(*ry == 1);

                    assert(has_resolved(o->A_0.0.1));

                    *r_pair_0 = 20;
                    assert(mut_ref_future(r_pair_0) == pair.0);
                    **rx = 21;
                    *ry = 22;
                }
            }

            assert(pair.0 == 20);
            assert(x == 21);
            assert(y == 22);
            assert(false); // FAILS
        }

        fn test_big_enum1_with_mut_ref_fails() {
            let mut x = 0;
            let mut y = 1;
            let mut z = 2;

            let x_ref = &mut x;
            let mut pair = (4, x_ref);
            let pair_ref = &mut pair;

            let y_ref = &mut y;
            let mut big_pair = (pair_ref, y_ref);

            let z_ref = &mut z;

            let bg = BigEnum1::A(big_pair);

            // mostly the same as previous case, but with a &mut ref at the top
            let mut o = bg;
            let mut o_ref = &mut o;
            match o_ref {
                BigEnum1::A(((r_pair_0, rx), ry)) => {
                    assert(*r_pair_0 == 4);
                    assert(**rx == 0);
                    assert(**ry == 1);

                    assert(has_resolved(o->A_0.0.1));
                    assert(has_resolved(o->A_0.1));

                    *r_pair_0 = 20;
                    **rx = 21;
                    **ry = 22;

                    assert(has_resolved(r_pair_0));
                }
            }

            assert(pair.0 == 20);
            assert(x == 21);
            assert(y == 22);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] let_decl_complex_nesting_enum_1_variant ["new-mut-ref"] => verus_code! {
        enum BigEnum1<'a, 'b, 'c> {
            A((&'a mut (u64, &'b mut u64), &'c mut u64)),
        }

        fn test_big_enum1() {
            let mut x = 0;
            let mut y = 1;
            let mut z = 2;

            let x_ref = &mut x;
            let mut pair = (4, x_ref);
            let pair_ref = &mut pair;

            let y_ref = &mut y;
            let mut big_pair = (pair_ref, y_ref);

            let z_ref = &mut z;

            let bg = BigEnum1::A(big_pair);

            let mut o = bg;
            let BigEnum1::A(((r_pair_0, rx), ry)) = o;
            assert(*r_pair_0 == 4);
            assert(**rx == 0);
            assert(*ry == 1);

            assert(has_resolved(o->A_0.0.1)); // TODO(new_mut_ref): better triggering

            *r_pair_0 = 20;
            assert(mut_ref_future(r_pair_0) == pair.0);
            **rx = 21;
            *ry = 22;

            assert(pair.0 == 20);
            assert(x == 21);
            assert(y == 22);
        }

        fn test_big_enum1_with_mut_ref() {
            let mut x = 0;
            let mut y = 1;
            let mut z = 2;

            let x_ref = &mut x;
            let mut pair = (4, x_ref);
            let pair_ref = &mut pair;

            let y_ref = &mut y;
            let mut big_pair = (pair_ref, y_ref);

            let z_ref = &mut z;

            let bg = BigEnum1::A(big_pair);

            // mostly the same as previous case, but with a &mut ref at the top
            let mut o = bg;
            let mut o_ref = &mut o;
            let BigEnum1::A(((r_pair_0, rx), ry)) = o_ref;
            assert(*r_pair_0 == 4);
            assert(**rx == 0);
            assert(**ry == 1);

            assert(has_resolved(o->A_0.0.1)); // TODO(new_mut_ref): better triggering
            assert(has_resolved(o->A_0.1));

            *r_pair_0 = 20;
            **rx = 21;
            **ry = 22;

            assert(has_resolved(r_pair_0));

            assert(pair.0 == 20);
            assert(x == 21);
            assert(y == 22);
        }

        fn test_big_enum1_fails() {
            let mut x = 0;
            let mut y = 1;
            let mut z = 2;

            let x_ref = &mut x;
            let mut pair = (4, x_ref);
            let pair_ref = &mut pair;

            let y_ref = &mut y;
            let mut big_pair = (pair_ref, y_ref);

            let z_ref = &mut z;

            let bg = BigEnum1::A(big_pair);

            let mut o = bg;
            let BigEnum1::A(((r_pair_0, rx), ry)) = o;
            assert(*r_pair_0 == 4);
            assert(**rx == 0);
            assert(*ry == 1);

            assert(has_resolved(o->A_0.0.1));

            *r_pair_0 = 20;
            assert(mut_ref_future(r_pair_0) == pair.0);
            **rx = 21;
            *ry = 22;

            assert(pair.0 == 20);
            assert(x == 21);
            assert(y == 22);
            assert(false); // FAILS
        }

        fn test_big_enum1_with_mut_ref_fails() {
            let mut x = 0;
            let mut y = 1;
            let mut z = 2;

            let x_ref = &mut x;
            let mut pair = (4, x_ref);
            let pair_ref = &mut pair;

            let y_ref = &mut y;
            let mut big_pair = (pair_ref, y_ref);

            let z_ref = &mut z;

            let bg = BigEnum1::A(big_pair);

            // mostly the same as previous case, but with a &mut ref at the top
            let mut o = bg;
            let mut o_ref = &mut o;
            let BigEnum1::A(((r_pair_0, rx), ry)) = o_ref;
            assert(*r_pair_0 == 4);
            assert(**rx == 0);
            assert(**ry == 1);

            assert(has_resolved(o->A_0.0.1));
            assert(has_resolved(o->A_0.1));

            *r_pair_0 = 20;
            **rx = 21;
            **ry = 22;

            assert(has_resolved(r_pair_0));

            assert(pair.0 == 20);
            assert(x == 21);
            assert(y == 22);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] complex_nesting_enum_2_variant ["new-mut-ref"] => verus_code! {
        enum BigEnum<'a, 'b, 'c> {
            A((&'a mut (u64, &'b mut u64), &'c mut u64)),
            B(&'c mut u64)
        }

        fn test_big_enum(cond: bool) {
            let mut x = 0;
            let mut y = 1;
            let mut z = 2;

            let x_ref = &mut x;
            let mut pair = (4, x_ref);
            let pair_ref = &mut pair;

            let y_ref = &mut y;
            let mut big_pair = (pair_ref, y_ref);

            let z_ref = &mut z;

            let bg = if cond {
                BigEnum::A(big_pair)
            } else {
                BigEnum::B(z_ref)
            };

            let mut o = bg;
            match o {
                BigEnum::A(((r_pair_0, rx), ry)) => {
                    assume(has_resolved(o->A_0.0)); // TODO(new_mut_ref): incompleteness in resolution analysis

                    assert(*r_pair_0 == 4);
                    assert(**rx == 0);
                    assert(*ry == 1);

                    *r_pair_0 = 20;
                    **rx = 21;
                    *ry = 22;

                    assert(has_resolved(o->A_0.0));
                    assert(has_resolved(o->A_0.0.1));
                    assert(has_resolved(r_pair_0));
                }
                BigEnum::B(rz) => {
                    assert(*rz == 2);
                    *rz = 35;
                }
            }

            if cond {
                assert(pair.0 == 20);
                assert(x == 21);
                assert(y == 22);
            } else {
                assert(z == 35);
            }
        }

        fn test_big_enum2(cond: bool) {
            let mut x = 0;
            let mut y = 1;
            let mut z = 2;

            let x_ref = &mut x;
            let mut pair = (4, x_ref);
            let pair_ref = &mut pair;

            let y_ref = &mut y;
            let mut big_pair = (pair_ref, y_ref);

            let z_ref = &mut z;

            let bg = if cond {
                BigEnum::A(big_pair)
            } else {
                BigEnum::B(z_ref)
            };

            let mut o = bg;
            let mut o_ref = &mut o;
            match o_ref {
                BigEnum::A(((r_pair_0, rx), ry)) => {
                    assert(*r_pair_0 == 4);
                    assert(**rx == 0);
                    assert(**ry == 1);

                    *r_pair_0 = 20;
                    **rx = 21;
                    **ry = 22;

                    assert(has_resolved(o->A_0.0.1)); // TODO(new_mut_ref): better triggering
                    assert(has_resolved(o->A_0.1));
                    assert(has_resolved(r_pair_0));
                }
                BigEnum::B(rz) => {
                    assert(**rz == 2);
                    **rz = 35;

                    assert(has_resolved(o->B_0));
                }
            }

            if cond {
                assert(pair.0 == 20);
                assert(x == 21);
                assert(y == 22);
            } else {
                assert(z == 35);
            }
        }

        fn test_big_enum_fails(cond: bool) {
            let mut x = 0;
            let mut y = 1;
            let mut z = 2;

            let x_ref = &mut x;
            let mut pair = (4, x_ref);
            let pair_ref = &mut pair;

            let y_ref = &mut y;
            let mut big_pair = (pair_ref, y_ref);

            let z_ref = &mut z;

            let bg = if cond {
                BigEnum::A(big_pair)
            } else {
                BigEnum::B(z_ref)
            };

            let mut o = bg;
            match o {
                BigEnum::A(((r_pair_0, rx), ry)) => {
                    assume(has_resolved(o->A_0.0));

                    assert(*r_pair_0 == 4);
                    assert(**rx == 0);
                    assert(*ry == 1);

                    *r_pair_0 = 20;
                    **rx = 21;
                    *ry = 22;

                    assert(has_resolved(o->A_0.0));
                    assert(has_resolved(o->A_0.0.1));
                    assert(has_resolved(r_pair_0));
                }
                BigEnum::B(rz) => {
                    assert(*rz == 2);
                    *rz = 35;
                }
            }

            if cond {
                assert(pair.0 == 20);
                assert(x == 21);
                assert(y == 22);
                assert(false); // FAILS
            } else {
                assert(z == 35);
                assert(false); // FAILS
            }
        }

        fn test_big_enum2_fails(cond: bool) {
            let mut x = 0;
            let mut y = 1;
            let mut z = 2;

            let x_ref = &mut x;
            let mut pair = (4, x_ref);
            let pair_ref = &mut pair;

            let y_ref = &mut y;
            let mut big_pair = (pair_ref, y_ref);

            let z_ref = &mut z;

            let bg = if cond {
                BigEnum::A(big_pair)
            } else {
                BigEnum::B(z_ref)
            };

            let mut o = bg;
            let mut o_ref = &mut o;
            match o_ref {
                BigEnum::A(((r_pair_0, rx), ry)) => {
                    assert(*r_pair_0 == 4);
                    assert(**rx == 0);
                    assert(**ry == 1);

                    *r_pair_0 = 20;
                    **rx = 21;
                    **ry = 22;

                    assert(has_resolved(o->A_0.0.1));
                    assert(has_resolved(o->A_0.1));
                    assert(has_resolved(r_pair_0));
                }
                BigEnum::B(rz) => {
                    assert(**rz == 2);
                    **rz = 35;

                    assert(has_resolved(o->B_0));
                }
            }

            if cond {
                assert(pair.0 == 20);
                assert(x == 21);
                assert(y == 22);
                assert(false); // FAILS
            } else {
                assert(z == 35);
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] mut_ref_to_struct_with_immut_refs ["new-mut-ref"] => verus_code! {
        struct BigStruct<'a, 'b>(&'a u64, &'b (u64, u64));

        fn test_mut_ref_to_struct_with_immut_refs() {
            let x = 0;
            let y = (2, 3);
            let mut big = BigStruct(&x, &y);

            let w = 4;

            let mut big_ref = &mut big;
            match big_ref {
                BigStruct(x1, (y1, z1)) => {
                    // x1 has type &mut &u64
                    // y1 and z1 each have type &u64
                    assert(**x1 == 0);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                    *x1 = &w;
                }
            }

            assert(x == 0);
            assert(big.0 == 4);
            assert(big.1 === &(2, 3));
        }

        fn test_mut_ref_to_struct_with_immut_refs_fails() {
            let x = 0;
            let y = (2, 3);
            let mut big = BigStruct(&x, &y);

            let w = 4;

            let mut big_ref = &mut big;
            match big_ref {
                BigStruct(x1, (y1, z1)) => {
                    // x1 has type &mut &u64
                    // y1 and z1 each have type &u64
                    assert(**x1 == 0);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                    *x1 = &w;
                }
            }

            assert(x == 0);
            assert(big.0 == 4);
            assert(big.1 === &(2, 3));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] let_decl_mut_ref_to_struct_with_immut_refs ["new-mut-ref"] => verus_code! {
        struct BigStruct<'a, 'b>(&'a u64, &'b (u64, u64));

        fn test_mut_ref_to_struct_with_immut_refs() {
            let x = 0;
            let y = (2, 3);
            let mut big = BigStruct(&x, &y);

            let w = 4;

            let mut big_ref = &mut big;
            let BigStruct(x1, (y1, z1)) = big_ref;
            // x1 has type &mut &u64
            // y1 and z1 each have type &u64
            assert(**x1 == 0);
            assert(*y1 == 2);
            assert(*z1 == 3);
            *x1 = &w;

            assert(x == 0);
            assert(big.0 == 4);
            assert(big.1 === &(2, 3));
        }

        fn test_mut_ref_to_struct_with_immut_refs_fails() {
            let x = 0;
            let y = (2, 3);
            let mut big = BigStruct(&x, &y);

            let w = 4;

            let mut big_ref = &mut big;
            let BigStruct(x1, (y1, z1)) = big_ref;
            // x1 has type &mut &u64
            // y1 and z1 each have type &u64
            assert(**x1 == 0);
            assert(*y1 == 2);
            assert(*z1 == 3);
            *x1 = &w;

            assert(x == 0);
            assert(big.0 == 4);
            assert(big.1 === &(2, 3));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] mut_ref_to_enum_with_immut_refs ["new-mut-ref"] => verus_code! {
        enum BigEnum<'a, 'b> {
          A(&'a u64, &'b (u64, u64)),
          B(&'a u64),
        }

        fn test_enum(cond: bool) {
            let x = 0;
            let y = (2, 3);
            let v = 5;
            let mut big = if cond {
                BigEnum::A(&x, &y)
            } else {
                BigEnum::B(&v)
            };

            let w = 4;

            let mut big_ref = &mut big;
            match big_ref {
                BigEnum::A(x1, (y1, z1)) => {
                    // x1 has type &mut &u64
                    // y1 and z1 each have type &u64
                    assert(**x1 == 0);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                    *x1 = &w;
                }
                BigEnum::B(v1) => {
                    assert(**v1 == 5);
                    *v1 = &w;
                }
            }

            assert(x == 0);
            assert(v == 5);
            if cond {
                assert(big->A_0 == 4);
                assert(big->A_1 === &(2, 3));
            } else {
                assert(big->B_0 == 4);
            }
        }

        fn test_enum_fails(cond: bool) {
            let x = 0;
            let y = (2, 3);
            let v = 5;
            let mut big = if cond {
                BigEnum::A(&x, &y)
            } else {
                BigEnum::B(&v)
            };

            let w = 4;

            let mut big_ref = &mut big;
            match big_ref {
                BigEnum::A(x1, (y1, z1)) => {
                    // x1 has type &mut &u64
                    // y1 and z1 each have type &u64
                    assert(**x1 == 0);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                    *x1 = &w;
                }
                BigEnum::B(v1) => {
                    assert(**v1 == 5);
                    *v1 = &w;
                }
            }

            assert(x == 0);
            assert(v == 5);
            if cond {
                assert(big->A_0 == 4);
                assert(big->A_1 === &(2, 3));
                assert(false); // FAILS
            } else {
                assert(big->B_0 == 4);
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] struct_mut_refs_immut_refs ["new-mut-ref"] => verus_code! {
        struct BigStruct<'a, 'b>(&'a mut (u64, &'b (u64, u64)));

        fn test_struct() {
            let pair = (2, 3);
            let mut big_pair = (4, &pair);
            let mut big = BigStruct(&mut big_pair);

            match big {
                BigStruct((x1, (y1, z1))) => {
                    // x1 has type &mut u64
                    // y1 and z1 each have type &u64
                    assert(*x1 == 4);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                    *x1 = 5;
                }
            }

            assert(pair === (2, 3));
            assert(big_pair.0 === 5);
            assert(big_pair === (5, &(2, 3)));
        }

        fn test_struct_fails() {
            let pair = (2, 3);
            let mut big_pair = (4, &pair);
            let mut big = BigStruct(&mut big_pair);

            match big {
                BigStruct((x1, (y1, z1))) => {
                    // x1 has type &mut u64
                    // y1 and z1 each have type &u64
                    assert(*x1 == 4);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                    *x1 = 5;
                }
            }

            assert(pair === (2, 3));
            assert(big_pair.0 === 5);
            assert(big_pair === (5, &(2, 3)));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] enum_mut_refs_immut_refs ["new-mut-ref"] => verus_code! {
        enum BigEnum<'a, 'b> {
          A(&'a mut (u64, &'b (u64, u64))),
          B,
        }

        fn test_enum(cond: bool) {
            let pair = (2, 3);
            let mut big_pair = (4, &pair);
            let mut big = if cond {
                BigEnum::A(&mut big_pair)
            } else {
                BigEnum::B
            };

            match big {
                BigEnum::A((x1, (y1, z1))) => {
                    // x1 has type &mut u64
                    // y1 and z1 each have type &u64
                    assert(*x1 == 4);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                    *x1 = 5;
                }
                BigEnum::B => { }
            }

            if cond {
                assert(pair === (2, 3));
                assert(big_pair.0 === 5);
                assert(big_pair === (5, &(2, 3)));
            } else {
                assert(pair === (2, 3));
                assert(big_pair === (4, &(2, 3)));
            }
        }

        fn test_enum_fails(cond: bool) {
            let pair = (2, 3);
            let mut big_pair = (4, &pair);
            let mut big = if cond {
                BigEnum::A(&mut big_pair)
            } else {
                BigEnum::B
            };

            match big {
                BigEnum::A((x1, (y1, z1))) => {
                    // x1 has type &mut u64
                    // y1 and z1 each have type &u64
                    assert(*x1 == 4);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                    *x1 = 5;
                }
                BigEnum::B => { }
            }

            if cond {
                assert(pair === (2, 3));
                assert(big_pair.0 === 5);
                assert(big_pair === (5, &(2, 3)));
                assert(false); // FAILS
            } else {
                assert(pair === (2, 3));
                assert(big_pair === (4, &(2, 3)));
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] struct_immut_refs_mut_refs ["new-mut-ref"] => verus_code! {
        struct BigStruct<'a, 'b>(&'a (u64, &'b mut (u64, u64)));

        fn test_struct() {
            let mut pair = (2, 3);
            let mut big_pair = (4, &mut pair);
            let mut big = BigStruct(&big_pair);

            match big {
                BigStruct((x1, (y1, z1))) => {
                    // all have  type &u64
                    assert(*x1 == 4);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                }
            }

            assert(pair === (2, 3));
            assert(big_pair.0 === 4);
        }

        fn test_struct2() {
            let mut pair = (2, 3);
            let mut big_pair = (4, &mut pair);
            let mut big = BigStruct(&big_pair);

            match big {
                BigStruct((x1, (y1, z1))) => {
                    // all have  type &u64
                    assert(*x1 == 4);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                }
            }

            *big_pair.1 = (10, 11);

            assert(pair === (10, 11));
            assert(big_pair.0 === 4);
        }

        fn test_struct_fails() {
            let mut pair = (2, 3);
            let mut big_pair = (4, &mut pair);
            let mut big = BigStruct(&big_pair);

            match big {
                BigStruct((x1, (y1, z1))) => {
                    // all have  type &u64
                    assert(*x1 == 4);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                }
            }

            assert(pair === (2, 3));
            assert(big_pair.0 === 4);
            assert(false); // FAILS
        }

        fn test_struct2_fails() {
            let mut pair = (2, 3);
            let mut big_pair = (4, &mut pair);
            let mut big = BigStruct(&big_pair);

            match big {
                BigStruct((x1, (y1, z1))) => {
                    // all have  type &u64
                    assert(*x1 == 4);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                }
            }

            *big_pair.1 = (10, 11);

            assert(pair === (10, 11));
            assert(big_pair.0 === 4);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] enum_immut_refs_mut_refs ["new-mut-ref"] => verus_code! {
        enum BigEnum<'a, 'b> {
            A(&'a (u64, &'b mut (u64, u64))),
            B,
        }

        fn test_enum(cond: bool) {
            let mut pair = (2, 3);
            let mut big_pair = (4, &mut pair);
            let mut big = if cond {
                BigEnum::A(&big_pair)
            } else {
                BigEnum::B
            };

            match big {
                BigEnum::A((x1, (y1, z1))) => {
                    assert(*x1 == 4);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                }
                BigEnum::B => { }
            }

            if cond {
                assert(pair === (2, 3));
                assert(big_pair.0 === 4);
            } else {
                assert(has_resolved(big_pair.1)); // TODO(new_mut_ref): triggers
                assert(pair === (2, 3));
                assert(big_pair.0 === 4);
            }
        }

        fn test_enum2(cond: bool) {
            let mut pair = (2, 3);
            let mut big_pair = (4, &mut pair);
            let mut big = if cond {
                BigEnum::A(&big_pair)
            } else {
                BigEnum::B
            };

            match big {
                BigEnum::A((x1, (y1, z1))) => {
                    assert(*x1 == 4);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                }
                BigEnum::B => { }
            }

            *big_pair.1 = (10, 11);

            if cond {
                assert(pair === (10, 11));
                assert(big_pair.0 === 4);
            } else {
                assert(pair === (10, 11));
                assert(big_pair.0 === 4);
            }
        }

        fn test_enum_fails(cond: bool) {
            let mut pair = (2, 3);
            let mut big_pair = (4, &mut pair);
            let mut big = if cond {
                BigEnum::A(&big_pair)
            } else {
                BigEnum::B
            };

            match big {
                BigEnum::A((x1, (y1, z1))) => {
                    assert(*x1 == 4);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                }
                BigEnum::B => { }
            }

            if cond {
                assert(pair === (2, 3));
                assert(big_pair.0 === 4);
                assert(false); // FAILS
            } else {
                assert(has_resolved(big_pair.1));
                assert(pair === (2, 3));
                assert(big_pair.0 === 4);
                assert(false); // FAILS
            }
        }

        fn test_enum2_fails(cond: bool) {
            let mut pair = (2, 3);
            let mut big_pair = (4, &mut pair);
            let mut big = if cond {
                BigEnum::A(&big_pair)
            } else {
                BigEnum::B
            };

            match big {
                BigEnum::A((x1, (y1, z1))) => {
                    assert(*x1 == 4);
                    assert(*y1 == 2);
                    assert(*z1 == 3);
                }
                BigEnum::B => { }
            }

            *big_pair.1 = (10, 11);

            if cond {
                assert(pair === (10, 11));
                assert(big_pair.0 === 4);
                assert(false); // FAILS
            } else {
                assert(pair === (10, 11));
                assert(big_pair.0 === 4);
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] enum_immut_refs_mut_refs2 ["new-mut-ref"] => verus_code! {
        struct BigStruct<'a, 'b>(&'a &'b mut (u64, u64));

        enum BigEnum<'a, 'b> {
          A(&'a &'b mut (u64, u64)),
          B,
        }

        fn test_struct() {
            let mut pair = (2, 3);
            let mut pair_ref = &mut pair;
            let mut big = BigStruct(&pair_ref);

            match big {
                BigStruct((x1, y1)) => {
                    assert(*x1 == 2);
                    assert(*y1 == 3);
                }
            }

            assert(pair === (2, 3));
        }

        fn test_struct_fails() {
            let mut pair = (2, 3);
            let mut pair_ref = &mut pair;
            let mut big = BigStruct(&pair_ref);

            match big {
                BigStruct((x1, y1)) => {
                    assert(*x1 == 2);
                    assert(*y1 == 3);
                }
            }

            assert(pair === (2, 3));
            assert(false); // FAILS
        }

        fn test_enum(cond: bool) {
            let mut pair = (2, 3);
            let mut pair_ref = &mut pair;
            let mut big = if cond {
                BigEnum::A(&pair_ref)
            } else {
                BigEnum::B
            };

            match big {
                BigEnum::A((x1, y1)) => {
                    assert(*x1 == 2);
                    assert(*y1 == 3);
                }
                BigEnum::B => { }
            }
        }

        fn test_enum_fails(cond: bool) {
            let mut pair = (2, 3);
            let mut pair_ref = &mut pair;
            let mut big = if cond {
                BigEnum::A(&pair_ref)
            } else {
                BigEnum::B
            };

            match big {
                BigEnum::A((x1, y1)) => {
                    assert(*x1 == 2);
                    assert(*y1 == 3);
                }
                BigEnum::B => { }
            }

            if cond {
                assert(false); // FAILS
            } else {
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] ref_mut_binding_and_nothing_else ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 3;
            match x {
                ref mut y => {
                    assert(*y == 3);
                    *y = 10;
                }
            }
            assert(x == 10);
        }

        fn test_fails() {
            let mut x = 3;
            match x {
                ref mut y => {
                    assert(*y == 3);
                    *y = 10;
                }
            }
            assert(x == 10);
            assert(false); // FAILS
        }

        fn test_let() {
            let mut x = 3;
            let ref mut y = x;
            assert(*y == 3);
            *y = 10;
            assert(x == 10);
        }

        fn test_let_fails() {
            let mut x = 3;
            let ref mut y = x;
            assert(*y == 3);
            *y = 10;
            assert(x == 10);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] enum_take_mut_refs_to_same_var_in_both_branches ["new-mut-ref"] => verus_code! {
        enum BigEnum<'a, 'b, 'c, 'd> {
          A(&'a mut (u64,), &'b mut (u64,)),
          B(&'c mut (u64,), &'d mut (u64,)),
        }

        fn test(cond: bool) {
            let mut x = (20,);
            let mut y = (30,);

            let mut big = if cond {
                BigEnum::A(&mut x, &mut y)
            } else {
                BigEnum::B(&mut y, &mut x)
            };
            let big_ref = &mut big;

            match big_ref {
                BigEnum::A((x1,), (y1,)) => {
                    assert(has_resolved((*big_ref)->A_0)); // TODO(new_mut_ref) triggering
                    assert(has_resolved((*big_ref)->A_1));

                    assert(*x1 == 20);
                    assert(*y1 == 30);
                    *x1 = 70;
                    *y1 = 90;
                }
                BigEnum::B((x1,), (y1,),) => {
                    assert(has_resolved((*big_ref)->B_0));
                    assert(has_resolved((*big_ref)->B_1));

                    assert(*x1 == 30);
                    assert(*y1 == 20);
                    *x1 = 70;
                    *y1 = 90;
                }
            }

            if cond {
                assert(x === (70,));
                assert(y === (90,));
            } else {
                assert(x === (90,));
                assert(y === (70,));
            }
        }

        fn test_fails(cond: bool) {
            let mut x = (20,);
            let mut y = (30,);

            let mut big = if cond {
                BigEnum::A(&mut x, &mut y)
            } else {
                BigEnum::B(&mut y, &mut x)
            };
            let big_ref = &mut big;

            match big_ref {
                BigEnum::A((x1,), (y1,)) => {
                    assert(has_resolved((*big_ref)->A_0)); // TODO(new_mut_ref) triggering
                    assert(has_resolved((*big_ref)->A_1));

                    assert(*x1 == 20);
                    assert(*y1 == 30);
                    *x1 = 70;
                    *y1 = 90;
                }
                BigEnum::B((x1,), (y1,),) => {
                    assert(has_resolved((*big_ref)->B_0));
                    assert(has_resolved((*big_ref)->B_1));

                    assert(*x1 == 30);
                    assert(*y1 == 20);
                    *x1 = 70;
                    *y1 = 90;
                }
            }

            if cond {
                assert(x === (70,));
                assert(y === (90,));
                assert(false); // FAILS
            } else {
                assert(x === (90,));
                assert(y === (70,));
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] mut_ref_with_range_and_const_patterns ["new-mut-ref"] => verus_code! {
        const MY_CONST: u64 = 24;

        fn test_match_const_and_ranges(p: (u64, u64)) {
            let mut pair = p;
            let mut pair_ref = &mut pair;
            let b = match pair_ref {
                (MY_CONST, 3 .. 14) => true,
                _ => false,
            };

            assert(pair == p);
            assert(b <==> (p.0 == 24 && 3 <= p.1 < 14));
        }

        fn test_match_const_and_ranges_fails(p: (u64, u64)) {
            let mut pair = p;
            let mut pair_ref = &mut pair;
            let b = match pair_ref {
                (MY_CONST, 3 .. 14) => true,
                _ => false,
            };

            assert(pair == p);
            assert(b <==> (p.0 == 24 && 3 <= p.1 < 14));
            if b {
                assert(false); // FAILS
            } else {
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] binders_in_pattern_copy_vs_no_copy ["new-mut-ref"] => verus_code! {
        enum Option<A> {
            Some(A),
            None,
        }
        use crate::Option::Some;
        use crate::Option::None;

        fn consume<X>(x: X) { }

        fn test_copy<X: Copy>(x: X, y: X) {
            let t = (x, y);

            match t {
                (x, _) => { consume(x); }
            }

            assert(has_resolved(t));
        }

        fn test_no_copy<X>(x: X, y: X) {
            let t = (x, y);

            match t {
                (x, _) => { consume(x); }
            }

            assert(has_resolved(t)); // FAILS
        }

        fn test_option_copy<X: Copy>(x: X, y: X) {
            let t = Some((x, y));

            match t {
                Some((x, _)) => { consume(x); }
                None => { }
            }

            assert(has_resolved(t));
        }

        fn test_option_no_copy<X>(x: X, y: X) {
            let t = Some((x, y));

            match t {
                Some((x, _)) => { consume(x); }
                None => { }
            }

            assert(has_resolved(t)); // FAILS
        }

        fn test_let_copy<X: Copy>(x: X, y: X) {
            let t = (x, y);

            let (x, _) = t;
            consume(x);

            assert(has_resolved(t));
        }

        fn test_let_no_copy<X>(x: X, y: X) {
            let t = (x, y);

            let (x, _) = t;
            consume(x);

            assert(has_resolved(t)); // FAILS
        }




        fn atbinder_test_copy<X: Copy>(x: X, y: X) {
            let t = (x, y);

            match t {
                x @ (_, _) => { consume(x); }
            }

            assert(has_resolved(t));
        }

        fn atbinder_test_no_copy<X>(x: X, y: X) {
            let t = (x, y);

            match t {
                x @ (_, _) => { consume(x); }
            }

            assert(has_resolved(t)); // FAILS
        }

        fn atbinder_test_option_copy<X: Copy>(x: X, y: X) {
            let t = Some((x, y));

            match t {
                Some(x @ (_, _)) => { consume(x); }
                None => { }
            }

            assert(has_resolved(t));
        }

        fn atbinder_test_option_no_copy<X>(x: X, y: X) {
            let t = Some((x, y));

            match t {
                Some(x @ (_, _)) => { consume(x); }
                None => { }
            }

            assert(has_resolved(t)); // FAILS
        }

        fn atbinder_test_let_copy<X: Copy>(x: X, y: X) {
            let t = (x, y);

            let x @ (_, _) = t;
            consume(x);

            assert(has_resolved(t));
        }

        fn atbinder_test_let_no_copy<X>(x: X, y: X) {
            let t = (x, y);

            let x @ (_, _) = t;
            consume(x);

            assert(has_resolved(t)); // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] binders_in_pattern_ghost_vs_no_ghost ["new-mut-ref"] => verus_code! {
        tracked struct Pair<A, B>(tracked A, tracked B);

        tracked struct GhostPair<A, B>(ghost A, ghost B);

        enum Option<A> {
            Some(A),
            None,
        }
        use crate::Option::Some;
        use crate::Option::None;

        tracked enum GhostOption<A> {
            Some(ghost A),
            None,
        }

        proof fn consume<X>(tracked x: X) { }
        proof fn use_ghost<X>(x: X) { }

        proof fn test_ghost<X>(x: X, y: X) {
            let tracked t = GhostPair(x, y);

            match t {
                GhostPair(x, _) => { use_ghost(x); }
            }

            assert(has_resolved(t));
        }

        proof fn test_no_ghost<X>(tracked x: X, tracked y: X) {
            let tracked t = Pair(x, y);

            match t {
                Pair(x, _) => { consume(x); }
            }

            assert(has_resolved(t)); // FAILS
        }

        proof fn test_option_ghost<X>(x: X, y: X) {
            let tracked t = Some(GhostPair(x, y));

            match t {
                Some(GhostPair(x, _)) => { use_ghost(x); }
                None => { }
            }

            assert(has_resolved(t));
        }

        proof fn test_option_no_ghost<X>(tracked x: X, tracked y: X) {
            let tracked t = Some(Pair(x, y));

            match t {
                Some(Pair(x, _)) => { consume(x); }
                None => { }
            }

            assert(has_resolved(t)); // FAILS
        }

        proof fn test_let_ghost<X>(x: X, y: X) {
            let tracked t = GhostPair(x, y);

            let GhostPair(x, _) = t;
            use_ghost(x);

            assert(has_resolved(t));
        }

        proof fn test_let_no_ghost<X>(tracked x: X, tracked y: X) {
            let tracked t = Pair(x, y);

            let tracked Pair(x, _) = t;
            consume(x);

            assert(has_resolved(t)); // FAILS
        }


        proof fn atbinder_test_ghost<X>(x: X, y: X) {
            let tracked t = GhostPair(x, y);

            match t {
                x @ GhostPair(_, _) => { use_ghost(x); }
            }

            assert(has_resolved(t));
        }

        proof fn atbinder_test_no_ghost<X>(tracked x: X, tracked y: X) {
            let tracked t = Pair(x, y);

            match t {
                x @ Pair(_, _) => { consume(x); }
            }

            assert(has_resolved(t)); // FAILS
        }

        proof fn atbinder_test_option_ghost<X>(x: X, y: X) {
            let tracked t = GhostOption::Some(Pair(x, y));

            match t {
                GhostOption::Some(x @ Pair(_, _)) => { use_ghost(x); }
                GhostOption::None => { }
            }

            assert(has_resolved(t));
        }

        proof fn atbinder_test_option_no_ghost<X>(tracked x: X, tracked y: X) {
            let tracked t = Some(Pair(x, y));

            match t {
                Some(x @ Pair(_, _)) => { consume(x); }
                None => { }
            }

            assert(has_resolved(t)); // FAILS
        }

        proof fn atbinder_test_let_ghost<X>(x: X, y: X) {
            let tracked t = GhostPair(x, y);

            let x @ GhostPair(_, _) = t;
            use_ghost(x);

            assert(has_resolved(t));
        }

        proof fn atbinder_test_let_no_ghost<X>(tracked x: X, tracked y: X) {
            let tracked t = Pair(x, y);

            let tracked x @ Pair(_, _) = t;
            consume(x);

            assert(has_resolved(t)); // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] no_resolve_ghost_binders ["new-mut-ref"] => verus_code! {
        proof fn test1<T>(x: (T, T)) {
            match x {
                (y, z) => {
                    assert(has_resolved(y)); // FAILS
                }
            }
        }

        proof fn test2<T>(x: (T, T)) {
            let (y, z) = x;
            assert(has_resolved(y)); // FAILS
        }

        tracked struct TG<T, G> {
            tracked t: T,
            ghost g: G,
        }

        proof fn test_tg1<T>(tracked x: TG<T, T>) {
            match x {
                TG { t, g } => {
                    assert(has_resolved(g)); // FAILS
                }
            }
        }

        proof fn test_tg2<T>(tracked x: TG<T, T>) {
            match x {
                TG { t, g } => {
                    assert(has_resolved(t));
                }
            }
        }

        proof fn test_tg1_let<T>(tracked x: TG<T, T>) {
            let tracked TG { t, g } = x;
            assert(has_resolved(g)); // FAILS
        }

        proof fn test_tg2_let<T>(tracked x: TG<T, T>) {
            let tracked TG { t, g } = x;
            assert(has_resolved(t));
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] mut_ref_ghost_binder_forbidden ["new-mut-ref"] => verus_code! {
        struct X {
            a: u64
        }

        proof fn test(x: X) {
            match x {
                X { a: ref mut y } => {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a 'mut ref' binding in a pattern is only allowed for exec mode")
}

test_verify_one_file_with_options! {
    #[test] mut_ref_ghost_atbinder_forbidden ["new-mut-ref"] => verus_code! {
        struct X {
            a: u64
        }

        struct Y {
            x: X
        }

        proof fn test(y: Y) {
            match y {
                Y { x: ref mut x0 @ X { a: _ } } => {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a 'mut ref' binding in a pattern is only allowed for exec mode")
}

test_verify_one_file_with_options! {
    #[test] mut_ref_tracked_binder_forbidden ["new-mut-ref"] => verus_code! {
        tracked struct X {
            tracked a: u64
        }

        proof fn test(tracked x: X) {
            match x {
                X { a: ref mut y } => {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a 'mut ref' binding in a pattern is only allowed for exec mode")
}

test_verify_one_file_with_options! {
    #[test] mut_ref_tracked_atbinder_forbidden ["new-mut-ref"] => verus_code! {
        tracked struct X {
            a: u64
        }

        tracked struct Y {
            tracked x: X
        }

        proof fn test(tracked y: Y) {
            match y {
                Y { x: ref mut x0 @ X { a: _ } } => {
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a 'mut ref' binding in a pattern is only allowed for exec mode")
}

test_verify_one_file_with_options! {
    #[test] mut_ref_tracked_unwrap ["new-mut-ref"] => verus_code! {
        fn test<T>(t: &mut Tracked<T>) {
            let Tracked(r) = t;
        }
        // TODO(new_mut_ref): needs better error msg
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of a mutable reference")
}

test_verify_one_file_with_options! {
    #[test] mut_ref_ghost_unwrap ["new-mut-ref"] => verus_code! {
        fn test<T>(t: &mut Ghost<T>) {
            let Ghost(r) = t;
            assert(r == (*t));
        }
        // TODO(new_mut_ref): is this the desired behavior?
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] mut_ref_ghost_binder_forbidden_mut_ref_field ["new-mut-ref"] => verus_code! {
        enum Opt<T> { Some(T), None }

        struct X {
            a: u64
        }

        proof fn test(x: Opt<&mut X>) {
            match x {
                Opt::Some(X { a: a }) => {
                }
                Opt::None => { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a 'mut ref' binding in a pattern is only allowed for exec mode")
}

test_verify_one_file_with_options! {
    #[test] mut_ref_ghost_binder_forbidden_ghost_type ["new-mut-ref"] => verus_code! {
        enum Opt<T> { Some(T), None }
        struct X { a: u64 }

        fn test() {
            let x = Ghost(Opt::Some(X { a: 5 }));
            match x.borrow_mut() {
                Opt::Some(X { a: a }) => {
                }
                Opt::None => { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot access spec-mode place in executable context")
}

test_verify_one_file_with_options! {
    #[test] mut_ref_ghost_binder_forbidden_trk_type ["new-mut-ref"] => verus_code! {
        enum Opt<T> { Some(T), None }
        struct X { a: u64 }

        fn test(Tracked(x): Tracked<X>) {
            let x = Tracked(Opt::Some(x));
            match x.borrow_mut() {
                Opt::Some(X { a: a }) => {
                }
                Opt::None => { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot access proof-mode place in executable context")
}

test_verify_one_file_with_options! {
    #[test] mut_ref_ghost_match_ok_when_no_binder ["new-mut-ref"] => verus_code! {
        enum Opt<T> { Some(T), None }

        struct X {
            a: u64
        }

        proof fn test(x: Opt<&mut X>) {
            match x {
                Opt::Some(X { a: _ }) => {
                }
                Opt::None => { }
            }
        }

        proof fn test2(x: Opt<&mut X>) {
            match x {
                Opt::Some(X { a: _ }) => {
                }
                Opt::None => { }
            }

            assert(x.is_none()); // FAILS
        }

        proof fn test3(x: Opt<&mut X>) {
            match x {
                Opt::Some(X { a: _ }) => {
                }
                Opt::None => { }
            }

            assert(x.is_some()); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] partial_move_from_enum_with_mut_ref ["new-mut-ref"] => verus_code! {
        use vstd::*;

        enum Option<T> { Some(T), None }
        use crate::Option::Some;
        use crate::Option::None;

        // Verus's analysis doesn't account for this, so we need to make sure Rust disallows it
        fn test(xyz: Option<(Box<u64>, Box<u64>)>) {
            let mut xyz = xyz;
            let fst_ref = match xyz {
                Some((ref mut a, _)) => a,
                None => { loop { } }
            };

            let snd = match xyz {
                Some((_, b)) => b,
                None => { loop { } }
            };

            *fst_ref = Box::new(20);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot use `xyz` because it was mutably borrowed")
}

test_verify_one_file_with_options! {
    #[test] partial_move_from_pair_with_mut_ref ["new-mut-ref"] => verus_code! {
        use vstd::*;

        fn test() {
            let mut xyz: (Box<u64>, Box<u64>) = (Box::new(0), Box::new(1));

            let fst_ref = match xyz {
                (ref mut a, _) => a,
            };

            let snd = match xyz {
                (_, b) => b,
            };

            assert(mut_ref_current(fst_ref) == 0);
            *fst_ref = Box::new(20);

            assert(snd == 1);
            assert(xyz.0 == 20);
            assert(xyz.1 == 1);
        }

        fn test_fails() {
            let mut xyz: (Box<u64>, Box<u64>) = (Box::new(0), Box::new(1));

            let fst_ref = match xyz {
                (ref mut a, _) => a,
            };

            let snd = match xyz {
                (_, b) => b,
            };

            assert(mut_ref_current(fst_ref) == 0);
            *fst_ref = Box::new(20);

            assert(snd == 1);
            assert(xyz.0 == 20);
            assert(xyz.1 == 1);
            assert(false); // FAILS
        }

    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] mut_refs_with_if_let ["new-mut-ref"] => verus_code! {
        enum Option<T> { Some(T), None }
        use crate::Option::Some;
        use crate::Option::None;

        fn test_opt(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            if let Some(i) = o_ref {
                assert(orig == Some(*i));

                *i = 20;
            }

            assert(orig is None ==> o is None);
            assert(orig is Some ==> o === Some(20));
        }

        fn test_opt_fails1(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            let mut o_ref = &mut o;
            if let Some(i) = o_ref {
                assert(orig == Some(*i));

                *i = 20;
            }

            assert(orig is None ==> o is None);
            assert(orig is Some ==> o === Some(20));

            assert(o is Some); // FAILS
            assert(o is None); // FAILS
        }

        fn test_explicit_ref_mut(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            if let Some(ref mut i) = o {
                assert(orig == Some(*i));

                *i = 20;
            }

            assert(orig is None ==> o is None);
            assert(orig is Some ==> o === Some(20));
        }

        fn test_explicit_ref_mut_fails(o: Option<u64>, orig: Option<u64>) {
            assume(orig == o);

            let mut o = o;
            if let Some(ref mut i) = o {
                assert(orig == Some(*i));

                *i = 20;
            }

            assert(orig is None ==> o is None);
            assert(orig is Some ==> o === Some(20));

            assert(o is Some); // FAILS
            assert(o is None); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] side_effects_in_match_arg ["new-mut-ref"] => verus_code! {
        enum Blah {
            A(bool),
            B(bool, bool),
            C,
        }

        fn add1(b: &mut u64) -> (ret: (Blah, Blah))
            requires mut_ref_current(b) < 100
            ensures mut_ref_future(b) == mut_ref_current(b) + 1
        {
            *b = *b + 1;
            (Blah::C, Blah::C)
        }

        fn test1() {
            let mut i = 0;

            match add1(&mut i) {
                (Blah::A(t), _) => { }
                (Blah::B(t, u), _) => { }
                _ => { }
            }

            assert(i == 1);
        }

        fn test2() {
            let mut i = 0;

            match add1(&mut i).0 {
                Blah::A(t) => { }
                Blah::B(t, u) => { }
                _ => { }
            }

            assert(i == 1);
        }

        fn test1_fails() {
            let mut i = 0;

            match add1(&mut i) {
                (Blah::A(t), _) => {
                    assert(false); // FAILS
                }
                (Blah::B(t, u), _) => {
                    assert(false); // FAILS
                }
                _ => { }
            }

            assert(i == 1);
        }

        fn test2_fails() {
            let mut i = 0;

            match add1(&mut i).0 {
                Blah::A(t) => {
                    assert(false); // FAILS
                }
                Blah::B(t, u) => { }
                _ => {
                    assert(false); // FAILS
                }
            }

            assert(i == 1);
        }

        fn test3() {
            let mut i = 0;

            let (r, t) = add1(&mut i);

            assert(i == 1);
        }

        fn test3_fails() {
            let mut i = 0;

            let (r, t) = add1(&mut i);

            assert(i == 1);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] enum_conditional_resolution ["new-mut-ref"] => verus_code! {
        enum Foo<A, B> {
            Bar(A, B),
            Qux(A, B),
        }

        fn consume<A>(a: A) { }

        fn test<A, B>(foo: Foo<A, B>) {
            assert(foo is Qux ==> has_resolved(foo->Qux_1));

            match foo {
                Foo::Bar(a, b) => {
                    consume(a);
                    consume(b);
                }
                Foo::Qux(a, _) => {
                    consume(a);
                }
            }
        }

        fn test_fails<A, B>(foo: Foo<A, B>) {
            match foo {
                Foo::Bar(a, b) => {
                    consume(a);
                    consume(b);
                }
                Foo::Qux(a, _) => {
                    consume(a);
                }
            }

            assert(foo is Qux ==> has_resolved(foo->Qux_0)); // FAILS
        }

        fn test_fails2<A, B>(foo: Foo<A, B>) {
            match foo {
                Foo::Bar(a, b) => {
                    consume(a);
                    consume(b);
                }
                Foo::Qux(a, _) => {
                    consume(a);
                }
            }

            assert(foo is Bar ==> has_resolved(foo->Bar_0)); // FAILS
        }

        fn test_fails3<A, B>(foo: Foo<A, B>) {
            match foo {
                Foo::Bar(a, b) => {
                    consume(a);
                    consume(b);
                }
                Foo::Qux(a, _) => {
                    consume(a);
                }
            }

            assert(has_resolved(foo->Qux_1)); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] enum_conditional_resolution_with_mut_refs ["new-mut-ref"] => verus_code! {
        enum Foo<A, B> {
            Bar(A, B),
            Qux(A, B),
        }

        fn test<A, B>(cond: bool) {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;
            let mut d = 3;

            let m_ref = if cond {
                Foo::Bar(&mut a, &mut b)
            } else {
                Foo::Qux(&mut c, &mut d)
            };

            match m_ref {
                Foo::Bar(a_ref, b_ref) => {
                    assert(*a_ref == 0);
                    assert(*b_ref == 1);
                    *a_ref = 100;
                    *b_ref = 101;
                }
                Foo::Qux(_, d_ref) => {
                    assert(*d_ref == 3);
                    *d_ref = 103;
                }
            }

            assert(a === (if cond { 100 } else { 0 }));
            assert(b === (if cond { 101 } else { 1 }));
            assert(c === 2);
            assert(d === (if cond { 3 } else { 103 }));
        }

        fn test_fails<A, B>(cond: bool) {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;
            let mut d = 3;

            let m_ref = if cond {
                Foo::Bar(&mut a, &mut b)
            } else {
                Foo::Qux(&mut c, &mut d)
            };

            match m_ref {
                Foo::Bar(a_ref, b_ref) => {
                    assert(*a_ref == 0);
                    assert(*b_ref == 1);
                    *a_ref = 100;
                    *b_ref = 101;
                }
                Foo::Qux(_, d_ref) => {
                    assert(*d_ref == 3);
                    *d_ref = 103;
                }
            }

            assert(a === (if cond { 100 } else { 0 }));
            assert(b === (if cond { 101 } else { 1 }));
            assert(c === 2);
            assert(d === (if cond { 3 } else { 103 }));

            if cond {
                assert(false); // FAILS
            } else {
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] enum_conditional_resolution_with_mut_refs_and_moves ["new-mut-ref"] => verus_code! {
        enum Foo<A, B> {
            Bar(A, B),
            Qux(A, B),
        }

        fn test<A, B>(cond: bool) {
            let mut a = 0;
            let mut c = 2;

            let mut m_ref = if cond {
                Foo::Bar(&mut a, 1)
            } else {
                Foo::Qux(&mut c, 3)
            };

            match m_ref {
                Foo::Bar(a_ref, ref mut b_ref) => {
                    assert(*a_ref == 0);
                    assert(*b_ref == 1);
                    *a_ref = 100;
                    *b_ref = 101;
                }
                Foo::Qux(_, ref mut d_ref) => {
                    assert(*d_ref == 3);
                    *d_ref = 103;
                }
            }

            assert(a === (if cond { 100 } else { 0 }));
            assert(c === 2);

            if cond {
                assert(m_ref->Bar_1 == 101);
            } else {
                assert(m_ref->Qux_1 == 103);
            }
        }

        fn test_fails<A, B>(cond: bool) {
            let mut a = 0;
            let mut c = 2;

            let mut m_ref = if cond {
                Foo::Bar(&mut a, 1)
            } else {
                Foo::Qux(&mut c, 3)
            };

            match m_ref {
                Foo::Bar(a_ref, ref mut b_ref) => {
                    assert(*a_ref == 0);
                    assert(*b_ref == 1);
                    *a_ref = 100;
                    *b_ref = 101;
                }
                Foo::Qux(_, ref mut d_ref) => {
                    assert(*d_ref == 3);
                    *d_ref = 103;
                }
            }

            assert(a === (if cond { 100 } else { 0 }));
            assert(c === 2);

            if cond {
                assert(m_ref->Bar_1 == 101);
                assert(false); // FAILS
            } else {
                assert(m_ref->Qux_1 == 103);
                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] enum_conditional_resolution_nested ["new-mut-ref"] => verus_code! {
        enum Option<T> { Some(T), None }
        use crate::Option::Some;
        use crate::Option::None;

        fn consume<A>(a: A) { }

        fn test<A, B, C>(x: Option<(Option<(A, B)>, C)>) {
            assert(x is Some && x->Some_0.0 is Some ==> has_resolved(x->Some_0.0->Some_0.1));

            match x {
                Some((Some((a, _)), c)) => {
                    consume(a);
                    consume(c);
                }
                _ => { }
            }
        }

        fn test_fails<A, B, C>(x: Option<(Option<(A, B)>, C)>) {
            match x {
                Some((Some((a, _)), c)) => {
                    consume(a);
                    consume(c);
                }
                _ => { }
            }

            assert(x is Some ==> has_resolved(x->Some_0.0->Some_0.1)); // FAILS
        }

        fn test_fails2<A, B, C>(x: Option<(Option<(A, B)>, C)>) {
            match x {
                Some((Some((a, _)), c)) => {
                    consume(a);
                    consume(c);
                }
                _ => { }
            }

            assert(x->Some_0.0 is Some ==> has_resolved(x->Some_0.0->Some_0.1)); // FAILS
        }

        fn test_fails3<A, B, C>(x: Option<(Option<(A, B)>, C)>) {
            match x {
                Some((Some((a, _)), c)) => {
                    consume(a);
                    consume(c);
                }
                _ => { }
            }

            assert(x is Some && x->Some_0.0 is Some ==> has_resolved(x->Some_0.0->Some_0.0)); // FAILS
        }

        fn test_fails4<A, B, C>(x: Option<(Option<(A, B)>, C)>) {
            match x {
                Some((Some((a, _)), c)) => {
                    consume(a);
                    consume(c);
                }
                _ => { }
            }

            assert(x is Some && x->Some_0.0 is Some ==> has_resolved(x->Some_0.1)); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] enum_conditional_resolution_nested_with_mut_refs ["new-mut-ref"] => verus_code! {
        enum Option<T> { Some(T), None }
        use crate::Option::Some;
        use crate::Option::None;

        fn test() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;

            let x = Some((Some((&mut a, &mut b)), &mut c));

            match x {
                Some((Some((a_ref, _)), c_ref)) => {
                    *a_ref = 10;
                    *c_ref = 12;
                }
                _ => { }
            }

            assert(a == 10);
            assert(b == 1);
            assert(c == 12);
        }

        fn test_fails() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;

            let x = Some((Some((&mut a, &mut b)), &mut c));

            match x {
                Some((Some((a_ref, _)), c_ref)) => {
                    *a_ref = 10;
                    *c_ref = 12;
                }
                _ => { }
            }

            assert(a == 10);
            assert(b == 1);
            assert(c == 12);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] partial_move_out_of_enum ["new-mut-ref"] => verus_code! {
        enum Option<T> { Some(T), None }
        use crate::Option::Some;
        use crate::Option::None;

        fn test() {
            let mut a = 0;
            let mut b = 1;
            let x = Some((&mut a, &mut b));

            match x {
                Some((a, _)) => {
                    *a = 5;
                }
                _ => { }
            }

            match x {
                Some((_, b)) => {
                    *b = 6;
                }
                _ => { }
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "use of partially moved value: `x`")
}

test_verify_one_file_with_options! {
    #[test] partial_move_out_of_enum_no_lifetime ["new-mut-ref", "--no-lifetime"] => verus_code! {
        // Rust's ownership-checking rejects this with "use of partially moved value: `x`"
        // at the second match statement. (As shown in the above test case.)
        // According to a rust dev, this is because the second match statement has to
        // check the discriminant, which is not allowed after a partial move.
        //
        // I still want to check that our resolution analysis does the right thing in this
        // scenario so this test is done with no-lifetime enabled.

        enum Option<T> { Some(T), None }
        use crate::Option::Some;
        use crate::Option::None;

        fn test() {
            let mut a = 0;
            let mut b = 1;
            let x = Some((&mut a, &mut b));

            match x {
                Some((a_ref, _)) => {
                    *a_ref = 5;
                }
                _ => { }
            }

            match x {
                Some((_, b_ref)) => {
                    *b_ref = 6;
                }
                _ => { }
            }

            assert(a == 5);
            assert(b == 6);
        }

        fn test2() {
            let mut a = 0;
            let mut b = 1;
            let x = Some((&mut a, &mut b));

            match x {
                Some((a_ref, _)) => {
                    *a_ref = 5;
                }
                _ => { }
            }

            match x {
                Some((_, b_ref)) => {
                    *b_ref = 6;
                }
                _ => { }
            }

            assert(a == 5);
            assert(b == 6);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] partial_move_out_of_enum2 ["new-mut-ref"] => verus_code! {
        // One way to get around the error more legitimately is to use an enum where
        // one variant is impossible.
        // However, I am told this may be disallowed in the future as well.

        enum Option<T, U> { Some(T), None(U) }
        use crate::Option::Some;
        use crate::Option::None;

        fn test() {
            let mut a = 0;
            let mut b = 1;
            let x = Some::<_, !>((&mut a, &mut b));

            match x {
                Some((a_ref, _)) => {
                    *a_ref = 5;
                }
            }

            match x {
                Some((_, b_ref)) => {
                    *b_ref = 6;
                }
            }

            assert(a == 5);
            assert(b == 6);
        }

        fn test2() {
            let mut a = 0;
            let mut b = 1;
            let x = Some::<_, !>((&mut a, &mut b));

            match x {
                Some((a_ref, _)) => {
                    *a_ref = 5;
                }
            }

            match x {
                Some((_, b_ref)) => {
                    *b_ref = 6;
                }
            }

            assert(a == 5);
            assert(b == 6);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] partial_move_out_of_enum3 ["new-mut-ref"] => verus_code! {
        // Or we could just have an enum with only 1 variant
        // (though this is basically the same as a struct anyway
        // so not a very interesting test case)

        enum Option<T> { Some(T) }
        use crate::Option::Some;

        fn test() {
            let mut a = 0;
            let mut b = 1;
            let x = Some((&mut a, &mut b));

            match x {
                Some((a_ref, _)) => {
                    *a_ref = 5;
                }
            }

            match x {
                Some((_, b_ref)) => {
                    *b_ref = 6;
                }
            }

            assert(a == 5);
            assert(b == 6);
        }

        fn test2() {
            let mut a = 0;
            let mut b = 1;
            let x = Some((&mut a, &mut b));

            match x {
                Some((a_ref, _)) => {
                    *a_ref = 5;
                }
            }

            match x {
                Some((_, b_ref)) => {
                    *b_ref = 6;
                }
            }

            assert(a == 5);
            assert(b == 6);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] not_support_pattern_mut_ref_binding_with_guard ["new-mut-ref"] => verus_code! {
        fn test() {
            let m = (0, 1);
            match m {
                (ref mut a, b) if b == 1 => { }
                _ => { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Not supported: pattern containing both an if-guard and a binding by mutable reference")
}

test_verify_one_file_with_options! {
    #[test] not_support_pattern_mut_ref_binding_with_or_pat ["new-mut-ref"] => verus_code! {
        fn test() {
            let m = (0, false);
            match m {
                (ref mut a, false) | (ref mut a, true) => { }
                _ => { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Not supported: pattern containing both an or-pattern (|) and a binding by mutable reference")
}

test_verify_one_file_with_options! {
    #[test] not_support_let_pattern_mut_ref_binding_with_or_pat ["new-mut-ref"] => verus_code! {
        fn test() {
            let x = Some((5, true));
            let Some((ref mut i, true | false)) = x;
        }
    } => Err(err) => assert_vir_error_msg(err, "Not supported: pattern containing both an or-pattern (|) and a binding by mutable reference")
}
