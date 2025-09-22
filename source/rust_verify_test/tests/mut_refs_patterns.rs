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
