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
    #[test] explicit_ref_mut_binding ["new-mut-ref"] => verus_code! {
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

// TODO(new_mut_ref): fix (failing because of the variant-related corner cases in match resolution inference)
test_verify_one_file_with_options! {
    #[test] #[ignore] complex_nesting_enum_2_variant ["new-mut-ref"] => verus_code! {
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
                    assert(*r_pair_0 == 4);
                    assert(**rx == 0);
                    assert(*ry == 1);

                    *r_pair_0 = 20;
                    **rx = 21;
                    *ry = 22;

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

                    assert(has_resolved(r_pair_0));
                }
                BigEnum::B(rz) => {
                    assert(**rz == 2);
                    **rz = 35;
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
