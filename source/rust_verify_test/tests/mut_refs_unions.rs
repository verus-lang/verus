#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] test_basic ["new-mut-ref"] => verus_code! {
        union X { a: u64, b: (bool, bool) }

        fn test_mut_ref() {
            unsafe {
                let mut x = X { a: 5 };
                let field_ref = &mut x.a;
                *field_ref = 6;

                let y = x.a;
                assert(y == 6);
            }
        }

        fn fails_mut_ref() {
            unsafe {
                let mut x = X { a: 5 };
                let field_ref = &mut x.a;
                *field_ref = 6;

                let y = x.a;
                assert(y == 6);
                assert(false); // FAILS
            }
        }

        fn test_mut_ref_nested() {
            unsafe {
                let mut x = X { b: (true, false) };
                let field_ref = &mut x.b.1;
                *field_ref = true;

                let y = x.b;
            }
        }

        fn fails_mut_ref_nested() {
            unsafe {
                let mut x = X { b: (true, false) };
                let field_ref = &mut x.b.1;
                *field_ref = true;

                let y = x.b;
                assert(y == (true, true));
                assert(false); // FAILS
            }
        }

        fn test_assign() {
            unsafe {
                let mut x = X { a: 5 };
                x.a = 6;

                let y = x.a;
                assert(y == 6);
            }
        }

        fn fails_assign() {
            unsafe {
                let mut x = X { a: 5 };
                x.a = 6;

                let y = x.a;
                assert(y == 6);
                assert(false); // FAILS
            }
        }

        fn test_assign_nested() {
            unsafe {
                let mut x = X { b: (true, false) };
                x.b.1 = true;

                let y = x.b;
                assert(y == (true, true));
            }
        }

        fn fails_assign_nested() {
            unsafe {
                let mut x = X { b: (true, false) };
                x.b.1 = true;

                let y = x.b;
                assert(y == (true, true));
                assert(false); // FAILS
            }
        }
    } => Err(e) => assert_fails(e, 4)
}

test_verify_one_file_with_options! {
    #[test] test_wrong_variant_mut_ref ["new-mut-ref"] => verus_code! {
        union X { a: u64, b: (bool, bool) }

        fn test_mut_ref() {
            unsafe {
                let mut x = X { b: (true, false) };
                let field_ref = &mut x.a; // FAILS
            }
        }

        fn test_mut_ref_nested() {
            unsafe {
                let mut x = X { a: 5 };
                let field_ref = &mut x.b.1; // FAILS
            }
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file_with_options! {
    #[test] test_wrong_variant_assign ["new-mut-ref"] => verus_code! {
        union X { a: u64, b: (bool, bool) }
        fn test_assign() {
            let mut x = X { b: (true, false) };

            // this could actually be supported
            x.a = 6; // FAILS
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file_with_options! {
    #[test] test_wrong_variant_assign_nested ["new-mut-ref"] => verus_code! {
        union X { a: u64, b: (bool, bool) }
        fn test_assign_nested() {
            let mut x = X { a: 0 };
            // this is safe Rust, but the semantics would be hard for us to support
            x.b.1 = true; // FAILS
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file_with_options! {
    #[test] ctor_update_tail ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        #[derive(Clone, Copy)]
        struct Pair { a: bool, b: bool }

        union X { a: u64, b: Pair }

        fn test_update() {
            unsafe {
                let x = X { b: Pair { a: false, b: true } };
                let r = Pair { a: true, .. x.b };
                assert(r.a && r.b);
            }
        }

        fn fails_update() {
            unsafe {
                let x = X { b: Pair { a: false, b: true } };
                let r = Pair { a: true, .. x.b };
                assert(r.a && r.b);
                assert(false); // FAILS
            }
        }

        fn wrong_variant() {
            unsafe {
                let x = X { a: 3 };
                let r = Pair { a: true, .. x.b }; // FAILS
            }
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file_with_options! {
    #[test] test_match ["new-mut-ref"] => verus_code! {
        union X { a: u64, b: (bool, bool) }

        fn test_match() {
            unsafe {
                let mut x = X { b: (true, false) };
                match x.b {
                    (ref mut bool1, ref mut bool2) => {
                        assert(*bool1 == true);
                        assert(*bool2 == false);
                        *bool1 = false;
                        *bool2 = true;
                    }
                }
                let y = x.b;
                assert(y == (false, true));
            }
        }

        fn fails_match() {
            unsafe {
                let mut x = X { b: (true, false) };
                match x.b {
                    (ref mut bool1, ref mut bool2) => {
                        assert(*bool1 == true);
                        assert(*bool2 == false);
                        *bool1 = false;
                        *bool2 = true;
                    }
                }
                let y = x.b;
                assert(y == (false, true));
                assert(false); // FAILS
            }
        }

        fn wrong_variant() {
            unsafe {
                let mut x = X { a: 0 };
                match
                    x.b // FAILS
                {
                    (ref mut bool1, ref mut bool2) => {
                    }
                }
            }
        }

        fn wrong_variant2() {
            unsafe {
                let mut x = X { a: 0 };
                match
                    x.b // FAILS
                {
                    _ => {
                    }
                }
            }
        }
    } => Err(e) => assert_fails(e, 3)
}

test_verify_one_file_with_options! {
    #[test] test_temporary ["new-mut-ref"] => verus_code! {
        union X { a: u64, b: (bool, bool) }

        fn test1() {
            let r = &mut (X { a: 0 }).a;
            assert(*r == 0);
        }

        fn fails_test1() {
            let r = &mut (X { a: 0 }).a;
            assert(*r == 0);
            assert(false); // FAILS
        }

        fn test_wrong_variant() {
            let r = &mut (X { a: 0 }).b; // FAILS
        }

        fn test_counts() {
            let mut count = 0;
            let z = ({ count = count + 1; X { b: (true, false) } }).b;
            assert(z == (true, false));
            assert(count == 1);
        }

        fn fail_counts() {
            let mut count = 0;
            let z = ({ count = count + 1; X { b: (true, false) } }).b;
            assert(z == (true, false));
            assert(count == 1);
            assert(false); // FAILS
        }

        fn test_counts_mut_ref() {
            let mut count = 0;
            let z = &mut ({ count = count + 1; X { b: (true, false) } }).b;
            assert(*z == (true, false));
            assert(count == 1);
        }

        fn fail_counts_mut_ref() {
            let mut count = 0;
            let z = &mut ({ count = count + 1; X { b: (true, false) } }).b;
            assert(*z == (true, false));
            assert(count == 1);
            assert(false); // FAILS
        }

        fn test_counts_match() {
            let mut count = 0;
            match ({ count = count + 1; X { b: (true, false) } }).b {
                (ref mut bool1, ref mut bool2) => {
                    assert(*bool1 == true);
                    assert(*bool2 == false);
                }
            }
            assert(count == 1);
        }

        fn fail_counts_match() {
            let mut count = 0;
            match ({ count = count + 1; X { b: (true, false) } }).b {
                (ref mut bool1, ref mut bool2) => {
                    assert(*bool1 == true);
                    assert(*bool2 == false);
                }
            }
            assert(count == 1);
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 5)
}

test_verify_one_file_with_options! {
    #[test] array_plus_union_field ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        union X { a: u64, b: (bool, bool) }

        fn test() {
            let mut a: [X; 2] = [X { a: 0 }, X { b: (true, false) }];
            let mut count = 0;
            let r = &mut a[({ count = count + 1; 0 })].a;
            assert(*r == 0);
            *r = 20;

            let y1 = a[0].a;
            let y2 = a[1].b;
            assert(y1 == 20);
            assert(y2 == (true, false));
            assert(count == 1);
        }

        fn test2() {
            let mut a: [X; 2] = [X { a: 0 }, X { b: (true, false) }];
            let mut count = 0;
            let r = &mut a[({ count = count + 1; 0 })].a;
            assert(*r == 0);
            *r = 20;

            let y1 = a[0].a;
            let y2 = a[1].b;
            assert(y1 == 20);
            assert(y2 == (true, false));
            assert(count == 1);
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file_with_options! {
    #[test] union_has_resolved ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;
        use std::mem::ManuallyDrop;

        union Foo<'a> {
            a: ManuallyDrop<&'a mut u64>,
            b: ManuallyDrop<&'a mut u64>,
        }

        proof fn test<'a>(foo: Foo<'a>) {
            assert(has_resolved(foo) ==> is_variant(foo, "a") ==>
                has_resolved(get_union_field::<_, ManuallyDrop<&'a mut u64>>(foo, "a")@));

            assert(has_resolved(foo) ==> is_variant(foo, "b") ==>
                has_resolved(get_union_field::<_, ManuallyDrop<&'a mut u64>>(foo, "b")@));
        }

        proof fn test2<'a>(foo: Foo<'a>) {
            assert(has_resolved(foo) ==>
                has_resolved(get_union_field::<_, ManuallyDrop<&'a mut u64>>(foo, "a")@)); // FAILS
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file_with_options! {
    #[test] union_with_mut_ref_in_fields ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;
        use std::mem::ManuallyDrop;
        use std::ops::DerefMut;

        union Foo<'a> {
            a: ManuallyDrop<&'a mut u64>,
            b: ManuallyDrop<&'a mut u64>,
        }

        #[verifier::external_body]
        fn manually_drop_deref_mut<T>(m: &mut ManuallyDrop<T>) -> (ret: &mut T)
            ensures
                mut_ref_current(ret) == mut_ref_current(m)@,
                mut_ref_future(ret) == mut_ref_future(m)@,
        {
            m.deref_mut()
        }

        fn test<'a>() {
            let mut a = 0;
            let a_ref = &mut a;
            let foo = Foo { a: ManuallyDrop::new(a_ref) };
            assert(has_resolved(get_union_field::<_, ManuallyDrop<&mut u64>>(foo, "a"))); // TODO(new_mut_ref): bad triggers
            assert(a == 0);
        }

        fn fail<'a>() {
            let mut a = 0;
            let a_ref = &mut a;
            let foo = Foo { a: ManuallyDrop::new(a_ref) };
            assert(has_resolved(get_union_field::<_, ManuallyDrop<&mut u64>>(foo, "a"))); // TODO(new_mut_ref): bad triggers
            assert(a == 0);
            assert(false); // FAILS
        }

        fn test2<'a>() {
            let mut a = 0;
            let a_ref = &mut a;
            let mut foo = Foo { a: ManuallyDrop::new(a_ref) };
            **manually_drop_deref_mut(&mut foo.a) = 5;
            assert(a == 5);
        }

        fn fail2<'a>() {
            let mut a = 0;
            let a_ref = &mut a;
            let mut foo = Foo { a: ManuallyDrop::new(a_ref) };
            **manually_drop_deref_mut(&mut foo.a) = 5;
            assert(a == 5);
            assert(false); // FAILS
        }

        fn test3<'a>() {
            let mut a = 0;
            let a_ref = &mut a;
            let mut foo = Foo { a: ManuallyDrop::new(a_ref) };
            **manually_drop_deref_mut(&mut foo.a) = 5;
            let a_ref2 = foo.a;
            assert(a == 5);
        }

        fn fail3<'a>() {
            let mut a = 0;
            let a_ref = &mut a;
            let mut foo = Foo { a: ManuallyDrop::new(a_ref) };
            **manually_drop_deref_mut(&mut foo.a) = 5;
            let a_ref2 = foo.a;
            assert(a == 5);
            assert(false); // FAILS
        }

        fn test4<'a>() {
            let mut a = 0;
            let a_ref = &mut a;
            let mut foo = Foo { a: ManuallyDrop::new(a_ref) };
            **manually_drop_deref_mut(&mut foo.a) = 5;
            let a_ref2 = foo.a;
            let a_ref2 = ManuallyDrop::into_inner(a_ref2);
            *a_ref2 = 20;
            assert(a == 20);
        }

        fn fail4<'a>() {
            let mut a = 0;
            let a_ref = &mut a;
            let mut foo = Foo { a: ManuallyDrop::new(a_ref) };
            **manually_drop_deref_mut(&mut foo.a) = 5;
            let a_ref2 = foo.a;
            let a_ref2 = ManuallyDrop::into_inner(a_ref2);
            *a_ref2 = 20;
            assert(a == 20);
            assert(false); // FAILS
        }

        fn test5<'a>() {
            let mut a = 0;
            let a_ref = &mut a;
            let mut foo = Foo { a: ManuallyDrop::new(a_ref) };
            **manually_drop_deref_mut(&mut foo.a) = 5;
            let a_ref2 = ManuallyDrop::into_inner(foo.a);
            *a_ref2 = 20;
            assert(a == 20);
        }

        fn fail5<'a>() {
            let mut a = 0;
            let a_ref = &mut a;
            let mut foo = Foo { a: ManuallyDrop::new(a_ref) };
            **manually_drop_deref_mut(&mut foo.a) = 5;
            let a_ref2 = ManuallyDrop::into_inner(foo.a);
            *a_ref2 = 20;
            assert(a == 20);
            assert(false); // FAILS
        }
    } => Err(e) => assert_fails(e, 5)
}
