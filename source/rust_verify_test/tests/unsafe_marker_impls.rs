#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] primitive_fields verus_code! {
        use vstd::prelude::*;
        struct Foo {
            x: u32,
            b: bool,
            c: char,
            t: (u8, [u16; 3]),
        }

        unsafe impl Send for Foo { }
        unsafe impl Sync for Foo { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] raw_pointers verus_code! {
        use vstd::prelude::*;
        struct X<T> {
            ptr: *mut T,
        }

        unsafe impl<T> Send for X<T> { }
        unsafe impl<T> Sync for X<T> { }

        struct Y<T> {
            ptr: *const T,
            ptr2: *mut std::rc::Rc<T>,
        }

        unsafe impl<T> Send for Y<T> { }
        unsafe impl<T> Sync for Y<T> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] phantom_data verus_code! {
        use vstd::prelude::*;
        use std::marker::PhantomData;
        struct X<T> {
            p: PhantomData<T>,
            q: PhantomData<std::rc::Rc<u8>>,
            r: PhantomData<*mut T>,
        }

        unsafe impl<T> Send for X<T> { }
        unsafe impl<T> Sync for X<T> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] rc_fails_send verus_code! {
        use vstd::prelude::*;
        struct Y<T> {
            rc: std::rc::Rc<T>,
        }

        unsafe impl<T: Send + Sync> Send for Y<T> { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `std::rc::Rc<T>: Send`")
}

test_verify_one_file! {
    #[test] rc_fails_sync verus_code! {
        use vstd::prelude::*;
        struct Y<T> {
            rc: std::rc::Rc<T>,
        }

        unsafe impl<T: Send + Sync> Sync for Y<T> { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `std::rc::Rc<T>: Sync`")
}

test_verify_one_file! {
    #[test] type_param_needs_bound verus_code! {
        use vstd::prelude::*;
        struct X<T> {
            ptr: *mut T,
            t: T,
        }

        unsafe impl<T> Send for X<T> { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `T: Send`")
}

test_verify_one_file! {
    #[test] type_param_with_bound verus_code! {
        use vstd::prelude::*;
        struct X<T> {
            ptr: *mut T,
            t: T,
            v: Vec<T>,
            b: Box<T>,
        }

        unsafe impl<T: Send> Send for X<T> { }
        unsafe impl<T: Sync> Sync for X<T> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] type_param_wrong_bound verus_code! {
        use vstd::prelude::*;
        struct X<T> {
            ptr: *mut T,
            t: T,
        }

        unsafe impl<T: Send> Sync for X<T> { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `T: Sync`")
}

test_verify_one_file! {
    #[test] where_clause verus_code! {
        use vstd::prelude::*;
        struct X<T> {
            ptr: *mut T,
            t: T,
        }

        unsafe impl<T> Send for X<T> where T: Send { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] shared_ref_send_needs_sync verus_code! {
        use vstd::prelude::*;
        struct X<'a, T> {
            r: &'a T,
        }

        unsafe impl<'a, T: Sync> Send for X<'a, T> { }
        unsafe impl<'a, T: Sync> Sync for X<'a, T> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] shared_ref_send_fails_with_send verus_code! {
        use vstd::prelude::*;
        struct X<'a, T> {
            r: &'a T,
        }

        unsafe impl<'a, T: Send> Send for X<'a, T> { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `T: Sync`")
}

test_verify_one_file! {
    #[test] mut_ref_send_needs_send verus_code! {
        use vstd::prelude::*;
        struct X<'a, T> {
            r: &'a mut T,
        }

        unsafe impl<'a, T: Send> Send for X<'a, T> { }
        unsafe impl<'a, T: Sync> Sync for X<'a, T> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mut_ref_send_fails_with_sync verus_code! {
        use vstd::prelude::*;
        struct X<'a, T> {
            r: &'a mut T,
        }

        unsafe impl<'a, T: Sync> Send for X<'a, T> { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `T: Send`")
}

test_verify_one_file! {
    #[test] ref_to_raw_pointer verus_code! {
        use vstd::prelude::*;
        struct X<'a> {
            r: &'a *mut u8,
            m: &'a mut *const u8,
        }

        unsafe impl<'a> Send for X<'a> { }
        unsafe impl<'a> Sync for X<'a> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] nested_transparent verus_code! {
        use vstd::prelude::*;
        struct Inner<T> {
            p: *mut T,
            q: (u8, *const T),
        }

        struct Outer<T> {
            i: Inner<T>,
            a: [Inner<T>; 2],
        }

        unsafe impl<T> Send for Outer<T> { }
        unsafe impl<T> Sync for Outer<T> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] nested_transparent_fails verus_code! {
        use vstd::prelude::*;
        struct Inner<T> {
            p: *mut T,
            rc: std::rc::Rc<u8>,
        }

        struct Outer<T> {
            i: Inner<T>,
        }

        unsafe impl<T> Send for Outer<T> { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `std::rc::Rc<u8>: Send`")
}

test_verify_one_file! {
    #[test] nested_enum verus_code! {
        use vstd::prelude::*;
        enum E<T> {
            A(*mut T),
            B { x: u8, y: *const T },
            C,
        }

        struct Outer<T> {
            e: E<T>,
            o: Option<*mut T>,
        }

        unsafe impl<T> Send for Outer<T> { }
        unsafe impl<T> Send for E<T> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] enum_fails verus_code! {
        use vstd::prelude::*;
        enum E<T> {
            A(*mut T),
            B(std::rc::Rc<u8>),
        }

        unsafe impl<T> Sync for E<T> { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `std::rc::Rc<u8>: Sync`")
}

test_verify_one_file! {
    #[test] opaque_inner_fails verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        struct Inner {
            p: *mut u8,
        }

        struct Outer {
            i: Inner,
        }

        unsafe impl Send for Outer { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `Inner: Send`")
}

test_verify_one_file! {
    #[test] opaque_std_type_fails verus_code! {
        use vstd::prelude::*;
        struct X {
            v: Vec<*mut u8>,
        }

        unsafe impl Send for X { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `std::vec::Vec<*mut u8>: Send`")
}

test_verify_one_file! {
    #[test] private_fields_in_other_module_fail verus_code! {
        use vstd::prelude::*;
        mod a {
            pub struct Inner {
                p: *mut u8,
            }
        }

        mod b {
            pub struct Outer {
                i: crate::a::Inner,
            }

            unsafe impl Send for Outer { }
        }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `a::Inner: Send`")
}

test_verify_one_file! {
    #[test] public_fields_in_other_module verus_code! {
        use vstd::prelude::*;
        mod a {
            pub struct Inner {
                pub p: *mut u8,
            }
        }

        mod b {
            pub struct Outer {
                i: crate::a::Inner,
            }

            unsafe impl Send for Outer { }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] self_type_opaque_in_impl_module verus_code! {
        use vstd::prelude::*;
        mod a {
            pub struct X {
                p: *mut u8,
            }
        }

        mod b {
            unsafe impl Send for crate::a::X { }
        }
    } => Err(err) => assert_vir_error_msg(err, "must be transparent to Verus in this module")
}

test_verify_one_file! {
    #[test] self_type_external_body verus_code! {
        use vstd::prelude::*;
        #[verifier::external_body]
        struct X {
            p: *mut u8,
        }

        unsafe impl Send for X { }
    } => Err(err) => assert_vir_error_msg(err, "must be transparent to Verus in this module")
}

test_verify_one_file! {
    #[test] external_impl_not_checked verus_code! {
        use vstd::prelude::*;
        struct X {
            p: std::rc::Rc<u8>,
        }

        #[verifier::external]
        unsafe impl Send for X { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] recursive_through_box verus_code! {
        use vstd::prelude::*;
        struct List<T> {
            p: *mut T,
            next: Option<Box<List<T>>>,
        }

        unsafe impl<T> Send for List<T> { }
        unsafe impl<T> Sync for List<T> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] recursive_through_ref verus_code! {
        use vstd::prelude::*;
        struct List<'a, T> {
            p: *mut T,
            next: Option<&'a List<'a, T>>,
        }

        unsafe impl<'a, T> Send for List<'a, T> { }
        unsafe impl<'a, T> Sync for List<'a, T> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mutually_recursive verus_code! {
        use vstd::prelude::*;
        struct A<'a> {
            p: *mut u8,
            b: Option<&'a B<'a>>,
        }

        struct B<'a> {
            q: *const u8,
            a: Option<&'a A<'a>>,
        }

        unsafe impl<'a> Send for A<'a> { }
        unsafe impl<'a> Sync for A<'a> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] field_with_explicit_impl verus_code! {
        use vstd::prelude::*;
        struct Y<T> {
            p: *mut T,
            t: T,
        }

        unsafe impl<T: Send> Send for Y<T> { }

        struct Z<T> {
            y: Y<T>,
        }

        unsafe impl<T: Send> Send for Z<T> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] field_with_explicit_impl_fails verus_code! {
        use vstd::prelude::*;
        struct Y<T> {
            p: *mut T,
            t: T,
        }

        unsafe impl<T: Send> Send for Y<T> { }

        struct Z {
            y: Y<*mut u8>,
        }

        // `Y` has an explicit impl, which requires `*mut u8: Send` in Rust
        unsafe impl Send for Z { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `Y<*mut u8>: Send`")
}

test_verify_one_file! {
    #[test] field_with_negative_impl verus_code! {
        use vstd::prelude::*;
        // Uses vstd's `impl !Send for IsThread`
        struct Z {
            t: vstd::thread::IsThread,
        }

        unsafe impl Send for Z { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `vstd::thread::IsThread: Send`")
}

test_verify_one_file! {
    #[test] specialized_impl verus_code! {
        use vstd::prelude::*;
        struct X<T> {
            p: *mut T,
            t: T,
        }

        unsafe impl Send for X<u8> { }
        unsafe impl Send for X<*mut u8> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] specialized_impl_fails verus_code! {
        use vstd::prelude::*;
        struct X<T> {
            p: *mut T,
            t: T,
        }

        unsafe impl Send for X<std::rc::Rc<u8>> { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `std::rc::Rc<u8>: Send`")
}

test_verify_one_file! {
    #[test] ghost_and_tracked_fields verus_code! {
        use vstd::prelude::*;
        struct X<T> {
            p: *mut T,
            g: Ghost<std::rc::Rc<T>>,
            t: Tracked<vstd::raw_ptr::PointsTo<u8>>,
        }

        unsafe impl<T> Send for X<T> { }
        unsafe impl<T> Sync for X<T> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tracked_field_fails verus_code! {
        use vstd::prelude::*;
        struct X<T> {
            p: *mut T,
            t: Tracked<vstd::raw_ptr::PointsTo<T>>,
        }

        unsafe impl<T> Send for X<T> { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `verus_builtin::Tracked<vstd::raw_ptr::PointsTo<T>>: Send`")
}

test_verify_one_file! {
    #[test] tracked_field_with_bound verus_code! {
        use vstd::prelude::*;
        struct X<T> {
            p: *mut T,
            t: Tracked<vstd::raw_ptr::PointsTo<T>>,
        }

        unsafe impl<T: Send> Send for X<T> { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] dyn_field_fails verus_code! {
        use vstd::prelude::*;
        trait Tr { }

        struct X {
            p: *mut u8,
            f: Box<dyn Tr>,
        }

        unsafe impl Send for X { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `std::boxed::Box<(dyn Tr + 'static)>: Send`")
}

test_verify_one_file! {
    #[test] normalized_projection verus_code! {
        use vstd::prelude::*;
        trait Tr {
            type A;
        }

        impl Tr for u8 {
            type A = *mut u8;
        }

        struct X {
            a: <u8 as Tr>::A,
        }

        unsafe impl Send for X { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] rigid_projection verus_code! {
        use vstd::prelude::*;
        trait Tr {
            type A;
        }

        struct X<T: Tr> {
            a: T::A,
        }

        unsafe impl<T: Tr> Send for X<T> where T::A: Send { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] rigid_projection_fails verus_code! {
        use vstd::prelude::*;
        trait Tr {
            type A;
        }

        struct X<T: Tr> {
            a: T::A,
        }

        unsafe impl<T: Tr> Send for X<T> { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `<T as Tr>::A: Send`")
}

test_verify_one_file! {
    #[test] lifetime_requirements_of_explicit_impls verus_code! {
        use vstd::prelude::*;
        struct Y<'a> {
            r: &'a u8,
            p: *mut u8,
        }

        unsafe impl Send for Y<'static> { }

        struct Z<'a> {
            y: Y<'a>,
        }

        // `Y<'a>: Send` only holds if `'a: 'static`
        unsafe impl<'a> Send for Z<'a> { }
    } => Err(err) => assert_vir_error_msg(err, "could not prove `Y<'a>: Send`")
}

test_verify_one_file! {
    #[test] lifetime_requirements_of_explicit_impls_ok verus_code! {
        use vstd::prelude::*;
        struct Y<'a> {
            r: &'a u8,
            p: *mut u8,
        }

        unsafe impl Send for Y<'static> { }

        struct Z {
            y: Y<'static>,
        }

        unsafe impl Send for Z { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] error_points_to_field verus_code! {
        use vstd::prelude::*;
        struct Inner {
            p: *mut u8,
            rc: std::rc::Rc<u8>,
        }

        struct Outer {
            inner: Inner,
        }

        unsafe impl Send for Outer { }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        let e = &err.errors[0];
        assert!(e.message.contains("cannot verify `unsafe impl Send for Outer`"));
        assert!(e.spans.iter().any(|s| s.label.as_ref().is_some_and(|l| l.contains("field `inner` of `Outer`"))));
        assert!(e.spans.iter().any(|s| s.label.as_ref().is_some_and(|l| l.contains("field `rc` of `Inner`"))));
    }
}

test_verify_one_file! {
    #[test] multiple_errors verus_code! {
        use vstd::prelude::*;
        struct X {
            rc: std::rc::Rc<u8>,
        }

        unsafe impl Send for X { }
        unsafe impl Sync for X { }
    } => Err(err) => assert_vir_error_msgs(err, &[
        "could not prove `std::rc::Rc<u8>: Send`",
        "could not prove `std::rc::Rc<u8>: Sync`",
    ])
}

test_verify_one_file! {
    #[test] polymorphic_recursion_overflow verus_code! {
        use vstd::prelude::*;
        struct W<'a, T> {
            p: *mut T,
            r: Option<&'a W<'a, Option<T>>>,
        }

        unsafe impl<'a, T> Send for W<'a, T> { }
    } => Err(err) => assert_vir_error_msg(err, "recursion limit reached")
}

test_verify_one_file! {
    #[test] use_in_exec_code verus_code! {
        use vstd::prelude::*;
        struct X {
            p: *mut u8,
        }

        unsafe impl Send for X { }

        fn needs_send<T: Send>(t: T) { }

        fn test(x: X) {
            needs_send(x);
        }
    } => Ok(())
}
