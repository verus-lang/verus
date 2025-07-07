#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// See https://doc.rust-lang.org/std/mem/fn.size_of.html
// for stable guarantees about the size of Rust types

test_verify_one_file! {
    #[test] sizeof_test verus_code! {
        use vstd::layout::*;
        use std::sync::Arc;
        use std::rc::Rc;

        // this size of a pointer/reference should be the same as usize ONLY
        // for sized types V

        fn test_unsized_wrong<V: ?Sized>() {
            assert(size_of::<&V>() == size_of::<usize>()); // FAILS
        }

        fn test_unsized_wrong2() {
            assert(size_of::<&[u8]>() == size_of::<usize>()); // FAILS
        }

        // (&mut not supported right now)
        //fn test_unsized_wrong3<V: ?Sized>() {
        //    assert(size_of::<&mut V>() == size_of::<usize>()); // FAILS
        //}

        //fn test_unsized_wrong4() {
        //    assert(size_of::<&mut [u8]>() == size_of::<usize>()); // FAILS
        //}

        fn test_unsized_wrong5<V: ?Sized>() {
            assert(size_of::<Box<V>>() == size_of::<usize>()); // FAILS
        }

        fn test_unsized_wrong6() {
            assert(size_of::<Box<[u8]>>() == size_of::<usize>()); // FAILS
        }

        // I don't think Rust guarantees this, so this should fail.

        fn test_tuple_wrong<A, B>() {
            assert(size_of::<(A, B)>() == size_of::<A>() + size_of::<B>()); // FAILS
        }

        // &A and A need to be distinguished

        fn test_ref_distinguished<A, B>() {
            assert(size_of::<A>() == size_of::<&A>()); // FAILS
        }

        //fn test_mut_ref_distinguished<A, B>() {
        //    assert(size_of::<A>() == size_of::<&mut A>()); // FAILS
        //}

        fn test_box_distinguished<A, B>() {
            assert(size_of::<A>() == size_of::<Box<A>>()); // FAILS
        }

        fn test_rc_distinguished<A, B>() {
            assert(size_of::<A>() == size_of::<Rc<A>>()); // FAILS
        }

        fn test_arc_distinguished<A, B>() {
            assert(size_of::<A>() == size_of::<Arc<A>>()); // FAILS
        }

        // See the explanation in vstd/layout.rs for why we don't make this assumption.

        fn test_not_assumed_bounded<V>() {
            assert(size_of::<V>() as usize as int == size_of::<V>()); // FAILS
        }

        fn test_not_assumed_bounded_align<V>() {
            assert(align_of::<V>() as usize as int == align_of::<V>()); // FAILS
        }

        fn test_not_assumed_nonzero<V>() {
            assert(size_of::<V>() != 0); // FAILS
        }
    } => Err(err) => assert_fails(err, 12)
}

test_verify_one_file! {
    #[test] sized_trait_broadcast verus_code! {
        mod m {
            use super::*;

            pub spec fn is_sized<T: ?Sized>() -> bool;

            pub broadcast proof fn is_sized_from_trait<T: Sized>()
                ensures is_sized::<T>()
            {
                assume(false);
            }
        }

        use m::is_sized;
        broadcast use m::is_sized_from_trait;

        proof fn test() {
            assert(is_sized::<u64>());
        }

        proof fn test2<T>() {
            assert(is_sized::<T>());
        }

        proof fn test3<T: ?Sized>() {
            assert(is_sized::<T>()); // FAILS
        }

        proof fn test4<T>() {
            assert(is_sized::<[T]>()); // FAILS
        }

        struct Y {
            a: u32,
            b: u32,
        }

        struct X {
            a: u32,
            b: [u32],
        }

        struct Z<B: ?Sized> {
            a: u32,
            b: B,
        }

        proof fn test_sized_struct<T>() {
            assert(is_sized::<Y>());
        }

        proof fn test_unsized_struct<T>() {
            assert(is_sized::<X>()); // FAILS
        }

        proof fn test_conditional_struct<T>() {
            assert(is_sized::<Z<T>>());
        }

        proof fn test_conditional_struct_fail<T: ?Sized>() {
            assert(is_sized::<Z<T>>()); // FAILS
        }

        proof fn test_conditional_struct_specific() {
            assert(is_sized::<Z<u32>>());
        }

        proof fn test_conditional_struct_specific_fail() {
            assert(is_sized::<Z<[bool]>>()); // FAILS
        }

        #[verifier::external_body]
        #[verifier::reject_recursive_types(B)]
        struct Zopaque<B: ?Sized> {
            a: u32,
            b: B,
        }

        proof fn test_conditional_struct_opaque<T>() {
            assert(is_sized::<Zopaque<T>>());
        }

        proof fn test_conditional_struct_opaque_fail<T: ?Sized>() {
            assert(is_sized::<Zopaque<T>>()); // FAILS
        }

        proof fn test_conditional_struct_opaque_specific() {
            assert(is_sized::<Zopaque<u32>>());
        }

        proof fn test_conditional_struct_opaque_specific_fail() {
            assert(is_sized::<Zopaque<[bool]>>()); // FAILS
        }

        proof fn test_reference<T: ?Sized>() {
            assert(is_sized::<&T>());
            assert(is_sized::<T>()); // FAILS
        }

        proof fn test_tuple<T: ?Sized>() {
            assert(is_sized::<(u64, T)>()); // FAILS
        }

        proof fn test_tuple_sized<T: Sized>() {
            assert(is_sized::<()>());
            assert(is_sized::<(u64, )>());
            assert(is_sized::<(T, )>());
            assert(is_sized::<(u64, T)>());
            assert(is_sized::<(u64, u32, T)>());
        }
    } => Err(err) => assert_fails(err, 9)
}

test_verify_one_file! {
    #[test] pointee_metadata verus_code! {
        use core::ptr::Pointee;

        struct X { }

        struct Pair<A, B: ?Sized> {
            a: A,
            b: B,
        }

        uninterp spec fn typefn<M>() -> int;

        spec fn metatypefn<T: ?Sized>() -> int {
            typefn::<<T as Pointee>::Metadata>()
        }

        fn test() {
            assert(metatypefn::<X>() == typefn::<()>());
            assert(metatypefn::<[X]>() == typefn::<usize>());
        }
        fn test2() {
            assert(metatypefn::<X>() == typefn::<()>());
            assert(metatypefn::<[X]>() == typefn::<usize>());
            assert(false); // FAILS
        }

        fn test_sized<Y>() {
            assert(metatypefn::<Y>() == typefn::<()>());
        }

        fn test_unsized<Y: ?Sized>() {
            assert(metatypefn::<Y>() == typefn::<()>()); // FAILS
        }

        fn test_dst_struct<B: ?Sized>() {
            assert(metatypefn::<B>() == metatypefn::<Pair<u32, B>>());
        }
    } => Err(err) => assert_fails(err, 2)
}
