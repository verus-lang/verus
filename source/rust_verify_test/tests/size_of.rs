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
