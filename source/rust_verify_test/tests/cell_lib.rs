#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    #[allow(unused_imports)] use vstd::*;
    #[allow(unused_imports)] use vstd::pervasive::*;
    #[allow(unused_imports)] use vstd::{cell::*};
    #[allow(unused_imports)] use vstd::{raw_ptr::*};
    #[allow(unused_imports)] use vstd::layout::*;
    #[allow(unused_imports)] use vstd::{modes::*};
    #[allow(unused_imports)] use vstd::prelude::*;
};

/// With contradiction_smoke_test, add a final `assert(false)` that is expected to fail at the end
/// of the test, as a cheap way to check that the trusted specs aren't contradictory
fn test_body(tests: &str, contradiction_smoke_test: bool) -> String {
    IMPORTS.to_string()
        + "    verus!{ fn test() {"
        + tests
        + if contradiction_smoke_test { "assert(false); // FAILS\n" } else { "" }
        + "    } }"
}

const CELL_TEST: &str = code_str! {
    let (cell, Tracked(mut token)) = PCell::<u32>::empty();
    assert(equal(token.view().pcell, cell.id()));
    assert(equal(token.mem_contents(), TypedValue::Empty));

    cell.put(Tracked(&mut token), 5);
    assert(equal(token.view().pcell, cell.id()));
    assert(token.mem_contents().is_valid() && token.mem_contents().value() == 5);

    let x = cell.replace(Tracked(&mut token), 7);
    assert(equal(token.view().pcell, cell.id()));
    assert(token.mem_contents().is_valid() && token.mem_contents().value() == 7);
    assert(equal(x, 5));

    let t = cell.borrow(Tracked(&token));
    assert(equal(*t, 7));

    let x = cell.take(Tracked(&mut token));
    assert(equal(token.view().pcell, cell.id()));
    assert(equal(token.mem_contents(), TypedValue::Empty));
    assert(equal(x, 7));
};

test_verify_one_file! {
    #[test] test_cell_pass test_body(CELL_TEST, false) => Ok(())
}

test_verify_one_file! {
    #[test] test_cell_smoke test_body(CELL_TEST, true) => Err(e) => assert_one_fails(e)
}

const PTR_TEST: &str = code_str! {
    assume(size_of::<u32>() == 4);
    assume(align_of::<u32>() == 4);
    layout_for_type_is_valid::<u32>();
    let (ptr, Tracked(token)) = allocate(4, 4);
    let tracked mut token = raw_ptr::PointsTo::<u32>::from_untyped(token, ());
    let ptr = ptr as *mut u32;

    assert(equal(token.ptr(), ptr));
    assert(equal(token.typed_value(), TypedValue::Empty));

    ptr_mut_write(ptr, Tracked(&mut token), 5);
    assert(equal(token.ptr(), ptr));
    assert(token.is_valid() && token.value() == 5);

    let t = ptr_ref(ptr, Tracked(&token));
    assert(equal(*t, 5));

    let x = ptr_mut_read(ptr, Tracked(&mut token));
    assert(equal(token.ptr(), ptr));
    assert(equal(token.typed_value(), TypedValue::Empty));
    assert(equal(x, 5));

    let tracked token = token.into_untyped();
    deallocate(ptr as *mut u8, 4, 4, Tracked(token));
};

test_verify_one_file! {
    #[test] test_ptr_pass test_body(PTR_TEST, false) => Ok(())
}

test_verify_one_file! {
    #[test] test_ptr_smoke test_body(PTR_TEST, true) => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] cell_mismatch_put IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (cell1, Tracked(mut token1)) = PCell::<u32>::empty();
            let (cell2, Tracked(mut token2)) = PCell::<u32>::empty();
            cell1.put(Tracked(&mut token2), 5); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_mismatch_take IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (cell1, Tracked(mut token1)) = PCell::<u32>::empty();
            let (cell2, Tracked(mut token2)) = PCell::<u32>::empty();
            cell1.put(Tracked(&mut token1), 5);
            cell2.put(Tracked(&mut token2), 5);
            let x = cell1.take(Tracked(&mut token2)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_mismatch_replace IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (cell1, Tracked(mut token1)) = PCell::<u32>::empty();
            let (cell2, Tracked(mut token2)) = PCell::<u32>::empty();
            cell1.put(Tracked(&mut token1), 5);
            cell2.put(Tracked(&mut token2), 5);
            let x = cell1.replace(Tracked(&mut token2), 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_mismatch_borrow IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (cell1, Tracked(mut token1)) = PCell::<u32>::empty();
            let (cell2, Tracked(mut token2)) = PCell::<u32>::empty();
            cell1.put(Tracked(&mut token1), 5);
            cell2.put(Tracked(&mut token2), 5);
            let x = cell1.borrow(Tracked(&token2)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_some_put IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (cell1, Tracked(mut token1)) = PCell::<u32>::empty();
            cell1.put(Tracked(&mut token1), 7);
            cell1.put(Tracked(&mut token1), 5); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_none_take IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (cell1, Tracked(mut token1)) = PCell::<u32>::empty();
            let x = cell1.take(Tracked(&mut token1)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_none_replace IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (cell1, Tracked(mut token1)) = PCell::<u32>::empty();
            let x = cell1.replace(Tracked(&mut token1), 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_none_borrow IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (cell1, Tracked(mut token1)) = PCell::<u32>::empty();
            let x = cell1.borrow(Tracked(&token1)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_put IMPORTS.to_string() + verus_code_str! {
        global layout u32 is size == 4, align == 4;
        pub fn f() {
            layout_for_type_is_valid::<u32>();
            let (ptr1, Tracked(token1)) = allocate(4, 4);
            let (ptr2, Tracked(token2)) = allocate(4, 4);
            let tracked mut token1 = raw_ptr::PointsTo::<u32>::from_untyped(token1, ());
            let tracked mut token2 = raw_ptr::PointsTo::<u32>::from_untyped(token2, ());
            let ptr1 = ptr1 as *mut u32;
            let ptr2 = ptr2 as *mut u32;

            ptr_mut_write(ptr1, Tracked(&mut token2), 5); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_take IMPORTS.to_string() + verus_code_str! {
        global layout u32 is size == 4, align == 4;
        pub fn f() {
            layout_for_type_is_valid::<u32>();
            let (ptr1, Tracked(token1)) = allocate(4, 4);
            let (ptr2, Tracked(token2)) = allocate(4, 4);
            let tracked mut token1 = raw_ptr::PointsTo::<u32>::from_untyped(token1, ());
            let tracked mut token2 = raw_ptr::PointsTo::<u32>::from_untyped(token2, ());
            let ptr1 = ptr1 as *mut u32;
            let ptr2 = ptr2 as *mut u32;
            ptr_mut_write(ptr1, Tracked(&mut token1), 5);
            ptr_mut_write(ptr2, Tracked(&mut token2), 5);

            let x = ptr_mut_read(ptr1, Tracked(&mut token2)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_borrow IMPORTS.to_string() + verus_code_str! {
        global layout u32 is size == 4, align == 4;
        pub fn f() {
            layout_for_type_is_valid::<u32>();
            let (ptr1, Tracked(token1)) = allocate(4, 4);
            let (ptr2, Tracked(token2)) = allocate(4, 4);
            let tracked mut token1 = raw_ptr::PointsTo::<u32>::from_untyped(token1, ());
            let tracked mut token2 = raw_ptr::PointsTo::<u32>::from_untyped(token2, ());
            let ptr1 = ptr1 as *mut u32;
            let ptr2 = ptr2 as *mut u32;
            ptr_mut_write(ptr1, Tracked(&mut token1), 5);
            ptr_mut_write(ptr2, Tracked(&mut token2), 5);

            let x = ptr_ref(ptr1, Tracked(&token2)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_dispose IMPORTS.to_string() + verus_code_str! {
        global layout u32 is size == 4, align == 4;
        pub fn f() {
            layout_for_type_is_valid::<u32>();
            let (ptr1, Tracked(mut token1)) = allocate(4, 4);
            let (ptr2, Tracked(mut token2)) = allocate(4, 4);
            deallocate(ptr1, 4, 4, Tracked(token2)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_dispose2 IMPORTS.to_string() + verus_code_str! {
        global layout u32 is size == 4, align == 4;
        pub fn f() {
            layout_for_type_is_valid::<u32>();
            let (ptr1, Tracked(mut token1)) = allocate(4, 4);
            let (ptr2, Tracked(mut token2)) = allocate(4, 4);
            // The facts that the `Dealloc` token carried are now on the pointer's provenance,
            // so the counterpart of passing the other allocation's `Dealloc` is passing its pointer.
            deallocate(ptr2, 4, 4, Tracked(token1)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_some_put IMPORTS.to_string() + verus_code_str! {
        global layout u32 is size == 4, align == 4;
        pub fn f() {
            layout_for_type_is_valid::<u32>();
            let (ptr1, Tracked(token1)) = allocate(4, 4);
            let tracked mut token1 = raw_ptr::PointsTo::<u32>::from_untyped(token1, ());
            let ptr1 = ptr1 as *mut u32;

            ptr_mut_write(ptr1, Tracked(&mut token1), 7);
            ptr_mut_write(ptr1, Tracked(&mut token1), 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ptr_write_with_read_perm IMPORTS.to_string() + verus_code_str! {
        global layout u32 is size == 4, align == 4;
        pub fn f() {
            layout_for_type_is_valid::<u32>();
            let (ptr1, Tracked(token1)) = allocate(4, 4);
            let tracked mut token1 = raw_ptr::PointsTo::<u32>::from_untyped(token1, ());
            let ptr1 = ptr1 as *mut u32;

            ptr_mut_write(ptr1, Tracked(&token1), 7); // FAILS because ptr_mut_write expects mutable reference
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_write_after_dealloc IMPORTS.to_string() + verus_code_str! {
        global layout u32 is size == 4, align == 4;
        pub fn f() {
            layout_for_type_is_valid::<u32>();
            let (ptr1, Tracked(token1)) = allocate(4, 4);
            let tracked mut token1 = raw_ptr::PointsTo::<u32>::from_untyped(token1, ());
            let ptr1 = ptr1 as *mut u32;
            let tracked untyped1 = token1.into_untyped();
            deallocate(ptr1 as *mut u8, 4, 4, Tracked(untyped1));
            ptr_mut_write(ptr1, Tracked(&mut token1), 7); // FAILS because lifetime of permission has ended
        }
    } => Err(err) => assert_rust_error_msg(err, "borrow of moved value: `token1`")
}

test_verify_one_file! {
    #[test] ptr_none_take IMPORTS.to_string() + verus_code_str! {
        global layout u32 is size == 4, align == 4;
        pub fn f() {
            layout_for_type_is_valid::<u32>();
            let (ptr1, Tracked(token1)) = allocate(4, 4);
            let tracked mut token1 = raw_ptr::PointsTo::<u32>::from_untyped(token1, ());
            let ptr1 = ptr1 as *mut u32;

            let x = ptr_mut_read(ptr1, Tracked(&mut token1)); // FAILS because memory is uninitialized
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_none_borrow IMPORTS.to_string() + verus_code_str! {
        global layout u32 is size == 4, align == 4;
        pub fn f() {
            layout_for_type_is_valid::<u32>();
            let (ptr1, Tracked(token1)) = allocate(4, 4);
            let tracked mut token1 = raw_ptr::PointsTo::<u32>::from_untyped(token1, ());
            let ptr1 = ptr1 as *mut u32;

            let x = ptr_ref(ptr1, Tracked(&token1)); // FAILS because memory is uninitialized
        }
    } => Err(err) => assert_one_fails(err)
}

// Test that cell::PointsTo<T> correctly inherits the Send and Sync properties of T

test_verify_one_file! {
    #[test] permission_inherits_sync IMPORTS.to_string() + code_str! {
        struct Foo {
            i: u8,
        }

        impl !Sync for Foo { }

        pub fn f<T: Sync>(t: T) {
        }

        pub fn foo(r: cell::PointsTo<Foo>) {
            f(r);
        }
    } => Err(e) => assert_rust_error_msg(e, "`Foo` cannot be shared between threads safely")
}

test_verify_one_file! {
    #[test] permission_inherits_send IMPORTS.to_string() + code_str! {
        struct Foo {
            i: u8,
        }

        impl !Send for Foo { }

        pub fn f<T: Send>(t: T) {
        }

        pub fn foo(r: cell::PointsTo<Foo>) {
            f(r);
        }
    } => Err(e) => assert_rust_error_msg(e, "`Foo` cannot be sent between threads safely")
}

test_verify_one_file_with_options! {
    #[test] cell_borrow_mut [] => IMPORTS.to_string() + code_str! {
        verus!{

        fn cell_test() {
            let (c, Tracked(points_to)) = PCell::<u64>::new(0);

            let r = c.borrow_mut(Tracked(&mut points_to));
            *r = 20;

            let x = c.into_inner(Tracked(points_to));
            assert(x == 20);
        }

        fn cell_test2() {
            let (c, Tracked(points_to)) = PCell::<u64>::new(0);

            *c.borrow_mut(Tracked(&mut points_to)) = 20;

            let x = c.into_inner(Tracked(points_to));
            assert(x == 20);
        }

        fn fails_cell_test() {
            let (c, Tracked(points_to)) = PCell::<u64>::new(0);

            let r = c.borrow_mut(Tracked(&mut points_to));
            *r = 20;

            let x = c.into_inner(Tracked(points_to));
            assert(x == 20);
            assert(false); // FAILS
        }

        fn fails_cell_test2() {
            let (c, Tracked(points_to)) = PCell::<u64>::new(0);

            *c.borrow_mut(Tracked(&mut points_to)) = 20;

            let x = c.into_inner(Tracked(points_to));
            assert(x == 20);
            assert(false); // FAILS
        }

        }
    } => Err(e) => assert_fails(e, 2)
}
