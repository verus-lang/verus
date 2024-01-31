#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    #[allow(unused_imports)] use vstd::*;
    #[allow(unused_imports)] use vstd::pervasive::*;
    #[allow(unused_imports)] use vstd::{cell::*};
    #[allow(unused_imports)] use vstd::{ptr::*};
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
    assert(equal(token.view().value, Option::None));

    cell.put(Tracked(&mut token), 5);
    assert(equal(token.view().pcell, cell.id()));
    assert(equal(token.view().value, Option::Some(5)));

    let x = cell.replace(Tracked(&mut token), 7);
    assert(equal(token.view().pcell, cell.id()));
    assert(equal(token.view().value, Option::Some(7)));
    assert(equal(x, 5));

    let t = cell.borrow(Tracked(&token));
    assert(equal(*t, 7));

    let x = cell.take(Tracked(&mut token));
    assert(equal(token.view().pcell, cell.id()));
    assert(equal(token.view().value, Option::None));
    assert(equal(x, 7));
};

test_verify_one_file! {
    #[test] test_cell_pass test_body(CELL_TEST, false) => Ok(())
}

test_verify_one_file! {
    #[test] test_cell_smoke test_body(CELL_TEST, true) => Err(e) => assert_one_fails(e)
}

const PTR_TEST: &str = code_str! {
    let (ptr, Tracked(mut token), Tracked(dealloc)) = PPtr::<u32>::empty();
    assert(equal(token.view().pptr, ptr.id()));
    assert(equal(token.view().value, Option::None));

    ptr.put(Tracked(&mut token), 5);
    assert(equal(token.view().pptr, ptr.id()));
    assert(equal(token.view().value, Option::Some(5)));

    let x = ptr.replace(Tracked(&mut token), 7);
    assert(equal(token.view().pptr, ptr.id()));
    assert(equal(token.view().value, Option::Some(7)));
    assert(equal(x, 5));

    let t = ptr.borrow(Tracked(&token));
    assert(equal(*t, 7));

    let x = ptr.take(Tracked(&mut token));
    assert(equal(token.view().pptr, ptr.id()));
    assert(equal(token.view().value, Option::None));
    assert(equal(x, 7));

    ptr.dispose(Tracked(token), Tracked(dealloc));
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
        pub fn f() {
            let (ptr1, Tracked(mut token1), Tracked(dealloc)) = PPtr::<u32>::empty();
            let (ptr2, Tracked(mut token2), Tracked(dealloc)) = PPtr::<u32>::empty();
            ptr1.put(Tracked(&mut token2), 5); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_take IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (ptr1, Tracked(mut token1), Tracked(dealloc1)) = PPtr::<u32>::empty();
            let (ptr2, Tracked(mut token2), Tracked(dealloc2)) = PPtr::<u32>::empty();
            ptr1.put(Tracked(&mut token1), 5);
            ptr2.put(Tracked(&mut token2), 5);
            let x = ptr1.take(Tracked(&mut token2)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_replace IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (ptr1, Tracked(mut token1), Tracked(dealloc)) = PPtr::<u32>::empty();
            let (ptr2, Tracked(mut token2), Tracked(dealloc)) = PPtr::<u32>::empty();
            ptr1.put(Tracked(&mut token1), 5);
            ptr2.put(Tracked(&mut token2), 5);
            let x = ptr1.replace(Tracked(&mut token2), 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_borrow IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (ptr1, Tracked(mut token1), Tracked(dealloc)) = PPtr::<u32>::empty();
            let (ptr2, Tracked(mut token2), Tracked(dealloc)) = PPtr::<u32>::empty();
            ptr1.put(Tracked(&mut token1), 5);
            ptr2.put(Tracked(&mut token2), 5);
            let x = ptr1.borrow(Tracked(&token2)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_dispose IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (ptr1, Tracked(mut token1), Tracked(dealloc1)) = PPtr::<u32>::empty();
            let (ptr2, Tracked(mut token2), Tracked(dealloc2)) = PPtr::<u32>::empty();
            ptr1.dispose(Tracked(token2), Tracked(dealloc1)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_dispose2 IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (ptr1, Tracked(mut token1), Tracked(dealloc1)) = PPtr::<u32>::empty();
            let (ptr2, Tracked(mut token2), Tracked(dealloc2)) = PPtr::<u32>::empty();
            ptr1.dispose(Tracked(token1), Tracked(dealloc2)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_some_put IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (ptr1, Tracked(mut token1), Tracked(dealloc)) = PPtr::<u32>::empty();
            ptr1.put(Tracked(&mut token1), 7);
            ptr1.put(Tracked(&mut token1), 5); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_none_take IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (ptr1, Tracked(mut token1), Tracked(dealloc)) = PPtr::<u32>::empty();
            let x = ptr1.take(Tracked(&mut token1)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_none_replace IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (ptr1, Tracked(mut token1), Tracked(dealloc)) = PPtr::<u32>::empty();
            let x = ptr1.replace(Tracked(&mut token1), 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_none_borrow IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (ptr1, Tracked(mut token1), Tracked(dealloc)) = PPtr::<u32>::empty();
            let x = ptr1.borrow(Tracked(&token1)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_some_dispose IMPORTS.to_string() + verus_code_str! {
        pub fn f() {
            let (ptr1, Tracked(mut token1), Tracked(dealloc)) = PPtr::<u32>::empty();
            ptr1.put(Tracked(&mut token1), 5);
            ptr1.dispose(Tracked(token1), Tracked(dealloc)); // FAILS
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
