#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    #[allow(unused_imports)] use crate::pervasive::{cell::*};
    #[allow(unused_imports)] use crate::pervasive::{ptr::*};
    #[allow(unused_imports)] use crate::pervasive::{modes::*};
    #[allow(unused_imports)] use crate::pervasive::{option::*};
    #[allow(unused_imports)] use crate::pervasive::result::*;
};

/// With contradiction_smoke_test, add a final `assert(false)` that is expected to fail at the end
/// of the test, as a cheap way to check that the trusted specs aren't contradictory
fn test_body(tests: &str, contradiction_smoke_test: bool) -> String {
    IMPORTS.to_string()
        + "    fn test() {"
        + tests
        + if contradiction_smoke_test { "assert(false); // FAILS\n" } else { "" }
        + "    }"
}

const CELL_TEST: &str = code_str! {
    let (cell, mut token) = PCell::<u32>::empty();
    assert(equal(token.view().pcell, cell.id()));
    assert(equal(token.view().value, option::Option::None));

    cell.put(&mut token, 5);
    assert(equal(token.view().pcell, cell.id()));
    assert(equal(token.view().value, option::Option::Some(5)));

    let x = cell.replace(&mut token, 7);
    assert(equal(token.view().pcell, cell.id()));
    assert(equal(token.view().value, option::Option::Some(7)));
    assert(equal(x, 5));

    let t = cell.borrow(&token);
    assert(equal(*t, 7));

    let x = cell.take(&mut token);
    assert(equal(token.view().pcell, cell.id()));
    assert(equal(token.view().value, option::Option::None));
    assert(equal(x, 7));
};

test_verify_one_file! {
    #[test] test_cell_pass test_body(CELL_TEST, false) => Ok(())
}

test_verify_one_file! {
    #[test] test_cell_smoke test_body(CELL_TEST, true) => Err(e) => assert_one_fails(e)
}

const PTR_TEST: &str = code_str! {
    let (ptr, mut token) = PPtr::<u32>::empty();
    assert(equal(token.view().pptr, ptr.id()));
    assert(equal(token.view().value, option::Option::None));

    ptr.put(&mut token, 5);
    assert(equal(token.view().pptr, ptr.id()));
    assert(equal(token.view().value, option::Option::Some(5)));

    let x = ptr.replace(&mut token, 7);
    assert(equal(token.view().pptr, ptr.id()));
    assert(equal(token.view().value, option::Option::Some(7)));
    assert(equal(x, 5));

    let t = ptr.borrow(&token);
    assert(equal(*t, 7));

    let x = ptr.take(&mut token);
    assert(equal(token.view().pptr, ptr.id()));
    assert(equal(token.view().value, option::Option::None));
    assert(equal(x, 7));

    ptr.dispose(token);
};

test_verify_one_file! {
    #[test] test_ptr_pass test_body(PTR_TEST, false) => Ok(())
}

test_verify_one_file! {
    #[test] test_ptr_smoke test_body(PTR_TEST, true) => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] cell_mismatch_put IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (cell1, mut token1) = PCell::<u32>::empty();
            let (cell2, mut token2) = PCell::<u32>::empty();
            cell1.put(&mut token2, 5); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_mismatch_take IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (cell1, mut token1) = PCell::<u32>::empty();
            let (cell2, mut token2) = PCell::<u32>::empty();
            cell1.put(&mut token1, 5);
            cell2.put(&mut token2, 5);
            let x = cell1.take(&mut token2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_mismatch_replace IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (cell1, mut token1) = PCell::<u32>::empty();
            let (cell2, mut token2) = PCell::<u32>::empty();
            cell1.put(&mut token1, 5);
            cell2.put(&mut token2, 5);
            let x = cell1.replace(&mut token2, 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_mismatch_borrow IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (cell1, mut token1) = PCell::<u32>::empty();
            let (cell2, mut token2) = PCell::<u32>::empty();
            cell1.put(&mut token1, 5);
            cell2.put(&mut token2, 5);
            let x = cell1.borrow(&token2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_some_put IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (cell1, mut token1) = PCell::<u32>::empty();
            cell1.put(&mut token1, 7);
            cell1.put(&mut token1, 5); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_none_take IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (cell1, mut token1) = PCell::<u32>::empty();
            let x = cell1.take(&mut token1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_none_replace IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (cell1, mut token1) = PCell::<u32>::empty();
            let x = cell1.replace(&mut token1, 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cell_none_borrow IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (cell1, mut token1) = PCell::<u32>::empty();
            let x = cell1.borrow(&token1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_put IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (ptr1, mut token1) = PPtr::<u32>::empty();
            let (ptr2, mut token2) = PPtr::<u32>::empty();
            ptr1.put(&mut token2, 5); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_take IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (ptr1, mut token1) = PPtr::<u32>::empty();
            let (ptr2, mut token2) = PPtr::<u32>::empty();
            ptr1.put(&mut token1, 5);
            ptr2.put(&mut token2, 5);
            let x = ptr1.take(&mut token2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_replace IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (ptr1, mut token1) = PPtr::<u32>::empty();
            let (ptr2, mut token2) = PPtr::<u32>::empty();
            ptr1.put(&mut token1, 5);
            ptr2.put(&mut token2, 5);
            let x = ptr1.replace(&mut token2, 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_borrow IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (ptr1, mut token1) = PPtr::<u32>::empty();
            let (ptr2, mut token2) = PPtr::<u32>::empty();
            ptr1.put(&mut token1, 5);
            ptr2.put(&mut token2, 5);
            let x = ptr1.borrow(&token2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_mismatch_dispose IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (ptr1, mut token1) = PPtr::<u32>::empty();
            let (ptr2, mut token2) = PPtr::<u32>::empty();
            ptr1.dispose(token2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_some_put IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (ptr1, mut token1) = PPtr::<u32>::empty();
            ptr1.put(&mut token1, 7);
            ptr1.put(&mut token1, 5); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_none_take IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (ptr1, mut token1) = PPtr::<u32>::empty();
            let x = ptr1.take(&mut token1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_none_replace IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (ptr1, mut token1) = PPtr::<u32>::empty();
            let x = ptr1.replace(&mut token1, 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_none_borrow IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (ptr1, mut token1) = PPtr::<u32>::empty();
            let x = ptr1.borrow(&token1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ptr_some_dispose IMPORTS.to_string() + code_str! {
        pub fn f() {
            let (ptr1, mut token1) = PPtr::<u32>::empty();
            ptr1.put(&mut token1, 5);
            ptr1.dispose(token1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// Test that cell::Permission<T> correctly inherits the Send and Sync properties of T

test_verify_one_file! {
    #[test] permission_inherits_sync IMPORTS.to_string() + code_str! {
        struct Foo {
            i: u8,
        }

        impl !Sync for Foo { }

        pub fn f<T: Sync>(t: T) {
        }

        pub fn foo(r: cell::Permission<Foo>) {
            f(r);
        }
    } => Err(e) => assert_error_msg(e, "the trait `std::marker::Sync` is not implemented for `Foo`")
}

test_verify_one_file! {
    #[test] permission_inherits_send IMPORTS.to_string() + code_str! {
        struct Foo {
            i: u8,
        }

        impl !Send for Foo { }

        pub fn f<T: Send>(t: T) {
        }

        pub fn foo(r: cell::Permission<Foo>) {
            f(r);
        }
    } => Err(e) => assert_error_msg(e, "the trait `std::marker::Send` is not implemented for `Foo`")
}
