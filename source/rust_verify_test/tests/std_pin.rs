#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] pin_unpin_transparent verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::pin::PinAdditionalFns;
        use core::pin::Pin;
        broadcast use vstd::std_specs::pin::group_pin_axioms;

        fn store(x: &mut u64)
            ensures *final(x) == 5,
        {
            let p: Pin<&mut u64> = Pin::new(x);
            let r: &mut u64 = p.get_mut();
            *r = 5;
        }

        fn read(x: &u64) -> (r: u64)
            ensures r == *x,
        {
            let p: Pin<&u64> = Pin::new(x);
            let q = p.get_ref();
            *q
        }

        fn roundtrip(x: &u64) -> (r: u64)
            ensures r == *x,
        {
            let p: Pin<&u64> = Pin::new(x);
            assert(p@ == x);
            *Pin::into_inner(p)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] pin_unpin_fails verus_code! {
        use vstd::prelude::*;
        use core::pin::Pin;
        broadcast use vstd::std_specs::pin::group_pin_axioms;

        fn wrong(x: &mut u64)
            ensures *final(x) == 6, // FAILS
        {
            let p: Pin<&mut u64> = Pin::new(x);
            *p.get_mut() = 5;
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] pin_new_unchecked_ok verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::pin::{PinAdditionalFns, PinAdditionalSpecFns};
        use core::pin::Pin;
        broadcast use vstd::std_specs::pin::group_pin_axioms;

        struct A { }
        struct S { a: A, b: u64 }

        fn test_u64() {
            let mut x: u64 = 5;
            let p: Pin<&mut u64> = unsafe { Pin::new_unchecked(&mut x) };
            assert(*p.pointer() == 5);
            assert(p.mut_ref().current == 5); // trigger axiom_pin_has_resolved
            let y = x;
            assert(y == 5);
        }

        fn test_struct() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            assert(p.pointer().b == 7);
            assert(p.mut_ref().current.b == 7); // trigger axiom_pin_has_resolved
            // non-moving uses are fine
            let r = &s;
            let b = s.b;
            assert(b == 7);
            let ghost g = s;
            assert(g.b == 7);
            let S { a: ref a1, b: b1 } = s;
            match s {
                S { a: ref a2, .. } => { }
            }
        }

        fn test_param(mut s: S) {
            let p = unsafe { Pin::new_unchecked(&mut s) };
            s.b = 5;
            assert(s.b == 5);
        }

        fn test_closure_ok() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            let c = || { let mut t = S { a: A { }, b: 7 }; t.b };
        }
    } => Ok(())
}

fn assert_pin_error(err: TestErr, label: &str) {
    assert_eq!(err.errors.len(), 1);
    let e = &err.errors[0];
    assert!(e.message.contains(
        "possible safety violation: unable to check that the argument to `Pin::new_unchecked` obeys pinning restrictions"
    ));
    assert!(e.rendered.contains("Verus requires the following conditions to be met:"));
    assert!(e.rendered.contains(label));
    assert!(e.rendered.contains("this condition is violated:"));
}

const PIN_STRUCTS: &str = verus_code_str! {
    use vstd::prelude::*;
    use core::pin::Pin;

    struct A { }
    struct S { a: A, b: u64 }

    fn consume<T>(t: T) { }
};

test_verify_one_file! {
    #[test] pin_new_unchecked_arg_not_local PIN_STRUCTS.to_string() + verus_code_str! {
        fn test(s: &mut S) {
            let p = unsafe { Pin::new_unchecked(s) };
        }
    } => Err(err) => assert_pin_error(err, "the argument is not a mutable borrow of a local variable")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_arg_reborrow PIN_STRUCTS.to_string() + verus_code_str! {
        fn test(s: &mut S) {
            let p = unsafe { Pin::new_unchecked(&mut *s) };
        }
    } => Err(err) => assert_pin_error(err, "the argument is not a mutable borrow of a local variable")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_arg_field PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s.a) };
        }
    } => Err(err) => assert_pin_error(err, "the argument is not a mutable borrow of a local variable")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_arg_shared_ref PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&s) };
        }
    } => Err(err) => assert_pin_error(err, "the argument is not a mutable borrow of a local variable")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_move_after PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            let t = s;
        }
    } => Err(err) => assert_pin_error(err, "`s` is moved here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_move_before PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let mut i = 0;
            while i < 2
                decreases 2 - i
            {
                if i == 1 {
                    consume(s);
                    return;
                }
                let p = unsafe { Pin::new_unchecked(&mut s) };
                i = i + 1;
            }
        }
    } => Err(err) => assert_pin_error(err, "`s` is moved here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_move_call_arg PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            consume(s);
        }
    } => Err(err) => assert_pin_error(err, "`s` is moved here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_move_field PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            consume(s.a);
        }
    } => Err(err) => assert_pin_error(err, "`s` is moved here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_move_return PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() -> S {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            s
        }
    } => Err(err) => assert_pin_error(err, "`s` is moved here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_unused PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            s;
        }
    } => Err(err) => assert_pin_error(err, "`s` is moved here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_unused_field PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            s.a;
        }
    } => Err(err) => assert_pin_error(err, "`s` is moved here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_pattern_move PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            let S { a, b } = s;
        }
    } => Err(err) => assert_pin_error(err, "`s` is moved here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_match_move PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            match s {
                S { a, .. } => { }
            }
        }
    } => Err(err) => assert_pin_error(err, "`s` is moved here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_ctor_update_move PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            let t = S { b: 8, .. s };
        }
    } => Err(err) => assert_pin_error(err, "`s` is moved here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_captured PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            let c = || { let r = &s; };
        }
    } => Err(err) => assert_pin_error(err, "`s` is captured by a closure here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_captured_before PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let c = || { let b = s.b; };
            let p = unsafe { Pin::new_unchecked(&mut s) };
        }
    } => Err(err) => assert_pin_error(err, "`s` is captured by a closure here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_in_closure_local PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let c = || {
                let mut s = S { a: A { }, b: 7 };
                let p = unsafe { Pin::new_unchecked(&mut s) };
            };
        }
    } => Err(err) => assert_pin_error(err, "`Pin::new_unchecked` is called inside a closure")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_in_closure_captured PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let mut c = move || {
                let p = unsafe { Pin::new_unchecked(&mut s) };
            };
        }
    } => Err(_) => () // currently rejected because closures can't mutably borrow captured vars;
                       // otherwise, rejected by the pin_new_unchecked check
}

test_verify_one_file! {
    #[test] pin_new_unchecked_ok_assign_and_repin PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            s.b = 8;
            let q = unsafe { Pin::new_unchecked(&mut s) };
            s = S { a: A { }, b: 9 };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] pin_new_unchecked_mut_borrow_after PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            let r = &mut s;
        }
    } => Err(err) => assert_pin_error(err, "`s` is mutably borrowed here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_mut_borrow_before PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let r = &mut s;
            let p = unsafe { Pin::new_unchecked(&mut s) };
        }
    } => Err(err) => assert_pin_error(err, "`s` is mutably borrowed here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_mut_borrow_field PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            let r = &mut s.b;
        }
    } => Err(err) => assert_pin_error(err, "`s` is mutably borrowed here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_mut_borrow_swap PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let mut t = S { a: A { }, b: 8 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            core::mem::swap(&mut s, &mut t);
        }
    } => Err(err) => assert_pin_error(err, "`s` is mutably borrowed here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_mut_borrow_method PIN_STRUCTS.to_string() + verus_code_str! {
        impl S {
            fn set(&mut self) { self.b = 0; }
        }

        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            s.set();
        }
    } => Err(err) => assert_pin_error(err, "`s` is mutably borrowed here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_mut_borrow_pattern PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            let S { a: ref mut a1, .. } = s;
        }
    } => Err(err) => assert_pin_error(err, "`s` is mutably borrowed here")
}

test_verify_one_file! {
    #[test] pin_new_unchecked_mut_borrow_match PIN_STRUCTS.to_string() + verus_code_str! {
        fn test() {
            let mut s = S { a: A { }, b: 7 };
            let p = unsafe { Pin::new_unchecked(&mut s) };
            match s {
                S { ref mut b, .. } => { }
            }
        }
    } => Err(err) => assert_pin_error(err, "`s` is mutably borrowed here")
}
