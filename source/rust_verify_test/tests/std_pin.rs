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
