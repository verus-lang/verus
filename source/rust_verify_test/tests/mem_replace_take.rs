#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] mem_replace verus_code! {
        use vstd::prelude::*;

        fn test_u32() {
            let mut x: u32 = 5;
            let old = std::mem::replace(&mut x, 7);
            assert(old == 5);
            assert(x == 7);
        }

        fn test_vec(v: Vec<u8>) {
            let mut v = v;
            let ghost v0 = v@;
            let w = core::mem::replace(&mut v, Vec::new());
            assert(w@ == v0);
            assert(v@.len() == 0);
        }

        fn test_generic<T>(dest: &mut T, src: T) -> (res: T)
            ensures
                res == *old(dest),
                *final(dest) == src,
            no_unwind
        {
            std::mem::replace(dest, src)
        }

        fn test_field(p: &mut (u8, u16)) {
            let ghost old_p = *p;
            let a = std::mem::replace(&mut p.0, 1);
            assert(a == old_p.0);
            assert(p.0 == 1);
            assert(p.1 == old_p.1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mem_replace_returns_old_value_not_new verus_code! {
        use vstd::prelude::*;

        fn test_wrong() {
            let mut x: u32 = 5;
            let old = std::mem::replace(&mut x, 7);
            assert(old == 7); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] mem_take verus_code! {
        use vstd::prelude::*;

        fn test_u64() {
            let mut x: u64 = 9;
            let old = std::mem::take(&mut x);
            assert(old == 9);
            assert(x == 0);
        }

        fn test_option() {
            let mut o: Option<u8> = Some(3);
            let old = core::mem::take(&mut o);
            assert(old == Some(3u8));
            assert(o.is_none());
        }

        fn test_vec(v: Vec<u8>) {
            let mut v = v;
            let ghost v0 = v@;
            let w = std::mem::take(&mut v);
            assert(w@ == v0);
            assert(v@.len() == 0);
        }

        fn test_generic<T: Default>(dest: &mut T) -> (res: T)
            ensures
                res == *old(dest),
                T::default.ensures((), *final(dest)),
        {
            std::mem::take(dest)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mem_take_does_not_leave_old_value verus_code! {
        use vstd::prelude::*;

        fn test_wrong() {
            let mut x: u64 = 9;
            let _ = std::mem::take(&mut x);
            assert(x == 9); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] mem_take_may_unwind verus_code! {
        use vstd::prelude::*;

        fn test<T: Default>(dest: &mut T) -> (res: T)
            no_unwind
        {
            std::mem::take(dest) // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
