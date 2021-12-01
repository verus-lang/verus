#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] struct1 code! {
        struct S {
            #[spec] i: bool,
            j: bool,
        }
        fn test1(i: bool, j: bool) {
            let s = S { i, j };
        }
        fn test2(#[spec] i: bool, j: bool) {
            let s = S { i, j };
        }
        fn test3(i: bool, #[spec] j: bool) {
            #[spec] let s = S { i, j };
            #[spec] let jj = s.j;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] struct_fails1 code! {
        struct S {
            #[spec] i: bool,
            j: bool,
        }
        fn test(i: bool, #[spec] j: bool) {
            let s = S { i, j };
        }
    } => Err(_) => ()
}

test_verify_one_file! {
    #[test] struct_fails1b code! {
        struct S {
            #[spec] i: bool,
            j: bool,
        }
        fn test(i: bool, #[spec] j: bool) {
            let s = S { j, i };
        }
    } => Err(_) => ()
}

test_verify_one_file! {
    #[test] struct_fails2 code! {
        struct S {
            #[spec] i: bool,
            j: bool,
        }
        fn test(i: bool, j: bool) {
            let s = S { i, j };
            let ii = s.i;
        }
    } => Err(_) => ()
}

test_verify_one_file! {
    #[test] struct_fails3 code! {
        struct S {
            #[spec] i: bool,
            j: bool,
        }
        fn test(i: bool, #[spec] j: bool) {
            #[spec] let s = S { i, j };
            let jj = s.j;
        }
    } => Err(_) => ()
}

test_verify_one_file! {
    #[test] tuple1 code! {
        fn test1(i: bool, j: bool) {
            let s = (i, j);
        }
        fn test3(i: bool, #[spec] j: bool) {
            #[spec] let s = (i, j);
            #[spec] let ii = s.0;
            #[spec] let jj = s.1;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tuple_fails1 code! {
        fn test(i: bool, #[spec] j: bool) {
            let s = (i, j);
        }
    } => Err(_) => ()
}

test_verify_one_file! {
    #[test] tuple_fails2 code! {
        fn test(i: bool, j: bool) {
            #[spec] let s = (i, j);
            let ii = s.0;
        }
    } => Err(_) => ()
}

test_verify_one_file! {
    #[test] tuple_fails3 code! {
        fn test(i: bool, #[spec] j: bool) {
            #[spec] let s = (i, j);
            let jj = s.0;
        }
    } => Err(_) => ()
}

test_verify_one_file! {
    #[test] spec_struct_not_exec code! {
        #[spec]
        struct Set<A> {
            pub dummy: A,
        }

        fn set_exec() {
            let a: Set<u64> = Set { dummy: 3 }; // FAILS
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] spec_enum_not_exec code! {
        #[spec]
        struct E {
            A,
            B,
        }

        fn set_exec() {
            let e: E = E::A; // FAILS
        }
    } => Err(_)
}
