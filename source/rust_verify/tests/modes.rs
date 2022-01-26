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

test_verify_one_file! {
    #[test] eq_mode code! {
        fn eq_mode(#[spec] i: int) {
            #[spec] let b: bool = i == 13;
        }
    } => Ok(_)
}

test_verify_one_file! {
    #[test] if_spec_cond code! {
        fn if_spec_cond(#[spec] i: int) -> u64 {
            let mut a: u64 = 2;
            if i == 3 {
                a = a + 1; // ERROR
            }
            a
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] if_spec_cond_proof code! {
        #[proof]
        fn if_spec_cond_proof(i: int) -> u64 {
            let mut a: u64 = 2;
            if i == 3 {
                a = a + 1;
            }
            a
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] regression_int_if code! {
        fn int_if() {
            #[spec] let a: int = 3;
            if a == 4 {
                assert(false);
            }; // TODO not require the semicolon here?
        }

        #[spec]
        fn int_if_2(a: int) -> int {
            if a == 2 {
                3
            } else if a == 3 {
                4
            } else {
                arbitrary()
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ret_mode code! {
        #[verifier(returns(spec))]
        fn ret_spec() -> int {
            ensures(|i: int| i == 3);
            #[spec] let a: int = 3;
            a
        }

        fn test_ret() {
            #[spec] let x = ret_spec();
            assert(x == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ret_mode_fail2 code! {
        #[verifier(returns(spec))]
        fn ret_spec() -> int {
            ensures(|i: int| i == 3);
            #[spec] let a: int = 3;
            a
        }

        fn test_ret() {
            let x = ret_spec();
            assert(x == 3);
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] ret_mode_fail_requires code! {
        fn f() {
            requires({while false {}; true});
        }
    } => Err(TestErr { has_vir_error: true, .. })
}
