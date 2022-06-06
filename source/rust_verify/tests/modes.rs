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
    #[test] verus_struct1 verus_code! {
        use crate::pervasive::modes::*;
        struct S {
            i: Ghost<bool>,
            j: bool,
        }
        fn test1(i: bool, j: bool) {
            let s = S { i: ghost(i), j };
        }
        fn test2(i: Ghost<bool>, j: bool) {
            let s = S { i, j };
        }
        fn test3(i: bool, j: Ghost<bool>) {
            let s: Ghost<S> = ghost(S { i: Ghost::new(i), j: *j });
            let jj: Ghost<bool> = ghost((*s).j);
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
    #[test] verus_struct_fails1 verus_code! {
        use crate::pervasive::modes::*;
        struct S {
            i: Ghost<bool>,
            j: bool,
        }
        fn test(i: bool, j: Ghost<bool>) {
            let s = S { i: ghost(i), j: *j };
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
    #[test] spec_struct_not_exec verus_code! {
        ghost struct Set<A> {
            pub dummy: A,
        }

        fn set_exec() {
            let a: Set<u64> = Set { dummy: 3 }; // FAILS
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] spec_enum_not_exec verus_code! {
        ghost struct E {
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

test_verify_one_file! {
    #[test] spec_let_decl_init_fail code! {
        #[spec]
        fn test1() -> u64 {
            let x: u64;
            x = 23;
            x
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] let_spec_pass code! {
        fn test1() {
            #[spec] let x: u64 = 2;
            assert(x == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] decl_init_let_spec_fail code! {
        fn test1() {
            #[spec] let x: u64;
            x = 2;
            x = 3;
            assert(false); // FAILS
        }
    } => Err(e) => assert_vir_error(e)
}

const FIELD_UPDATE: &str = code_str! {
    #[derive(PartialEq, Eq, Structural)]
    struct S {
        #[spec] a: u64,
        b: bool,
    }
};

test_verify_one_file! {
    #[test] test_field_update_fail FIELD_UPDATE.to_string() + code_str! {
        fn test() {
            let mut s = S { a: 5, b: false };
            #[spec] let b = true;
            s.b = b;
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] test_mut_ref_field_fail FIELD_UPDATE.to_string() + code_str! {
        fn muts_exec(a: &mut u64) {
            requires(*old(a) < 30);
            ensures(*a == *old(a) + 1);
            *a = *a + 1;
        }

        fn test() {
            let mut s = S { a: 5, b: false };
            muts_exec(&mut s.a);
        }
    } => Err(e) => assert_vir_error(e)
}

const PROOF_FN_COMMON: &str = code_str! {
    #[proof]
    struct Node {
        v: nat,
    }
};

test_verify_one_file! {
    #[test] test_proof_fn_call_fail PROOF_FN_COMMON.to_string() + code_str! {
        #[proof]
        fn lemma(#[proof] node: Node) {
            requires(node.v < 10);
            ensures(node.v * 2 < 20);
        }

        #[proof]
        fn other(#[proof] node: Node) {
            assume(node.v < 10);
            lemma(node);
            lemma(node);
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_associated_proof_fn_call_pass PROOF_FN_COMMON.to_string() + code_str! {
        impl Node {
            #[proof]
            fn lemma(&self) {
                requires(self.v < 10);
                ensures(self.v * 2 < 20);
            }

            #[proof]
            fn other(&self, other_node: Node) {
                assume(other_node.v < 10);
                other_node.lemma();
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_associated_proof_fn_call_fail_1 PROOF_FN_COMMON.to_string() + code_str! {
        impl Node {
            #[proof]
            fn lemma(#[proof] self) {
                requires(self.v < 10);
                ensures(self.v * 2 < 20);
            }

            #[proof]
            fn other(#[proof] self) {
                assume(other_node.v < 10);
                self.lemma();
                self.lemma();
            }
        }
    } => Err(_)
}

test_verify_one_file! {
    // TODO un-ignore when #124 is fixed
    #[test] #[ignore] test_associated_proof_fn_call_fail_2_regression_124 PROOF_FN_COMMON.to_string() + code_str! {
        struct Token {}

        impl Node {
            #[proof]
            fn lemma(self, #[proof] t: Token) {}

            #[proof]
            fn other(self, #[proof] t: Token) {
                self.lemma(t);
                self.lemma(t);
            }
        }
    } => Err(_)
}
