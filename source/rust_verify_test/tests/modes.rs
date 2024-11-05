#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] struct1 code! {
        struct S {
            #[verifier::spec] i: bool,
            j: bool,
        }
        fn test1(i: bool, j: bool) {
            let s = S { i, j };
        }
        fn test2(#[verifier::spec] i: bool, j: bool) {
            let s = S { i, j };
        }
        fn test3(i: bool, #[verifier::spec] j: bool) {
            #[verifier::spec] let s = S { i, j };
            #[verifier::spec] let jj = s.j;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] verus_struct1 verus_code! {
        use vstd::modes::*;
        struct S {
            i: Ghost<bool>,
            j: bool,
        }
        fn test1(i: bool, j: bool) {
            let s = S { i: Ghost(i), j };
        }
        fn test2(i: Ghost<bool>, j: bool) {
            let s = S { i, j };
        }
        fn test3(i: bool, j: Ghost<bool>) {
            let s: Ghost<S> = Ghost(S { i: Ghost::new(i), j: j@ });
            let jj: Ghost<bool> = Ghost(s@.j);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] struct_fails1 code! {
        struct S {
            #[verifier::spec] i: bool,
            j: bool,
        }
        fn test(i: bool, #[verifier::spec] j: bool) {
            let s = S { i, j };
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] verus_struct_fails1 verus_code! {
        use vstd::modes::*;
        struct S {
            i: Ghost<bool>,
            j: bool,
        }
        fn test(i: bool, j: Ghost<bool>) {
            let s = S { i: Ghost(i), j: j@ };
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot perform operation with mode spec")
}

test_verify_one_file! {
    #[test] struct_fails1b code! {
        struct S {
            #[verifier::spec] i: bool,
            j: bool,
        }
        fn test(i: bool, #[verifier::spec] j: bool) {
            let s = S { j, i };
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] struct_fails2 code! {
        struct S {
            #[verifier::spec] i: bool,
            j: bool,
        }
        fn test(i: bool, j: bool) {
            let s = S { i, j };
            let ii = s.i;
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] struct_fails3 code! {
        struct S {
            #[verifier::spec] i: bool,
            j: bool,
        }
        fn test(i: bool, #[verifier::spec] j: bool) {
            #[verifier::spec] let s = S { i, j };
            let jj = s.j;
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] struct_fails4a verus_code! {
        struct S {
            ghost i: bool,
            j: bool,
        }
        fn test(s: Ghost<S>) -> bool {
            s@.j
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot perform operation with mode spec")
}

test_verify_one_file! {
    #[test] struct_fails4b verus_code! {
        struct S {
            ghost i: bool,
            j: bool,
        }
        fn test(s: &Ghost<S>) -> bool {
            s@.j
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot perform operation with mode spec")
}

test_verify_one_file! {
    #[test] struct_fails4c verus_code! {
        struct S {
            ghost i: bool,
            j: bool,
        }
        fn test(s: Ghost<&S>) -> bool {
            s@.j
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot perform operation with mode spec")
}

test_verify_one_file! {
    #[test] struct_fails5a verus_code! {
        struct S {
            ghost i: bool,
            j: bool,
        }
        impl S {
            spec fn get_j(self) -> bool {
                self.j
            }
        }
        fn test(s: Ghost<S>) -> bool {
            s@.get_j()
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `crate::S::get_j` with mode spec")
}

test_verify_one_file! {
    #[test] struct_fails5b verus_code! {
        struct S {
            ghost i: bool,
            j: bool,
        }
        impl S {
            spec fn get_j(self) -> bool {
                self.j
            }
        }
        fn test(s: &Ghost<S>) -> bool {
            s@.get_j()
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `crate::S::get_j` with mode spec")
}

test_verify_one_file! {
    #[test] struct_fails5c verus_code! {
        struct S {
            ghost i: bool,
            j: bool,
        }
        impl S {
            spec fn get_j(self) -> bool {
                self.j
            }
        }
        fn test(s: Ghost<&S>) -> bool {
            s@.get_j()
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `crate::S::get_j` with mode spec")
}

test_verify_one_file! {
    #[test] tuple1 code! {
        fn test1(i: bool, j: bool) {
            let s = (i, j);
        }
        fn test3(i: bool, #[verifier::spec] j: bool) {
            #[verifier::spec] let s = (i, j);
            #[verifier::spec] let ii = s.0;
            #[verifier::spec] let jj = s.1;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tuple_fails1 code! {
        fn test(i: bool, #[verifier::spec] j: bool) {
            let s = (i, j);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] tuple_fails2 code! {
        fn test(i: bool, j: bool) {
            #[verifier::spec] let s = (i, j);
            let ii = s.0;
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] tuple_fails3 code! {
        fn test(i: bool, #[verifier::spec] j: bool) {
            #[verifier::spec] let s = (i, j);
            let jj = s.0;
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] spec_struct_not_exec verus_code! {
        ghost struct Set<A> {
            pub dummy: A,
        }

        fn set_exec() {
            let a: Set<u64> = Set { dummy: 3 }; // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] spec_enum_not_exec verus_code! {
        ghost enum E {
            A,
            B,
        }

        fn set_exec() {
            let e: E = E::A; // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] eq_mode code! {
        fn eq_mode(#[verifier::spec] i: u128) {
            #[verifier::spec] let b: bool = i == 13;
        }
    } => Ok(_)
}

test_verify_one_file! {
    #[test] if_spec_cond code! {
        fn if_spec_cond(#[verifier::spec] i: u128) -> u64 {
            let mut a: u64 = 2;
            if i == 3 {
                a = a + 1; // ERROR
            }
            a
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot assign to exec variable from proof mode")
}

test_verify_one_file! {
    #[test] if_spec_cond_proof code! {
        #[verifier::proof]
        fn if_spec_cond_proof(i: u128) -> u64 {
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
        use vstd::pervasive::*;
        fn int_if() {
            #[verifier::spec] let a: u128 = 3;
            if a == 4 {
                assert(false);
            }; // TODO not require the semicolon here?
        }

        #[verifier::spec]
        fn int_if_2(a: u128) -> u128 {
            if a == 2 {
                3
            } else if a == 3 {
                4
            } else {
                vstd::pervasive::arbitrary()
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ret_mode code! {
        #[verifier::returns(spec)] /* vattr */
        fn ret_spec() -> u128 {
            ensures(|i: u128| i == 3);
            #[verifier::spec] let a: u128 = 3;
            a
        }

        fn test_ret() {
            #[verifier::spec] let x = ret_spec();
            builtin::assert_(x == 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ret_mode_fail2 code! {
        #[verifier::returns(spec)] /* vattr */
        fn ret_spec() -> u128 {
            ensures(|i: u128| i == 3);
            #[verifier::spec] let a: u128 = 3;
            a
        }

        fn test_ret() {
            let x = ret_spec();
            builtin::assert_(x == 3);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}

test_verify_one_file! {
    #[test] ret_mode_fail_requires code! {
        fn f() {
            requires({while false {}; true});
        }
    } => Err(err) => assert_vir_error_msg(err, "expected pure mathematical expression")
}

test_verify_one_file! {
    #[test] spec_let_decl_init_fail code! {
        #[verifier::spec]
        fn test1() -> u64 {
            let x: u64;
            x = 23;
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "delayed assignment to non-mut let not allowed for spec variables")
}

test_verify_one_file! {
    #[test] let_spec_pass code! {
        fn test1() {
            #[verifier::spec] let x: u64 = 2;
            builtin::assert_(x == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] decl_init_let_spec_fail code! {
        fn test1() {
            #[verifier::spec] let x: u64;
            x = 2;
            x = 3;
            builtin::assert_(false); // FAILS
        }
    } => Err(err) => assert_vir_error_msg(err, "delayed assignment to non-mut let not allowed for spec variables")
}

const FIELD_UPDATE: &str = code_str! {
    #[derive(PartialEq, Eq, Structural)]
    struct S {
        #[verifier::spec] a: u64,
        b: bool,
    }
};

test_verify_one_file! {
    #[test] test_field_update_fail FIELD_UPDATE.to_string() + code_str! {
        fn test() {
            let mut s = S { a: 5, b: false };
            #[verifier::spec] let b = true;
            s.b = b;
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
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
    } => Err(err) => assert_vir_error_msg(err, "expected mode exec, &mut argument has mode spec")
}

const PROOF_FN_COMMON: &str = code_str! {
    #[verifier::proof]
    struct Node {
        v: u32,
    }
};

test_verify_one_file! {
    #[test] test_mut_arg_fail1 code! {
        #[verifier::proof]
        fn f(#[verifier::proof] x: &mut bool, #[verifier::proof] b: bool) {
            requires(b);
            ensures(*x);

            *x = b;
        }

        fn g(#[verifier::proof] b: bool) {
            requires(b);

            #[verifier::spec] let tr = true;
            let mut e = false;
            if tr {
                f(&mut e, b); // should fail: exec <- proof out assign
            }
            builtin::assert_(e);
        }
    } => Err(err) => assert_vir_error_msg(err, "expected mode proof, &mut argument has mode exec")
}

test_verify_one_file! {
    #[test] test_mut_arg_fail2 verus_code! {
        proof fn f(x: &mut bool)
            ensures *x
        {
            *x = true;
        }

        fn g() {
            let mut e = false;
            proof {
                f(&mut e); // fails, exec <- ghost out assign
            }
            assert(e);
        }
    } => Err(err) => assert_vir_error_msg(err, "expected mode spec, &mut argument has mode proof")
}

test_verify_one_file! {
    #[test] test_mut_arg_fail3 verus_code! {
        struct S {
            ghost g: bool,
        }

        fn f(x: &mut bool) {}

        fn g(e: S) {
            let mut e = e;
            f(&mut e.g); // fails, exec <- ghost assign
        }
    } => Err(err) => assert_vir_error_msg(err, "expected mode exec, &mut argument has mode spec")
}

test_verify_one_file! {
    #[test] test_mut_arg_fail4 verus_code! {
        struct S {
            e: bool,
        }

        proof fn f(tracked x: &mut bool) {}

        proof fn g(g: S) {
            let mut g = g;
            f(&mut g.e); // fails, tracked <- ghost assign
        }
    } => Err(err) => assert_vir_error_msg(err, "expected mode proof, &mut argument has mode spec")
}

test_verify_one_file! {
    #[test] test_mut_arg_fail5 verus_code! {
        struct S {
            e: bool,
        }

        proof fn f(x: &mut bool) {}

        fn g(e: S) {
            let mut e = e;
            proof {
                f(&mut e.e); // fails, exec <- ghost out assign
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expected mode spec, &mut argument has mode proof")
}

test_verify_one_file! {
    #[test] test_mut_arg_fail6 verus_code! {
        struct S {
            tracked t: bool,
        }

        proof fn f(x: &mut bool) {}

        fn g(e: S) {
            let mut e = e;
            proof {
                f(&mut e.t); // fails, tracked <- ghost out assign
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expected mode spec, &mut argument has mode proof")
}

test_verify_one_file! {
    // TODO (erasure-todo)
    // This needs to be ported to verus_code
    #[ignore] #[test] test_proof_fn_call_fail PROOF_FN_COMMON.to_string() + code_str! {
        #[verifier::proof]
        fn lemma(#[verifier::proof] node: Node) {
            requires(node.v < 10);
            ensures(node.v * 2 < 20);
        }

        #[verifier::proof]
        fn other(#[verifier::proof] node: Node) {
            builtin::assume_(node.v < 10);
            lemma(node);
            lemma(node);
        }
    } => Err(err) => assert_rust_error_msg(err, "error[E0382]: use of moved value: `node`")
}

test_verify_one_file! {
    #[test] test_associated_proof_fn_call_pass PROOF_FN_COMMON.to_string() + code_str! {
        impl Node {
            #[verifier::proof]
            fn lemma(&self) {
                requires(self.v < 10);
                ensures(self.v * 2 < 20);
            }

            #[verifier::proof]
            fn other(&self, other_node: Node) {
                builtin::assume_(other_node.v < 10);
                other_node.lemma();
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_associated_proof_fn_call_fail_1 PROOF_FN_COMMON.to_string() + verus_code_str! {
        impl Node {
            proof fn lemma(tracked self) {
                requires(self.v < 10);
                ensures(self.v * 2 < 20);
            }

            proof fn other(tracked self) {
                assume(other_node.v < 10);
                self.lemma();
                self.lemma();
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot find value `other_node`")
}

test_verify_one_file! {
    #[test] test_associated_proof_fn_call_fail_2_regression_124 PROOF_FN_COMMON.to_string() + verus_code_str! {
        struct Token {}

        impl Node {
            proof fn lemma(self, tracked t: Token) {}

            proof fn other(self, tracked t: Token) {
                self.lemma(t);
                self.lemma(t);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value: `t`")
}

test_verify_one_file! {
    #[test] assign_from_proof code! {
        fn myfun(#[verifier::spec] a: bool) -> bool {
            let mut b = false;
            if a {
                b = true;
            }
            b
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot assign to exec variable from proof mode")
}

test_verify_one_file! {
    // TODO(main_new) this should be passing; the issue may be due to the changes in the lifetime checker
    #[ignore] #[test] tracked_double_deref code! {
        use vstd::modes::*;

        fn foo<V>(x: Tracked<V>) {
            let y = &x;

            builtin::assert_(equal((*y).view(), x.view()));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ghost_wrapper_assign_fail1 verus_code! {
        use vstd::modes::*;

        fn f() {
            let g: Ghost<bool> = Ghost(true);
            proof {
                let tracked t: bool = g@; // fails: tracked <- ghost assign
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] ghost_wrapper_assign_fail2 verus_code! {
        use vstd::modes::*;

        fn f() {
            let g: Ghost<bool> = Ghost(true);
            let e: bool = g@; // fails: exec <- ghost assign
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot perform operation with mode spec")
}

test_verify_one_file! {
    #[test] ghost_wrapper_assign_fail3 verus_code! {
        use vstd::modes::*;

        fn f() {
            let mut e: bool = false;
            proof {
                e = true; // fails: exec assign from proof mode
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot assign to exec variable from proof mode")
}

test_verify_one_file! {
    #[test] ghost_wrapper_assign_fail4 verus_code! {
        use vstd::modes::*;

        fn f(t: Tracked<bool>) {
            let g: Ghost<bool> = Ghost(true);
            let mut t = t;
            proof {
                t@ = g@; // fails: tracked <- ghost assign
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] ghost_wrapper_call_fail1 verus_code! {
        use vstd::modes::*;

        fn f(x: bool) {
        }

        fn g(g: Ghost<bool>) {
            f(g@); // fails, exec <- ghost assign
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot perform operation with mode spec")
}

test_verify_one_file! {
    #[test] ghost_wrapper_call_fail2 verus_code! {
        use vstd::modes::*;

        fn f(x: bool) {
        }

        fn g(t: Tracked<bool>) {
            f(t@); // fails, exec <- tracked assign
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot perform operation with mode spec")
}

test_verify_one_file! {
    #[test] ghost_wrapper_call_fail3 verus_code! {
        use vstd::modes::*;

        proof fn f(tracked x: bool) {
        }

        fn g(g: Ghost<bool>) {
            proof {
                f(g@); // fails, tracked <- ghost assign
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] ghost_wrapper_call_mut_fail1 verus_code! {
        use vstd::modes::*;

        fn f(x: &mut bool) {
        }

        fn g(g: Ghost<bool>) {
            let mut g = g;
            f(g.borrow_mut()); // fails, exec <- ghost assign
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot perform operation with mode proof")
}

test_verify_one_file! {
    #[test] ghost_wrapper_call_mut_fail2 verus_code! {
        use vstd::modes::*;

        fn f(x: &mut bool) {
        }

        fn g(t: Tracked<bool>) {
            let mut t = t;
            f(t.borrow_mut()); // fails, exec <- tracked assign
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot perform operation with mode proof")
}

test_verify_one_file! {
    #[test] ghost_wrapper_call_mut_fail3 verus_code! {
        use vstd::modes::*;

        proof fn f(tracked x: &mut bool) {
        }

        fn g(g: Ghost<bool>) {
            let mut g = g;
            proof {
                f(g.borrow_mut()); // fails, tracked <- ghost assign
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expected mode proof, &mut argument has mode spec")
}

test_verify_one_file! {
    #[test] ghost_wrapper_call_mut_fail4 verus_code! {
        use vstd::modes::*;

        proof fn f(x: &mut bool) {
        }

        fn g(t: Tracked<bool>) {
            let mut t = t;
            proof {
                f(t.borrow_mut()); // fails, tracked <- ghost out assign
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expected mode spec, &mut argument has mode proof")
}

test_verify_one_file! {
    #[test] ghost_wrapper_assign_struct_fail1 verus_code! {
        use vstd::modes::*;
        struct S {
            e: bool,
        }
        fn f(g: Ghost<S>) {
            proof {
                let tracked t: bool = g@.e; // fails: tracked <- ghost assign
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] ghost_wrapper_assign_struct_fail2 verus_code! {
        use vstd::modes::*;
        struct S {
            e: bool,
        }
        fn f(g: Ghost<S>) {
            let e: bool = g@.e; // fails: exec <- ghost assign
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot perform operation with mode spec")
}

test_verify_one_file! {
    #[test] ghost_wrapper_assign_struct_fail3 verus_code! {
        use vstd::modes::*;
        struct S {
            e: bool,
        }
        fn f(t: Tracked<S>) {
            let g: Ghost<bool> = Ghost(true);
            let mut t = t;
            proof {
                t@.e = g@; // fails: tracked <- ghost assign
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

const TRACKED_TYP_PARAMS_COMMON: &str = verus_code_str! {
    use vstd::modes::*;
    tracked struct Tok {
        v: nat,
    }

    tracked struct B<T> {
        t: T,
    }
};

test_verify_one_file! {
    #[test] tracked_ghost_typ_params_make verus_code! {
        use vstd::modes::*;

        tracked struct Tok {
            ghost v: nat,
        }

        struct B<T> {
            t: T,
        }

        proof fn make_tracked_proof() {
            let tracked t2: B<Tok> = B { t: Tok { v: 12 } };
        }

        fn make_tracked_exec() {
            let t: Tracked<Tok> = Tracked({
                let v = 12nat;
                Tok { v: v }
            });
            let b: B<Tracked<Tok>> = B { t: t };
        }

        // This isn't currently possible
        // proof fn make_ghost_proof() {
        //     let tracked t2: B<Ghost<Tok>> = Tracked(B { t: Ghost::new(Tok { v: 12 }) });
        // }

        fn make_ghost_exec() {
            let g: Ghost<Tok> = Ghost(Tok { v: 12nat });
            let b: B<Ghost<Tok>> = B { t: g };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tracked_tracked_typ_params_misc TRACKED_TYP_PARAMS_COMMON.to_owned() + verus_code_str! {
        proof fn identity(tracked b: B<Tracked<Tok>>) -> (tracked out: B<Tracked<Tok>>) {
            b
        }

        fn foo_exec(tok: Tracked<Tok>) -> Tracked<Tok> {
            let b: Tracked<B<Tracked<Tok>>> = Tracked(B { t: tok });
            let t = Tracked({
                let tracked B { t } = b.get();
                t.get()
            });
            t
        }

        proof fn foo_proof(tracked tok: Tracked<Tok>) -> (tracked out: B<Tracked<Tok>>) {
            let tracked b1: B<Tracked<Tok>> = B { t: tok };
            let tracked b2 = identity(b1);
            b2
        }

        fn caller(tok: Tracked<Tok>) -> Tracked<B<Tracked<Tok>>> {
            let b: Tracked<B<Tracked<Tok>>> = Tracked(B { t: tok });
            let b1 = Tracked({
                identity(b.get())
            });
            b1
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] tracked_ghost_typ_params_misc TRACKED_TYP_PARAMS_COMMON.to_owned() + verus_code_str! {
        use vstd::modes::*;

        proof fn identity(tracked b: B<Ghost<Tok>>) -> (tracked out: B<Ghost<Tok>>) {
            b
        }

        fn foo_exec() -> Ghost<Tok> {
            let g: Ghost<Tok> = Ghost(Tok { v: 12nat });
            // The exec->tracked coercion may be removed
            let b: Tracked<B<Ghost<Tok>>> = Tracked(B { t: g });
            let t = Ghost({
                let tracked B { t } = b.get();
                t@
            });
            t
        }

        proof fn foo_proof(tracked tok: Ghost<Tok>) -> tracked Ghost<Tok> {
            let tracked b: B<Ghost<Tok>> = B { t: tok };
            let tracked t = {
                let tracked B { t } = b;
                t
            };
            t
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_or_pattern_mode_inconsistent verus_code! {
        enum Foo {
            Bar(#[verifier::spec] u64),
            Qux(#[verifier::proof] u64),
        }

        proof fn blah(foo: Foo) {
            #[verifier::proof] let (Foo::Bar(x) | Foo::Qux(x)) = foo;
        }
    } => Err(err) => assert_vir_error_msg(err, "variable `x` has different modes across alternatives")
}

test_verify_one_file! {
    #[test] test_or_pattern_mode_inconsistent2 verus_code! {
        enum Foo {
            Bar(#[verifier::spec] u64, #[verifier::proof] u64),
        }

        proof fn blah(foo: Foo) {
            #[verifier::proof] let (Foo::Bar(x, y) | Foo::Bar(y, x)) = foo;
        }
    } => Err(err) => assert_vir_error_msg(err, "variable `x` has different modes across alternatives")
}

test_verify_one_file! {
    #[test] test_struct_pattern_fields_out_of_order_fail_issue_348 verus_code! {
        tracked struct Foo {
            ghost a: u64,
            tracked b: u64,
        }

        proof fn some_call(#[verifier::proof] y: u64) { }

        proof fn t() {
            let tracked foo = Foo { a: 5, b: 6 };
            let tracked Foo { b, a } = foo;

            // Variable 'a' has the mode of field 'a' (that is, spec)
            // some_call requires 'proof'
            // So this should fail
            some_call(a);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] test_struct_pattern_fields_out_of_order_success_issue_348 verus_code! {
        struct X { }

        struct Foo {
            #[verifier::spec] a: u64,
            #[verifier::proof] b: X,
        }

        proof fn some_call(#[verifier::proof] y: X) { }

        proof fn t(#[verifier::proof] x: X) {
            #[verifier::proof] let foo = Foo { a: 5, b: x };
            #[verifier::proof] let Foo { b, a } = foo;

            // This should succeed, 'b' has mode 'proof'
            some_call(b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_struct_pattern_fields_numeric_out_of_order_fail verus_code! {
        tracked struct Foo(ghost u64, tracked u64);

        proof fn some_call(tracked y: u64) { }

        proof fn t() {
            let tracked foo = Foo(5, 6);
            let tracked Foo { 1: b, 0: a } = foo;

            // Variable 'a' has the mode of field '0' (that is, spec)
            // some_call requires 'proof'
            // So this should fail
            some_call(a);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] test_use_exec_var_in_forall verus_code! {
        spec fn some_fn(j: int) -> bool {
            true
        }

        fn test() {
            let i = 5;

            assert forall |j| some_fn(j) by {
                if j < i {
                    assert(some_fn(j));
                } else {
                    assert(some_fn(j));
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] initialize_proof_var_in_exec verus_code! {
        fn myfun() {
            let tracked b = false;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] initialize_spec_var_in_exec verus_code! {
        fn myfun() {
            let ghost b = false;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assign_proof_var_in_exec verus_code! {
        fn myfun() {
            let tracked b;
            b = false;
        }
    } => Err(err) => assert_vir_error_msg(err, "exec code cannot mutate non-exec variable")
}

test_verify_one_file! {
    #[test] assign_spec_var_in_exec verus_code! {
        fn myfun() {
            let ghost b;
            b = false;
        }
    } => Err(err) => assert_vir_error_msg(err, "exec code cannot mutate non-exec variable")
}

test_verify_one_file! {
    #[test] declare_proof_var_in_exec verus_code! {
        fn myfun() {
            let tracked b;
            proof {
                b = false;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] declare_spec_var_in_exec verus_code! {
        fn myfun() {
            // note: has to be 'mut' because we currently don't support
            // late-initialized non-mut spec variables
            let ghost mut b;
            proof {
                b = false;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ghost_decl_enters_ghost_code verus_code! {
        fn test(g: Ghost<int>) {
            let Ghost(i) = g;
            let ghost mut j = i + 1000000000000000000000000000000000000000000000000000000000000000;
            assert(j > g@);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] temp_vars_are_hygienic1 verus_code! {
        fn test(g: Ghost<int>) {
            let ghost j = g@ + 1;
            let ghost k = verus_tmp; // error
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot find value `verus_tmp`")
}

test_verify_one_file! {
    #[test] temp_vars_are_hygienic2 verus_code! {
        fn test(g: Ghost<int>) {
            let Ghost(j) = g;
            let ghost k = verus_tmp_j; // error
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot find value `verus_tmp_j`")
}

test_verify_one_file! {
    #[test] fn_param_wrappers verus_code! {
        struct S(int);

        fn test1(Ghost(g): Ghost<int>, Tracked(t): Tracked<S>)
            requires
                g > 100,
                t.0 > 200,
        {
            assert(g >= 100);
            assert(t.0 >= 200);
        }

        fn test2(Ghost(g): Ghost<int>, Tracked(t): Tracked<S>)
            requires
                g > 100,
                t.0 > 200,
        {
            test1(Ghost(g), Tracked(t));
        }

        fn test3(g: Ghost<int>, t: Tracked<S>)
            requires
                g@ > 100,
                t@.0 > 200,
        {
            test1(g, t);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fn_param_wrappers_mut verus_code! {
        struct S(int);

        fn test1(Ghost(g): Ghost<&mut int>, Tracked(t): Tracked<&mut S>)
            requires
                *old(g) > 100,
                old(t).0 > 100,
            ensures
                *g == *old(g) + *old(g),
                *g > 200,
                *t == *old(t),
        {
            assert(*g >= 100);
            proof {
                *g = *g * 2;
            }
        }

        fn test2(Tracked(t1): Tracked<S>) {
            assume(t1.0 > 100);
            let tracked mut t2 = t1;
            let ghost mut i = 1000;
            assert(i == 1000);
            test1(Ghost(&mut i), Tracked(&mut t2));
            assert(i == 2000);
            assert(t2.0 > 100);
        }

        fn test3(Tracked(t1): Tracked<S>) {
            assume(t1.0 > 100);
            let tracked mut t2 = t1;
            let ghost mut i = 1000;
            assert(i == 1000);
            test1(Ghost(&mut i), Tracked(&mut t2));
            assert(i == 2000);
            assert(t2.0 > 101); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] fn_param_wrappers_mut_fail1 verus_code! {
        struct S(int);

        fn test1(Tracked(g): Ghost<&mut int>, Tracked(t): Tracked<&mut S>)
        {
        }
    } => Err(err) => assert_rust_error_msg(err, "no method named `get` found for struct `builtin::Ghost` in the current scope")
}

test_verify_one_file! {
    #[test] fn_param_wrappers_mut_fail2 verus_code! {
        struct S(int);

        fn test1(Ghost(g): Ghost<&mut int>, Ghost(t): Tracked<&mut S>)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "ill-formed unwrap_parameter header")
}

test_verify_one_file! {
    #[test] fn_param_wrappers_mut_fail3 verus_code! {
        struct S(int);

        fn test1(Ghost(g): Ghost<&mut int>, Tracked(t): Tracked<&mut S>)
        {
        }

        fn test2(Tracked(t1): Tracked<S>) {
            let tracked mut t2 = t1;
            let ghost mut i = 1000;
            test1(Tracked(&mut i), Tracked(&mut t2));
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        let error = &err.errors[0];
        assert_eq!(error.message, "mismatched types");
        assert!(error.spans[0].label == Some("expected `Ghost<&mut int>`, found `Tracked<&mut _>`".to_string()));
    }
}

test_verify_one_file! {
    #[test] fn_param_wrappers_mut_well_formed1 verus_code! {
        struct S(int);

        fn test1(tmp_g: Ghost<&mut int>) {
            #[verus::internal(header_unwrap_parameter)] let g;
            #[verifier(proof_block)] { g = tmp_g.view() };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fn_param_wrappers_mut_ill_formed1 verus_code! {
        struct S(int);

        fn test1(tmp_g: Ghost<&mut int>, tmp_h: Ghost<&mut int>) {
            #[verus::internal(header_unwrap_parameter)] let g;
            #[verifier(proof_block)] { g = tmp_g.view() };
            // fails to unwrap h
        }
    } => Err(err) => assert_vir_error_msg(err, "must be unwrapped")
}

test_verify_one_file! {
    #[test] fn_param_wrappers_mut_ill_formed2 verus_code! {
        struct S(int);

        fn test1(tmp_g: Ghost<&mut int>, tmp_h: Ghost<&mut int>) {
            #[verus::internal(header_unwrap_parameter)] let g;
            #[verifier(proof_block)] { g = tmp_g.view() };
            #[verus::internal(header_unwrap_parameter)] let h;
            #[verifier(proof_block)] { h = g }; // should be tmp_h.view()
        }
    } => Err(err) => assert_vir_error_msg(err, "ill-formed unwrap_parameter header")
}

test_verify_one_file! {
    #[test] fn_param_wrappers_mut_wrong_mode1 verus_code! {
        struct S(int);

        fn test1(Ghost(g): Ghost<&mut int>, Tracked(t): Tracked<&mut S>)
        {
        }

        fn test2(Tracked(t1): Tracked<S>) {
            let ghost mut t2 = t1;
            let ghost mut i = 1000;
            test1(Ghost(&mut i), Tracked(&mut t2));
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] fn_param_wrappers_mut_wrong_mode2 verus_code! {
        struct S(int);

        fn test1(Ghost(g): Ghost<&mut S>)
        {
        }

        fn test2(Tracked(t1): Tracked<S>) {
            let tracked mut t2 = t1;
            test1(Ghost(&mut t2));
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot write to argument with mode exec")
}

test_verify_one_file! {
    #[test] ghost_tracked_new1 verus_code! {
        struct S {}
        fn test1(t: Tracked<S>) {
            let Tracked(x) = t;
            proof {
                let g: Ghost<int> = Ghost(5);
                let tracked z: Tracked<S> = Tracked(x);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ghost_tracked_new_fail1 verus_code! {
        fn test1() {
            let g = Ghost::new(true);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot perform operation with mode spec")
}

test_verify_one_file! {
    #[test] ghost_tracked_new_fail2 verus_code! {
        struct S {}
        fn test1(t: Tracked<S>) {
            let Tracked(x) = t;
            let t = Tracked::new(x);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot perform operation with mode proof")
}

test_verify_one_file! {
    #[test] ghost_tracked_new_fail3 verus_code! {
        struct S {}
        fn test1(t: Tracked<S>) {
            let Tracked(x) = t;
            proof {
                let tracked z: Tracked<S> = Tracked(x);
                let tracked z: Tracked<S> = Tracked(x);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value: `x`")
}

test_verify_one_file! {
    #[test] ghost_tracked_new_fail4 verus_code! {
        struct S {}
        fn test1(t: Tracked<S>) {
            let Tracked(x) = t;
            proof {
                let tracked z: Tracked<S> = Tracked(x);
            }
            let tracked y = x;
        }
    } => Err(err) => assert_vir_error_msg(err, "use of moved value: `x`")
}

test_verify_one_file! {
    #[test] ghost_tracked_new_fail5 verus_code! {
        struct S {}
        fn test1(t: Tracked<S>) {
            let Tracked(x) = t;
            proof {
                let g = x; // ghost
                let tracked z: Tracked<S> = Tracked(g);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] let_tracked_wildcard_in_exec verus_code! {
        struct X { }

        proof fn stuff() -> (tracked res: X)
            requires false,
        {
            X { }
        }

        fn test_r() {
            let tracked _ = stuff(); // FAILS
        }
    } => Err(err) => {
        dbg!(&err);
        assert_one_fails(err)
    }
}

test_verify_one_file! {
    #[test] destructure_tracked_shorthand verus_code! {
        struct Y { }
        struct Z { }

        tracked struct X {
            tracked y: Y,
            tracked z: Z
        }

        proof fn test2(tracked y: Y, z: Z) { }

        fn test(Tracked(x): Tracked<X>) {
            let tracked X { y, z } = x;
            proof {
                test2(y, z);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] destructure_ghost_shorthand verus_code! {
        struct Y { }
        struct Z { }

        struct X {
            y: Y,
            z: Z
        }

        proof fn test2(tracked y: Y, tracked z: Z) { }

        fn test(Tracked(x): Tracked<X>) {
            let ghost X { y, z } = x;
            proof {
                test2(y, z);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] new_ghost_wrapper_is_tracked verus_code! {
        proof fn test1() -> (tracked t: Ghost<bool>) {
            Ghost(true)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ghost_wrapper_is_copyable verus_code! {
        struct NonCopy { a: u64 }

        fn use_g(g: Ghost<NonCopy>) {
        }

        fn with_g(g: Ghost<NonCopy>) {
            use_g(g);
            use_g(g);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] old_in_exec_mode_issue922 verus_code! {
        fn stuff(x: &mut u8) {
            let y = *old(x);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use `old` in exec-code")
}

test_verify_one_file! {
    #[test] match_tracked_ghost_field verus_code! {
        struct Y;
        struct Z;

        tracked struct X {
            tracked y: Y,
            ghost z: Z
        }

        fn test(Tracked(x): Tracked<X>) {
            let tracked X { y: yy, z: zz } = x;
            assert(zz == zz);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] empty_tuple_ghost verus_code! {
        spec fn f() -> () { () }

        fn test() {
            let x = Ghost(());
            let y = Tracked(());
            assert(f() == ());
            assert(x@ == ());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] old_is_spec_issue963 verus_code! {
        struct X { }

        proof fn g(tracked m: &X) {

        }

        proof fn f(tracked m: &mut X) {
            g(&*old(m));
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}
