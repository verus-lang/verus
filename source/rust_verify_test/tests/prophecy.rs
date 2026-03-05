#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const PROPH: &str = verus_code_str! {
    #[verifier::external_body]
    #[verifier::reject_recursive_types_in_ground_variants(T)]
    pub tracked struct Prophecy<T> { _t: core::marker::PhantomData<T> }

    impl<T> Prophecy<T> {
        #[verifier::prophetic]
        pub uninterp spec fn value(&self) -> T;

        pub uninterp spec fn may_resolve(&self) -> bool;

        #[verifier::external_body]
        pub proof fn new() -> (tracked s: Self)
            ensures s.may_resolve()
        { unimplemented!() }

        #[verifier::external_body]
        pub proof fn resolve(tracked &mut self, value: T)
            requires old(self).may_resolve(),
            ensures !self.may_resolve(),
                self.value() == old(self).value(),
                self.value() == value,
        { unimplemented!() }
    }
};

test_verify_one_file! {
    #[test] once_flip PROPH.to_string() + verus_code_str! {
        use vstd::*;

        fn rand() -> bool { true }

        struct OnceFlip {
            value: Option<bool>,
            proph: Tracked<Prophecy<bool>>,
        }

        impl OnceFlip {
            #[verifier::prophetic]
            pub closed spec fn result(&self) -> bool {
                if self.proph@.may_resolve() {
                    self.proph@.value()
                } else {
                    self.value.unwrap()
                }
            }

            pub closed spec fn wf(&self) -> bool {
                self.value.is_some() <==> !self.proph@.may_resolve()
            }

            pub fn new() -> (s: Self)
                ensures s.wf(),
            {
                OnceFlip {
                    value: None,
                    proph: Tracked(Prophecy::new()),
                }
            }

            pub fn get_result(&mut self) -> (b: bool)
                requires
                    old(self).wf(),
                ensures
                    self.wf(),
                    self.result() == old(self).result(),
                    b == self.result(),
            {
                if self.value.is_none() {
                    let flip = rand();
                    self.value = Some(flip);
                    proof {
                        self.proph.borrow_mut().resolve(flip);
                    }
                }
                self.value.unwrap()
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] grandfather_paradox PROPH.to_string() + verus_code_str! {
        proof fn grandfather_paradox() {
            let tracked proph = Prophecy::<bool>::new();

            let luigi = proph.value();
            let waluigi = !luigi;

            proph.resolve(waluigi);

            assert(luigi == proph.value());
            assert(waluigi == proph.value());
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for argument to proof-mode function with tracked parameters")
}

test_verify_one_file! {
    #[test] proph_dep1 PROPH.to_string() + verus_code_str! {
        spec fn stuff(p: Prophecy<bool>) -> bool {
            p.value()
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
}

test_verify_one_file! {
    #[test] proph_dep2 PROPH.to_string() + verus_code_str! {
        proof fn stuff(p: Prophecy<bool>) {
            // This would be okay as long as we track how x is used
            let x = p.value();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_not_proph_impl_proph_err PROPH.to_string() + verus_code_str! {
        trait Tr {
            spec fn f(&self) -> bool;
        }

        impl Tr for Prophecy<bool> {
            #[verifier::prophetic]
            spec fn f(&self) -> bool { self.value() }
        }
    } => Err(err) => assert_vir_error_msg(err, "implementation of trait function cannot be marked prophetic if the trait function is not")
}

test_verify_one_file! {
    #[test] trait_and_impl_both_proph_ok PROPH.to_string() + verus_code_str! {
        trait Tr {
            #[verifier::prophetic]
            spec fn f(&self) -> bool;
        }

        impl Tr for Prophecy<bool> {
            #[verifier::prophetic]
            spec fn f(&self) -> bool { self.value() }
        }

        #[verifier::prophetic]
        spec fn general_fn<T: Tr>(t: &T) -> bool {
            t.f()
        }

        #[verifier::prophetic]
        spec fn specific_fn(t: &Prophecy<bool>) -> bool {
            t.f()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_and_impl_both_proph_err PROPH.to_string() + verus_code_str! {
        trait Tr {
            #[verifier::prophetic]
            spec fn f(&self) -> bool;
        }

        impl Tr for Prophecy<bool> {
            #[verifier::prophetic]
            spec fn f(&self) -> bool { self.value() }
        }

        spec fn specific_fn(t: &Prophecy<bool>) -> bool {
            t.f()
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
}

test_verify_one_file! {
    #[test] trait_proph_err PROPH.to_string() + verus_code_str! {
        trait Tr {
            #[verifier::prophetic]
            spec fn f(&self) -> bool;
        }

        spec fn general_fn<T: Tr>(t: &T) -> bool {
            t.f()
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
}

test_verify_one_file! {
    #[test] trait_proph_and_impl_not_proph_ok PROPH.to_string() + verus_code_str! {
        trait Tr {
            #[verifier::prophetic]
            spec fn f(&self) -> bool;
        }

        impl Tr for Prophecy<bool> {
            spec fn f(&self) -> bool { true }
        }

        spec fn specific_fn(t: &Prophecy<bool>) -> bool {
            t.f()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_proph_and_impl_not_proph_err PROPH.to_string() + verus_code_str! {
        trait Tr {
            #[verifier::prophetic]
            spec fn f(&self) -> bool;
        }

        impl Tr for Prophecy<bool> {
            spec fn f(&self) -> bool { self.value() }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
}

test_verify_one_file! {
    #[test] calls_requires_ensures PROPH.to_string() + verus_code_str! {
        fn freq(tracked t: Prophecy<bool>)
            requires t.value() == false,
        { }

        proof fn test_req(tracked t: Prophecy<bool>)
            requires t.may_resolve(),
        {
            let tracked mut t = t;

            let b = call_requires(freq, (t,));
            t.resolve(b);

            assert(false); // FAILS
        }

        fn fens(tracked t: Prophecy<bool>)
            ensures t.value() == false,
        { assume(false); }

        proof fn test_ens(tracked t: Prophecy<bool>)
            requires t.may_resolve(),
        {
            let tracked mut t = t;

            let b = call_ensures(freq, (t,), ());
            t.resolve(b);

            assert(false); // FAILS
        }

        fn test_req_closure(Tracked(t): Tracked<Prophecy<bool>>)
            requires t.may_resolve(),
        {
            let tracked mut t = t;

            let clos = |t: Prophecy<bool>|
                requires t.value() == false,
            { };

            proof {
                let b = call_requires(clos, (t,));
                t.resolve(b);

                assert(false); // FAILS
            }
        }

        fn test_ens_closure(tracked t: Prophecy<bool>)
            requires t.may_resolve(),
        {
            let tracked mut t = t;

            let clos = |t: Prophecy<bool>|
                ensures t.value() == false,
            { assume(false); };

            proof {
                let b = call_ensures(clos, (t,), ());
                t.resolve(b);

                assert(false); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] decreases_clause_proof_fn_cannot_be_prophetic verus_code! {
        #[verifier::prophetic]
        uninterp spec fn foo() -> int;

        proof fn test()
            decreases foo()
        {
            test();
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for 'decreases' clause")
}

test_verify_one_file! {
    #[test] decreases_clause_exec_fn_cannot_be_prophetic verus_code! {
        #[verifier::prophetic]
        uninterp spec fn foo() -> int;

        fn test()
            decreases foo()
        {
            test();
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for 'decreases' clause")
}

test_verify_one_file! {
    #[test] decreases_clause_loop_cannot_be_prophetic verus_code! {
        #[verifier::prophetic]
        uninterp spec fn foo() -> int;

        fn test()
        {
            loop
                decreases foo()
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for 'decreases' clause")
}

test_verify_one_file! {
    #[test] ghost_ctor_okay_in_spec_code verus_code! {
        #[verifier::prophetic]
        uninterp spec fn proph() -> bool;

        proof fn test_proof() {
            let x = proph();
            let y = Ghost(x); // ok since this is ghost
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ghost_ctor_fail_in_tracked_code verus_code! {
        #[verifier::prophetic]
        uninterp spec fn proph() -> bool;

        proof fn test_proof() {
            let x = proph();
            let tracked y = Ghost(x);
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for 'Ghost' wrapper")
}

test_verify_one_file! {
    #[test] ghost_ctor_fail verus_code! {
        #[verifier::prophetic]
        uninterp spec fn proph() -> bool;

        fn test_proof() {
            let ghost x = proph();
            let y = Ghost(x);
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for 'Ghost' wrapper")
}

test_verify_one_file! {
    #[test] prophetic_decl_fail verus_code! {
        #[verifier::prophetic]
        uninterp spec fn proph() -> bool;

        fn test_proof() {
            #[verifier::prophetic]
            let ghost x = false;
            let y = Ghost(x);
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for 'Ghost' wrapper")
}

test_verify_one_file! {
    #[test] prophetic_func_fail verus_code! {
        #[verifier::prophetic]
        uninterp spec fn proph() -> bool;

        proof fn bad(b: bool, tracked t: ()) { }

        fn test_proof() {
            #[verifier::prophetic]
            let ghost x = false;
            proof { bad(x, ()); }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for argument to proof-mode function with tracked parameters")
}

test_verify_one_file! {
    #[test] prophetic_func_fail_ret verus_code! {
        #[verifier::prophetic]
        uninterp spec fn proph() -> bool;

        tracked struct X { }
        proof fn bad(b: bool) -> (tracked t: X) { X{} }

        fn test_proof() {
            #[verifier::prophetic]
            let ghost x = false;
            proof { bad(x); }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for argument to proof-mode function with tracked parameters")
}

test_verify_one_file! {
    #[test] prophetic_func_fail2 verus_code! {
        #[verifier::prophetic]
        uninterp spec fn proph() -> bool;

        proof fn bad(b: bool, tracked t: ()) { }

        fn test_proof() {
            let ghost x = proph();
            proof { bad(x, ()); }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for argument to proof-mode function with tracked parameters")
}

test_verify_one_file! {
    #[test] proph_assign_to_proph_location_ok verus_code! {
        #[verifier::prophetic]
        uninterp spec fn proph() -> bool;

        proof fn test() {
            let mut x = proph();
            x = proph();
        }

        proof fn test2() {
            #[verifier::prophetic] let mut x = false;
            x = proph();
        }

        fn exec_test() {
            let ghost mut x = proph();
            proof { x = proph(); }
        }

        fn exec_test2() {
            #[verifier::prophetic] let ghost mut x = false;
            proof { x = proph(); }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] proph_assign_to_nonproph_location_bad verus_code! {
        #[verifier::prophetic]
        uninterp spec fn proph() -> bool;

        proof fn test() {
            let mut x = false;
            x = proph();
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for assignment to non-prophetic location")
}

test_verify_one_file! {
    #[test] proph_assign_to_nonproph_location_bad2 verus_code! {
        #[verifier::prophetic]
        uninterp spec fn proph() -> bool;

        fn test() {
            let ghost mut x = false;
            proof { x = proph(); }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for assignment to non-prophetic location")
}

test_verify_one_file! {
    #[test] prophecy_conditional_assign verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn test_if() {
            let mut x = false;
            if proph() {
                x = true;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "assignment to non-prophetic location cannot occur in prophecy-conditional context")
}

test_verify_one_file! {
    #[test] prophecy_conditional_assign_else verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn test_if() {
            let mut x = false;
            if proph() {
            } else {
                x = true;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "assignment to non-prophetic location cannot occur in prophecy-conditional context")
}

test_verify_one_file! {
    #[test] prophecy_conditional_call verus_code! {
        proof fn bad(b: bool, tracked t: ()) { }
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn test_if() {
            let mut x = false;
            if proph() {
                bad(true, ());
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "call to proof-mode function with tracked parameters cannot occur in prophecy-conditional context")
}

test_verify_one_file! {
    #[test] prophecy_conditional_return verus_code! {
        proof fn bad(b: bool, tracked t: ()) { }
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn test_if() {
            let mut x = false;
            if proph() {
                return;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "return cannot occur in prophecy-conditional context")
}

test_verify_one_file! {
    #[test] prophecy_conditional_loop verus_code! {
        proof fn bad(b: bool, tracked t: ()) { }
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn test_if() {
            let mut x = false;
            if proph() {
                loop { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "loop cannot occur in prophecy-conditional context")
}

test_verify_one_file! {
    #[test] loop_condition_prophetic verus_code! {
        proof fn bad(b: bool, tracked t: ()) { }
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn test_while() {
            while proph() {
            }
        }
    //} => Err(err) => assert_vir_error_msg(err, "loop cannot occur in prophecy-conditional context")
    } => Err(err) => assert_vir_error_msg(err, "cannot use while in proof or spec mode")
}

test_verify_one_file! {
    #[test] loop_break_prophetic verus_code! {
        proof fn bad(b: bool, tracked t: ()) { }
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn test_break() {
            loop
                decreases 0nat
            {
                if proph() { break; }
            }
        }
    //} => Err(err) => assert_vir_error_msg(err, "loop cannot occur in prophecy-conditional context")
    } => Err(err) => assert_vir_error_msg(err, "cannot use while in proof or spec mode")
}

test_verify_one_file! {
    #[test] loop_continue_prophetic verus_code! {
        proof fn bad(b: bool, tracked t: ()) { }
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn test_continue() {
            loop
                decreases 0nat
            {
                if proph() { continue; }
            }
        }
    //} => Err(err) => assert_vir_error_msg(err, "loop cannot occur in prophecy-conditional context")
    } => Err(err) => assert_vir_error_msg(err, "cannot use while in proof or spec mode")
}

test_verify_one_file! {
    #[test] prophecy_conditional_let_else verus_code! {
        proof fn bad(b: bool, tracked t: ()) { }
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        enum A {
            B, C
        }

        axiom fn never() -> (tracked t: !);

        proof fn test(a: A) {
            if proph() {
                let A::B = a else { never(); };
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: let-else in spec/proof")
}

test_verify_one_file! {
    #[test] let_else_prophetic_scrutinee verus_code! {
        proof fn bad(b: bool, tracked t: ()) { }
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        enum A {
            B, C
        }

        axiom fn never() -> (tracked t: !);

        fn test() {
            #[verifier::prophetic]
            let ghost a = A::B;

            proof {
                let A::B = a else { never(); };
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "let-else only work in exec mode")
}

test_verify_one_file! {
    #[test] conditional_short_circuit_and verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn sc() {
            let mut x = false;
            let y = proph() && ({ x = true; false });
        }
    } => Err(err) => assert_vir_error_msg(err, "assignment to non-prophetic location cannot occur in prophecy-conditional context")
}

test_verify_one_file! {
    #[test] conditional_short_circuit_or verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn sc() {
            let mut x = false;
            let y = proph() || ({ x = true; false });
        }
    } => Err(err) => assert_vir_error_msg(err, "assignment to non-prophetic location cannot occur in prophecy-conditional context")
}

test_verify_one_file! {
    #[test] conditional_short_circuit_implies verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn sc() {
            let mut x = false;
            let y = proph() ==> ({ x = true; false });
        }
    } => Err(err) => assert_vir_error_msg(err, "assignment to non-prophetic location cannot occur in prophecy-conditional context")
}

test_verify_one_file! {
    #[test] conditional_match0 verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn test() {
            let mut x = false;
            match proph() {
                false => { }
                true => { x = true; }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "assignment to non-prophetic location cannot occur in prophecy-conditional context")
}

test_verify_one_file! {
    #[test] conditional_match1 verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn test(b: bool) {
            let mut x = false;
            match b {
                false if proph() => { x = true }
                true => { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "assignment to non-prophetic location cannot occur in prophecy-conditional context")
}

test_verify_one_file! {
    #[test] conditional_match2 verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn test(b: bool) {
            let mut x = false;
            match b {
                false if proph() => { }
                false => { x = true; }
                true => { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "assignment to non-prophetic location cannot occur in prophecy-conditional context")
}

test_verify_one_file! {
    #[test] conditional_match3 verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;

        proof fn test(b: bool) {
            let mut x = false;
            match b {
                true => { x = true; }
                false if proph() => { }
                false => { }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lemma_call_ok verus_code! {
        proof fn easy_lemma(a: int, b: int)
            ensures a <= b ==> a <= b + 1
        { }

        proof fn lemma_add(a: int, b: int) -> (r: int)
            ensures r == a + b
        { a + b }

        #[verifier::prophetic] uninterp spec fn proph() -> bool;
        #[verifier::prophetic] uninterp spec fn proph_int() -> int;

        proof fn test(b: bool) {
            if proph() {
                easy_lemma(0, 1);
            }
            easy_lemma(proph_int(), proph_int());
            let x = lemma_add(proph_int(), proph_int());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lemma_call_propagate verus_code! {
        #[verifier::prophetic] uninterp spec fn proph_int() -> int;

        proof fn lemma_add(a: int, b: int) -> (r: int)
            ensures r == a + b
        { a + b }

        proof fn test(b: bool) {
            let mut x = false;
            if lemma_add(proph_int(), 0) == 0 {
                x = true;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "assignment to non-prophetic location cannot occur in prophecy-conditional context")
}

test_verify_one_file! {
    #[test] lemma_return_fail verus_code! {
        #[verifier::prophetic] uninterp spec fn proph_int() -> int;

        proof fn test(b: bool) -> int {
            proph_int()
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for return value")
}

test_verify_one_file! {
    #[test] lemma_return_fail2 verus_code! {
        #[verifier::prophetic] uninterp spec fn proph_int() -> int;

        proof fn test(b: bool) -> int {
            return proph_int();
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for return value")
}

test_verify_one_file! {
    #[test] conditional_expression_propagate verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;
        #[verifier::prophetic] uninterp spec fn proph_int() -> int;

        spec fn test(b: bool, x: int, y: int) -> int {
            if proph() { 0 } else { 1 }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
}

test_verify_one_file! {
    #[test] conditional_expression_propagate1 verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;
        #[verifier::prophetic] uninterp spec fn proph_int() -> int;

        spec fn test(b: bool, x: int, y: int) -> int {
            if b { proph_int() } else { x }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
}

test_verify_one_file! {
    #[test] conditional_expression_propagate2 verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;
        #[verifier::prophetic] uninterp spec fn proph_int() -> int;

        spec fn test(b: bool, x: int, y: int) -> int {
            if b { x } else { proph_int() }
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
}

test_verify_one_file! {
    #[test] decls_in_conditional verus_code! {
        #[verifier::prophetic] uninterp spec fn proph() -> bool;
        #[verifier::prophetic] uninterp spec fn proph_int() -> int;

        proof fn test() {
            let mut z = proph_int();
            if proph() {
                let mut x = 0;
                x = proph_int();
                z = x;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] use_prophetic_fn_as_fn_spec_closure verus_code! {
        use vstd::prelude::*;

        #[verifier::prophetic]
        spec fn f() -> int {
            5
        }

        spec fn test() -> int {
            let g = || f();
            g()
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
}

test_verify_one_file! {
    #[test] use_prophetic_fn_as_fn_spec verus_code! {
        use vstd::prelude::*;

        #[verifier::prophetic]
        spec fn f() -> int {
            5
        }

        spec fn test() -> int {
            let g = f; // may be supported in the future, meaning the same as "let g = || f();"
            g() // returning g() should fail, because the result of calling g() is a prophetic int, not an unrestricted int
        }
    //} => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for body of non-prophetic spec function")
    } => Err(err) => assert_vir_error_msg(err, "cannot use a function as a value unless it as mode 'exec'")
}
