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
    } => Err(err) => assert_vir_error_msg(err, "cannot call prophecy-dependent function in prophecy-independent context")
}

test_verify_one_file! {
    #[test] proph_dep1 PROPH.to_string() + verus_code_str! {
        spec fn stuff(p: Prophecy<bool>) -> bool {
            p.value()
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call prophecy-dependent function in prophecy-independent context")
}

test_verify_one_file! {
    #[test] proph_dep2 PROPH.to_string() + verus_code_str! {
        proof fn stuff(p: Prophecy<bool>) {
            // This would be okay as long as we track how x is used
            let x = p.value();
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call prophecy-dependent function in prophecy-independent context")
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
    } => Err(err) => assert_vir_error_msg(err, "cannot call prophecy-dependent function in prophecy-independent context")
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
    } => Err(err) => assert_vir_error_msg(err, "cannot call prophecy-dependent function in prophecy-independent context")
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
    } => Err(err) => assert_vir_error_msg(err, "cannot call prophecy-dependent function in prophecy-independent context")
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
    } => Err(err) => assert_vir_error_msg(err, "cannot call prophecy-dependent function in prophecy-independent context")
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
    } => Err(err) => assert_vir_error_msg(err, "cannot call prophecy-dependent function in prophecy-independent context")
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
    } => Err(err) => assert_vir_error_msg(err, "cannot call prophecy-dependent function in prophecy-independent context")
}
