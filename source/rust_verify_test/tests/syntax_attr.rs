#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] verus_verify_basic_while  code! {
        #[verus_spec]
        fn test1() {
            let mut i = 0;
            #[verus_spec(
                invariant
                    i <= 10
            )]
            while i < 10
            {
                i = i + 1;
            }
            proof!{assert(i == 10);}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] verus_verify_basic_loop code! {
        #[verus_spec]
        fn test1() {
            let mut i = 0;
            let mut ret = 0;
            #[verus_spec(
                invariant i <= 10,
                invariant_except_break i <= 9,
                ensures i == 10, ret == 10
            )]
            loop
            {
                i = i + 1;
                if (i == 10) {
                    ret = i;
                    break;
                }
            }
            proof!{assert(ret == 10);}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] verus_verify_basic_for_loop_verus_spec  code! {
        use vstd::prelude::*;
        #[verus_spec(v =>
            ensures
                v.len() == n,
                forall|i: int| 0 <= i < n ==> v[i] == i
        )]
        fn test_for_loop(n: u32) -> Vec<u32>
        {
            let mut v: Vec<u32> = Vec::new();
            #[verus_spec(
                invariant
                    v@ =~= Seq::new(i as nat, |k| k as u32),
            )]
            for i in 0..n
            {
                v.push(i);
            }
            v
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] verus_verify_for_loop_verus_spec_naming_iter  code! {
        use vstd::prelude::*;
        #[verus_spec(v =>
            ensures
                v.len() == n,
                forall|i: int| 0 <= i < n ==> v[i] == 0
        )]
        fn test(n: u32) -> Vec<u32>
        {
            let mut v: Vec<u32> = Vec::new();
            #[verus_spec(iter =>
                invariant
                    v@ =~= Seq::new(iter.cur as nat, |k| 0u32),
            )]
            for _ in 0..n
            {
                v.push(0);
            }
            v
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] verus_verify_basic_while_fail1 code! {
        #[verus_spec]
        fn test1() {
            let mut i = 0;
            while i < 10 {
                i = i + 1;
            }
            proof!{assert(i == 10);} // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] basic_while_false_invariant code! {
        #[verus_verify]
        fn test1() {
            let mut i = 0;
            #[verus_spec(
                invariant
                    i <= 10, false
            )]
            while i < 10 {
                i = i + 1;
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "invariant not satisfied before loop")
}

test_verify_one_file! {
    #[test] verus_verify_invariant_on_func code! {
        #[verus_spec(
            invariant true
        )]
        fn test1() {}
    } => Err(err) => assert_any_vir_error_msg(err, "unexpected token")
}

test_verify_one_file! {
    #[test] test_use_macro_attributes code!{
        struct Abc<T> {
            t: T,
        }

        trait SomeTrait {
            #[verus_spec(ret =>
                requires true
                ensures ret
            )]
            fn f(&self) -> bool;
        }

        impl<S> Abc<S> {
            fn foo(&self)
                where S: SomeTrait
            {
                let ret = self.t.f();
                proof!{assert(ret);}
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_bad_macro_attributes_in_trait code!{
        trait SomeTrait {
            #[verus_spec(
                ensures
                    true
            )]
            type T;
        }
    } => Err(err) => assert_any_vir_error_msg(err, "Misuse of #[verus_spec]")
}

test_verify_one_file! {
    #[test] test_no_verus_verify_attributes_in_trait_impl code!{
        struct Abc<T> {
            t: T,
        }

        #[verus_verify]
        trait SomeTrait {
            #[verus_spec(requires true)]
            fn f(&self) -> bool;
        }

        impl<S> Abc<S> {
            fn foo(&self)
                where S: SomeTrait
            {
                let ret = self.t.f();
                proof!{assert(ret);}
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "assertion failed")
}

test_verify_one_file! {
    #[test] test_failed_ensures_macro_attributes code!{
        trait SomeTrait {
            #[verus_spec(ret =>
                requires true
                ensures true, ret
            )]
            fn f(&self) -> bool;
        }

        impl SomeTrait for bool {
            fn f(&self) -> bool {
                *self
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "postcondition not satisfied")
}

test_verify_one_file! {
    #[test] test_default_fn_use_macro_attributes code!{
        struct Abc<T> {
            t: T,
        }

        #[verus_verify]
        trait SomeTrait {
            #[verus_spec(ret =>
                requires true
                ensures ret
            )]
            fn f(&self) -> bool {
                true
            }
        }

        #[verus_verify]
        impl<S> Abc<S> {
            fn foo(&self)
                where S: SomeTrait
            {
                let ret = self.t.f();
                proof!{assert(ret);}
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_default_failed_fn_use_macro_attributes code!{
        struct Abc<T> {
            t: T,
        }

        #[verus_verify]
        trait SomeTrait {
            #[verus_spec(ret =>
                requires true
                ensures ret, !ret
            )]
            fn f(&self) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "postcondition not satisfied")
}

test_verify_one_file! {
    #[test] test_external_body code!{
        #[verus_verify(external_body)]
        #[verus_spec(ret =>
            requires true
            ensures ret
        )]
        fn f() -> bool {
            false
        }

        fn g() {
            let r = f();
            proof!{assert(r);}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_with code!{
        #[verus_spec(ret =>
            with
                Tracked(y): Tracked<&mut u32>,
                Ghost(w): Ghost<u32>,
                -> z: Ghost<u32>
            requires
                x < 100,
                *old(y) < 100,
            ensures
                *y == x,
                ret.0 == x,
                ret.1@ == x,
        )]
        fn test_mut_tracked(x: u32) -> u32 {
            proof!{
                *y = x;
            }
            #[verus_io(with @Ghost(x))]
            x
        }

        #[verus_spec]
        fn test_call_mut_tracked(x: u32) {
            verus_extra_stmts!{
                let tracked mut y = 0u32;
            }
            {#[verus_io(with Tracked(&mut y), Ghost(0) => _)]
            test_mut_tracked(1);
            };

            if x < 100 && #[verus_io(with Tracked(&mut y), Ghost(0) => _)]test_mut_tracked(x) == 0 {
                return;
            }

            #[verus_io(with Tracked(&mut y), Ghost(0) => Ghost(z))]
            let _ = test_mut_tracked(1);

            proof!{
                assert(y == 1);
                assert(z == 1);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_trait_signature code!{
        trait X {
            #[verus_spec(ret =>
                with
                    Tracked(y): Tracked<&mut u32>,
                    Ghost(w): Ghost<u32>,
                    -> z: Ghost<u32>
            )]
            fn f(&self, x: u32) -> bool;
        }
    } => Err(e) => assert_any_vir_error_msg(e, "`with` does not support trait")
}

test_verify_one_file! {
    #[test] test_unverified_code_signature code!{
        #[verus_spec(ret =>
            with
                Tracked(y): Tracked<&mut u32>,
                Ghost(w): Ghost<u32>,
                -> z: Ghost<u32>
        )]
        fn test_mut_tracked(x: u32) -> u32 {
            proof!{
                *y = x;
            }
            #[verus_io(with @Ghost(x))]
            x
        }

        #[verifier::external]
        fn external_call_with_dummy(x: u32) -> u32 {
            #[verus_io(with Tracked::assume_new(), Ghost::assume_new() => _)]
            test_mut_tracked(0)
        }

        #[verifier::external]
        fn external_call_untouched(x: u32) -> u32 {
            test_mut_tracked(0)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_verified_call_unverified_signature code!{
        #[verus_spec(ret =>
            with
                Tracked(y): Tracked<&mut u32>,
                Ghost(w): Ghost<u32>,
                -> z: Ghost<u32>
        )]
        fn test_mut_tracked(x: u32) -> u32 {
            proof!{
                *y = x;
            }
            #[verus_io(with @Ghost(x))]
            x
        }

        #[verus_spec]
        fn verified_call_unverified(x: u32) {
            test_mut_tracked(0); // FAILS
        }
    } => Err(e) => {
        assert!(e.errors[0].rendered.contains("with"));
        assert_one_fails(e)
    }
}

test_verify_one_file! {
    #[test] test_with2 code!{
        #[verus_spec(ret =>
            with
                Tracked(y): Tracked<&mut u32>,
                Ghost(w): Ghost<u32>,
                -> z: Ghost<u32>
            requires
                x < 100,
                *old(y) < 100,
            ensures
                *y == x,
                ret.0 == x,
                ret.1@ == x,
        )]
        fn test_mut_tracked(x: u32) -> u32 {
            proof!{
                *y = x;
            }
            #[verus_io(with @Ghost(x))]
            x
        }

        #[verus_spec]
        fn test_cal_mut_tracked(x: u32) {
            verus_extra_stmts!{
                let ghost mut z = 0u32;
                let tracked mut y = 0u32;
            }
            if #[verus_io(with Tracked(&mut y), Ghost(0) => Ghost(z))] test_mut_tracked(1) == 0 {
                proof!{
                    assert(z == 1);
                }
                return;
            }

            proof!{
                assert(y == 1);
            }
        }
    } => Ok(())
}
