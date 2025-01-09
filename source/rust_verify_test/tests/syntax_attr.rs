#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] verus_verify_basic_while code! {
        #[verus_verify]
        fn test1() {
            let mut i = 0;
            #[invariant(i <= 10)]
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
        #[verus_verify]
        fn test1() {
            let mut i = 0;
            #[invariant(i <= 10)]
            #[invariant_except_break(i <= 9)]
            #[ensures(i == 10)]
            loop
            {
                i = i + 1;
                if (i == 10) {
                    break;
                }
            }
            proof!{assert(i == 10);}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] verus_verify_basic_while_fail1 code! {
        #[verus_verify]
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
            #[invariant(i <= 10, false)]
            while i < 10 {
                i = i + 1;
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "invariant not satisfied before loop")
}

test_verify_one_file! {
    #[test] verus_verify_bad_loop_spec code! {
        #[verus_verify]
        #[invariant(true)]
        fn test1() {}
    } => Err(err) => assert_any_vir_error_msg(err, "'verus_spec' attribute expected")
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
            #[ensures(true)]
            type T;
        }
    } => Err(err) => assert_custom_attr_error_msg(err, "Misuse of #[ensures()]")
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
