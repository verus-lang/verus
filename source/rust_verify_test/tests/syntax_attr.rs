#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] verus_verify_basic_while ["exec_allows_no_decreases_clause"] =>  code! {
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

test_verify_one_file_with_options! {
    #[test] verus_verify_basic_loop ["exec_allows_no_decreases_clause"] => code! {
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

test_verify_one_file_with_options! {
    #[test] verus_verify_basic_for_loop_verus_spec ["exec_allows_no_decreases_clause"] =>  code! {
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

test_verify_one_file_with_options! {
    #[test] verus_verify_for_loop_verus_spec_naming_iter ["exec_allows_no_decreases_clause"] =>  code! {
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

test_verify_one_file_with_options! {
    #[test] verus_verify_basic_while_fail1 ["exec_allows_no_decreases_clause"] => code! {
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

test_verify_one_file_with_options! {
    #[test] basic_while_false_invariant ["exec_allows_no_decreases_clause"] => code! {
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

test_verify_one_file_with_options! {
    #[test] verus_verify_invariant_on_func ["exec_allows_no_decreases_clause"] => code! {
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

test_verify_one_file_with_options! {
    #[test] test_no_verus_verify_attributes_in_trait_impl ["--no-external-by-default"] => code!{
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
        #[verus_verify]
        trait SomeTrait {
            #[verus_spec(ret =>
                requires true
                ensures true, ret
            )]
            fn f(&self) -> bool;
        }

        #[verus_verify]
        impl SomeTrait for bool {
            fn f(&self) -> bool {
                *self
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "postcondition not satisfied")
}

test_verify_one_file! {
    #[test] test_default_fn_use_macro_attributes code!{
        #[verus_verify]
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
        #[verus_verify]
        struct Abc<T> {
            t: T,
        }

        #[verus_verify(rlimit(2))]
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
    #[test] test_external_with_unsupported_features code!{
        #[verus_verify(external)]
        fn f<'a>(v: &'a mut [usize]) -> &'a mut usize {
            unimplemented!()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_prover_attributes code!{
        #[verus_verify(spinoff_prover, rlimit(2))]
        #[verus_spec(
            ensures
                true
        )]
        fn test()
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_invalid_combination_attr code!{
        #[verus_verify(external, spinoff_prover)]
        fn f<'a>(v: &'a mut [usize]) -> &'a mut usize {
            unimplemented!()
        }
    } => Err(e) => assert_any_vir_error_msg(e, "conflict parameters")
}

test_verify_one_file! {
    #[test] test_proof_decl code!{
        #[verus_spec]
        fn f() {}
        #[verus_spec]
        fn test() {
            proof!{
                let x = 1 as int;
                assert(x == 1);
            }
            proof_decl!{
                let ghost mut x;
                let tracked y = false;
                x = 2int;
                assert(!y);
                if x == 1 {
                    assert(false);
                }
            }

            f();
            proof!{
                assert(!y);
                assert(x == 2);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_decl_reject_exec code!{
        #[verus_spec]
        fn f() {}
        #[verus_spec]
        fn test() {
            proof_decl!{
                f();
            }
            f();
        }
    } => Err(e) => assert_vir_error_msg(e, "cannot call function `crate::f` with mode exec")
}

test_verify_one_file! {
    #[test] test_proof_decl_reject_exec_local code!{
        #[verus_spec]
        fn test() {
            proof_decl!{
                let x = true;
            }
        }
    } => Err(e) => assert_vir_error_msg(e, "Exec local is not allowed in proof_decl")
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
                ret == x,
                z@ == x,
        )]
        fn test_mut_tracked(x: u32) -> u32 {
            proof!{
                *y = x;
            }
            #[verus_spec(with |= Ghost(x))]
            x
        }

        #[verus_spec]
        fn test_call_mut_tracked(x: u32) {
            proof_decl!{
                let tracked mut y = 0u32;
            }
            {#[verus_spec(with Tracked(&mut y), Ghost(0) => _)]
            test_mut_tracked(1);
            };

            if x < 100 && #[verus_spec(with Tracked(&mut y), Ghost(0) => _)]test_mut_tracked(x) == 0 {
                return;
            }

            #[verus_spec(with Tracked(&mut y), Ghost(0) => Ghost(z))]
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
            #[verus_spec(with |= Ghost(x))]
            x
        }

        #[verifier::external]
        fn external_call_with_dummy(x: u32) -> u32 {
            #[verus_spec(with Tracked::assume_new(), Ghost::assume_new() => _)]
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
            #[verus_spec(with |= Ghost(x))]
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
                ->  z: Ghost<u32>
            requires
                x < 100,
                *old(y) < 100,
            ensures
                *y == x,
                ret == x,
                z@ == x,
        )]
        fn test_mut_tracked(x: u32) -> u32 {
            proof!{
                *y = x;
            }
            #[verus_spec(with |= Ghost(x))]
            x
        }

        #[verus_spec]
        fn test_cal_mut_tracked(x: u32) {
            proof_decl!{
                let ghost mut z = 0u32;
                let tracked mut y = 0u32;
            }
            if #[verus_spec(with Tracked(&mut y), Ghost(0) => Ghost(z))] test_mut_tracked(1) == 0 {
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

test_verify_one_file! {
    #[test] test_proof_with code!{
        #[verus_spec(ret =>
            with
                Tracked(y): Tracked<&mut u32>,
                Ghost(w): Ghost<u32>,
                ->  z: Ghost<u32>
            requires
                x < 100,
                *old(y) < 100,
            ensures
                *y == x,
                ret == x,
                z@ == x,
        )]
        fn test_mut_tracked(x: u32) -> u32 {
            proof!{
                *y = x;
            }
            proof_with!{|= Ghost(x)}
            x
        }

        #[verus_spec]
        fn test_cal_mut_tracked(x: u32) {
            proof_decl!{
                let ghost mut z = 0u32;
                let tracked mut y = 0u32;
            }
            if {
                proof_with!{Tracked(&mut y), Ghost(0) => Ghost(z)} test_mut_tracked(1)
            } == 0 {
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

test_verify_one_file! {
    #[test] test_proof_with_try code!{
        use vstd::prelude::*;
        #[verus_spec(
            with Tracked(y): Tracked<&mut u32>
        )]
        fn f() -> Result<(), ()> {
            Ok(())
        }

        #[verus_spec(
            with Tracked(y): Tracked<&mut u32>
        )]
        fn test_try_call() -> Result<(), ()> {
            proof_with!{Tracked(y)}
            let _ = f()?;
            Ok(())
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_err code!{
        #[verus_spec]
        fn test_mut_tracked(x: u32) -> u32 {
            proof_declare!{
                let ghost y = x;
            }
            proof_with!{Ghost(y)}
            x
        }
    } => Err(e) => assert_any_vir_error_msg(e, "with ghost inputs/outputs cannot be applied to a non-call expression")
}

test_verify_one_file! {
    #[test] test_dual_spec code!{
        #[verus_verify(dual_spec(spec_f))]
        #[verus_spec(
            requires
                x < 100,
                y < 100,
            returns f(x, y)
        )]
        fn f(x: u32, y: u32) -> u32 {
            proof!{
                assert(true);
            }
            {
                proof!{assert(true);}
                x + y
            }
        }

        #[verus_verify(dual_spec)]
        #[verus_spec(
            requires
                x < 100,
            returns
                f2(x),
        )]
        pub fn f2(x: u32) -> u32 {
            f(x, 1)
        }

        #[verus_verify]
        struct S;

        impl S {
            #[verus_verify(dual_spec)]
            #[verus_spec(
                returns
                    self.foo(x),
            )]
            fn foo(&self, x: u32) -> u32 {
                x
            }
        }

        verus!{
        proof fn lemma_f(x: u32, y: u32)
        requires
            x < 100,
        ensures
            y == 1 ==> f(x, y) == f2(x),
            f(x, y) == spec_f(x, y),
            f2(x) == __VERUS_SPEC_f2(x),
            f(x, y) == (x + y) as u32,
            __VERUS_SPEC_f2(x) == x + 1,
        {}

        mod inner {
            use super::*;
            proof fn lemma_f(x: u32)
            requires
                x < 100,
            ensures
                f2(x) == __VERUS_SPEC_f2(x),
                __VERUS_SPEC_f2(x) == (x + 1),
            {}
        }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_dual_spec_unsupported_body code!{
        #[verus_verify(dual_spec(spec_f))]
        #[verus_spec(
            requires
                *x < 100,
                y < 100,
            returns
                f(x, y),
        )]
        fn f(x: &mut u32, y: u32) -> u32 {
            *x = *x + y;
            *x
        }
    } => Err(e) => assert_vir_error_msg(e, "&mut parameter not allowed for spec functions")
}

test_verify_one_file! {
    #[test] test_dual_spec_unsupported_trait code!{
        trait X {
            fn f(&self) -> u32;
        }

        impl X for u32 {
            #[verus_verify(dual_spec(spec_f))]
            #[verus_spec(
                ensures
                    self.spec_f(),
            )]
            fn f(&self) -> u32{
                *self
            }
        }

    } => Err(e) => assert_rust_error_msg(e, "method `spec_f` is not a member of trait `X`")
}

test_verify_one_file! {
    #[test] test_macro_inside_proof_decl code!{
        macro_rules! inline_proof {
            ($val: expr => $x: ident, $y: ident) => {
                proof_decl!{
                    let tracked $x: int = $val;
                    let ghost $y: int = $val;
                    assert($x == $y);
                }
             }
        }

        fn test_inline_proof_via_macro() {
            proof_decl!{
                inline_proof!(0 => x, y);
                assert(x == 0);
            }
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_test code! {
        use vstd::prelude::*;

        fn testfn() {

            let f =
            #[verus_spec(z: u64 =>
                requires y == 2
                ensures z == 2
            )]
            |y: u64| { y };

            proof!{
                assert(f.requires((2,)));
                assert(!f.ensures((2,),3));
            }

            let t = f(2);
            proof!{
                assert(t == 2);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_no_ret_fails code! {
        use vstd::prelude::*;

        fn testfn() {

            let f =
            #[verus_spec(
                requires y == 2
            )]
            |y: u64| {  };
        }
    } => Err(e) => assert_any_vir_error_msg(e, "Closure must have a return type")
}

test_verify_one_file! {
    #[test] test_no_ret_ok code! {
        use vstd::prelude::*;

        fn testfn() {

            let f1 =
            #[verus_spec(
                requires y == 2
            )]
            |y: u64| -> () {  };

            let f2 =
            #[verus_spec(ret: () =>
                requires y == 2
            )]
            |y: u64| {  };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_const_fn_eval_via_proxy code!{
        use vstd::prelude::*;
        #[verus_spec(ret =>
            ensures ret == x
        )]
        #[allow(unused_variables)]
        pub const fn const_fn(x: u64) -> u64 {
            proof!{
                assert(true);
            }
            {
                proof!{assert(true);}
            }
            x
        }

        pub const X: u64 = const_fn(1);
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_const_fn_with_ghost code!{
        use vstd::prelude::*;
        #[verus_spec(ret =>
            with Ghost(g): Ghost<u64>
        )]
        #[allow(unused_variables)]
        pub const fn const_fn(x: u64) -> u64 {
            proof!{
                assert(true);
            }
            {
                proof!{assert(true);}
            }
            x
        }

        #[verus_spec(
            with Ghost(g): Ghost<u64>
        )]
        pub const fn call_const_fn(x: u64) -> u64 {
            proof_with!{Ghost(g)}
            const_fn(x)
        }


        // external call to const_fn does not need ghost var.
        pub const X: u64 = const_fn(1);
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_method code!{
        use vstd::prelude::*;

        pub struct Foo;

        #[verus_verify]
        impl Foo {
            #[verus_spec(ret =>
                with
                    Tracked(c): Tracked<&mut ()>
                requires
                    true,
                ensures
                    ret == 1,
            )]
            fn test(a: u64, b: u64) -> u64 {
                1
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_no_verus_verify_attribute_on_impl_block_fails code!{
        use vstd::prelude::*;

        pub struct Foo;

        impl Foo {
            #[verus_verify]
            #[verus_spec(ret =>
                with
                    Tracked(c): Tracked<&mut ()>
                requires
                    true,
                ensures
                    ret == 1,
            )]
            fn test(a: u64, b: u64) -> u64 {
                1
            }
        }
    } => Err(_) => {}
}

test_verify_one_file! {
    #[test] test_unverified_in_impl code!{
        use vstd::prelude::*;

        pub struct X;

        #[verus_verify]
        impl X {
            fn unverified() {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_item_const_dual code!{
        use vstd::prelude::*;

        #[verus_spec]
        const CONST_ITEM: u64 = 42;

        #[verus_spec]
        fn test() {
            let v = CONST_ITEM;
            proof! {
                assert(v == 42);
                assert(CONST_ITEM == 42);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_item_const_error code!{
        use vstd::prelude::*;

        const CONST_ITEM: u64 = 42;

        #[verus_spec]
        fn test() {
            let v = CONST_ITEM;
            proof! {
                assert(v == 42);
            }
        }
    } => Err(e) => assert_any_vir_error_msg(e, "cannot use function `test_crate::CONST_ITEM` which is ignored")
}

test_verify_one_file! {
    #[test] test_item_const_ensures code!{
        use vstd::prelude::*;

        #[verus_spec(ret=>
            ensures ret == 42
        )]
        const fn const_item_fn() -> u64 {
            42
        }

        #[verus_spec(
            ensures CONST_ITEM == 42
        )]
        const CONST_ITEM: u64 = const_item_fn();

        #[verus_spec]
        fn test() {
            let v = CONST_ITEM;
            proof! {
                assert(v == 42);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_item_const_ensures_is_exec_mode code!{
        use vstd::prelude::*;

        #[verus_spec(ret=>
            ensures ret == 42
        )]
        const fn const_item_fn() -> u64 {
            42
        }

        #[verus_spec(
            ensures CONST_ITEM == 42
        )]
        const CONST_ITEM: u64 = const_item_fn();

        #[verus_spec]
        fn test() {
            proof! {
                assert(CONST_ITEM == 42);
            }
        }
    } => Err(e) => assert_any_vir_error_msg(e, "cannot read const with mode exec")
}

test_verify_one_file! {
    #[test] test_impl_item_const_dual code!{
        use vstd::prelude::*;

        struct X;

        #[verus_verify]
        impl X {
            const A: usize = 1;
            const B: usize = Self::A + 1;
            const C: usize = Self::B + 1;
        }

         #[verus_spec(ensures true)]
        fn test() {
            let v = X::C;
            proof! {
                assert(v == 3);
                assert(X::A == 1);
                assert(X::B == 2);
                assert(X::C == 3);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_item_const_requires_erasure code!{
        use vstd::prelude::*;

        struct X;

        #[verus_verify]
        impl X {
            const A: usize = 1;
        }

        // This requires to use const_proxy in const.
        #[verus_verify]
        enum Y {
            A,
            B = (1 << X::A) - 1,
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_item_const_use_unverified code!{
        use vstd::prelude::*;

        struct X;

        const fn const_fn() -> u64 {
            42
        }

        #[verus_verify]
        impl X {
            const CONST_ITEM: u64 = const_fn();
        }
    } => Err(e) => assert_any_vir_error_msg(e, "cannot use function `test_crate::const_fn` which is ignored")
}

test_verify_one_file! {
    #[test] test_impl_item_const_external code!{
        use vstd::prelude::*;

        struct X;

        const fn const_fn() -> u64 {
            42
        }

        #[verus_verify]
        impl X {
            #[verus_verify(external)]
            const CONST_ITEM: u64 = const_fn();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_impl_item_const_ensures code!{
        use vstd::prelude::*;

        struct X;

        #[verus_spec(ret=>
            ensures ret == 42
        )]
        const fn const_fn() -> u64 {
            42
        }

        #[verus_verify]
        impl X {
            #[verus_spec(ensures Self::CONST_ITEM != 42)]
            const CONST_ITEM: u64 = const_fn();
        }
    } => Err(e) => assert_any_vir_error_msg(e, "postcondition not satisfied")
}

test_verify_one_file! {
    #[test] test_verus_spec_with_trailing_comma_simple code! {
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with
                Tracked(y): Tracked<&mut u32>,
                Ghost(w): Ghost<u32>,
            requires
                x < 100,
            ensures
        )]
        fn foo(x: u32) -> u32 {
            (x + 1)
        }

        #[verus_spec(ret =>
            with
                Tracked(y): Tracked<&mut u32>,
            requires
                x < 100,
        )]
        fn bar(x: u32) -> u32 {
            (x + 1)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_verus_spec_with_trailing_comma_complex code!{
        use vstd::prelude::*;

        #[verus_spec(ret =>
            with
                Tracked(y): Tracked<&mut u32>,
                Ghost(w): Ghost<u32>,
                    -> z: Ghost<u32>,
            requires
                x < 100,
            ensures
                ret == x + 1,
                z@ == x,
            )]
        fn foo(x: u32) -> u32 {
            proof_with!(|= Ghost(x));
            (x + 1)
        }

        #[verus_spec(ret =>
            with
                Tracked(y): Tracked<&mut u32>,
                Ghost(w): Ghost<u32>
                    -> z: Ghost<u32>,
            requires
                x < 100,
            ensures
                ret == x + 1,
                z@ == x,
        )]
        fn bar(x: u32) -> u32 {
            proof_with!(|= Ghost(x));
            (x + 1)
        }

        #[verus_spec(ret =>
            with
                Tracked(y): Tracked<&mut u32>,
                Ghost(w): Ghost<u32>,
                    -> z: Ghost<u32>
            requires
                x < 100,
            ensures
                ret == x + 1,
                z@ == x,
        )]
        fn baz(x: u32) -> u32 {
            proof_with!(|= Ghost(x));
            (x + 1)
        }

        #[verus_spec(ret =>
            with
                Tracked(y): Tracked<&mut u32>,
                Ghost(w): Ghost<u32>
                    -> z: Ghost<u32>
            requires
                x < 100,
            ensures
                ret == x + 1,
                z@ == x,
        )]
        fn qux(x: u32) -> u32 {
            proof_with!(|= Ghost(x));
            (x + 1)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_erase_unverified_code code!{
        use vstd::prelude::*;
        #[verus_spec(
            with Tracked(x): Tracked<()>,
            ensures true,
        )]
        fn foo() {
            proof!{
                let abcd = Tracked(x);
                let y = x;
            }
            #[cfg_attr(not(customized_cfg), verus_spec(
                invariant x == (),
            ))]
            for i in 0..10 {
            }
        }
    } => Ok(())
}
