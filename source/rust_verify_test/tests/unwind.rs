#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] standard_try_operations_no_unwind verus_code! {
        use vstd::prelude::*;
        use core::convert::Infallible;
        use core::ops::{ControlFlow, FromResidual, Try};

        fn option_branch<T>(value: Option<T>) -> ControlFlow<Option<Infallible>, T>
            no_unwind
        {
            value.branch()
        }

        fn result_branch<T, E>(value: Result<T, E>) -> ControlFlow<Result<Infallible, E>, T>
            no_unwind
        {
            value.branch()
        }

        fn control_flow_branch<B, C>(value: ControlFlow<B, C>) ->
            ControlFlow<ControlFlow<B, Infallible>, C>
            no_unwind
        {
            value.branch()
        }

        fn option_from_residual<T>(residual: Option<Infallible>) -> Option<T>
            no_unwind
        {
            Option::from_residual(residual)
        }

        fn control_flow_from_residual<B, C>(residual: ControlFlow<B, Infallible>) ->
            ControlFlow<B, C>
            no_unwind
        {
            ControlFlow::from_residual(residual)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] generic_try_operations_conditional_unwind verus_code! {
        use vstd::prelude::*;
        use core::ops::{ControlFlow, FromResidual, Try};
        use vstd::std_specs::control_flow::{FromResidualSpec, TrySpec};

        fn branch<T: Try>(value: T) -> ControlFlow<T::Residual, T::Output>
            no_unwind when !value.may_unwind()
        {
            value.branch()
        }

        fn from_residual<T: FromResidual<R>, R>(residual: R) -> T
            no_unwind when !<T as FromResidualSpec<R>>::may_unwind(&residual)
        {
            T::from_residual(residual)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] custom_try_operations_check_conditional_unwind verus_code! {
        use vstd::prelude::*;
        use core::convert::Infallible;
        use core::ops::{ControlFlow, FromResidual, Try};
        use vstd::std_specs::control_flow::{FromResidualSpecImpl, TrySpecImpl};

        pub struct MyTry {
            pub value: u32,
            pub may_panic: bool,
        }

        // The default contract permits unwinding.
        fn maybe_panic() {}

        impl TrySpecImpl for MyTry {
            open spec fn may_unwind(&self) -> bool { self.may_panic }
            open spec fn branch_model_is_valid() -> bool { true }
            open spec fn branch_model(self) -> ControlFlow<Option<Infallible>, u32> {
                ControlFlow::Continue(self.value)
            }
        }

        impl FromResidualSpecImpl<Option<Infallible>> for MyTry {
            open spec fn may_unwind(residual: &Option<Infallible>) -> bool { false }
        }

        impl FromResidual<Option<Infallible>> for MyTry {
            fn from_residual(residual: Option<Infallible>) -> Self {
                maybe_panic(); // FAILS: this implementation promised not to unwind.
                MyTry { value: 0, may_panic: false }
            }
        }

        impl Try for MyTry {
            type Output = u32;
            type Residual = Option<Infallible>;

            fn from_output(value: u32) -> Self {
                MyTry { value, may_panic: false }
            }

            fn branch(self) -> ControlFlow<Option<Infallible>, u32> {
                if self.may_panic {
                    maybe_panic();
                }
                ControlFlow::Continue(self.value)
            }
        }

        fn safe(value: u32) -> ControlFlow<Option<Infallible>, u32>
            no_unwind
        {
            MyTry { value, may_panic: false }.branch()
        }

        fn unguarded(value: MyTry) -> ControlFlow<Option<Infallible>, u32>
            no_unwind
        {
            value.branch() // FAILS: this value may permit unwinding.
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] try_operations_do_not_assume_no_unwind verus_code! {
        use vstd::prelude::*;
        use core::convert::Infallible;
        use core::ops::{ControlFlow, FromResidual, Try};

        fn branch<T: Try>(value: T) -> ControlFlow<T::Residual, T::Output>
            no_unwind
        {
            value.branch() // FAILS: the implementation's flag is unknown.
        }

        fn from_residual<T: FromResidual<R>, R>(residual: R) -> T
            no_unwind
        {
            T::from_residual(residual) // FAILS: the implementation's flag is unknown.
        }

        fn result_from_residual<T, E, F: From<E>>(residual: Result<Infallible, E>) ->
            Result<T, F>
            no_unwind
        {
            Result::from_residual(residual) // FAILS: error conversion may unwind.
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] basic ["exec_allows_no_decreases_clause"] => verus_code! {
        use vstd::prelude::*;
        use vstd::invariant::*;

        fn ensures_no_comma()
            requires
                true,
            ensures
                true
            no_unwind
        {
        }

        fn ensures_with_comma()
            requires
                true,
            ensures
                true,
            no_unwind
        {
        }

        fn fn_may_unwind()
            opens_invariants none
        {
        }

        fn fn_no_unwind()
            opens_invariants none
            no_unwind
        {
        }

        fn fn_conditional_unwind(i: u8)
            opens_invariants none
            no_unwind when i >= 5
        {
        }

        fn test_caller_may_unwind() {
            fn_may_unwind();
            fn_no_unwind();
            fn_conditional_unwind(0);
            fn_conditional_unwind(20);
        }

        fn test_caller_no_unwind1()
            no_unwind
        {
            fn_may_unwind(); // FAILS
        }

        fn test_caller_no_unwind2()
            no_unwind
        {
            fn_conditional_unwind(3); // FAILS
        }

        fn test_caller_no_unwind3()
            no_unwind
        {
            fn_conditional_unwind(20);
            fn_no_unwind();
        }

        fn test_caller_conditional1(j: u8)
            no_unwind when j >= 10
        {
            fn_may_unwind(); // FAILS
        }

        fn test_caller_conditional2(j: u8)
            no_unwind when j >= 10
        {
            fn_no_unwind();
        }

        fn test_caller_conditional3(j: u8)
            no_unwind when j >= 10
        {
            fn_conditional_unwind(j);
        }

        fn test_caller_conditional4(j: u8)
            no_unwind when j >= 4
        {
            fn_conditional_unwind(j); // FAILS
        }

        fn call_from_invariant<A, B: InvariantPredicate<A, u8>>(Tracked(inv): Tracked<&LocalInvariant<A, u8, B>>) {
            open_local_invariant!(inv => inner => {
                fn_no_unwind();
            });
        }

        fn call_from_invariant2<A, B: InvariantPredicate<A, u8>>(Tracked(inv): Tracked<&LocalInvariant<A, u8, B>>) {
            open_local_invariant!(inv => inner => {
                fn_may_unwind(); // FAILS
            });
        }

        fn call_from_invariant3<A, B: InvariantPredicate<A, u8>>(Tracked(inv): Tracked<&LocalInvariant<A, u8, B>>) {
            open_local_invariant!(inv => inner => {
                fn_conditional_unwind(5);
            });
        }

        fn call_from_invariant4<A, B: InvariantPredicate<A, u8>>(Tracked(inv): Tracked<&LocalInvariant<A, u8, B>>) {
            open_local_invariant!(inv => inner => {
                fn_conditional_unwind(4); // FAILS
            });
        }

        fn call_from_invariant5<A, B: InvariantPredicate<A, u8>>(Tracked(inv): Tracked<&LocalInvariant<A, u8, B>>, k: u8)
            no_unwind when k >= 8
        {
            open_local_invariant!(inv => inner => {
                fn_conditional_unwind(k); // FAILS
            });
        }

        fn call_from_invariant6<A, B: InvariantPredicate<A, u8>>(Tracked(inv): Tracked<&LocalInvariant<A, u8, B>>, k: u8)
            no_unwind when k >= 8
        {
            loop {
                open_local_invariant!(inv => inner => {
                    fn_conditional_unwind(k); // FAILS
                });
            }
        }

        fn test_closure()
            no_unwind
        {
            let f = || {
                // This is fine since it's in the closure
                fn_may_unwind();
            };
        }

        fn test_closure2()
            no_unwind
        {
            let f = || {
            };

            // not fine, closures always unwind (for now)
            f(); // FAILS
        }
    } => Err(err) => assert_fails(err, 9)
}

test_verify_one_file! {
    #[test] call_trait_methods_generic verus_code! {
        use vstd::prelude::*;
        use vstd::invariant::*;

        trait Tr {
            fn fn_may_unwind();

            fn fn_no_unwind()
                no_unwind;

            fn fn_conditional_unwind(i: u8)
                no_unwind when i >= 5;
        }

        fn test_caller_may_unwind<T: Tr>() {
            T::fn_may_unwind();
            T::fn_no_unwind();
            T::fn_conditional_unwind(0);
            T::fn_conditional_unwind(20);
        }

        fn test_caller_no_unwind1<T: Tr>()
            no_unwind
        {
            T::fn_may_unwind(); // FAILS
        }

        fn test_caller_no_unwind2<T: Tr>()
            no_unwind
        {
            T::fn_conditional_unwind(3); // FAILS
        }

        fn test_caller_no_unwind3<T: Tr>()
            no_unwind
        {
            T::fn_conditional_unwind(20);
            T::fn_no_unwind();
        }

        fn test_caller_conditional1<T: Tr>(j: u8)
            no_unwind when j >= 10
        {
            T::fn_may_unwind(); // FAILS
        }

        fn test_caller_conditional2<T: Tr>(j: u8)
            no_unwind when j >= 10
        {
            T::fn_no_unwind();
        }

        fn test_caller_conditional3<T: Tr>(j: u8)
            no_unwind when j >= 10
        {
            T::fn_conditional_unwind(j);
        }

        fn test_caller_conditional4<T: Tr>(j: u8)
            no_unwind when j >= 4
        {
            T::fn_conditional_unwind(j); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] call_trait_methods_specific verus_code! {
        use vstd::prelude::*;
        use vstd::invariant::*;

        trait Tr {
            fn fn_may_unwind();

            fn fn_no_unwind()
                no_unwind;

            fn fn_conditional_unwind(i: u8)
                no_unwind when i >= 5;
        }

        struct Y { }

        impl Tr for Y {
            fn fn_may_unwind();
            fn fn_no_unwind();
            fn fn_conditional_unwind(i: u8);
        }

        fn test_caller_may_unwind<T: Tr>() {
            Y::fn_may_unwind();
            Y::fn_no_unwind();
            Y::fn_conditional_unwind(0);
            Y::fn_conditional_unwind(20);
        }

        fn test_caller_no_unwind1<T: Tr>()
            no_unwind
        {
            Y::fn_may_unwind(); // FAILS
        }

        fn test_caller_no_unwind2<T: Tr>()
            no_unwind
        {
            Y::fn_conditional_unwind(3); // FAILS
        }

        fn test_caller_no_unwind3<T: Tr>()
            no_unwind
        {
            Y::fn_conditional_unwind(20);
            Y::fn_no_unwind();
        }

        fn test_caller_conditional1<T: Tr>(j: u8)
            no_unwind when j >= 10
        {
            Y::fn_may_unwind(); // FAILS
        }

        fn test_caller_conditional2<T: Tr>(j: u8)
            no_unwind when j >= 10
        {
            Y::fn_no_unwind();
        }

        fn test_caller_conditional3<T: Tr>(j: u8)
            no_unwind when j >= 10
        {
            Y::fn_conditional_unwind(j);
        }

        fn test_caller_conditional4<T: Tr>(j: u8)
            no_unwind when j >= 4
        {
            Y::fn_conditional_unwind(j); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] call_from_trait_fns verus_code! {
        fn fn_may_unwind()
            opens_invariants none
        {
        }

        fn fn_no_unwind()
            opens_invariants none
            no_unwind
        {
        }

        fn fn_conditional_unwind(i: u8)
            opens_invariants none
            no_unwind when i >= 5
        {
        }

        trait Tr {
            fn tr_fn_may_unwind();

            fn tr_fn_no_unwind()
                no_unwind;

            fn tr_fn_conditional_unwind(i: u8)
                no_unwind when i >= 3;
        }

        struct Y { }

        impl Tr for Y {
            fn tr_fn_may_unwind() {
                fn_may_unwind();
            }

            fn tr_fn_no_unwind() {
                fn_may_unwind(); // FAILS
            }

            fn tr_fn_conditional_unwind(i: u8)
            {
                fn_conditional_unwind(i); // FAILS
            }
        }

        struct Z { }

        impl Tr for Z {
            fn tr_fn_may_unwind() {
                fn_may_unwind();
            }

            fn tr_fn_no_unwind() {
                fn_conditional_unwind(3); // FAILS
            }

            fn tr_fn_conditional_unwind(i: u8)
            {
                assume(i >= 9);
                fn_conditional_unwind(i);
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] apply_to_trait_fn verus_code! {
        trait Tr {
            fn stuff(j: u8)
                no_unwind;
        }

        struct X { }

        impl Tr for X {
            fn stuff(j: u8)
                no_unwind when j >= 4
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "trait method implementation cannot declare an `unwind` specification")
}

test_verify_one_file! {
    #[test] mode1 verus_code! {
        proof fn stuff(j: u8)
            no_unwind
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "an `unwind` specification can only be given on exec functions")
}

test_verify_one_file! {
    #[test] mode2 verus_code! {
        spec fn stuff(j: u8)
            no_unwind
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "an `unwind` specification can only be given on exec functions")
}

test_verify_one_file! {
    #[test] mode3 verus_code! {
        proof fn stuff(j: u8)
            no_unwind when j >= 3
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "an `unwind` specification can only be given on exec functions")
}

test_verify_one_file! {
    #[test] mode4 verus_code! {
        fn some_exec_fn(j: u8) -> bool { true }

        fn stuff(j: u8)
            no_unwind when some_exec_fn(j)
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::some_exec_fn` with mode exec")
}

test_verify_one_file! {
    #[test] specs_on_external_body verus_code! {
        #[verifier::external_body]
        fn fn_may_unwind()
            opens_invariants none
        {
        }

        #[verifier::external_body]
        fn fn_no_unwind()
            opens_invariants none
            no_unwind
        {
        }

        #[verifier::external_body]
        fn fn_conditional_unwind(i: u8)
            opens_invariants none
            no_unwind when i >= 5
        {
        }

        fn test_caller_may_unwind() {
            fn_may_unwind();
            fn_no_unwind();
            fn_conditional_unwind(0);
            fn_conditional_unwind(20);
        }

        fn test_caller_no_unwind1()
            no_unwind
        {
            fn_may_unwind(); // FAILS
        }

        fn test_caller_no_unwind2()
            no_unwind
        {
            fn_conditional_unwind(3); // FAILS
        }

        fn test_caller_no_unwind3()
            no_unwind
        {
            fn_conditional_unwind(20);
            fn_no_unwind();
        }

        fn test_caller_conditional1(j: u8)
            no_unwind when j >= 10
        {
            fn_may_unwind(); // FAILS
        }

        fn test_caller_conditional2(j: u8)
            no_unwind when j >= 10
        {
            fn_no_unwind();
        }

        fn test_caller_conditional3(j: u8)
            no_unwind when j >= 10
        {
            fn_conditional_unwind(j);
        }

        fn test_caller_conditional4(j: u8)
            no_unwind when j >= 4
        {
            fn_conditional_unwind(j); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] specs_on_external_fn_specification verus_code! {
        #[verifier::external]
        fn fn_may_unwind() { }

        #[verifier::external]
        fn fn_no_unwind() { }

        #[verifier::external]
        fn fn_conditional_unwind(i: u8) { }

        #[verifier::external_fn_specification]
        fn ex_fn_may_unwind()
            opens_invariants none
        {
            fn_may_unwind()
        }

        #[verifier::external_fn_specification]
        fn ex_fn_no_unwind()
            opens_invariants none
            no_unwind
        {
            fn_no_unwind()
        }

        #[verifier::external_fn_specification]
        fn ex_fn_conditional_unwind(i: u8)
            opens_invariants none
            no_unwind when i >= 5
        {
            fn_conditional_unwind(i)
        }

        fn test_caller_may_unwind() {
            fn_may_unwind();
            fn_no_unwind();
            fn_conditional_unwind(0);
            fn_conditional_unwind(20);
        }

        fn test_caller_no_unwind1()
            no_unwind
        {
            fn_may_unwind(); // FAILS
        }

        fn test_caller_no_unwind2()
            no_unwind
        {
            fn_conditional_unwind(3); // FAILS
        }

        fn test_caller_no_unwind3()
            no_unwind
        {
            fn_conditional_unwind(20);
            fn_no_unwind();
        }

        fn test_caller_conditional1(j: u8)
            no_unwind when j >= 10
        {
            fn_may_unwind(); // FAILS
        }

        fn test_caller_conditional2(j: u8)
            no_unwind when j >= 10
        {
            fn_no_unwind();
        }

        fn test_caller_conditional3(j: u8)
            no_unwind when j >= 10
        {
            fn_conditional_unwind(j);
        }

        fn test_caller_conditional4(j: u8)
            no_unwind when j >= 4
        {
            fn_conditional_unwind(j); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] vstd_checked_integer_operations_no_unwind verus_code! {
        use vstd::prelude::*;

        fn unsigned_operations(x: u64, y: u64, z: i64)
            no_unwind
        {
            let _ = x.checked_add(y);
            let _ = x.checked_add_signed(z);
            let _ = x.checked_sub(y);
            let _ = x.checked_mul(y);
            let _ = x.checked_next_multiple_of(y);
            let _ = x.checked_div(y);
            let _ = x.checked_div_euclid(y);
            let _ = x.checked_rem(y);
            let _ = x.checked_rem_euclid(y);
            let _ = x.saturating_add(y);
            let _ = x.saturating_sub(y);
            let _ = x.saturating_mul(y);
            let _ = x.is_multiple_of(y);
        }

        fn signed_operations(x: i64, y: i64, z: u64)
            no_unwind
        {
            let _ = x.checked_add(y);
            let _ = x.checked_add_unsigned(z);
            let _ = x.checked_sub(y);
            let _ = x.checked_sub_unsigned(z);
            let _ = x.checked_mul(y);
            let _ = x.checked_div(y);
            let _ = x.checked_div_euclid(y);
            let _ = x.checked_rem(y);
            let _ = x.checked_rem_euclid(y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] vstd_len_and_view_accessors_no_unwind verus_code! {
        use vstd::prelude::*;

        fn slice_operations<T>(s: &[T], a: &[T; 4])
            opens_invariants none
            no_unwind
        {
            let _ = s.len();
            let _ = s.is_empty();
            let _ = a.as_slice();
        }

        fn str_operations(s: &str, t: &String)
            opens_invariants none
            no_unwind
        {
            let _ = s.len();
            let _ = s.is_empty();
            let _ = s.as_bytes();
            let _ = t.as_str();
            let _ = t.is_empty();
        }

        fn vec_operations<T>(v: &mut Vec<T>)
            opens_invariants none
            no_unwind
        {
            let _ = v.is_empty();
            let _ = v.as_slice();
            let _ = v.as_mut_slice();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] no_unwind_box_rc_arc_new verus_code! {
        use vstd::prelude::*;
        use std::rc::Rc;
        use std::sync::Arc;

        fn test_box()
            no_unwind
        {
            let b = Box::new(8); // FAILS
        }

        fn test_rc()
            no_unwind
        {
            let b = Rc::new(8); // FAILS
        }

        fn test_arc()
            no_unwind
        {
            let b = Arc::new(8); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] vstd_core_atomic_ordering_ok verus_code! {
        use vstd::prelude::*;
        use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};

        fn ok_ops(a: &AtomicU32, b: &AtomicBool)
            no_unwind
        {
            let _ = a.load(Ordering::Acquire);
            let _ = a.load(Ordering::SeqCst);
            a.store(7, Ordering::Release);
            a.store(8, Ordering::Relaxed);
            let _ = a.swap(3, Ordering::AcqRel);
            let _ = a.compare_exchange(1, 2, Ordering::AcqRel, Ordering::Acquire);
            let _ = a.compare_exchange_weak(1, 2, Ordering::Release, Ordering::Relaxed);
            let _ = a.fetch_add(1, Ordering::AcqRel);
            let _ = a.fetch_max(5, Ordering::SeqCst);
            let _ = b.load(Ordering::Acquire);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] vstd_core_atomic_ordering_fail verus_code! {
        use vstd::prelude::*;
        use core::sync::atomic::{AtomicU32, Ordering};

        fn bad_load(a: &AtomicU32) {
            let _ = a.load(Ordering::Release); // FAILS
        }

        fn bad_store(a: &AtomicU32) {
            a.store(1, Ordering::Acquire); // FAILS
        }

        fn bad_cmpxchg(a: &AtomicU32) {
            let _ = a.compare_exchange(1, 2, Ordering::SeqCst, Ordering::AcqRel); // FAILS
        }

        fn bad_cmpxchg_weak(a: &AtomicU32) {
            let _ = a.compare_exchange_weak(1, 2, Ordering::SeqCst, Ordering::Release); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] option_from_residual_infallible_no_false verus_code! {
        // Since Rust 1.100, `Infallible` is an alias for `!`
        use vstd::prelude::*;
        use core::convert::Infallible;
        use core::ops::FromResidual;

        fn test(residual: Option<Infallible>) -> Option<u8> {
            let r = Option::from_residual(residual);
            assert(false); // FAILS
            r
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] header_after_statements_in_block verus_code! {
        fn f(x: u8) -> (r: u8)
            ensures
                r == x,
        {
            {
                if x == 0 {
                    return 1;
                }
                verus_builtin::no_unwind();
            }
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "invalid nested header block")
}

test_verify_one_file_with_options! {
    #[test] requires_no_unwind ["exec_allows_no_decreases_clause"] => verus_code! {
        use vstd::prelude::*;

        fn fn_may_unwind() {
        }

        fn f(i: u8)
            requires[no_unwind]
                i >= 5,
        {
        }

        fn f2(i: u8, j: u8)
            requires
                i < 200,
            requires[no_unwind]
                i >= 5,
                j >= 5,
        {
        }

        fn f3(i: u8, j: u8)
            requires[no_unwind]
                i >= 5,
            requires
                j < 200,
            ensures
                true,
        {
        }

        fn caller1() {
            f(10);
            f2(10, 10);
            f3(10, 10);
        }

        fn caller2() {
            f(3); // FAILS
        }

        fn caller3(j: u8) {
            f(j); // FAILS
        }

        fn caller4() {
            f2(10, 3); // FAILS
        }

        #[verifier::restrict_unwind(false)]
        fn caller5() {
            f(3);
            f2(10, 3);
        }

        #[verifier::restrict_unwind(false)]
        fn caller6()
            no_unwind
        {
            f(3); // FAILS
        }

        #[verifier::restrict_unwind(false)]
        fn caller7()
            no_unwind
        {
            f(10);
        }

        fn caller8() {
            #[verifier::restrict_unwind(false)] f(3);
            f(3); // FAILS
        }

        #[verifier::restrict_unwind(false)]
        fn caller9() {
            #[verifier::restrict_unwind(true)] f(3); // FAILS
        }

        fn body1(i: u8)
            requires[no_unwind]
                i >= 5,
        {
            fn_may_unwind(); // FAILS
        }

        fn body2(i: u8)
            requires[no_unwind]
                i >= 5,
        {
            // the caller's own requires[no_unwind] conditions are not preconditions,
            // so with restrict_unwind, this must be proven unconditionally
            f(i); // FAILS
        }

        #[verifier::restrict_unwind(false)]
        fn body3(i: u8)
            requires[no_unwind]
                i >= 5,
        {
            f(i);
            if i < 5 {
                fn_may_unwind();
            }
        }

        #[verifier::restrict_unwind(false)]
        fn body4(i: u8)
            requires[no_unwind]
                i >= 4,
        {
            f(i); // FAILS
        }
    } => Err(err) => assert_fails(err, 9)
}

test_verify_one_file_with_options! {
    #[test] requires_no_unwind_exact ["exec_allows_no_decreases_clause"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::external_body]
        fn do_panic()
            ensures
                false,
        {
            panic!();
        }

        fn g(i: u8)
            requires[no_unwind exact]
                i >= 5,
        {
            if i < 5 {
                do_panic();
            }
        }

        fn g_bad(i: u8)
            requires[no_unwind exact]
                i >= 5, // FAILS
        {
        }

        fn g_bad2(i: u8)
            requires[no_unwind exact]
                i >= 5,
        {
            if i < 5 {
                do_panic();
            }
            do_panic(); // FAILS
        }

        #[verifier::restrict_unwind(false)]
        fn caller1(j: u8) {
            g(j);
            assert(j >= 5);
        }

        #[verifier::restrict_unwind(false)]
        fn caller2(j: u8) {
            g(j);
            assert(j >= 6); // FAILS
        }

        fn caller3(j: u8) {
            g(j); // FAILS
        }

        fn caller4(j: u8) {
            #[verifier::restrict_unwind(false)] g(j);
            #[verifier::restrict_unwind(true)] g(j);
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] requires_no_unwind_assume_specification verus_code! {
        use vstd::prelude::*;

        #[verifier::external]
        fn ext(i: u8) -> u8 {
            if i == 0 { panic!() }
            i
        }

        pub assume_specification[ext](i: u8) -> (r: u8)
            requires[no_unwind exact]
                i > 0,
            ensures
                r == i;

        fn test1() {
            let r = ext(3);
            assert(r == 3);
        }

        fn test2() {
            let r = ext(0); // FAILS
        }

        #[verifier::restrict_unwind(false)]
        fn test3(i: u8) {
            let r = ext(i);
            assert(i > 0);
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] requires_no_unwind_trait verus_code! {
        use vstd::prelude::*;

        trait T {
            fn m(&self, i: u8)
                requires[no_unwind]
                    i >= 5;
        }

        struct S;

        impl T for S {
            fn m(&self, i: u8) {
            }
        }

        struct S2;

        impl T for S2 {
            fn m(&self, i: u8) {
                if i < 5 {
                    may_unwind();
                }
                may_unwind(); // FAILS
            }
        }

        fn may_unwind() {
        }

        fn test1<A: T>(a: &A) {
            a.m(5);
            a.m(4); // FAILS
        }

        fn test2(s: &S) {
            s.m(5);
            s.m(4); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] requires_no_unwind_bad_syntax verus_code! {
        fn f(i: u8)
            requires[no_unwind bogus]
                i >= 5,
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "expected `exact`")
}

test_verify_one_file! {
    #[test] requires_no_unwind_with_no_unwind verus_code! {
        fn f(i: u8)
            requires[no_unwind]
                i >= 5,
            no_unwind
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "only one `unwind` spec allowed")
}

test_verify_one_file! {
    #[test] requires_no_unwind_proof_fn verus_code! {
        proof fn f(i: u8)
            requires[no_unwind]
                i >= 5,
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "an `unwind` specification can only be given on exec functions")
}

test_verify_one_file! {
    #[test] ensures_on_unwind verus_code! {
        use vstd::prelude::*;

        fn may_unwind() {
        }

        fn f(i: u8)
            ensures[on unwind]
                i >= 10,
        {
            if i >= 10 {
                may_unwind();
            }
        }

        fn f_fail(i: u8)
            ensures[on unwind]
                i >= 10,
        {
            may_unwind(); // FAILS
        }

        // the callee's ensures[on unwind] can be assumed on its unwind path
        fn g(i: u8)
            ensures[on unwind]
                i >= 10,
        {
            f(i);
        }

        fn g_fail(i: u8)
            ensures[on unwind]
                i >= 11,
        {
            f(i); // FAILS
        }

        // ensures[on unwind] is not a precondition
        fn h() {
            f(3);
        }

        // multiple clauses are all checked
        fn multi(i: u8, j: u8)
            ensures[on unwind]
                i >= 10,
                j >= 10,
        {
            if i >= 10 {
                may_unwind(); // FAILS
            }
        }

        fn multi2(i: u8, j: u8)
            ensures[on unwind]
                i >= 10,
                j >= 10,
        {
            if i >= 10 && j >= 10 {
                may_unwind();
            }
            if j >= 10 {
                f(i);
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] ensures_on_unwind_syntax verus_code! {
        use vstd::prelude::*;

        fn may_unwind() {
        }

        fn f1(i: u8) -> (r: u8)
            requires
                i < 100,
            ensures
                r == i + 1,
            ensures[on unwind]
                i >= 10,
        {
            if i >= 10 {
                may_unwind();
            }
            i + 1
        }

        fn f2(i: u8) -> (r: u8)
            requires
                i < 100,
            ensures[on unwind]
                i >= 10,
            ensures
                r == i + 1,
        {
            if i >= 10 {
                may_unwind();
            }
            i + 1
        }

        fn test() {
            let r = f1(5);
            assert(r == 6);
            let r = f2(5);
            assert(r == 6);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ensures_on_unwind_with_no_unwind_when verus_code! {
        use vstd::prelude::*;

        fn may_unwind() {
        }

        fn nu(i: u8)
            no_unwind when i < 10
        {
            if i >= 10 {
                may_unwind();
            }
        }

        // the callee only unwinds when i >= 10
        fn f(i: u8)
            ensures[on unwind]
                i >= 10,
        {
            nu(i);
        }

        // the endpoint of the unwind path checks both the legacy `no_unwind when`
        // and `ensures[on unwind]`
        fn g(i: u8, j: u8)
            ensures[on unwind]
                j == 0,
            no_unwind when i < 10
        {
            if i >= 10 && j == 0 {
                may_unwind();
            }
            if i >= 10 {
                may_unwind(); // FAILS
            }
        }

        fn g2(i: u8, j: u8)
            ensures[on unwind]
                j == 0,
            no_unwind when i < 10
        {
            if j == 0 {
                may_unwind(); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] ensures_on_unwind_with_requires_no_unwind verus_code! {
        use vstd::prelude::*;

        fn may_unwind() {
        }

        fn r(i: u8)
            requires[no_unwind]
                i < 10,
        {
            if i >= 10 {
                may_unwind();
            }
        }

        // unwinding of r implies !(i < 10)
        #[verifier::restrict_unwind(false)]
        fn f(i: u8)
            ensures[on unwind]
                i >= 10,
        {
            r(i);
        }

        #[verifier::restrict_unwind(false)]
        fn f_fail(i: u8)
            ensures[on unwind]
                i >= 11,
        {
            r(i); // FAILS
        }

        // the endpoint of the unwind path checks the negation of requires[no_unwind]
        // and the ensures[on unwind] conditions
        fn g(i: u8, j: u8)
            requires[no_unwind]
                i < 10,
            ensures[on unwind]
                j == 0,
        {
            if i >= 10 && j == 0 {
                may_unwind();
            }
        }

        fn g_fail1(i: u8, j: u8)
            requires[no_unwind]
                i < 10,
            ensures[on unwind]
                j == 0,
        {
            if j == 0 {
                may_unwind(); // FAILS
            }
        }

        fn g_fail2(i: u8, j: u8)
            requires[no_unwind]
                i < 10,
            ensures[on unwind]
                j == 0,
        {
            if i >= 10 {
                may_unwind(); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] ensures_on_unwind_closure verus_code! {
        use vstd::prelude::*;

        fn may_unwind() {
        }

        // closure bodies are checked separately (closures may always unwind)
        fn f(i: u8)
            ensures[on unwind]
                i >= 10,
        {
            let c = || { may_unwind(); };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ensures_on_unwind_trait verus_code! {
        use vstd::prelude::*;

        fn may_unwind() {
        }

        trait T {
            fn m(&self, i: u8)
                ensures[on unwind]
                    i >= 5;
        }

        struct S;

        impl T for S {
            fn m(&self, i: u8) {
                if i >= 5 {
                    may_unwind();
                }
            }
        }

        struct S2;

        impl T for S2 {
            fn m(&self, i: u8) {
                may_unwind(); // FAILS
            }
        }

        fn test1<A: T>(a: &A, i: u8)
            ensures[on unwind]
                i >= 5,
        {
            a.m(i);
        }

        fn test2(s: &S, i: u8)
            ensures[on unwind]
                i >= 6,
        {
            s.m(i); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] ensures_on_unwind_trait_impl_not_allowed verus_code! {
        trait T {
            fn m(&self, i: u8);
        }

        struct S;

        impl T for S {
            fn m(&self, i: u8)
                ensures[on unwind]
                    i >= 5,
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "trait method implementation cannot declare `ensures[on unwind]` clauses")
}

test_verify_one_file! {
    #[test] ensures_on_unwind_assume_specification verus_code! {
        use vstd::prelude::*;

        #[verifier::external]
        fn ext(i: u8) -> u8 {
            if i == 0 { panic!() }
            i
        }

        pub assume_specification[ext](i: u8) -> (r: u8)
            ensures
                r == i,
            ensures[on unwind]
                i == 0;

        fn test1(i: u8)
            ensures[on unwind]
                i == 0,
        {
            let r = ext(i);
            assert(r == i);
        }

        fn test2(i: u8)
            ensures[on unwind]
                i == 1,
        {
            let r = ext(i); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] ensures_on_unwind_bad_syntax verus_code! {
        fn f(i: u8)
            ensures[on bogus]
                i >= 5,
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "expected `unwind`")
}

test_verify_one_file! {
    #[test] ensures_on_unwind_proof_fn verus_code! {
        proof fn f(i: u8)
            ensures[on unwind]
                i >= 5,
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "`ensures[on unwind]` clauses can only be given on exec functions")
}

test_verify_one_file! {
    #[test] ensures_on_unwind_private_field verus_code! {
        mod m {
            pub struct S { x: u8 }

            pub fn f(s: &S)
                ensures[on unwind]
                    s.x == 0,
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "disallowed: field expression for an opaque datatype")
}
