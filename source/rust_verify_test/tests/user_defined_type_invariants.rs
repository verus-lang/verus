#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] type_inv_conflict verus_code! {
        struct X {
            i: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                true
            }

            #[verifier::type_invariant]
            spec fn the_inv2(&self) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "multiple type invariants defined for the same type")
}

test_verify_one_file! {
    #[test] type_inv_nonstruct verus_code! {
        #[verifier::type_invariant]
        spec fn the_inv(i: u8) -> bool {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "expected parameter to be a datatype declared in this crate")
}

test_verify_one_file! {
    #[test] type_inv_defined_in_other_crate verus_code! {
        #[verifier::type_invariant]
        spec fn the_inv<T>(i: Option<T>) -> bool {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "expected parameter to be a datatype declared in this crate")
}

test_verify_one_file! {
    #[test] type_inv_return_nonbool verus_code! {
        struct X {
            i: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> u8 {
                20
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "#[verifier::type_invariant] function must return bool")
}

test_verify_one_file! {
    #[test] type_not_spec_fn verus_code! {
        struct X {
            i: u8,
        }

        impl X {
            #[verifier::type_invariant]
            proof fn the_inv(&self) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "#[verifier::type_invariant] function must be `spec`")
}

test_verify_one_file! {
    #[test] type_inv_trait_decl_fn verus_code! {
        struct X {
            i: u8,
        }

        trait Tr {
            #[verifier::type_invariant]
            spec fn the_inv(x: X) -> bool;
        }
    } => Err(err) => assert_vir_error_msg(err, "#[verifier::type_invariant] function cannot be a trait function")
}

test_verify_one_file! {
    #[test] type_inv_trait_impl_fn verus_code! {
        struct X {
            i: u8,
        }

        trait Tr {
            spec fn the_inv(&self) -> bool;
        }

        impl Tr for X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool { true }
        }
    } => Err(err) => assert_vir_error_msg(err, "#[verifier::type_invariant] function cannot be a trait function")
}

test_verify_one_file! {
    #[test] type_inv_no_recommends verus_code! {
        struct X {
            i: u8,
        }

        #[verifier::type_invariant]
        spec fn the_inv(x: X) -> bool
            recommends x.i >= 5,
        {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "#[verifier::type_invariant] function should not have a 'recommends' clause")
}

test_verify_one_file! {
    #[test] type_inv_no_when verus_code! {
        struct X {
            i: int,
        }

        #[verifier::type_invariant]
        spec fn the_inv(x: X) -> bool
            decreases x.i
            when x.i >= 0
        {
            the_inv(X { i: x.i - 1 })
        }
    } => Err(err) => assert_vir_error_msg(err, "#[verifier::type_invariant] function should not have a 'when' clause")
}

test_verify_one_file! {
    #[test] type_inv_wrong_num_args0 verus_code! {
        struct X {
            i: int,
        }

        #[verifier::type_invariant]
        spec fn the_inv() -> bool
        {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "#[verifier::type_invariant]: expected 1 parameter")
}

test_verify_one_file! {
    #[test] type_inv_wrong_num_args2 verus_code! {
        struct X {
            i: int,
        }

        #[verifier::type_invariant]
        spec fn the_inv(x: X, x2: X) -> bool
        {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "#[verifier::type_invariant]: expected 1 parameter")
}

test_verify_one_file! {
    #[test] type_inv_extra_generic_args verus_code! {
        struct X<T> {
            t: T,
            s: T,
            i: int,
        }

        #[verifier::type_invariant]
        spec fn the_inv<T, S>(x: X<T>) -> bool
        {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "expected generics to match")
}

test_verify_one_file! {
    #[test] type_inv_generic_args_wrong_order verus_code! {
        struct X<S, T> {
            t: T,
            s: S,
            i: int,
        }

        #[verifier::type_invariant]
        spec fn the_inv<T, S>(x: X<S, T>) -> bool
        {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "expected generics to match")
}

test_verify_one_file! {
    #[test] type_inv_extra_trait_bounds verus_code! {
        trait Tr { }
        trait Sr { }

        struct X<T: Tr> {
            t: T,
            s: T,
            i: int,
        }

        #[verifier::type_invariant]
        spec fn the_inv<T: Tr + Sr>(x: X<T>) -> bool {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "trait bounds should match")
}

test_verify_one_file! {
    #[test] type_inv_type_cycle1 verus_code! {
        struct X {
            i: int,
        }

        #[verifier::type_invariant]
        spec fn the_inv(x: X) -> bool {
            some_spec_fn(x.i)
        }

        spec fn some_spec_fn(i: int) -> bool
            decreases i via dcby
        {
            some_spec_fn(i - 1)
        }

        #[verifier::external_body]
        proof fn get_tracked_int() -> (tracked i: int) {
            unimplemented!();
        }

        #[verifier::decreases_by]
        proof fn dcby(i: int) {
            let tracked x = X { i: get_tracked_int() };
        }
    } => Err(err) => assert_vir_error_msg(err, "found cyclic dependency in decreases_by function")
}

test_verify_one_file! {
    #[test] type_inv_type_cycle_with_trait verus_code! {
        trait Tr {
            spec fn stuff(&self) -> bool;
        }

        struct X<T: Tr> {
            t: T,
            i: int,
        }

        #[verifier::type_invariant]
        spec fn the_inv<T: Tr>(x: X<T>) -> bool {
            T::stuff(&x.t)
        }

        struct Y { i: int }

        impl Tr for Y {
            spec fn stuff(&self) -> bool {
                some_spec_fn(self.i)
            }
        }

        spec fn some_spec_fn(i: int) -> bool
            decreases i via dcby
        {
            some_spec_fn(i - 1)
        }

        #[verifier::external_body]
        proof fn get_tracked_int() -> (tracked i: int) {
            unimplemented!();
        }

        #[verifier::decreases_by]
        proof fn dcby(i: int) {
            let tracked x = X::<Y> { t: Y { i: get_tracked_int() }, i: get_tracked_int() };
        }
    } => Err(err) => assert_vir_error_msg(err, "found cyclic dependency in decreases_by function")
}

test_verify_one_file! {
    #[test] test_ctors verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        fn test_exec1() {
            let a = X { i: 10, j: 100 };
        }

        fn test_exec2() {
            let a = X { i: 20, j: 100 }; // FAILS
        }

        fn test_exec3() {
            let a = X { i: 10, j: 100 };
            let b = X { i: 20, .. a }; // FAILS
        }

        proof fn tr_test_exec1() {
            let tracked a = X { i: 10u8, j: 100u8 };
        }

        proof fn tr_test_exec2() {
            let tracked a = X { i: 20u8, j: 100u8 }; // FAILS
        }

        proof fn tr_test_exec3() {
            let tracked a = X { i: 10u8, j: 100u8 };
            let tracked b = X { i: 20u8, .. a }; // FAILS
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 4)
}

test_verify_one_file! {
    #[test] test_ctor_spec_code verus_code! {
        proof fn tr_test_exec2() {
            // Currently, modes.rs identifies this as 'proof-mode'
            // with an immediate coercion to 'spec-mode'.
            // That's why Verus adds a check here. It would probably be better
            // to mark it as spec to begin with.
            let a = X { i: 20, j: 100 }; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_mut_ref_field_unwind_fail verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        fn test(i: &mut u8) {
        }

        fn test2() {
            let mut x = X { i: 10, j: 8 };
            test(&mut x.i);
        }
    } => Err(err) => assert_vir_error_msg(err, "this function call takes a &mut ref of a field of a datatype with a user-defined type invariant; thus, this function should be marked no_unwind")
}

test_verify_one_file! {
    #[test] test_mut_ref_field_nested_unwind_fail verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        struct Y {
            x: X,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        fn test(i: &mut u8) -> bool {
            true
        }

        fn test2() {
            let mut y = Y { x: X { i: 10, j: 8 } };
            let j = test(&mut y.x.i);
        }
    } => Err(err) => assert_vir_error_msg(err, "this function call takes a &mut ref of a field of a datatype with a user-defined type invariant; thus, this function should be marked no_unwind")
}

test_verify_one_file! {
    #[test] mut_ref_tests verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        struct Y {
            i: u8,
            j: u8,
        }

        impl Y {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                self.i == self.j
            }
        }

        fn mutate_int(i: &mut u8) no_unwind { }

        fn test1() {
            let mut x = X { i: 10, j: 8 };
            mutate_int(&mut x.j);
        }

        fn test2() {
            let mut x = X { i: 10, j: 8 };
            mutate_int(&mut x.i); // FAILS
        }


        fn mutate_int2(i: &mut u8, j: &mut u8)
            ensures *i == *j
            no_unwind
        {
            *i = 100;
            *j = 100;
        }

        fn test4() {
            let mut x = X { i: 10, j: 8 };
            mutate_int2(&mut x.i, &mut x.j); // FAILS
        }

        fn test5() {
            let mut y = Y { i: 8, j: 8 };
            mutate_int2(&mut y.i, &mut y.j);
        }

        struct Z {
            x: X,
            y: Y
        }

        impl Z {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                self.x.i == self.y.i
            }
        }

        fn mutate_int4_meet_all(a: &mut u8, b: &mut u8, c: &mut u8, d: &mut u8)
            ensures *a == 10, *b == 30, *c == 10, *d == 10
            no_unwind
        { assume(false); }

        fn mutate_int4_fail_x(a: &mut u8, b: &mut u8, c: &mut u8, d: &mut u8)
            ensures *a == 20, *b == 30, *c == 20, *d == 20
            no_unwind
        { assume(false); }

        fn mutate_int4_fail_y(a: &mut u8, b: &mut u8, c: &mut u8, d: &mut u8)
            ensures *a == 10, *b == 30, *c == 10, *d == 11
            no_unwind
        { assume(false); }

        fn mutate_int4_fail_z(a: &mut u8, b: &mut u8, c: &mut u8, d: &mut u8)
            ensures *a == 10, *b == 30, *c == 11, *d == 11
            no_unwind
        { assume(false); }

        fn test8() {
            let x = X { i: 8, j: 8 };
            let y = Y { i: 8, j: 8 };
            let mut z = Z { x, y };
            mutate_int4_meet_all(&mut z.x.i, &mut z.x.j, &mut z.y.i, &mut z.y.j);
        }

        fn test9() {
            let mut x = X { i: 8, j: 8 };
            let mut y = Y { i: 8, j: 8 };
            let mut z = Z { x, y };
            mutate_int4_fail_x(&mut z.x.i, &mut z.x.j, &mut z.y.i, &mut z.y.j); // FAILS
        }

        fn test10() {
            let mut x = X { i: 8, j: 8 };
            let mut y = Y { i: 8, j: 8 };
            let mut z = Z { x, y };
            mutate_int4_fail_y(&mut z.x.i, &mut z.x.j, &mut z.y.i, &mut z.y.j); // FAILS
        }

        fn test11() {
            let mut x = X { i: 8, j: 8 };
            let mut y = Y { i: 8, j: 8 };
            let mut z = Z { x, y };
            mutate_int4_fail_z(&mut z.x.i, &mut z.x.j, &mut z.y.i, &mut z.y.j); // FAILS
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 5)
}

test_verify_one_file! {
    #[test] mut_ref_nested_calls verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                self.i <= self.j
            }
        }

        fn set_to(i: &mut u8, x: u8, y: u8) -> (ret: u8)
            ensures *i == x, ret == y
            no_unwind
        {
            *i = x;
            y
        }

        fn test_nested_calls() {
            let mut x = X { i: 5, j: 10 };

            // Set i to 2; then set j to 3
            set_to(&mut x.j, set_to(&mut x.i, 2, 3), 0);
        }

        fn test_nested_calls2() {
            let mut x = X { i: 5, j: 10 };

            // Set j to 3; then set i to 2
            // in principle this could be ok but right now we put an assertion right after
            // the inner call.
            set_to(&mut x.i,
                set_to(&mut x.j, 3, 2) // FAILS
                , 0);
        }

        fn test_nested_calls3() {
            let mut x = X { i: 5, j: 10 };

            // This should definitely fail one way or another, either at the call
            // or at the assert
            set_to(&mut x.i,
                set_to(&mut x.j, 3, 2) // FAILS
                , {
                  assert(false);
                 0 });
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 2)
}

test_verify_one_file! {
    #[test] mut_ref_nested_calls_fail verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                self.i <= self.j
            }
        }

        fn set_to(i: &mut u8, x: u8, y: u8) -> (ret: u8)
            ensures *i == x, ret == y
            no_unwind
        {
            *i = x;
            y
        }

        fn test_nested_calls3() {
            let mut x = X { i: 5, j: 10 };

            // This should definitely fail one way or another, either at the call, the assert
            // or a lifetime error ...
            set_to(&mut x.i,
                set_to(&mut x.j, 3, 2) // FAILS
                , {
                  assert(x.the_inv());
                 0 });
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}

test_verify_one_file! {
    #[test] mut_ref_nested_calls_fail2 verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                self.i <= self.j
            }
        }

        fn set_to(i: &mut u8, x: u8, y: u8) -> (ret: u8)
            ensures *i == x, ret == y
            no_unwind
        {
            *i = x;
            y
        }

        fn test_nested_calls3() {
            let mut x = X { i: 5, j: 10 };

            set_to(&mut x.i,
                set_to(&mut x.j, 3, 2) // FAILS
                , {
                  proof { use_type_invariant(&x); }
                 0 });
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot borrow `x` as immutable because it is also borrowed as mutable")
}

test_verify_one_file! {
    #[test] mut_ref_nested_calls_fail3_two_phase_borrow verus_code! {
        struct Y(u8);
        struct X {
            i: Y,
            j: Y,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                self.i.0 <= self.j.0
            }
        }

        impl Y {
            fn set_to(&mut self, x: u8, y: u8) -> (ret: u8)
                ensures self.0 == x, ret == y
                no_unwind
            {
                self.0 = x;
                y
            }
        }

        fn test_nested_calls3() {
            let mut x = X { i: Y(5), j: Y(10) };

            // This should definitely fail one way or another, either at the call, the assert
            // or a lifetime error ...
            x.i.set_to(
                x.j.set_to(3, 2) // FAILS
                , {
                  assert(false);
                 0 });
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}

test_verify_one_file! {
    #[test] mut_ref_nested_calls_fail4_two_phase_borrow verus_code! {
        struct Y(u8);
        struct X {
            i: Y,
            j: Y,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                self.i.0 <= self.j.0
            }
        }

        impl Y {
            fn set_to(&mut self, x: u8, y: u8) -> (ret: u8)
                ensures self.0 == x, ret == y
                no_unwind
            {
                self.0 = x;
                y
            }
        }

        fn test_nested_calls3() {
            let mut x = X { i: Y(5), j: Y(10) };

            // This should definitely fail one way or another, either at the call, the assert
            // or a lifetime error ...
            x.i.set_to(
                x.j.set_to(3, 2) // FAILS
                , {
                  assert(x.the_inv());
                 0 });
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}

test_verify_one_file! {
    #[test] mut_ref_nested_calls_fail5_two_phase_borrow verus_code! {
        struct Y(u8);
        struct X {
            i: Y,
            j: Y,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                self.i.0 <= self.j.0
            }
        }

        impl Y {
            fn set_to(&mut self, x: u8, y: u8) -> (ret: u8)
                ensures self.0 == x, ret == y
                no_unwind
            {
                self.0 = x;
                y
            }
        }

        fn test_nested_calls3() {
            let mut x = X { i: Y(5), j: Y(10) };

            // This should definitely fail ... somewhere
            // Right now, we call it a lifetime error, but that's because Verus
            // lifetime-generate doesn't handle two-phase borrows correctly.
            // therefore, the error message here will probably change once we support
            // two-phase borrows. Either way, it needs to be an error.

            x.i.set_to(
                x.j.set_to(3, 2)
                , {
                  proof { use_type_invariant(&x); }
                 0 });
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot borrow `x` as immutable because it is also borrowed as mutable")
}

test_verify_one_file! {
    #[test] test_mut_ref_whole_ok verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        fn test(x: &mut X) {
            x.i = 7;
        }

        fn test2() {
            let mut x = X { i: 10, j: 8 };
            test(&mut x);
        }

        fn test3(x: &mut X, x2: X) {
            *x = x2;
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mut_ref_whole_fail verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        fn test(x: &mut X) {
            x.i = 100; // FAILS
        }

        fn test2() {
            let mut x = X { i: 10, j: 8 };
            test(&mut x);
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}

test_verify_one_file! {
    #[test] test_mut_ref_nested verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        struct Y {
            x: X,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        impl Y {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                20 <= self.x.j < 30
            }
        }

        fn test(y: &mut Y) {
            y            // FAILS
              .x.i = 19; // FAILS
        }

        fn test2(y: &mut Y) {
            y.x.j = 45; // FAILS
        }

        fn test_ok(y: &mut Y)
            requires old(y).x.j == 26
        {
            y.x.i = 10;
            y.x.j = 25;
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 3)
}

test_verify_one_file! {
    #[test] test_mut_ref_nested_compound verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        struct Y {
            x: X,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        impl Y {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                20 <= self.x.j < 30
            }
        }

        fn test_assign_op(y: &mut Y)
            requires old(y).x.i < 100
        {
            y.x.i += 2; // FAILS
        }

        fn test2_assign_op(y: &mut Y)
            requires old(y).x.j < 100
        {
            y.x.j += 2; // FAILS
        }

        fn test3_assign_op(x: &mut X)
            requires old(x).i + 4 < 100
        {
            x.i += 4; // FAILS
        }

    } => Err(err) => assert_vir_error_msg(err, "not yet implemented: lhs of compound assignment")
        //assert_fails_type_invariant_error(err, 3)
}

test_verify_one_file! {
    #[test] test_mut_ref_assign_call verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        struct Y {
            x: X,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        impl Y {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                20 <= self.x.j < 30
            }
        }

        fn get_i() -> (res: u8) ensures res == 10 { 10 }
        fn get_i_bad() -> (res: u8) ensures res == 102 { 102 }

        fn get_j() -> (res: u8) ensures res == 25 { 25 }
        fn get_j_bad() -> (res: u8) ensures res == 102 { 102 }

        fn test1(y: &mut Y)
            requires 20 <= old(y).x.j < 30, 0 <= old(y).x.i < 15
        {
            y.x.i = get_i();
        }

        fn test1_bad(y: &mut Y)
            requires 20 <= old(y).x.j < 30, 0 <= old(y).x.i < 15
        {
            y.x.i = get_i_bad(); // FAILS
        }

        fn test2(y: &mut Y)
            requires 20 <= old(y).x.j < 30, 0 <= old(y).x.i < 15
        {
            y.x.j = get_j();
        }

        fn test2_bad(y: &mut Y)
            requires 20 <= old(y).x.j < 30, 0 <= old(y).x.i < 15
        {
            y.x.j = get_j_bad(); // FAILS
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 2)
}

test_verify_one_file! {
    #[test] test_normal_var_whole_fail verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        fn test() {
            let mut x = X { i: 10, j: 123 };
            x.i = 100; // FAILS
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}

test_verify_one_file! {
    #[test] test_normal_var_nested verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        struct Y {
            x: X,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        impl Y {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                20 <= self.x.j < 30
            }
        }

        fn test() {
            let mut y = Y { x: X { i: 12, j: 25 } };
            y.x.i = 19; // FAILS
        }

        fn test2() {
            let mut y = Y { x: X { i: 12, j: 25 } };
            y.x.j = 45; // FAILS
        }

        fn test_ok() {
            let mut y = Y { x: X { i: 12, j: 25 } };
            y.x.i = 10;
            y.x.j = 25;
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 2)
}

test_verify_one_file! {
    #[test] test_normal_var_nested_compound verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        struct Y {
            x: X,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        impl Y {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                20 <= self.x.j < 30
            }
        }

        fn test_assign_op() {
            let mut y = Y { x: X { i: 12, j: 25 } };
            y.x.i += 2; // FAILS
        }

        fn test2_assign_op() {
            let mut y = Y { x: X { i: 12, j: 25 } };
            y.x.j += 2; // FAILS
        }

        fn test3_assign_op() {
            let mut x = X { i: 14, j: 123 };
            x.i += 4; // FAILS
        }

        fn test4_assign_op_ok() {
            let mut x = X { i: 2, j: 123 };
            x.i += 4;
        }
    } => Err(err) => assert_vir_error_msg(err, "not yet implemented: lhs of compound assignment")
    //assert_fails_type_invariant_error(err, 3)
}

test_verify_one_file! {
    #[test] test_normal_var_assign_call verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        struct Y {
            x: X,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        impl Y {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                20 <= self.x.j < 30
            }
        }

        fn get_i() -> (res: u8) ensures res == 10 { 10 }
        fn get_i_bad() -> (res: u8) ensures res == 102 { 102 }

        fn get_j() -> (res: u8) ensures res == 25 { 25 }
        fn get_j_bad() -> (res: u8) ensures res == 102 { 102 }

        fn test1() {
            let mut y = Y { x: X { i: 12, j: 25 } };
            y.x.i = get_i();
        }

        fn test1_bad() {
            let mut y = Y { x: X { i: 12, j: 25 } };
            y.x.i = get_i_bad(); // FAILS
        }

        fn test2() {
            let mut y = Y { x: X { i: 12, j: 25 } };
            y.x.j = get_j();
        }

        fn test2_bad() {
            let mut y = Y { x: X { i: 12, j: 25 } };
            y.x.j = get_j_bad(); // FAILS
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 2)
}

test_verify_one_file! {
    #[test] assignment_to_spec_code_ok verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        proof fn test() {
            let mut x = X { i: 5, j: 20 };
            x.i = 20; // this is ok because x is spec-mode
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assignment_to_tracked_needs_check verus_code! {
        tracked struct X {
            ghost i: int,
            ghost j: int,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        proof fn test() {
            // i is a ghost field but this still needs a check because
            // it modifies x
            let tracked mut x = X { i: 5, j: 20 };
            x.i = 20; // FAILS
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}

test_verify_one_file! {
    #[test] assignment_to_tracked_needs_check_nested_with_ghost verus_code! {
        ghost struct Y {
            t: int,
        }

        tracked struct X {
            ghost i: int,
            ghost j: int,
            ghost y: Y,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
                  && self.y.t < 40
            }
        }

        proof fn test() {
            let tracked mut x = X { i: 5, j: 20, y: Y { t: 18 } };
            x.y.t = 50; // FAILS
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}

test_verify_one_file! {
    #[test] test_with_generics verus_code! {
        struct X<T> {
            i: T,
            j: T,
        }

        struct Y<T> {
            x: X<T>,
        }

        impl<T> X<T> {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                self.i == self.j
            }
        }

        fn test_ok() {
            let x = X::<u8> { i: 5, j: 5 };
        }

        fn test_fail() {
            let x = X::<u8> { i: 5, j: 7 }; // FAILS
        }

        fn test_ok2<T: Copy>(a: T) {
            let x = X::<T> { i: a, j: a };
        }

        fn test_fail2<T>(a: T, b: T) {
            let x = X::<T> { i: a, j: b }; // FAILS
        }

        fn test_fail3<T>(a: &mut X<T>, b: T) {
            a.i = b; // FAILS
        }

        fn test_fail4<T>(a: &mut Y<T>, b: T) {
            a.x.i = b; // FAILS
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 4)
}

test_verify_one_file! {
    #[test] test_with_generics_and_traits verus_code! {
        trait Tr {
            spec fn is_good(&self) -> bool;
        }

        struct X<T: Tr> {
            i: T,
            j: T,
        }

        struct Y<T: Tr> {
            x: X<T>,
        }

        impl<T: Tr> X<T> {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                self.i.is_good()
            }
        }

        impl Tr for u8 {
            spec fn is_good(&self) -> bool {
                0 <= *self < 15
            }
        }

        fn test_ok() {
            let x = X::<u8> { i: 5, j: 7 };
        }

        fn test_fail() {
            let x = X::<u8> { i: 20, j: 7 }; // FAILS
        }

        fn test_ok2<T: Copy + Tr>(a: T)
            requires a.is_good()
        {
            let x = X::<T> { i: a, j: a };
        }

        fn test_fail2<T: Tr>(a: T, b: T)
            requires b.is_good()
        {
            let x = X::<T> { i: a, j: b }; // FAILS
        }

        fn test_fail3<T: Tr>(a: &mut X<T>, b: T) {
            a.i = b; // FAILS
        }

        fn test_fail4<T: Tr>(a: &mut Y<T>, b: T) {
            a.x.i = b; // FAILS
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 4)
}

test_verify_one_file! {
    #[test] test_body_is_closed verus_code! {
        mod m {
            use super::*;

            pub(crate) struct X {
                pub i: u8,
                pub j: u8,
            }

            impl X {
                #[verifier::type_invariant]
                pub(crate) closed spec fn the_inv(&self) -> bool {
                    self.i == self.j
                }
            }
        }

        use m::*;

        fn test() {
            // this fails because we can't see the body of `the_inv`
            // we should probably make this a warning or something
            let j = X { i: 5, j: 5 }; // FAILS
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}

test_verify_one_file! {
    #[test] test_inv_is_private1 verus_code! {
        mod m {
            use super::*;

            pub(crate) struct X {
                pub i: u8,
                pub j: u8,
            }

            impl X {
                #[verifier::type_invariant]
                closed spec fn the_inv(&self) -> bool {
                    self.i == self.j
                }
            }
        }

        use m::*;

        fn test() {
            let j = X { i: 5, j: 5 };
        }
    } => Err(err) => assert_vir_error_msg(err, "type invariant function is not visible to this program point")
}

test_verify_one_file! {
    #[test] test_inv_is_private2 verus_code! {
        mod m {
            use super::*;

            pub(crate) struct X {
                pub i: u8,
                pub j: u8,
            }

            impl X {
                #[verifier::type_invariant]
                closed spec fn the_inv(&self) -> bool {
                    self.i == self.j
                }
            }
        }

        use m::*;

        fn test(x: X) {
            let mut y = x;
            y.i = 20;
        }
    } => Err(err) => assert_vir_error_msg(err, "type invariant function is not visible to this program point")
}

test_verify_one_file! {
    #[test] test_inv_is_private3 verus_code! {
        mod m {
            use super::*;

            pub(crate) struct X {
                pub i: u8,
                pub j: u8,
            }

            impl X {
                #[verifier::type_invariant]
                closed spec fn the_inv(&self) -> bool {
                    self.i == self.j
                }
            }
        }

        use m::*;

        fn stuff(i: &mut u8) { }

        fn test(x: X) {
            let mut y = x;
            stuff(&mut y.i);
        }
    } => Err(err) => assert_vir_error_msg(err, "type invariant function is not visible to this program point")
}

test_verify_one_file! {
    #[test] test_inv_implies_fields_private_to_crate verus_code! {
        pub struct X {
            pub f: u8,
        }

        impl X {
            #[verifier::type_invariant]
            pub open spec fn the_inv(&self) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a struct with a type invariant cannot have any fields public to the crate")
}

test_verify_one_file! {
    #[test] test_enum verus_code! {
        enum X {
            Foo(u8),
            Bar(u16),
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                match *self {
                    X::Foo(a) => 2 <= a <= 10,
                    X::Bar(b) => 20 <= b <= 30,
                }
            }
        }

        fn test1() {
            let x = X::Foo(6);
        }

        fn test2() {
            let x = X::Foo(15); // FAILS
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}

test_verify_one_file! {
    #[test] test_union_not_supported verus_code! {
        pub union X {
            u: u8,
            j: u16,
        }

        #[verifier::type_invariant]
        pub open spec fn the_inv(x: X) -> bool {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "not supported: #[verifier::type_invariant] for union types")
}

test_verify_one_file! {
    #[test] ctor_in_dual_exec_spec_const verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        const x: X = X { i: 20, j: 5 } // FAILS
            ;
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}

test_verify_one_file! {
    #[test] get_assumption verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        proof fn test_proof_mode(tracked x: X) {
            use_type_invariant(&x);
            // ok
            assert(0 <= x.i < 15);
        }

        fn test(x: X) {
            proof { use_type_invariant(&x); }
            // ok
            assert(0 <= x.i < 15);
        }

        fn test_tracked_type(x: Tracked<X>) {
            proof { use_type_invariant(&x); }
            // ok
            assert(0 <= x@.i < 15);
        }

        fn test_fail() {
            let x = X { i: 20, j: 20 }; // FAILS
            proof { use_type_invariant(&x); }
        }

        fn test_fail2() {
            let mut x = X { i: 2, j: 20 };
            x.i = 20; // FAILS
            proof { use_type_invariant(&x); }
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 2)
}

test_verify_one_file! {
    #[test] get_assumption_fail_moved verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        fn throw_away(x: X) { }

        fn test_move(x: X) {
            throw_away(x);
            // This specific case would actually be ok to allow
            proof { use_type_invariant(&x); }
        }
    } => Err(err) => assert_vir_error_msg(err, "borrow of moved value: `x`")
}

test_verify_one_file! {
    #[test] get_assumption_fail_uninitialized verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        fn test_unassigned() {
            let x: X;
            proof { use_type_invariant(&x); }
        }
    } => Err(err) => assert_vir_error_msg(err, "used binding `x` isn't initialized")
}

test_verify_one_file! {
    #[test] get_assumption_fail_uninitialized_proof_mode verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        proof fn test_unassigned() {
            let tracked x: X;
            use_type_invariant(&x);
        }
    } => Err(err) => assert_vir_error_msg(err, "used binding `x` isn't initialized")
}

test_verify_one_file! {
    #[test] get_assumption_fail_not_datatype verus_code! {
        fn test_int(x: int) {
            proof { use_type_invariant(&x); }
        }
    } => Err(err) => assert_vir_error_msg(err, "this type is not a datatype")
}

test_verify_one_file! {
    #[test] get_assumption_fail_no_invariant verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        fn test_normal_struct(x: X) {
            proof { use_type_invariant(&x); }
        }
    } => Err(err) => assert_vir_error_msg(err, "this type does not have any type invariant")
}

test_verify_one_file! {
    #[test] get_assumption_fail_private_invariant verus_code! {
        mod hello_mod {
            pub struct X {
                i: u8,
                j: u8,
            }

            impl X {
                #[verifier::type_invariant]
                spec fn the_inv(&self) -> bool {
                    0 <= self.i < 15
                }
            }
        }

        fn test_normal_struct(x: hello_mod::X) {
            proof { use_type_invariant(&x); }
        }
    } => Err(err) => assert_vir_error_msg(err, "type invariant function is not visible to this program point")
}

test_verify_one_file! {
    #[test] get_assumption_fail_ghost_type verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        fn test_tracked_type(x: Ghost<X>) {
            proof { use_type_invariant(&x); }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot apply use_type_invariant for Ghost<_>")
}

test_verify_one_file! {
    #[test] assert_type_inv_assign_ghost_type verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        impl X {
            #[verifier::type_invariant]
            spec fn the_inv(&self) -> bool {
                0 <= self.i < 15
            }
        }

        fn test_ghost_type(x: Ghost<X>) {
            let mut y = x;
            proof {
                let i = 22;
                let j = 88;
                // this is ok because it's all spec-mode
                y@ = X { i, j };
            }
        }

        fn test_tracked_type(x: Tracked<X>) {
            let tracked mut y = x;
            let i = 22;
            let j = 88;
            proof {
                y@ = X { i, j }; // FAILS
            }
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}
