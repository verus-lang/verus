#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] distinguish_returns_and_implict_units verus_code! {
        fn test_return_from_else(b: bool) {
            let x = if b {
                1
            } else {
                return;
            };
            assert(b);
            assert(x == 1);
        }

        fn test_return_from_if(b: bool) {
            let x = if b {
                return;
            } else {
                1
            };
            assert(!b);
            assert(x == 1);
        }

        pub enum Foo { A, B }

        fn test_return_from_match(foo: Foo) {
            let x = match foo {
                Foo::A => { return; }
                Foo::B => { 7 }
            };
            assert(x == 7);
            assert(match foo { Foo::A => false, Foo::B => true });
        }

        fn test_return_from_both(b: bool) {
            let x = if b { return; } else { return; };
            assert(false); // can't get here
        }

        fn test_return_from_both2(b: bool) {
            let x;
            x = if b { return; } else { return; };
            assert(false); // can't get here
        }

        // make sure we correctly distinguish the 'return' cases from implicit unit cases

        fn test_implicit_unit_block(b: bool) {
            let x = { };
            assert(equal(x, ()));
        }

        fn test_implicit_unit_block2(b: bool) {
            let x;
            x = { };
            assert(equal(x, ()));
        }

        fn test_implicit_unit_from_both(b: bool) {
            let x = if b { } else { };
            assert(equal(x, ()));
        }

        fn test_implicit_unit_from_both2(b: bool) {
            let x;
            x = if b { } else { };
            assert(equal(x, ()));
        }

        fn test_implicit_unit_from_left(b: bool) {
            let x = if b { () } else { };
            assert(equal(x, ()));
        }

        fn test_implicit_unit_from_left2(b: bool) {
            let x;
            x = if b { () } else { };
            assert(equal(x, ()));
        }

        fn test_implicit_unit_from_right(b: bool) {
            let x = if b { } else { () };
            assert(equal(x, ()));
        }

        fn test_implicit_unit_from_right2(b: bool) {
            let x;
            x = if b { } else { () };
            assert(equal(x, ()));
        }

        fn test_add_u32_and_never() -> u32 {
            ensures(|r: u32| r < 3);
            let x: u32 = {return 1; 3};
            let y: u32 = {return 2;};
            x + y
        }

        fn test_final_stmt_return() -> u8 {
            ensures(|y: u8| y == 5);
            return 5;
        }

        fn never_short_circuit_left() {
            let x = { return; } || true;
            assert(false);
        }

        fn never_short_circuit_right(b: bool) {
            let x = b || { return; };
            assert(b);
        }

        fn never_binop_left(b: bool) {
            let x = { return; 7 } + 5;
            assert(false);
        }

        fn never_binop_left2(b: bool) {
            let x = { return; 7 } + { assert(false); 5 };
        }

        fn never_binop_right(b: bool) {
            let x = 5 + { return; 7 };
            assert(false);
        }

        fn never_in_conditional(b: bool) {
            if { return; true } {
                assert(false);
            } else {
                assert(false);
            }
        }

        fn never_in_return() -> (i: u8)
            ensures i == 3
        {
            return { return 3; 5 };
        }

        fn return_return() -> (i: u8)
            ensures i == 3
        {
            return 3;
            return 5;
        }

        fn return_return2() -> (i: u8)
            ensures i == 3
        {
            return 3;
            5
        }

        fn if_unit_no_else() {
            let x = if true { () };
            assert(equal(x, ()));
        }

        fn if_let(b: bool) {
            let r = if b { let mut x = 5; x = 7; x } else { return; };
            assert(r == 7);
        }
    } => Ok(_err) => { /* allow unreachable warnings */ }
}

test_verify_one_file! {
    #[test] postconditions_fail_in_returns_in_conditional verus_code! {
        fn postcondition_fail_if(b: bool)
            ensures false
        {
            let x = if b {
                5
            } else {
                return; // FAILS
            };
            assume(false);
        }

        fn postcondition_fail_else(b: bool)
            ensures false
        {
            let x = if b {
                return; // FAILS
            } else {
                5
            };
            assume(false);
        }

        fn postcondition_fail_if_value(b: bool) -> (i: u8)
            ensures i == 4
        {
            let x = if b {
                return 7; // FAILS
            } else {
                5
            };
            4
        }

        fn postcondition_fail_else_value(b: bool) -> (i: u8)
            ensures i == 4
        {
            let x = if b {
                5
            } else {
                return 7; // FAILS
            };
            4
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] return_from_if_else_fail verus_code! {
        fn test_return_from_else(b: bool) {
            let x = if b {
                1
            } else {
                return;
            };
            assert(b);
            assert(x == 1);
            assert(false); // FAILS
        }

        fn test_return_from_if(b: bool) {
            let x = if b {
                return;
            } else {
                1
            };
            assert(!b);
            assert(x == 1);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] return_from_match_fail verus_code! {
        pub enum Foo { A, B }

        fn test_return_from_match(foo: Foo) {
            let x = match foo {
                Foo::A => { return; }
                Foo::B => { 7 }
            };
            assert(x == 7);
            assert(match foo { Foo::A => false, Foo::B => true });
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] implicit_unit_block_fail verus_code! {
        fn test_implicit_unit_block(b: bool) {
            let x = { };
            assert(equal(x, ()));
            assert(false); // FAILS
        }

        fn test_implicit_unit_block2(b: bool) {
            let x;
            x = { };
            assert(equal(x, ()));
            assert(false); // FAILS
        }

        fn test_implicit_unit_from_both(b: bool) {
            let x = if b { } else { };
            assert(equal(x, ()));
            assert(false); // FAILS
        }

        fn test_implicit_unit_from_both2(b: bool) {
            let x;
            x = if b { } else { };
            assert(equal(x, ()));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] implicit_unit_conditional_fail verus_code! {
        fn test_implicit_unit_from_left(b: bool) {
            let x = if b { () } else { };
            assert(equal(x, ()));
            assert(false); // FAILS
        }

        fn test_implicit_unit_from_left2(b: bool) {
            let x;
            x = if b { () } else { };
            assert(equal(x, ()));
            assert(false); // FAILS
        }

        fn test_implicit_unit_from_right(b: bool) {
            let x = if b { } else { () };
            assert(equal(x, ()));
            assert(false); // FAILS
        }

        fn test_implicit_unit_from_right2(b: bool) {
            let x;
            x = if b { } else { () };
            assert(equal(x, ()));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] return_in_let_fail verus_code! {
        fn test_add_u32_and_never() -> (r: u32)
            ensures r > 3
        {
            let x: u32 = {
              return 1; // FAILS
              3
            };
            let y: u32 = {return 2;};
            x + y
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] final_stmt_return_fail verus_code! {
        fn test_final_stmt_return() -> (y: u8)
            ensures y == 6
        {
            return 5; // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] short_circuit_returns_fail verus_code! {
        fn never_short_circuit_left() {
            let x = {
                assert(false); // FAILS
                return;
            } || true;
        }

        fn never_short_circuit_right(b: bool) {
            let x = b || { return; };
            assert(false); // FAILS
        }

        fn never_binop_left(b: bool) {
            let x = {
                assert(false); // FAILS
                return;
                7
            } + 5;
        }

        fn never_binop_left2(b: bool) {
            let x = {
                assert(false); // FAILS
                return;
                7
            } + { assert(false); 5 };
        }

        fn never_binop_right(b: bool) {
            let x = {
                assert(false); // FAILS
                5
            } + { return; 7 };
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file! {
    #[test] misc_never_returns_fail verus_code! {
        fn never_in_conditional(b: bool) -> (y: u8)
            ensures y == 7
        {
            let mut x = 7;
            if {
                x = 5;
                return x; // FAILS
                true
            } {
                assert(false);
            } else {
                assert(false);
            }

            return 9;
        }

        fn never_in_return() -> (i: u8)
            ensures i == 5
        {
            return {
                return 3; // FAILS
                5
            };
        }

        fn return_return() -> (i: u8)
            ensures i == 5
        {
            return 3; // FAILS
            return 5;
        }

        fn return_return2() -> (i: u8)
            ensures i == 5
        {
            return 3; // FAILS
            5
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] conditionals_units_return_fail verus_code! {
        fn if_unit_no_else() {
            let x = if true { () };
            assert(false); // FAILS
        }

        fn if_let(b: bool) {
            let r = if b { let mut x = 5; x = 7; x } else { return; };
            assert(r == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] block_with_no_return_as_arg verus_code! {
        fn foo(x: u8) {

        }

        fn main() {
            foo({ return; });
            assert(false);
        }
    } => Ok(_err) => { /* allow unreachable warnings */ }
}

test_verify_one_file! {
    #[test] block_with_no_return_as_arg2 verus_code! {
        fn foo(x: ()) {

        }

        fn x() {
            foo({ return; });
            assert(false);
        }
    } => Ok(_err) => { /* allow unreachable warnings */ }
}

test_verify_one_file! {
    #[test] block_with_no_return_as_arg3 verus_code! {
        fn foo(x: u8) {
        }

        fn bar() { }

        fn main() {
            foo({ return; bar(); });
            assert(false);
        }
    } => Ok(_err) => { /* allow unreachable warnings */ }
}

test_verify_one_file! {
    #[test] conditional_with_infinite_loop verus_code! {
        fn main(b: bool) {
            let x = if b {
                1
            } else {
                loop { }
            };
            assert(x == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] conditional_with_infinite_while_loop verus_code! {
        fn foo(b: bool) {
            let x = if b {
                1
            } else {
                while true { }
                5
            };
            assert(x == 1);
        }
    } => Ok(_err) => { /* allow unreachable warnings */ }
}

test_verify_one_file! {
    #[test] return_inside_while verus_code! {
        fn foo(b: bool) {
            let mut x = 5;
            while b
                invariant x == 5
            {

                x = 6;
                return;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] return_value_in_one_match_arm verus_code! {
        enum TreeSortedness {
            Unsorted,
            Empty,
        }

        fn moo(left_sortedness: TreeSortedness, b: bool) -> TreeSortedness {
            let x;
            match left_sortedness {
                TreeSortedness::Unsorted => return TreeSortedness::Unsorted,
                TreeSortedness::Empty => { x = 5; }
            }
            assert(x == 5);
            TreeSortedness::Unsorted
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] requires_in_conditional_pure verus_code! {
        fn f(b: bool) -> bool
            requires b
        {
            true
        }

        fn test() -> u64 {
            if f(false) { // FAILS
                20
            } else {
                30
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] requires_in_conditional_impure verus_code! {
        fn f(b: bool) -> bool
            requires b
        {
            true
        }

        fn test() -> u64 {
            let mut a = 5;
            if f(false) { // FAILS
                a = 7;
                a
            } else {
                30
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] requires_in_conditional_implicit_unit verus_code! {
        fn f(b: bool) -> bool
            requires b
        {
            true
        }

        fn test() -> u64 {
            let mut a = 5;
            if f(false) { // FAILS
                a = 7;
            } else {
                a = 9;
            }
            a
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] requires_in_conditional_never verus_code! {
        fn f(b: bool) -> bool
            requires b
        {
            true
        }

        fn test() -> u64 {
            if f(false) { // FAILS
                let a = 5;
            } else {
                return 9;
            }
            12
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] closure_call_eval_order ["vstd"] => verus_code! {
        // REVIEW: exec closures implicitly rely on vstd
        fn test(x1: bool, x2: bool) {
            let f = |i: u64, b: bool| {
                if b { i } else { 0 }
            };

            ({ assume(x1); f })(
              ({ assert(x1); assume(x2); 20 }),
              ({ assert(x2); false })
            );
        }

        fn test_never_return_1() {
            let f = |i: u64, b: bool| {
                if b { i } else { 0 }
            };

            ({ loop { } f })(
              ({ assert(false); 20 }),
              ({ assert(false); false })
            );
        }

        fn test_never_return_2() {
            let f = |i: u64, b: bool| {
                if b { i } else { 0 }
            };

            ({ f })(
              ({ loop { } 20 }),
              ({ assert(false); false })
            );
        }
    } => Ok(_err) => { /* allow unreachable warnings */ }
}

test_verify_one_file! {
    #[test] expressions_with_no_side_effects verus_code! {
        spec fn some_int(x: int) -> int {
            x
        }

        proof fn proof_fn() {
            some_int(12);
            assert(false); // FAILS
        }

        proof fn require_false_return_int() -> int
            requires false,
        {
            13
        }

        proof fn proof_fn2() {
            7 +
                require_false_return_int(); // FAILS
        }


        fn exec_fn() {
            5;
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}
