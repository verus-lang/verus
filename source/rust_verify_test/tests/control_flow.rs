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

test_verify_one_file_with_options! {
    #[test] conditional_with_infinite_loop ["exec_allows_no_decreases_clause"] => verus_code! {
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

test_verify_one_file_with_options! {
    #[test] conditional_with_infinite_while_loop ["exec_allows_no_decreases_clause"] => verus_code! {
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
                invariant x == 5,
                decreases 6 - x,
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
    #[test] closure_call_eval_order ["vstd", "exec_allows_no_decreases_clause"] => verus_code! {
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

test_verify_one_file! {
    #[test] side_effects_in_arg_call verus_code! {
        fn foo(x: u64, y: u64) -> (ret: (u64, u64))
            ensures ret == (x, y)
        {
            (x, y)
        }

        fn test_fails() {
            let mut x = 24;
            let mut y = 30;

            let z = foo(x, ({ x = 60; y }));

            assert(z === (60, 30)); // FAILS
        }

        fn test_ok() {
            let mut x = 24;
            let mut y = 30;

            let z = foo(x, ({ x = 60; y }));

            assert(z === (24, 30));
            assert(x == 60);
        }

        fn test2_fails() {
            let mut x = 24;
            let mut y = 30;

            let z = foo(({ x = 60; y }), x);

            assert(z === (30, 24)); // FAILS
        }

        fn test3_ok() {
            let mut x = 24;
            let mut y = 30;

            let z = foo(({ x = 60; x }), ({ x = 80; x }));

            assert(z === (60, 80));
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] side_effects_in_arg_tuple_ctor verus_code! {
        fn test_fails() {
            let mut x = 24;
            let mut y = 30;

            let z = (x, ({ x = 60; y }));

            assert(z === (60, 30)); // FAILS
        }

        fn test_ok() {
            let mut x = 24;
            let mut y = 30;

            let z = (x, ({ x = 60; y }));

            assert(z === (24, 30));
            assert(x == 60);
        }

        fn test2_fails() {
            let mut x = 24;
            let mut y = 30;

            let z = (({ x = 60; y }), x);

            assert(z === (30, 24)); // FAILS
        }

        fn test2_ok() {
            let mut x = 24;
            let mut y = 30;

            let z = (({ x = 60; y }), x);

            assert(z === (30, 60));
            assert(x == 60);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] side_effects_in_arg_paren_style_ctor verus_code! {
        struct Foo(u64, u64);

        fn test_fails() {
            let mut x = 24;
            let mut y = 30;

            let z = Foo(x, ({ x = 60; y }));

            assert(z === Foo(60, 30)); // FAILS
        }

        fn test_ok() {
            let mut x = 24;
            let mut y = 30;

            let z = Foo(x, ({ x = 60; y }));

            assert(z === Foo(24, 30));
            assert(x == 60);
        }

        fn test2_fails() {
            let mut x = 24;
            let mut y = 30;

            let z = Foo(({ x = 60; y }), x);

            assert(z === Foo(30, 24)); // FAILS
        }

        fn test2_ok() {
            let mut x = 24;
            let mut y = 30;

            let z = Foo(({ x = 60; y }), x);

            assert(z === Foo(30, 60));
            assert(x == 60);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] side_effects_in_arg_struct_style_ctor verus_code! {
        struct Foo { b: u64, a: u64 }

        fn test_fails() {
            let mut x = 24;
            let mut y = 30;

            let z = Foo { a: x, b: ({ x = 60; y }) };

            assert(z === Foo { a: 60, b: 30 }); // FAILS
        }

        fn test_ok() {
            let mut x = 24;
            let mut y = 30;

            let z = Foo { a: x, b: ({ x = 60; y }) };

            assert(z === Foo { a: 24, b: 30 });
            assert(x == 60);
        }

        fn test2_fails() {
            let mut x = 24;
            let mut y = 30;

            let z = Foo { a: ({ x = 60; y }), b: x };

            assert(z === Foo { a: 30, b: 24 }); // FAILS
        }

        fn test2_ok() {
            let mut x = 24;
            let mut y = 30;

            let z = Foo { a: ({ x = 60; y }), b: x };

            assert(z === Foo { a: 30, b: 60 });
            assert(x == 60);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] side_effects_in_arg_struct_style_ctor_with_update verus_code! {
        struct Foo { b: u64, a: u64, c: u64 }

        fn test_fails() {
            let foo0 = Foo { a: 0, b: 0, c: 19 };

            let mut x = 24;
            let mut y = 30;

            let z = Foo { a: x, b: ({ x = 60; y }), ..foo0 };

            assert(z === Foo { a: 60, b: 30, c: 19 }); // FAILS
        }

        fn test_ok() {
            let foo0 = Foo { a: 0, b: 0, c: 19 };

            let mut x = 24;
            let mut y = 30;

            let z = Foo { a: x, b: ({ x = 60; y }), ..foo0 };

            assert(z === Foo { a: 24, b: 30, c: 19 });
            assert(x == 60);
        }

        fn test2_fails() {
            let foo0 = Foo { a: 0, b: 0, c: 19 };

            let mut x = 24;
            let mut y = 30;

            let z = Foo { a: ({ x = 60; y }), b: x, ..foo0 };

            assert(z === Foo { a: 30, b: 24, c: 19 }); // FAILS
        }

        fn test2_ok() {
            let foo0 = Foo { a: 0, b: 0, c: 19 };

            let mut x = 24;
            let mut y = 30;

            let z = Foo { a: ({ x = 60; y }), b: x, ..foo0 };

            assert(z === Foo { a: 30, b: 60, c: 19 });
            assert(x == 60);
        }

        fn test3_fails() {
            let mut foo0 = Foo { a: 0, b: 0, c: 19 };

            let mut x = 24;
            let mut y = 30;

            let z = Foo { a: x, b: y, ..({ x = 20; foo0 }) };

            assert(z === Foo { a: 20, b: 30, c: 19 }); // FAILS
        }

        fn test3_ok() {
            let mut foo0 = Foo { a: 0, b: 0, c: 19 };

            let mut x = 24;
            let mut y = 30;

            let z = Foo { a: x, b: y, ..({ x = 20; foo0 }) };

            assert(z === Foo { a: 24, b: 30, c: 19 });
            assert(x == 20);
        }

        fn test4_fails() {
            let mut foo0 = Foo { a: 0, b: 0, c: 19 };

            let mut x = 24;
            let mut y = 30;

            let z = Foo { a: x, b: ({ foo0 = Foo { a: 13, b: 14, c: 199 }; 20  }), ..foo0 };

            assert(z === Foo { a: 24, b: 20, c: 19 }); // FAILS
        }

        fn test4_ok() {
            let mut foo0 = Foo { a: 0, b: 0, c: 19 };

            let mut x = 24;
            let mut y = 30;

            let z = Foo { a: x, b: ({ foo0 = Foo { a: 13, b: 14, c: 199 }; 20  }), ..foo0 };

            assert(z === Foo { a: 24, b: 20, c: 199 });
            assert(foo0 === Foo { a: 13, b: 14, c: 199 });
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] side_effects_in_arg_array_literal verus_code! {
        use vstd::prelude::*;

        fn test_fails() {
            let mut x = 24;
            let mut y = 30;

            let z = [x, ({ x = 60; y })];

            assert(z@[0] === 60); // FAILS
        }

        fn test_ok() {
            let mut x = 24;
            let mut y = 30;

            let z = [x, ({ x = 60; y })];

            assert(z@[0] === 24 && z@[1] === 30);
            assert(x == 60);
        }

        fn test2_fails() {
            let mut x = 24;
            let mut y = 30;

            let z = [({ x = 60; y }), x];

            assert(z@[1] === 24); // FAILS
        }

        fn test2_ok() {
            let mut x = 24;
            let mut y = 30;

            let z = [({ x = 60; y }), x];

            assert(z@[0] === 30 && z@[1] === 60);
            assert(x == 60);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] side_effects_in_arg_bin_op verus_code! {
        fn test_fails() {
            let mut x = 24;
            let mut y = 30;

            let z = x + ({ x = 60; y });

            assert(z == 90); // FAILS
        }

        fn test_ok() {
            let mut x = 24;
            let mut y = 30;

            let z = x + ({ x = 60; y });

            assert(z == 54);
            assert(x == 60);
        }

        fn test2_fails() {
            let mut x = 24;
            let mut y = 30;

            let z = ({ x = 60; y }) + x;

            assert(z == 54); // FAILS
        }

        fn test2_ok() {
            let mut x = 24;
            let mut y = 30;

            let z = ({ x = 60; y }) + x;

            assert(z == 90);
            assert(x == 60);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] side_effects_in_arg_bin_opr verus_code! {
        use vstd::prelude::*;

        proof fn test_fails() {
            let mut x: Seq<int> = seq![60];
            let mut y: Seq<int> = seq![30];
            assert(x[0] == 60 && y[0] == 30);

            let z = x =~= ({ x = seq![30]; y });
            assert(x[0] == 30);

            assert(z); // FAILS
        }

        proof fn test_ok() {
            let mut x: Seq<int> = seq![60];
            let mut y: Seq<int> = seq![30];
            assert(x[0] == 60 && y[0] == 30);

            let z = x =~= ({ x = seq![30]; y });
            assert(x[0] == 30);

            assert(!z);
        }

        proof fn test2_fails() {
            let mut x: Seq<int> = seq![30];
            let mut y: Seq<int> = seq![30];
            assert(x[0] == 30 && y[0] == 30);

            let z = ({ x = seq![60]; y }) =~= x;
            assert(x[0] == 60);

            assert(z); // FAILS
        }

        proof fn test2_ok() {
            let mut x: Seq<int> = seq![30];
            let mut y: Seq<int> = seq![30];
            assert(x[0] == 30 && y[0] == 30);

            let z = ({ x = seq![60]; y }) =~= x;
            assert(x[0] == 60);

            assert(!z);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] side_effects_in_arg_with_short_circuiting verus_code! {
        fn test_fails() {
            let mut x = true;
            let mut y = true;

            let z = x && ({ x = false; y });

            assert(z == false); // FAILS
        }

        fn test_ok() {
            let mut x = true;
            let mut y = true;

            let z = x && ({ x = false; y });

            assert(z == true);
            assert(x == false);
        }

        fn test2_fails() {
            let mut x = true;
            let mut y = true;

            let z = ({ x = false; y }) && x;

            assert(z == true); // FAILS
        }

        fn test2_ok() {
            let mut x = true;
            let mut y = true;

            let z = ({ x = false; y }) && x;

            assert(z == false);
            assert(x == false);
        }

        fn test3_fails() {
            let mut x = true;
            let mut y = true;
            let mut w = false;

            let z = ({ x = false; y }) && ({ w = true; x });

            assert(z == true); // FAILS
        }

        fn test3_ok() {
            let mut x = true;
            let mut y = true;
            let mut w = false;

            let z = ({ x = false; y }) && ({ w = true; x });

            assert(w == true);
            assert(x == false);
            assert(z == false);
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] chained_inequality_evaluation_order verus_code! {
        proof fn test1() {
            let mut y: int = 10;
            // Is second arg evaluated before the third?
            let b = (0 <= y <= ({ y = 30; 20 }) <= 40);
            assert(b);
        }

        proof fn test2() {
            // Is the second arg evaluated after the first?
            let mut y: int = 0;
            let b = (({ y = 1; 0 }) <= ({ assert(y == 1); 2 }) <= 3);
            assert(b);
        }

        proof fn test3() {
            // No short-circuiting
            let mut y: int = 0;
            let b = 1 <= 0 <= ({ y = 3; 10 }) <= 12;
            assert(y == 3);
        }

        proof fn test4() {
            // No short-circuiting
            let mut y: int = 0;
            let b = 1 <= 0 <= ({ y = 3; 10 });
            assert(y == 3);
        }
    } => Ok(())
}
