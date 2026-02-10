use vstd::prelude::*;

verus! {
    // basic recursive expression
    fn exec_basic_recursive_expr(i: u64) -> (r: u64)
        ensures r == i
        decreases i
    {
        if i == 0 { 0 } else { 1 + exec_basic_recursive_expr(i - 1) }
    }

    // basic recursive statement
    fn exec_basic_recursive_stmt(i: u64)
        decreases i 
    {
        if i != 0 {
            exec_basic_recursive_stmt(i - 1);
        }
    }

    // basic while loop
    fn exec_basic_while_loop() {
        let mut i = 0;
        while i < 10
            invariant i <= 10
            decreases 10 - i
        {
            i = i + 1;
        }
        assert(i == 10);
    }

    // nested while 
    fn exec_nested_while_loop() {
        let mut i = 0;
        let mut j = 0;
        while i < 10 
            invariant 
                i <= 10,
                j <= 5
            decreases 10 - i
            {
                i = i + 1;
                while j < 5
                    invariant j <= 5
                    decreases 5 - j
                    {
                        j = j + 1;
                    }
            }
    }

    // infinite loop with break
    fn exec_basic_loop_break() {
        let mut i: i8 = 0;
        loop
            invariant_except_break i <= 9
            invariant 0 <= i <= 10
            ensures 1 <= i
            decreases 10 - i
        {
            i = i + 1;
            if i == 10 {
                break;
            }
        }
    }

    // for loop 
    fn exec_for_loop() {
        let mut n: u64 = 0;
        for x in iter: 0..10
            invariant n == x * 3,
            // You can write a `decreases` if you want, but it's not needed
            // because Verus inserts a decreases automatically for `for` loops:
            //   decreases 10 - iter.cur,
        {
            n += 3;
        }
    }

    fn exec_for_loop_2() {
        let mut n: u64 = 0;
        let mut end = 10;
        for x in iter: 0..end 
            invariant 
                n == x * 3,
                end == 10,
            // You can write a `decreases` if you want, but it's not needed
            // because Verus inserts a decreases automatically for `for` loops:
            //   decreases end - iter.cur,
        {
            n += 3;
        }
    }

    // basic recursive expression + basic while loop
    #[verifier::loop_isolation(false)]
    fn exec_basic_recursive_stmt_basic_while_loop(mut i: u64)
        requires i <= 10,
        decreases i,
    {
        let ghost initial_i = i;
        while 0 < i && i <= 10
            invariant
                0 <= i <= 10,
                i <= initial_i,
            decreases i,
        {
            exec_basic_recursive_stmt_basic_while_loop(i - 1);
            i -= 1;
        }
    }
}
