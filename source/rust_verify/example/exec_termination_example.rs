use vstd::prelude::*;

verus! {
    // basic recursive expression
    fn exec_basic_recursive_expr(i: u64) -> u64
        decreases i
    {
        if i == 0 { 0 } else { i + exec_basic_recursive_expr(i - 1) }
    }
 
    fn exec_basic_recursive_expr_fail(i: u64) -> u64
    {
        if i == 0 { 0 } else { i + exec_basic_recursive_expr_fail(i - 1) }
    }

    // basic recursive statement
    fn exec_basic_recursive_stmt(i: u64)
        decreases i 
    {
        if i != 0 {
            exec_basic_recursive_stmt(i - 1);
        }
    }

    fn exec_basic_recursive_stmt_fail(i: u64)
    {
        if i != 0 {
            exec_basic_recursive_stmt_fail(i - 1);
        }
    }

    // multiple decreases fail
    fn dec1(i: u64) {
        if 0 < i { dec2(i, 100 * i); }
    }

    fn dec2(j: u64, k: u64) 
        decreases j, k 
    {
        if 0 < k { dec2(j, k-1); }
        if 0 < j {
            dec2(j - 1, 100 * j + k);
            dec1(j - 1);
        }
    }

    // multiple decreases #2 fail
    fn dec1a(i: u64)
        decreases i 
    {
        if 0 < i {
            dec1a(i - 1);
            dec2a(i, 100 * i);
        }
    }

    fn dec2a(j: u64, k: u64) {
        if 0 < j { dec1a(j - 1); }
    }

    // extra dependency fail
    fn dec1b(i: u64) {
        dec2b(i);
    }

    #[verifier(external_body)]
    fn dec2b(i: u64) {
        extra_dependency(dec1b);
        unimplemented!();
    }

    // check across modules fail
    mod M1 {
        use builtin::*;
        pub(crate) fn f1(i: u64) -> u64 { crate::M2::f2(i - 1) }
    }

    mod M2 {
        use builtin::*;
        pub(crate) fn f2(i: u64) -> u64 { crate::M1::f1(i - 1) }
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

    // need decreases
    fn exec_basic_while_loop_fail1() {
        let mut i = 0;
        while i < 10
            invariant i <= 10
        {
            i = i + 1;
        }
        assert(i == 10);
    }

    // still need invariant
    fn exec_basic_while_loop_fail2() {
        let mut i = 0;
        while i < 10
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

    fn exec_nested_while_loop_fail() {
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
                    {
                        j = j + 1;
                    }
            }
    }

    /* use vstd::modes::*;
    fn exec_basic_loop_with_ghost() { // what would be the appropriate decreases clause here?
        let ghost mut a: int = 5;
        loop 
            invariant a > 0
        {
            proof {
                a = a + 1;
            }
        }
    } */

    /* fn exec_basic_loop() { // same here?
        let mut a: u64 = 5;
        loop 
            invariant a > 0
            decreases (-1 * a)
        {
            a = a + 1;
        }
    } */

    // infinite loop
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

    fn exec_example_loop_break_fail() {
        let mut i: i8 = 0;
        loop
            invariant_except_break i <= 9
            invariant 0 <= i <= 10
            ensures 1 <= i
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
            invariant n == iter.cur * 3,
            decreases 10 - iter.cur 
        {
            n += 3;
        }
    }

    /* fn exec_for_loop_2() { // FAILS - decreases cannot see x?
        let mut n: u64 = 0;
        for x in 0..10
            invariant n == x * 3,
            decreases 10 - x
        {
            n += 3;
        }
    } */

    fn exec_for_loop_3() {
        let mut n: u64 = 0;
        let mut end = 10;
        for x in iter: 0..end 
            invariant 
                n == iter.cur * 3,
                end == 10,
                decreases end - iter.cur,
        {
            n += 3;
        }
    }
    
    fn exec_for_loop_fail() {
        let mut n: u64 = 0;
        for x in iter: 0..10
            invariant n == iter.cur * 3
        {
            n += 3;
        }
    }

    // basic recursive expression + basic while loop // TODO: think of while / recursive function tests...
    /* fn exec_basic_recursive_stmt_basic_while_loop_fail(i: u64)
        decreases i 
    {
        while 0 < i && i <= 10
            invariant 0 <= i && i <= 10
            decreases 10 - i
        {
            exec_basic_recursive_stmt_basic_while_loop_fail(i - 1);
        }
        exec_basic_recursive_stmt_basic_while_loop_fail(i - 1);
    } */
}