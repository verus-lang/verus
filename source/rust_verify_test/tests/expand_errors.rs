#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] test1_expand_error ["--expand-errors"] => verus_code! {
        spec fn is_good_integer(z: int) -> bool
        {
            z >= 0 && z != 5       // EXPAND-ERRORS
            //        ^^^^^^
        }

        proof fn test_expansion_easy()
        {
            let x = 5;
            assert(is_good_integer(x));     // FAILS
        }
    } => Err(e) => assert_expand_fails(e, 1)
}

test_verify_one_file_with_options! {
    #[test] test2_expand_error ["--expand-errors"] => verus_code! {
        #[derive(PartialEq, Eq)]
        pub enum Message {
            Quit(bool),
            Move { x: i32, y: i32 },
            Write(bool),
        }

        spec fn is_good_integer_2(x: int) -> bool
        {
            x >= 0  // EXPAND-ERRORS
        //  ^^^^^^^
                && x != 5
        }

        spec fn is_good_message_2(msg:Message) -> bool {
            match msg {
                Message::Quit(b) => b,
                Message::Move{x, y} => is_good_integer_2( (x as int)  - (y as int)),
        //                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                Message::Write(b) => b,
            }
        }

        spec fn is_good(msg: Message) -> bool {
            is_good_message_2(msg)
            //^^^^^^^^^^^^^^^^^^^^
        }

        proof fn test_expansion_multiple_call() {
            let x = Message::Move{x: 5, y:6};
            assert(is_good(x));             // FAILS
            //^^^^^^ ^^^^^^^^^^
        }
    } => Err(e) => assert_expand_fails(e, 1)
}

test_verify_one_file_with_options! {
    #[test] test3_expand_requires ["--expand-errors"] => verus_code! {
        #[derive(PartialEq, Eq)]
        pub enum Message {
            Quit(bool),
            Move { x: i32, y: i32 },
            Write(bool),
        }

        spec fn is_good_integer_3(x: int) -> bool
        {
            x >= 0 // EXPAND-ERRORS
        //  ^^^^^^
                && x != 5
        }
        spec fn is_good_message_3(msg:Message) -> bool {
            match msg {
                Message::Quit(b) => b,
            //  ^^^^^^^^^^^^^^^^ (TODO bad span due to match span)
                Message::Move{x, y} => is_good_integer_3( (x as int)  - (y as int)),
            //                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                Message::Write(b) => b,
            }
        }

        proof fn test_require_failure(m:Message, b: bool) -> (good_int: int)
            requires
                b,
                is_good_message_3(m),    // EXPAND-ERRORS
            //  ^^^^^^^^^^^^^^^^^^^^
            ensures
                is_good_integer_3(good_int),
        {
            return 0;
        }

        proof fn test_3(x:int) {
            let x = Message::Move{x: 0, y: 5};
            test_require_failure(x, true);          // FAILS
            //^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        }
    } => Err(e) => assert_expand_fails(e, 2)
}

test_verify_one_file_with_options! {
    #[test] test4_expand_ensures ["--expand-errors"] => verus_code! {
        #[derive(PartialEq, Eq)]
        pub enum Message {
            Quit(bool),
            Move { x: i32, y: i32 },
            Write(bool),
        }

        spec fn is_good_integer_4(x: int) -> bool
        {
            x >= 0
                && x != 5  // EXPAND-ERRORS
        //         ^^^^^^
        }

        spec fn is_good_message_4(msg:Message) -> bool {
            match msg {
                Message::Quit(b) => b,
                Message::Move{x, y} => is_good_integer_4( (x as int)  - (y as int)),
            //                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                Message::Write(b) => b,
            }
        }

        proof fn test_ensures_failure(b: bool) -> (good_msg: Message)
            ensures
                is_good_message_4(good_msg),            // FAILS
              //^^^^^^^^^^^^^^^^^^^^^^^^^^^
        {
            let mut ret =  Message::Write(true);
            if !b {ret = Message::Move{x: 10, y: 5};}
            ret
        }
    } => Err(e) => assert_expand_fails(e, 1)
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test5_expand_forall ["--expand-errors"] => verus_code! {
        use vstd::seq::*;
        spec fn seq_bounded_by_length(s1: Seq<int>) -> bool {
            (forall|i:int| (0 <= i && i < s1.len())  ==>   // EXPAND-ERRORS
                                                         (0 <= s1.index(i)
                                                          && s1.index(i) < s1.len()))
        }

        proof fn test_expansion_forall()
        {
            let mut ss = Seq::empty();
            ss = ss.push(0);
            ss = ss.push(10);
            assert(seq_bounded_by_length(ss));  // EXPAND-ERRORS
        }
    } => Err(e) => assert_expand_fails(e, 2)
}

test_verify_one_file_with_options! {
    // credit: (this example is copied from rust_verify/example/rw2022_scripts.rs, example C)
    #[test] test6_expand_forall ["--expand-errors"] => verus_code! {
        spec fn divides(factor: nat, candidate: nat) -> bool {
            candidate % factor == 0
        }
        spec fn is_prime(candidate: nat) -> bool {
            &&& 1 < candidate
            &&& forall|factor: nat| 1 < factor && factor < candidate ==>
                !divides(factor, candidate) // EXPAND-ERRORS
        }
        proof fn test_trigger() {
            assert(is_prime(6));                // FAILS
        }
    } => Err(e) => assert_expand_fails(e, 1)
}

test_verify_one_file_with_options! {
    // example: `reveal` does not flow
    #[test] test7_local_reveal ["--expand-errors"] => verus_code! {
        #[derive(PartialEq, Eq)]
        pub enum Message {
            Quit(bool),
            Move { x: i32, y: i32 },
            Write(bool),
        }

        #[verifier(opaque)]
        spec fn is_good_integer(x: int) -> bool
        {
            x >= 0 && x != 5
        }

        #[verifier(opaque)]
        spec fn is_good_message_10(msg:Message) -> bool {
            match msg {
                Message::Quit(b) => b,
                Message::Move{x, y} => is_good_integer( (x as int)  - (y as int)),
                Message::Write(b) => b,
            }
        }

        proof fn test_reveal(b: bool) {
            let good_msg = Message::Move{x: 0, y: 0};
            if b {
                reveal(is_good_message_10);
            } else {
                assert_by(true, {reveal(is_good_message_10);});
                assert(is_good_message_10(good_msg));           // FAILS
            }
        }
    } => Err(e) => assert_expand_fails(e, 0)
}

test_verify_one_file_with_options! {
    // example: `reveal` at function exit point
    #[test] test8_ensures_reveal ["--expand-errors"] => verus_code! {
        #[derive(PartialEq, Eq)]
        pub enum Message {
            Quit(bool),
            Move { x: i32, y: i32 },
            Write(bool),
        }

        #[verifier(opaque)]
        spec fn is_good_integer_13(x: int) -> bool
        {
            x >= 0 && x != 5
        }

        #[verifier(opaque)]
        spec fn is_good_message_13(msg:Message) -> bool {
            match msg {
                Message::Quit(b) => b,
                Message::Move{x, y} => is_good_integer_13( (x as int)  - (y as int)),        // EXPAND-ERRORS
                Message::Write(b) => b,
            }
        }

        proof fn test_reveal_at_ensures(b: bool) -> (good_msg: Message)
            ensures
                is_good_message_13(good_msg),        // FAILS
        {
            let good_msg = Message::Move{x: 0, y: 0};
            reveal(is_good_message_13);
            good_msg
        }
    } => Err(e) => assert_expand_fails(e, 1)
}

test_verify_one_file_with_options! {
    #[test] test9_assume_conjunct ["--expand-errors"] => verus_code! {
        spec fn p1(a: int) -> bool {
            a == 1
        }
        spec fn p2(a: int) -> bool {
            a == 2
        }

        spec fn p(a: int) -> bool {
            &&& p1(a)
            &&& p2(a) // EXPAND-ERRORS
        }

        proof fn test(a: int) {
            assume(p1(a));
            assert(p(a)); // FAILS
        }
    } => Err(e) => assert_expand_fails(e, 1)
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test10_expand_forall_assume ["--expand-errors"] => verus_code! {
        use vstd::seq::*;
        spec fn no(i: int) -> bool {
            false
        }

        spec fn seq_bounded_by_length(s1: Seq<int>) -> bool {
            (forall|i:int| (0 <= i && i < s1.len()) ==> no(i) && (0 <= #[trigger] s1[i] < s1.len()))
        }

        spec fn long_seq(s1: Seq<int>) -> bool {
            s1.len() > 20
        }

        spec fn seq_is_long_and_bounded_by_length(s1: Seq<int>) -> bool {
            &&& seq_bounded_by_length(s1)
            &&& long_seq(s1) // EXPAND-ERRORS
        }

        proof fn test_expansion_forall()
        {
            let mut ss = Seq::empty();
            ss = ss.push(0);
            ss = ss.push(10);
            assume(seq_bounded_by_length(ss));
            assert(seq_is_long_and_bounded_by_length(ss));  // EXPAND-ERRORS
        }
    } => Err(e) => assert_expand_fails(e, 2)
}

test_verify_one_file_with_options! {
    #[test] test11_traits_ensures ["--expand-errors"] => verus_code! {
        trait T {
            spec fn f() -> bool;
            proof fn test()
                ensures Self::f(); // FAILS
        }
        impl T for u64 {
            spec fn f() -> bool { false }

            proof fn test() {
            }
        }
    } => Err(e) => assert_expand_fails(e, 0)
}

test_verify_one_file_with_options! {
    #[test] assoc_types_issue952 ["--expand-errors"] => verus_code! {
        struct C;

        trait D<E> {
            spec fn l(&self, k: &E) -> u64;

            fn m(&self, k: &E) -> (p: u64)
                ensures
                    p == self.l(k), // FAILS
            ;
        }

        trait N {
            type O;

            fn m() -> u64;
        }

        impl<E> D<E::O> for E where E: N {
            spec fn l(&self, k: &E::O) -> u64;

            fn m(&self, k: &E::O) -> u64 {
                E::m()
            }
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file_with_options! {
    #[test] unboxing_and_negation_issue788 ["--expand-errors"] => verus_code! {
        trait Tr {
            spec fn stuff(&self) -> bool;
            spec fn stuff2(&self) -> bool;
        }

        spec fn hi<T: Tr>(t: T) -> bool {
            t.stuff() // EXPAND-ERRORS
            && !t.stuff2() // EXPAND-ERRORS
        }

        proof fn test<T: Tr>(t: T) {
            assert(hi(t)); // FAILS
        }
    } => Err(e) => assert_expand_fails(e, 2)
}

test_verify_one_file_with_options! {
    #[test] test_open_spec_is_already_open_387_discussioncomment_5679297_1 ["--expand-errors"] => verus_code! {
        use vstd::set::*;

        spec fn maybe() -> bool;

        // spec fn yes() -> bool { true }
        // spec fn both(s: Set<nat>) -> bool {
        //     &&& maybe()
        //     &&& s.contains(0) // EXPAND-ERRORS
        // }

        proof fn test(s: Set<nat>) {
            assert(maybe()); // FAILS
        }
    } => Err(err) => {
        assert!(err.expand_errors_notes[0].rendered.contains("function is uninterpreted"));
    }
}

test_verify_one_file_with_options! {
    #[test] test_open_spec_is_already_open_387_discussioncomment_5679297_2 ["--expand-errors"] => verus_code! {
        struct Z { _temp: (), }

        mod X {
            pub trait T {
                spec fn foo(&self) -> bool;
            }

            impl T for super::Z {
                open spec fn foo(&self) -> bool {
                    false
                }
            }
        }

        use X::T;

        fn f() {
            let z = Z { _temp: () };
            assert(z.foo()); // FAILS
        }
    } => Err(err) => {
        assert!(err.expand_errors_notes[0].rendered.contains("|   false"));
        assert_expand_fails(err, 0);
    }
}

test_verify_one_file_with_options! {
    #[test] test_requires_resolved_trait_fn ["--expand-errors"] => verus_code! {
        struct Z { _temp: (), }

        mod X {
            pub trait T {
                fn foo(&self)
                    requires false;
            }

            impl T for super::Z {
                fn foo(&self) { }
            }
        }

        use X::T;

        fn f() {
            let z = Z { _temp: () };
            z.foo(); // FAILS
        }
    } => Err(err) => {
        assert!(err.expand_errors_notes[0].rendered.contains("false"));
        assert_expand_fails(err, 0);
    }
}

test_verify_one_file_with_options! {
    #[test] test_forall_requiring_type_invariants ["--expand-errors"] => verus_code! {
        spec fn stuff(i: nat) -> bool;
        spec fn bar() -> bool;

        spec fn foo() -> bool {
            (forall |i: nat| stuff(i))
            &&
            bar() // EXPAND-ERRORS
        }

        fn test()
            requires forall |i: nat| stuff(i),
        {
            assert(foo()); // FAILS
        }
    } => Err(e) => assert_expand_fails(e, 1)
}
