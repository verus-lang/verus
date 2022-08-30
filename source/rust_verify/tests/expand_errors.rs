#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1_expand_error verus_code! {
        spec fn is_good_integer(z: int) -> bool
        {
            z >= 0 && z != 5       // EXPAND-ERRORS
            //        ^^^^^^
        }

        proof fn test_expansion_easy()
        {
            let x = 5;
            assert(is_good_integer(x));     // EXPAND-ERRORS
        }
    } => Err(e) => assert_expand_fails(e, 2)
}

test_verify_one_file! {
    #[test] test2_expand_error verus_code! {
        #[derive(PartialEq, Eq)]
        pub enum Message {
            Quit(bool),
            Move { x: i32, y: i32 },
            Write(bool),
        }

        spec fn is_good_integer_2(x: int) -> bool
        {
            x >= 0 && x != 5            // EXPAND-ERRORS
        //  ^^^^^^^
        }

        spec fn is_good_message_2(msg:Message) -> bool {
            match msg {
                Message::Quit(b) => b,
                Message::Move{x, y} => is_good_integer_2( (x as int)  - (y as int)),        // EXPAND-ERRORS
        //                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                Message::Write(b) => b,
            }
        }

        spec fn is_good(msg: Message) -> bool {
            is_good_message_2(msg)            // EXPAND-ERRORS
            //^^^^^^^^^^^^^^^^^^^^
        }

        proof fn test_expansion_multiple_call() {
            let x = Message::Move{x: 5, y:6};
            assert(is_good(x));             // EXPAND-ERRORS
            //^^^^^^ ^^^^^^^^^^
        }
    } => Err(e) => assert_expand_fails(e, 4)
}

test_verify_one_file! {
    #[test] test3_expand_requires verus_code! {
        #[derive(PartialEq, Eq)]
        pub enum Message {
            Quit(bool),
            Move { x: i32, y: i32 },
            Write(bool),
        }

        spec fn is_good_integer_3(x: int) -> bool
        {
            x >= 0 && x != 5            // EXPAND-ERRORS
        //  ^^^^^^
        }
        spec fn is_good_message_3(msg:Message) -> bool {
            match msg {
                Message::Quit(b) => b,
                Message::Move{x, y} => is_good_integer_3( (x as int)  - (y as int)),   // EXPAND-ERRORS
            //                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                Message::Write(b) => b,
            }
        }

        proof fn test_require_failure(m:Message, b: bool) -> (good_int: int)
            requires
                b,
                is_good_message_3(m),               // EXPAND-ERRORS
            //  ^^^^^^^^^^^^^^^^^^^^
            ensures
                is_good_integer_3(good_int),
        {
            return 0;
        }

        proof fn test_3(x:int) {
            let x = Message::Move{x: 0, y: 5};
            test_require_failure(x, true);          // EXPAND-ERRORS
            //^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
            assert(false);
        }
    } => Err(e) => assert_expand_fails(e, 4)
}

test_verify_one_file! {
    #[test] test4_expand_ensures verus_code! {
        #[derive(PartialEq, Eq)]
        pub enum Message {
            Quit(bool),
            Move { x: i32, y: i32 },
            Write(bool),
        }

        spec fn is_good_integer_4(x: int) -> bool
        {
            x >= 0 && x != 5                // EXPAND-ERRORS
        //            ^^^^^^
        }

        spec fn is_good_message_4(msg:Message) -> bool {
            match msg {
                Message::Quit(b) => b,
                Message::Move{x, y} => is_good_integer_4( (x as int)  - (y as int)),        // EXPAND-ERRORS
            //                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                Message::Write(b) => b,
            }
        }

        proof fn test_ensures_failure(b: bool) -> (good_msg: Message)
            ensures
                is_good_message_4(good_msg),            // EXPAND-ERRORS
              //^^^^^^^^^^^^^^^^^^^^^^^^^^^
        {
            let mut ret =  Message::Write(true);
            if !b {ret = Message::Move{x: 10, y: 5};}
            ret
        }
    } => Err(e) => assert_expand_fails(e, 3)
}

test_verify_one_file! {
    #[test] test5_expand_forall verus_code! {
        use crate::pervasive::{*, seq::*};
        spec fn seq_bounded_by_length(s1: Seq<int>) -> bool {
            (forall|i:int| (0 <= i && i < s1.len())  ==>
                                                         (0 <= s1.index(i)
                                                          && s1.index(i) < s1.len()))   // EXPAND-ERRORS
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

test_verify_one_file! {
    // credit: (this example is copied from rust_verify/example/rw2022_scripts.rs, example C)
    #[test] test6_expand_forall verus_code! {
        spec fn divides(factor: nat, candidate: nat) -> bool {
            candidate % factor == 0             // EXPAND-ERRORS
        }
        spec fn is_prime(candidate: nat) -> bool {
            &&& 1 < candidate
            &&& forall|factor: nat| 1 < factor && factor < candidate ==>
                !divides(factor, candidate)     // EXPAND-ERRORS
        }
        proof fn test_trigger() {
            assert(is_prime(6));                // EXPAND-ERRORS
        }
    } => Err(e) => assert_expand_fails(e, 3)
}

test_verify_one_file! {
    // example: `reveal` does not flow
    #[test] test7_local_reveal verus_code! {
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
        spec fn is_good_message_10(msg:Message) -> bool {   // EXPAND-ERRORS
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
                assert(is_good_message_10(good_msg));           // EXPAND-ERRORS
            }
        }
    } => Err(e) => assert_expand_fails(e, 2)
}

test_verify_one_file! {
    // example: `reveal` at function exit point
    #[test] test8_ensures_reveal verus_code! {
        #[derive(PartialEq, Eq)]
        pub enum Message {
            Quit(bool),
            Move { x: i32, y: i32 },
            Write(bool),
        }

        #[verifier(opaque)]
        spec fn is_good_integer_13(x: int) -> bool   // EXPAND-ERRORS
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
                is_good_message_13(good_msg),        // EXPAND-ERRORS
        {
            let good_msg = Message::Move{x: 0, y: 0};
            reveal(is_good_message_13);
            good_msg
        }
    } => Err(e) => assert_expand_fails(e, 3)
}
