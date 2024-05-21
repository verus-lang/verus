// rust_verify/tests/example.rs expect-failures
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
use vstd::prelude::*;

verus! {

#[verifier::external]
fn main() {
}

//example: simple conjunt
proof fn test_expansion_very_easy() {
    let x: int = 5;
    assert((x >= 0) && (x != 5));
    //                  ^^^^^^^
}

//example: simple function inline
spec fn is_good_integer(z: int) -> bool {
    z >= 0 && z != 5
    //        ^^^^^^

}

proof fn test_expansion_easy() {
    let x = 5;
    assert(is_good_integer(x));
}

//example: simple `match` inline
spec fn is_good_opt(opt: Option<int>) -> bool {
    match opt {
        Option::Some(k) => k > 10,
        Option::None => true,
    }
}

proof fn test_expansion_match() {
    let x: Option<int> = Option::Some(5);
    let y: Option<int> = Option::Some(4);
    assert(is_good_opt(x));
}

//example: 3-level failure
#[derive(PartialEq, Eq)]
pub enum Message {
    Quit(bool),
    Move { x: i32, y: i32 },
    Write(bool),
}

#[verusfmt::skip]
spec fn is_good_integer_3(x: int) -> bool {
    x >= 0 && x != 5
//  ^^^^^^

}

spec fn is_good_message(msg: Message) -> bool {
    match msg {
        Message::Quit(b) => b,
        Message::Move { x, y } => is_good_integer_3((x as int) - (y as int)),
        //                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        Message::Write(b) => b,
    }
}

spec fn is_good(msg: Message) -> bool {
    is_good_message(msg)
    //^^^^^^^^^^^^^^^^^^

}

proof fn test_expansion_multiple_call() {
    let x = Message::Move { x: 5, y: 6 };
    assert(is_good(x));
    //^^^^^^ ^^^^^^^^^
}

// example: boolean OR, negation
spec fn is_good_integer_5(x: int) -> bool {
    !(x < 0 || !(x != 5))
    //           ^^^^^^

}

proof fn test_expansion_negate() {
    assert(is_good_integer_5(5));
    //^^^^^^ ^^^^^^^^^^^^^^^^^^
}

//example: requires
#[verusfmt::skip]
spec fn is_good_integer_7(x: int) -> bool {
    x >= 0 && x != 5
//  ^^^^^^
}

spec fn is_good_message_7(msg: Message) -> bool {
    match msg {
        Message::Quit(b) => b,
        Message::Move { x, y } => is_good_integer_7((x as int) - (y as int)),
        //                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        Message::Write(b) => b,
    }
}

proof fn test_require_failure(m: Message, b: bool) -> (good_int: int)
    requires
        b,
        is_good_message_7(m),
//      ^^^^^^^^^^^^^^^^^^^^

    ensures
        is_good_integer_7(good_int),
{
    return 0;
}

proof fn test_7(x: int) {
    let x = Message::Move { x: 0, y: 5 };
    test_require_failure(x, true);
    //^^^^^^^^^^^^^^^^^^^^^^^^^^^
    assert(false);
}

//example: ensures
spec fn is_good_integer_8(x: int) -> bool {
    x >= 0 && x != 5
    //        ^^^^^^

}

spec fn is_good_message_8(msg: Message) -> bool {
    match msg {
        Message::Quit(b) => b,
        Message::Move { x, y } => is_good_integer_8((x as int) - (y as int)),
        //                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        Message::Write(b) => b,
    }
}

proof fn test_ensures_failure(b: bool) -> (good_msg: Message)
    ensures
        is_good_message_8(good_msg),
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^

{
    let mut ret = Message::Write(true);
    if !b {
        ret = Message::Move { x: 10, y: 5 };
    }
    ret
}

// example: opaque/reveal
#[verifier::opaque]
spec fn is_good_integer_9(
    x: int,
) -> bool
//   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Note: this function is opaque
 {
    x >= 0 && x != 5
}

#[verifier::opaque]
spec fn is_good_message_9(msg: Message) -> bool {
    match msg {
        Message::Quit(b) => b,
        Message::Move { x, y } => is_good_integer_9((x as int) - (y as int)),
        //                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        Message::Write(b) => b,
    }
}

proof fn test_opaque(b: bool) {
    let good_msg = Message::Move { x: 0, y: 0 };
    reveal(is_good_message_9);
    assert(is_good_message_9(good_msg));
    //^^^^^^ ^^^^^^^^^^^^^^^^^^^^^^^^^^^
}

// example: `reveal` does not flow
#[verifier::opaque]
spec fn is_good_message_10(msg: Message) -> bool {
    //^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Note: this function is opaque
    match msg {
        Message::Quit(b) => b,
        Message::Move { x, y } => is_good_integer_9((x as int) - (y as int)),
        Message::Write(b) => b,
    }
}

proof fn test_reveal(b: bool) {
    let good_msg = Message::Move { x: 0, y: 0 };
    if b {
        reveal(is_good_message_10);
    } else {
        assert_by(
            true,
            {
                reveal(is_good_message_10);
            },
        );
        assert(is_good_message_10(good_msg));
        //^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    }
}

//example:`hide`
spec fn is_good_integer_11(
    x: int,
) -> bool
//   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Note: this function is opaque
 {
    x >= 0 && x != 5
}

proof fn test_hide(b: bool) {
    hide(is_good_integer_11);
    let i = 0;
    assert(is_good_integer_11(i));
    //^^^^^^^^^^^^^^^^^^^^^^^^^^^
}

//example: publish
mod M3 {
    use builtin::*;

    pub closed spec fn is_good_integer(
        x: int,
    ) -> bool
    //^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Note: this function is closed at the module boundary
     {
        x >= 0 && x != 5
    }

}

mod M4 {
    #[allow(unused_imports)]


    use crate::M3;

    proof fn test_publish(b: bool) {
        let i = 0;
        assert(M3::is_good_integer(i));
        //^^^^^^ ^^^^^^^^^^^^^^^^^^^^^^
    }

}

// example: reveal at ensures
#[verifier::opaque]
spec fn is_good_integer_13(
    x: int,
) -> bool
//   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Note: this function is opaque
 {
    x >= 0 && x != 5
}

#[verifier::opaque]
spec fn is_good_message_13(msg: Message) -> bool {
    match msg {
        Message::Quit(b) => b,
        Message::Move { x, y } => is_good_integer_13((x as int) - (y as int)),
        //                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        Message::Write(b) => b,
    }
}

proof fn test_reveal_at_ensures(b: bool) -> (good_msg: Message)
    ensures
        is_good_message_13(good_msg),
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

{
    let good_msg = Message::Move { x: 0, y: 0 };
    reveal(is_good_message_13);
    good_msg
}

// example: recursive function
spec fn is_even(
    p: nat,
) -> bool
//   ------------------------- Note: this function is recursive with fuel 10
 {
    decreases(p);
    if p == 0 {
        true
    } else {
        !is_even((p - 1) as nat)
    }
}

proof fn test_rec() {
    reveal_with_fuel(is_even, 10);
    assert(is_even(1));
    //^^^^^^ ^^^^^^^^^^
}

spec fn are_equal(x: int, y: int, z: int, w: int) -> bool {
    #[verifier(custom_err("integers fail to be equal"))]
    (x == y) && #[verifier(custom_err("this ain't right. probably."))]
    (z <= w)
}

proof fn proof_test_are_equal(x: int, y: int, z: int, w: int) {
    assert(are_equal(x, y, z, w));
}

} // verus!
