use vstd::prelude::*;
use vstd::atomic::*;

use basic_verified_lib::*;

verus! {

fn main() {
    let x = double(42);
    assert(x == 84);
    let _x = opaque_hidden();

    let tracked mut token = Token { value: 5 };
    logatom_function() atomically |update| {
        token = Commit::get(update(token));
    };

    assert(token.value == 5);
}

} // verus!
