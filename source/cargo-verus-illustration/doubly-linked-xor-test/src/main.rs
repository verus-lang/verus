use vstd::{prelude::*, string::*};

use doubly_linked_xor::DListXor;

verus! {

#[verifier::external_body]
fn print_result(msg: StrSlice<'static>, value: u32) {
    println!("{}: {value}", msg.into_rust_str());
}

fn main() {
    let mut t = DListXor::<u32>::new();
    t.push_back(2);
    t.push_back(3);
    t.push_front(1);  // 1, 2, 3
    print_result(new_strlit("pushed"), 2);
    print_result(new_strlit("pushed"), 3);
    print_result(new_strlit("pushed"), 1);
    let x = t.pop_back();  // 3
    let y = t.pop_front();  // 1
    let z = t.pop_front();  // 2
    assert(x == 3);
    assert(y == 1);
    assert(z == 2);
    print_result(new_strlit("popped"), x);
    print_result(new_strlit("popped"), y);
    print_result(new_strlit("popped"), z);
}

} // verus!
