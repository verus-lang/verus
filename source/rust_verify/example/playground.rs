mod pervasive;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use pervasive::string::*;

verus! {
// const GREETING: StrSlice = StrSlice::new("Hello World");
const MYVALUE: u64 = 58421;
fn myconstfn() -> u64 {
    /* let _:() = GREETING.reveal();
    let m = GREETING.len(); */
    let x = MYVALUE + 23;
    x
}

}
fn main() {}

