use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::{*, option::Option, result::Result};
use pervasive::string::StrSlice;

use pervasive::seq::*;
use crate::pervasive::vec::*;

const MYVALUE: u32 = 10998;

const GREETING: StrSlice<'static> = StrSlice::new("Hello World");
fn myconstfn() {
    let x: u32 = 3 + MYVALUE;
    let mylocalstrslice = StrSlice::new("LOCAL_STR_SLICE");
}

fn main() {}

