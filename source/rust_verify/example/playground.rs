use builtin_macros::*;
use builtin::*;
mod pervasive;
use pervasive::{*, option::Option, result::Result};

use pervasive::seq::*;
use crate::pervasive::vec::*;

fn add1(v: &mut Vec<u64>) {
    requires(forall(|i: nat| i < old(v).len() >>= old(v).index(i) < 10));
}

fn main() { }
