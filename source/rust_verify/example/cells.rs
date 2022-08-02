#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{*, cell::*};
#[allow(unused_imports)]
use crate::cell::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;

verus!{

struct X {
    pub i: u64,
}

fn main() {
    let x = X { i: 5 };

    let (pcell, mut token) = PCell::empty();

    pcell.put(&mut token, x);

    assert((*token)@.value === option::Option::Some(X { i : 5 }));
}

}
