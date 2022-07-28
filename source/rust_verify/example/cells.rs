#[allow(unused_imports)]
use builtin::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{*, cell::*};
#[allow(unused_imports)]
use crate::cell::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;

struct X {
    pub i: u64,
}

fn main() {
    let x = X { i: 5 };

    let (pcell, mut token) = PCell::empty();

    pcell.put(&mut token, x);

    assert(equal(token.view().value, option::Option::Some(X { i : 5 })));
}
