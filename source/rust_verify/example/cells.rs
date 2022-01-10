#[allow(unused_imports)]
use builtin::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{*, cell::*};
use crate::cell::new_empty;
#[allow(unused_imports)]
use crate::cell::*;

struct X {
  pub i: u64,
}

fn main() {
  let x = X { i: 5 };

  match new_empty() {
    PCellWithToken{pcell, token} => {
      #[proof] let t1 = pcell.put(x, token);

      assert(equal(t1.value, option::Option::Some(X { i : 5 })));
    }
  }
}
