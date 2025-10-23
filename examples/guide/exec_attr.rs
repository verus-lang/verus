#![feature(proc_macro_hygiene)]

use vstd::prelude::*;

// ANCHOR: verus_spec
#[verus_spec(sum => 
     requires 
         x < 100, 
         y < 100, 
     ensures 
         sum < 200, 
)]
fn my_exec_fun(x: u32, y: u32) -> u32 
{ 
    x + y 
}
// ANCHOR_END: verus_spec

// ANCHOR: loop
#[verus_spec(v => ensures true)]
fn test_for_loop(n: u32) -> Vec<u32> {
    let mut v: Vec<u32> = Vec::new();

    #[verus_spec(
       invariant
           v@ =~= Seq::new(i as nat, |k| k as u32),
    )]
    for i in 0..n {
        v.push(i);
    }
    v
}
// ANCHOR_END: loop

// ANCHOR: proof
#[verus_spec]
fn exec_with_proof() {
   proof_decl!{
     let ghost mut i = 0int;
     assert(true);
   }
   test_for_loop(10);
   proof!{
    assert(i == 0);
   }
}
// ANCHOR_END: proof

// ANCHOR: proof_with
#[verus_spec(ret =>
with
  Tracked(y): Tracked<&mut u32>,
  Ghost(w): Ghost<u32> 
     -> z: Ghost<u32>
requires
  x < 100,
  *old(y) < 100,
ensures
  *y == x,
  ret == x + 1,
  z@ == x,
)]
fn exec_tracked(x: u32) -> u32 {
  proof! {
    *y = x;
  }
  proof_with!(|= Ghost(x));
  (x + 1)
}


#[verus_spec]
fn exec_tracked_test(x: u32) {
  proof_decl!{
   let ghost mut z = 0u32;
   let tracked mut y = 0u32;
  }

  proof_with!{Tracked(&mut y), Ghost(0)=> Ghost(z)}
  let x = exec_tracked(1);

  proof!{
    assert(y == 1);
    assert(z == 1);
    assert(x == 2);
  }
}

fn exec_external_test(x: u32) -> u32 {
   exec_tracked(1)
}

// ANCHOR_END: proof_with

// ANCHOR: dual_spec
#[verus_verify(dual_spec)]
#[verus_spec(
    requires
        x < 100,
        y < 100,
    returns f(x, y)
)]
fn f(x: u32, y: u32) -> u32 {
    proof!{
        assert(true);
    }
    {
        proof!{assert(true);}
        x + y
    }
}

#[verus_verify(dual_spec)]
#[verus_spec(
    requires
        x < 100,
    returns
        f2(x),
)]
pub fn f2(x: u32) -> u32 {
    f(x, 1)
}
// ANCHOR_END: dual_spec
