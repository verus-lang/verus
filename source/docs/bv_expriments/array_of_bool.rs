#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;
use builtin_macros::*;

#[spec]
#[verifier(external_body)]
pub fn get_bit(bv:u32, loc:u32) -> bool {
    unimplemented!();
}

#[spec]
#[verifier(external_body)]
pub fn set_bit(bv:u32, loc:u32, bit:bool) -> u32 {
    unimplemented!();
} 

#[spec]
fn bv_view_aux(bv: u32, i: u32) -> Seq<bool> {
    decreases(i);

    let bit = seq![get_bit(bv, i)];
    if i == 0 {
        bit
    } else {
        bv_view_aux(bv, i - 1).add(bit)
    }
}

#[spec]
fn bv_view(bv: u32) -> Seq<bool> {
    bv_view_aux(bv, 31)
}

#[proof]
fn bv_view_aux_correspond(bv: u32, i: u32) {
    decreases(i);
    requires(i<32u32);
    ensures([
        bv_view_aux(bv, i).len() == i as int + 1,
        forall(|j: u32| (j <= i) >>= (bv_view_aux(bv, i).index(j) == get_bit(bv, j)) )
    ]);

    if i != 0 {
        bv_view_aux_correspond(bv, i - 1);
    }
}

#[proof]
fn bv_view_correspond(bv: u32){
    ensures([
        bv_view(bv).len() == 32,
        forall(|i: u32| (i < 32) >>= bv_view(bv).index(i) == get_bit(bv, i))
    ]);
    bv_view_aux_correspond(bv, 31);
}

fn main(){
}
