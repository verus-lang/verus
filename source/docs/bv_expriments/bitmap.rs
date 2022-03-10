#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
mod pervasive;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::{*, seq::*, vec::*};

// a: bv, b: index
macro_rules! get_bit64{
    ($a:expr,$b:expr)=>{
        {
            (0x1u64 & ($a>>$b)) == 1u64
        }
    }
}

// a: bv, b: index, c: bit
macro_rules! set_bit64{
    ($a:expr,$b:expr, $c:expr)=>{
        {
             if $c {$a | 1u64 << $b}
             else {$a & (!(1u64 << $b))}
        }
    }
}

// #[spec]
// fn u64_view(u: u64) -> Seq<bool> {
//     Seq::new(64, |i: int| get_bit64!(u, i as u64))
// }

// #[proof]
// fn u64_view_proof(bv: u64){
//     ensures([
//         forall(|i: u64| (i < 64) >>= u64_view(bv).index(i) == get_bit64!(bv, i))
//     ]);
// }

// #[verifier(bit_vector)]
// #[proof]
// fn set_bit64_proof(bv_new: u64, bv_old: u64, index: u64, bit: bool){
//     requires([
//         bv_new == set_bit64!(bv_old, index, bit),
//         index < 64 ,
//     ]);
//     ensures([
//         get_bit64!(bv_new, index) == bit,
//         forall(|loc2:u64| (loc2 < 64 && loc2 != index) >>= (get_bit64!(bv_new, loc2) == get_bit64!(bv_old, loc2))),
//     ]);
// }


pub struct BitMap {
    bits: Vec<u64>,
    #[proof] ghost_bits: Seq<u64>,
}

impl BitMap {
    #[spec]
    fn view(&self) -> Seq<bool> {        
        let width = self.ghost_bits.len() * 64;
        Seq::new(width, |i: int| get_bit64!(self.ghost_bits.index(i/64), (i as u64)%64))
    }

    #[spec]
    fn inv(&self) -> bool {
        self.ghost_bits.ext_equal(self.bits.view())
    }
 
    // need to add "new" in pervasive/vec.rs
    // #[exec]
    // fn new(width: u64) -> BitMap {
    //     requires(width % 64 == 0);
    //     let mut len = width/64;
    //     let v:Vec<u64> = Vec::new();
    //     // add 0 len times
    //     BitMap{bits: v, width: width} 
    // }

    #[exec]
    fn get_bit(&self, index: u64) -> bool {
        requires([
            self.inv(),
            index < self.ghost_bits.len() * 64,
        ]);
        ensures(|ret:bool|
            ret == self.view().index(index),
        );
        let seq_index = index/64;
        let bit_index = index%64;
        let target:u64 = *self.bits.index(seq_index as usize);

        // why is it hard to prove the following line?
        assume(target == self.bits.view().index(seq_index as int));

        get_bit64!(target, bit_index)
    }

    // #[exec]
    // fn set_bit(self, index: u64, bit: bool) -> BitMap {
    //     requires([
    //         index < self.bits.view().len() * 64,
    //     ]);
    //     let seq_index = (index/64) as usize;
    //     let bv_old:u64 = *self.bits.index(seq_index);
    //     let bv_new:u64 = set_bit64!(bv_old, index%64, bit);
    //     BitMap{bits: self.bits.set(seq_index, bv_new)}
    // }
}

// #[verifier(external)]
fn main(){}






// 'rustc' panicked at 'unexpected qpath LangItem(Range, ... )
// for i in 0..len {
//     v.push(0);
 // }

// BitMap{bits: vec![0; len as usize], width: width} // panicked at 'no entry found for key', vir/src/well_formed.rs:133:30


// fn set_bit(&mut self, index: u64, bit: bool)  {
//     self.bits = self.bits.update(seq_index, bv_new);   //error: The verifier does not yet support the following Rust feature: field updates        
// }