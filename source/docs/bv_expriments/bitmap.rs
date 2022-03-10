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
            (0x1u64 & ($a>>($b as u64))) == 1u64
        }
    }
}

// a: bv, b: index, c: bit
macro_rules! set_bit64{
    ($a:expr,$b:expr, $c:expr)=>{
        {
             if $c {$a | 1u64 << ($b as u64)}
             else {$a & (!(1u64 << ($b as u64)))}
        }
    }
}

#[spec]
fn u64_view(u: u64) -> Seq<bool> {
    Seq::new(64, |i: int| get_bit64!(u, i as u64))
}

#[proof]
fn u64_view_proof(bv: u64){
    ensures([
        forall(|i: u32| (i < 64) >>= u64_view(bv).index(i) == get_bit64!(bv, i))
    ]);
}

#[verifier(bit_vector)]
#[proof]
fn set_bit64_proof(bv_new: u64, bv_old: u64, index: u32, bit: bool){
    requires([
        bv_new == set_bit64!(bv_old, index, bit),
        index < 64 ,
    ]);
    ensures([
        get_bit64!(bv_new, index) == bit,
        forall(|loc2:u32| (loc2 < 64 && loc2 != index) >>= (get_bit64!(bv_new, loc2) == get_bit64!(bv_old, loc2))),
    ]);
}


// #[derive(ViewEq)]
pub struct BitMap {
    bits: Vec<u64>,
    #[spec] ghost_bits: Seq<u64>,
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
    fn get_bit(&self, index: u32) -> bool {
        requires([
            self.inv(),
            index < self.ghost_bits.len() * 64,
        ]);
        ensures(|ret:bool|[
            ret == self.view().index(index),
        ]);
        let seq_index:usize = (index/64) as usize;
        let bit_index = index%64;
        let target:u64 = *self.bits.index(seq_index);
        // assert(target == self.bits.view().index(seq_index));
        // assert( self.bits.view().index(seq_index) == self.ghost_bits.index(seq_index));
        // assert(self.ghost_bits.index(seq_index) == target);
        // assert(index == (seq_index as u32) * 64 + bit_index);        
        // assert(u64_view(target).index(bit_index) == get_bit64!(target, bit_index));
        // assert(u64_view(target).index(bit_index) == self.view().index(index));
        get_bit64!(target, bit_index)
    }

    #[exec]
    fn set_bit(self, index: u32, bit: bool) -> BitMap {
        requires([
            self.inv(),
            index < self.ghost_bits.len() * 64,
        ]);
        ensures(|ret:BitMap| [
            ret.inv(),
            equal(ret.view(), self.view().update(index,bit)),
            ret.view().ext_equal(self.view().update(index,bit)),
        ]);
        let seq_index = (index/64) as usize;
        let bit_index = index%64;
        let bv_old:u64 = *self.bits.index(seq_index);
        let bv_new:u64 = set_bit64!(bv_old, bit_index, bit);
        set_bit64_proof(bv_new, bv_old, bit_index, bit);
        let bits:Vec<u64> = self.bits.set(seq_index, bv_new);
        // axiom_seq_update_len::<u64>(self.bits.view(), seq_index, bv_new);
        axiom_seq_update_same::<u64>(self.bits.view(), seq_index, bv_new);
        // assert_forall_by(|loc2:u32| {
        //     requires(loc2< self.ghost_bits.len());
        //     ensures( loc2 != (seq_index as u32) >>= (self.bits.index(loc2) == bits.index(loc2))  );
        //     axiom_seq_update_different::<u64>(self.bits.view(), seq_index, loc2, bv_new);
        // });

        assert(bits.view().len() == self.bits.view().len());       
        let result = BitMap{bits: bits, ghost_bits: bits.view()};
        assert(self.ghost_bits.len() == result.ghost_bits.len());

        assert(result.view().index(index) == bit);
        assert_forall_by(|loc2:u32|{
            requires(
                loc2 < self.ghost_bits.len() * 64 &&
                loc2 != index
            );
            ensures(self.view().index(loc2) == result.view().index(loc2)); 
        });        

        assert(result.view().ext_equal(self.view().update(index,bit)));
        result
    }
}

// #[verifier(external)]
fn main(){}




// in get_bit(),
// when index was u64, below couldn't be proved
// assert(index == (seq_index as u64) * 64 + bit_index);         
// in prelude, it says "usize == u32 or u64".

// 'rustc' panicked at 'unexpected qpath LangItem(Range, ... )
// for i in 0..len {
//     v.push(0);
// }

// BitMap{bits: vec![0; len as usize], width: width} // panicked at 'no entry found for key', vir/src/well_formed.rs:133:30

// fn set_bit(&mut self, index: u64, bit: bool)  {
//     self.bits = self.bits.update(seq_index, bv_new);   //error: The verifier does not yet support the following Rust feature: field updates        
// }