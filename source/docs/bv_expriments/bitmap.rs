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

#[verifier(bit_vector)]
#[proof]
fn bit_or_64_proof(bv1: u64, bv2: u64, bv_new:u64){
    requires([
        bv_new == bv1 | bv2,
    ]);
    ensures([
        forall(|i: u32| (i < 64) >>= get_bit64!(bv_new, i)  == (get_bit64!(bv1, i) || get_bit64!(bv2, i))),
    ]);
}

#[proof]
fn bit_or_64_view_proof(u1: u64, u2: u64, bv_new:u64){
    requires([
        bv_new == u1 | u2,
    ]);
    ensures([
        u64_view(bv_new).ext_equal(Seq::new(64, |i: int| u64_view(u1).index(i) || u64_view(u2).index(i))),
    ]);
    bit_or_64_proof(u1,u2, bv_new);
}

#[spec]
fn or_u64_relation(u1:u64, u2:u64, or_int:u64) -> bool {
    u64_view(or_int).ext_equal(Seq::new(64, |i: int| u64_view(u1).index(i) || u64_view(u2).index(i)))
}


pub struct BitMap {
    bits: Vec<u64>,
}

impl BitMap {
    #[spec]
    fn view(&self) -> Seq<bool> {        
        let width = self.bits.view().len() * 64;
        Seq::new(width, |i: int| u64_view(self.bits.view().index(i/64)).index(i%64))
    }

    #[exec]
    fn from(v: Vec<u64>) -> BitMap {
        BitMap{bits: v}
    }

    #[exec]
    fn get_bit(&self, index: u32) -> bool {
        requires([
            index < self.view().len(),
        ]);
        ensures(|ret:bool|[
            ret == self.view().index(index),
        ]);
        let seq_index:usize = (index/64) as usize;
        let bit_index = index%64;
        let target:u64 = *self.bits.index(seq_index);
        get_bit64!(target, bit_index)
    }

    #[exec]
    fn set_bit(self, index: u32, bit: bool) -> BitMap {
        requires([
            index < self.view().len(),
        ]);
        ensures(|ret:BitMap| [
            equal(ret.view(), self.view().update(index,bit)),
        ]);
        let seq_index = (index/64) as usize;
        let bit_index = index%64;
        let bv_old:u64 = *self.bits.index(seq_index);
        let bv_new:u64 = set_bit64!(bv_old, bit_index, bit);
        set_bit64_proof(bv_new, bv_old, bit_index, bit);
        let bits:Vec<u64> = self.bits.set(seq_index, bv_new);
        axiom_seq_update_same::<u64>(self.bits.view(), seq_index, bv_new);
        let result = BitMap{bits: bits};        
        assert(result.view().ext_equal(self.view().update(index,bit)));
        result
    }

    // bitwise-OR for bitmap
    #[exec]
    fn or(&self, bm: &BitMap, out: BitMap) -> BitMap {
        requires([
            self.view().len() == bm.view().len(),
            self.view().len() == out.view().len(),
        ]);
        ensures( |ret:BitMap| [
            self.view().len() == ret.view().len(),
            forall(|i: u32| (i < ret.view().len()) >>= (ret.view().index(i) == (self.view().index(i) || bm.view().index(i)))),
        ]);

        let n:usize = self.bits.len();
        let mut i:usize = 0;
        let mut v3:Vec<u64>;
        let mut result = BitMap{bits:out.bits};
        while i < n {
            invariant([
                i <= n,
                n == self.bits.view().len(),
                n == bm.bits.view().len(),
                n == result.bits.view().len(),
                forall(|k: usize| k < i >>=  or_u64_relation(self.bits.view().index(k), bm.bits.view().index(k), result.bits.view().index(k))),
                forall(|k: usize| k < i*64 >>= (result.view().index(k) == (self.view().index(k) || bm.view().index(k)))),
            ]);
            assert(i < n);
            v3 = result.bits;
            let u1:u64 = *self.bits.index(i);
            let u2:u64 = *bm.bits.index(i);
            let or_int:u64 = u1 | u2;
            bit_or_64_view_proof(u1, u2, or_int);
            axiom_seq_update_same::<u64>(result.bits.view(), i, or_int);
            v3 = v3.set(i, or_int);
            result = BitMap{bits:v3};
            i = i+1;
        }
        result
    }
}

#[verifier(external)]
fn main(){
    // Note that for bmap1, lsb is 0 from v1[0], and msb is 1 from v[3]
    let v1:Vec<u64> = Vec{vec: vec![0xfff0, 0xfff0, 0x000f, 0xf000_0000_0000_000f]};
    let v2:Vec<u64> = Vec{vec: vec![0x000f, 0x000f, 0xfff0, 0xfff0]};
    let v3:Vec<u64> = Vec{vec: vec![0x0, 0x0, 0x0, 0x0]}; // vector for output
    let mut bmap1 = BitMap::from(v1);
    println!("{:?}", bmap1.get_bit(255));
    println!("{:?}", bmap1.get_bit(0));
    bmap1 = bmap1.set_bit(0, true);
    println!("{:?}", bmap1.get_bit(0));
    println!("{:?}", bmap1.bits.vec);
    let bmap2 = BitMap::from(v2);
    let mut result = BitMap::from(v3);
    result = bmap1.or(&bmap2,result);
    println!("{:?}", result.bits.vec);
}       
