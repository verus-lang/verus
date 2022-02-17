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

#[exec]
fn get_bit_exec(bv:u32, loc:u32) -> bool {
    ensures(|ret:bool| ret == get_bit(bv,loc));
    assert_bit_vector((0x1u32 & (bv>>loc) == 1) == get_bit(bv, loc));
    if 0x1u32 & bv>>loc == 1 {true}
    else {false}
}

#[exec]
fn set_bit_exec(bv:u32, loc:u32, bit:bool) -> u32 {
    ensures(|ret:u32| ret == set_bit(bv,loc,bit));
    assert_bit_vector((if bit { bv | 1u32 << loc } else { bv & (!(1u32 << loc)) }) == set_bit(bv, loc, bit));
    let one = 1u32 << loc;
    if bit {
        bv | one
    }
    else {
        bv & (!one)
    }
}

#[proof]
fn set_bit_property_auto(bv:u32, bv2:u32, loc:u32, bit:bool) {
    requires([
        loc < 32,
        bv2 == set_bit(bv,loc,bit),
    ]);
    ensures([
        forall(|loc2:u32| (loc2 < 32 && loc != loc2) >>= (get_bit(bv2, loc2) == get_bit(bv, loc2))),
        get_bit(bv2, loc) == bit
    ]);
    assert_bit_vector(bv2 == set_bit(bv, loc, bit) >>= 
        ((forall(|loc2:u32| (loc2 < 32 && loc != loc2) >>= (get_bit(bv2, loc2) == get_bit(bv, loc2)))))) ;

    assert_bit_vector((loc < 32 && bv2 == set_bit(bv, loc, bit)) >>= 
        get_bit(bv2, loc) == bit);
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

#[proof]
fn bv_view_aux_correspond(bv: u32, i: u32) {
    decreases(i);
    ensures([
        bv_view_aux(bv, i).len() == i as int + 1,
        forall(|j: u32| (j < i) >>= bv_view_aux(bv, i).index(j) == get_bit(bv, j))
    ]);

    if i != 0 {
        bv_view_aux_correspond(bv, i - 1);
        let prev = bv_view_aux(bv, i - 1);
        let curr = bv_view_aux(bv, i);

       assert(forall(|j: u32| (j < i - 1) >>= prev.index(j) == get_bit(bv, j)));
       assert(prev.add(seq![get_bit(bv, i)]).ext_equal(curr));
    }
}

#[spec]
fn bv_view(bv: u32) -> Seq<bool> {
    bv_view_aux(bv, 31)
}

#[proof]
fn bv_view_correspond(bv: u32)
{
    ensures([
        bv_view(bv).len() == 32,
        forall(|i: u32| (i < 32) >>= bv_view(bv).index(i) == get_bit(bv, i))
    ]);
    bv_view_aux_correspond(bv, 31);
}

#[derive(Structural, PartialEq, Eq)]
enum Color {
    White,     // 00
    Gray,      // 01
    Black,     // 10
    Undefined, // 11
}

#[spec]
fn color_view(high:bool, low:bool) -> Color {
    if high {if low {Color::White} else {Color::Gray}}
    else {if low {Color::Black} else {Color::Undefined}}
}

#[exec]
fn color_to_bits(c: Color) -> (bool, bool) {
    match c {
        Color::White => (false, false),
        Color::Gray =>  (false, true),
        Color::Black => (true, false),
        Color::Undefined => (true, true),
    }
}

#[spec]
fn bucket_view(bucket: u32, index: u32) -> Seq<Color> {
    decreases(index);
    
    let up_bit:bool = get_bit(bucket, index*2 + 1);
    let low_bit:bool = get_bit(bucket, index*2);
    let c:Color = color_view(up_bit,low_bit);

    if index == 0 {
        seq![c]
    } else {
        bucket_view(bucket, index-1).add(seq![c])
    }
}

// #[exec]
// fn set_color(bucket:u32, high:bool, low:bool , index:u32, #[proof] ghost_bucket:Seq<Color>) -> u32 {
//     requires([
//         index < 16,
//         bucket_view(bucket, 15).ext_equal(ghost_bucket)
//     ]);
//     ensures(|new_bucket: u32| [
//         bucket_view(new_bucket, 15).ext_equal(ghost_bucket.update(index, color_view(high,low))),
//     ]);

//     reveal_with_fuel(bucket_view, 3);  // 15?

//     let bucket1 = set_bit_exec(bucket, 2*index+1, high);
//     let new_bucket = set_bit_exec(bucket1, 2*index, low);
//     assert(bucket_view(bucket,15).index(index) == color_view(high,low));
//     new_bucket
// }

fn main(){}

    // shift is uintshift, hence there is no sementic....  maybe I need `variable support` for assert_bit_vector
    // 1. I can support the  semantics of <<,!, etc.   OR
    // 2. make function mode, and interpret everything as bitvector in bv function mode
    
    // implement forall in assert_bit_vector
    // fix 
    // make gc work
    // bv function mode ?
    // separate process
