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
    requires(loc < 32);
    ensures(|ret:u32| ret == set_bit(bv,loc,bit));
    assert_bit_vector((if bit { bv | 1u32 << loc } else { bv & (!(1u32 << loc)) }) == set_bit(bv, loc, bit));
    let one = 1u32 << loc;
    if bit {bv | one}
    else {bv & (!one)}
}

#[exec]
fn get_two_bit_exec(bv:u32, index:u32) ->  Color {
    requires(index < 15);
    ensures(|c:Color| [
        c == color_view(get_bit(bv, 2*index +1), get_bit(bv, 2*index)),
    ]);
    let val = 3u32 & (bv >> index*2);
    assert_bit_vector(3u32 & (bv >> index*2) < 4);
    assert_bit_vector( 
        (if 3u32 & (bv >> index*2) == 3 {Color::Undefined} else if 3u32 & (bv >> index*2) == 2 {Color::Black} 
        else if 3u32 & (bv >> index*2)== 1 {Color::Gray} else {Color::White}) 
        == color_view(get_bit(bv, 2*index +1), get_bit(bv, 2*index)) 
    ); 

    if val == 3 {Color::Undefined} else if val == 2 {Color::Black} else if val == 1 {Color::Gray} else {Color::White}
}

#[exec]
fn set_two_bit_exec(bv:u32, low_loc:u32, high:bool, low:bool) -> u32 {
    requires(low_loc < 31);
    ensures(|ret:u32| [ 
        get_bit(ret, low_loc) == low,
        get_bit(ret, low_loc+1) == high,
        forall(|loc2:u32| (loc2 < 32 && loc2 != low_loc && loc2 != (low_loc+1)) >>= (get_bit(ret, loc2) == get_bit(bv, loc2))),
    ]);
    let target:u32 = {if high {if low {3u32} else {2u32}} else {if low {1u32} else {0u32}}} << low_loc;
    let mask:u32 = !(3u32 << low_loc);
    let result:u32 = (bv & mask) | target;
    assert_bit_vector(
        low_loc < 31 >>= 
        (get_bit((bv & (!(3u32 << low_loc))) |  
        ({if high {if low {3u32} else {2u32}} else {if low {1u32} else {0u32}}} << low_loc), low_loc) 
        == low));
    assert_bit_vector(
        low_loc < 31 >>= 
        (get_bit((bv & (!(3u32 << low_loc))) |  
        ({if high {if low {3u32} else {2u32}} else {if low {1u32} else {0u32}}} << low_loc), low_loc+1) 
        == high));
    assert_bit_vector(forall (|loc2:u32|  (low_loc <31 && loc2 < 32 && low_loc != loc2 && (low_loc+1) != loc2) >>=
            (get_bit((bv & (!(3u32 << low_loc))) |  
            ({if high {if low {3u32} else {2u32}} else {if low {1u32} else {0u32}}} << low_loc), loc2)
             ==  get_bit(bv, loc2))));
    result
}

// #[proof]
// fn set_bit_property_auto(bv:u32, bv2:u32, loc:u32, bit:bool) {
//     requires([
//         loc < 32,
//         bv2 == set_bit(bv,loc,bit),
//     ]);
//     ensures([
//         forall(|loc2:u32| (loc2 < 32 && loc != loc2) >>= (get_bit(bv2, loc2) == get_bit(bv, loc2))),
//         get_bit(bv2, loc) == bit,
//     ]);
//     assert_bit_vector(bv2 == set_bit(bv, loc, bit) >>= 
//         ((forall(|loc2:u32| (loc2 < 32 && loc != loc2) >>= (get_bit(bv2, loc2) == get_bit(bv, loc2)))))) ;

//     assert_bit_vector((loc < 32 && bv2 == set_bit(bv, loc, bit)) >>= 
//         get_bit(bv2, loc) == bit);
// }

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

#[spec]
fn bucket_view_aux(bucket: u32, index: u32) -> Seq<Color> {
    decreases(index);
    
    let up_bit:bool = get_bit(bucket, index*2 + 1);
    let low_bit:bool = get_bit(bucket, index*2);
    let c:Color = color_view(up_bit,low_bit);

    if index == 0 {
        seq![c]
    } else {
        bucket_view_aux(bucket, index-1).add(seq![c])
    }
}

#[proof]
fn bucket_view_aux_correspond(bucket: u32, i: u32) {
    decreases(i);
    requires(i < 16u32);
    ensures([
        bucket_view_aux(bucket, i).len() == i as int + 1,
        forall(|j: u32| (j <= i) >>= (bucket_view_aux(bucket, i).index(j) == color_view(get_bit(bucket, 2*j+1), get_bit(bucket, 2*j)))),
    ]);

    if i != 0 {
        bucket_view_aux_correspond(bucket, i - 1);
        // let prev = bucket_view_aux(bucket, i - 1);
        // let curr = bucket_view_aux(bucket, i);
        // let new_color:Color = color_view(get_bit(bucket, 2*i+1), get_bit(bucket, 2*i));
        // assert(forall(|j: u32| (j <= i - 1) >>= prev.index(j) == color_view(get_bit(bucket, 2*j+1), get_bit(bucket, 2*j))));
        // assert(curr.index(i) == new_color);
        // assert(prev.add(seq![new_color]).ext_equal(curr));
    }
}

#[spec]
fn bucket_view(bucket: u32) -> Seq<Color> {
    bucket_view_aux(bucket, 15)
}

#[proof]
fn bucket_view_correspond(bucket: u32) {
    ensures([
        bucket_view(bucket).len() == 16,
        forall(|i: u32| (i < 16) >>= bucket_view(bucket).index(i) == color_view(get_bit(bucket, 2*i+1), get_bit(bucket, 2*i)))
    ]);
    bucket_view_aux_correspond(bucket, 15);
}

#[exec]
fn set_color(bucket:u32, high:bool, low:bool , i:u32, #[proof] ghost_bucket:Seq<Color>) -> u32 {
    requires([
        i < 16,
        bucket_view(bucket).ext_equal(ghost_bucket)
    ]);
    ensures(|new_bucket: u32| [
        bucket_view(new_bucket).ext_equal(ghost_bucket.update(i, color_view(high,low))),
    ]);

    let new_bucket = set_two_bit_exec(bucket, 2*i, high, low);
    assert(color_view(high,low) == color_view(get_bit(new_bucket, 2*i+1), get_bit(new_bucket, 2*i)));
    bucket_view_correspond(bucket);
    bucket_view_correspond(new_bucket);
    new_bucket
}

fn main(){}
