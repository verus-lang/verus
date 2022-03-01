#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;
use builtin_macros::*;

// macro_rules! assert_bit_vector{
//     ($a:expr)=>{
//         {
//             assert_bit_vector($a)
//         }
//     }
// }

macro_rules! get_bit_trigger{
    ($a:expr,$b:expr)=>{
        {
            #[trigger](0x1u32 & ($a>>$b))  == 1
        }
    }
}

macro_rules! get_bit{
    ($a:expr,$b:expr)=>{
        {
            (0x1u32 & ($a>>$b)) == 1
        }
    }
}

macro_rules! set_bit{
       ($a:expr,$b:expr, $c:expr)=>{
           {
                if $c {$a | 1u32 << $b}
                else {$a & (!(1u32 << $b))}
           }
       }
}

// #[proof]
// fn set_bit_property_auto(bv:u32, bv2:u32, loc:u32, bit:bool) {
//     requires([
//         loc < 32,
//         bv2 == set_bit!(bv,loc,bit),
//     ]);
//     ensures([
//         forall(|loc2:u32| (loc2 < 32 && loc != loc2) >>= (get_bit_trigger!(bv2, loc2) == get_bit!(bv, loc2))),
//         get_bit!(bv2, loc) == bit,
//     ]);
//     assert_bit_vector(bv2 == set_bit!(bv, loc, bit) >>= 
//         ((forall(|loc2:u32| (loc2 < 32 && loc != loc2) >>= (get_bit_trigger!(bv2, loc2) == get_bit!(bv, loc2)))))) ;

//     assert_bit_vector((loc < 32 && bv2 == set_bit!(bv, loc, bit)) >>= 
//         get_bit!(bv2, loc) == bit);
// }

#[derive(Structural, PartialEq, Eq)]
enum Color {
    White,     // 11
    Gray,      // 10
    Black,     // 01
    Undefined, // 00
}

#[spec]
fn color_view(high:bool, low:bool) -> Color {
    if high {if low {Color::White} else {Color::Gray}}
    else {if low {Color::Black} else {Color::Undefined}}
}

#[spec]
fn bucket_view(bucket: u32) -> Seq<Color> {
    Seq::new(16, |i: int| color_view(get_bit!(bucket, (i as u32)*2 + 1),get_bit!(bucket, (i as u32) * 2)))
}

#[exec]
fn set_two_bit_exec(bv:u32, low_loc:u32, high:bool, low:bool) -> u32 {
    requires(low_loc < 31);
    ensures(|ret:u32| [ 
        get_bit!(ret, low_loc) == low,
        get_bit!(ret, low_loc+1) == high,
        forall(|loc2:u32| (loc2 < 32 && loc2 != low_loc && loc2 != (low_loc+1)) >>= (get_bit_trigger!(ret, loc2) == get_bit!(bv, loc2))),
    ]);
    let target:u32 = {if high {if low {3u32} else {2u32}} else {if low {1u32} else {0u32}}} << low_loc;
    let mask:u32 = !(3u32 << low_loc);
    let result:u32 = (bv & mask) | target;
    assert_bit_vector(
        low_loc < 31 >>= 
        (get_bit!((bv & (!(3u32 << low_loc))) |  
        ({if high {if low {3u32} else {2u32}} else {if low {1u32} else {0u32}}} << low_loc), low_loc) 
        == low));
    assert_bit_vector(
        low_loc < 31 >>= 
        (get_bit!((bv & (!(3u32 << low_loc))) |  
        ({if high {if low {3u32} else {2u32}} else {if low {1u32} else {0u32}}} << low_loc), low_loc+1) 
        == high));
    forall(|loc2:u32| { 
        ensures((low_loc <31 && loc2 < 32 && low_loc != loc2 && (low_loc+1) != loc2) >>=
        (get_bit!((bv & (!(3u32 << low_loc))) |  
        ({if high {if low {3u32} else {2u32}} else {if low {1u32} else {0u32}}} << low_loc), loc2)
         ==  get_bit_trigger!(bv, loc2)));

        assert_bit_vector((low_loc <31 && loc2 < 32 && low_loc != loc2 && (low_loc+1) != loc2) >>=
        (get_bit!((bv & (!(3u32 << low_loc))) |  
        ({if high {if low {3u32} else {2u32}} else {if low {1u32} else {0u32}}} << low_loc), loc2)
         ==  get_bit_trigger!(bv, loc2)));
    });
    result
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
    assert(color_view(high,low) == color_view(get_bit!(new_bucket, 2*i+1), get_bit!(new_bucket, 2*i)));
    new_bucket
}

#[exec]
fn get_color(bv:u32, index:u32) -> Color {
    requires(index < 15);
    ensures(|c:Color| [
        c == color_view(get_bit!(bv, 2*index +1), get_bit!(bv, 2*index)),
    ]);

    let v: u32 = 3u32 & (bv >> index*2);

    assert_bit_vector(0 <= 3u32 & (bv >> index*2));
    assert_bit_vector(3u32 & (bv >> index*2) < 4);

    assert_bit_vector((3u32 & (bv >> index*2) == 3) >>= get_bit!(bv, index*2));
    assert_bit_vector((3u32 & (bv >> index*2) == 3) >>= get_bit!(bv, index*2+1));

    assert_bit_vector((3u32 & (bv >> index*2) == 2) >>= !get_bit!(bv, index*2));
    assert_bit_vector((3u32 & (bv >> index*2) == 2) >>= get_bit!(bv, index*2+1));

    assert_bit_vector((3u32 & (bv >> index*2) == 1) >>= get_bit!(bv, index*2));
    assert_bit_vector((3u32 & (bv >> index*2) == 1) >>= !get_bit!(bv, index*2+1));

    assert_bit_vector((3u32 & (bv >> index*2) == 0) >>= !get_bit!(bv, index*2));
    assert_bit_vector((3u32 & (bv >> index*2) == 0) >>= !get_bit!(bv, index*2+1));

    let c = if v == 0 {
        Color::Undefined
    } else if v == 1 {
        Color::Black
    } else if v == 2 {
        Color::Gray
    } else {
        Color::White
    };
    assert(c == color_view(get_bit!(bv, 2*index +1), get_bit!(bv, 2*index)));
    c
}


fn main(){}
