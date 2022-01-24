#[allow(unused_imports)]
use builtin::*;
mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::seq::*;
use builtin_macros::*;

#[derive(Structural, PartialEq, Eq)]
enum Color {
    White,     // 00
    Gray,      // 01
    Black,     // 10
    Undefined, // 11
}

#[spec]
fn bucket_view(bucket: u32, index: u32) -> Seq<Color> {
    decreases(index);

    let mask:u32 = 3;
    let shift:u32 = (15 - index) * 2;
    let color_bit = mask & (bucket >> shift);
    let c:Color = 
       if color_bit == 0 {Color::White}
       else if color_bit == 1 {Color::Gray}
       else if color_bit == 2 {Color::Black}
       else {Color::Undefined};

    if index == 0 {
        seq![c]
    } else {
        seq![c].add(bucket_view(bucket, index-1))
    }
}

#[exec]
fn set_color(bucket:u32, c:Color, index:u32, #[proof] ghost_bucket:Seq<Color>) -> u32 {
    requires([
        index < 16,
        bucket_view(bucket, 0).ext_equal(ghost_bucket)
        // interpret(bucket, 0) == ghost_bucket,
    ]);
    ensures(|new_bucket: u32| [
        bucket_view(new_bucket, 0).ext_equal(ghost_bucket.update(index, c)),
        // interpret(new_bucket, 0) == ghost_bucket.update(index, c),
    ]);

    let mask:u32 = !( (3 as u32) << (index*2) );
    let bucket_masked = bucket & mask;
    let num_color:u32 = match c {
        Color::White => 0,
        Color::Gray =>  1,
        Color::Black => 2,
        Color::Undefined => 3,
    };
    let new_bucket:u32 = bucket_masked | (num_color << (index*2));
    new_bucket
}

fn main(){}
