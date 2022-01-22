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

#[proof]
fn interpret(bucket: u32, index: u32) -> Seq<Color> {
    requires([
        index < 16,
    ]);
    decreases(16-index);

    let mask:u32 = 3;
    let color_bit = mask & (bucket >> index*2);
    let c:Color = 
       if color_bit == 0 {Color::White}
       else if color_bit == 1 {Color::Gray}
       else if color_bit == 2 {Color::Black}
       else {Color::Undefined};

    if index == 15 {seq![c]}
    else {let rest = interpret(bucket, index+1); rest.push(c)}
}

#[exec]
fn set_color(bucket:u32, c:Color, index:u32, #[proof] ghost_bucket:Seq<Color>) -> u32 {
    requires([
        index < 16,
        interpret(bucket, 0).ext_equal(ghost_bucket)
        // interpret(bucket, 0) == ghost_bucket,
    ]);
    ensures(|new_bucket: u32| [
        interpret(new_bucket, 0).ext_equal(ghost_bucket.update(index, c)),
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
