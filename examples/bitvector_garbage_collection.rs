#[allow(unused_imports)]
use vstd::prelude::*;

macro_rules! get_bit_macro {
    ($a:expr, $b:expr) => {{
        (0x1u32 & ($a >> $b)) == 1
    }};
}

macro_rules! get_bit {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(get_bit_macro!($($a)*))
    }
}
fn main() {}

verus! {

#[derive(Structural, PartialEq, Eq)]
enum Color {
    White,  // 11
    Gray,  // 10
    Black,  // 01
    Undefined,  // 00
}

spec fn color_view(high: bool, low: bool) -> Color {
    if high {
        if low {
            Color::White
        } else {
            Color::Gray
        }
    } else {
        if low {
            Color::Black
        } else {
            Color::Undefined
        }
    }
}

spec fn bucket_view(bucket: u32) -> Seq<Color> {
    Seq::new(
        16,
        |i: int|
            color_view(
                get_bit!(bucket, add(mul(i as u32, 2), 1)),
                get_bit!(bucket, mul(i as u32, 2)),
            ),
    )
}

#[verifier::bit_vector]
proof fn set_two_bit_proof(
    bv: u32,
    target: u32,
    mask: u32,
    result: u32,
    low_loc: u32,
    high: bool,
    low: bool,
)
    requires
        low_loc < 31,
        target == (if high {
            if low {
                3u32
            } else {
                2u32
            }
        } else {
            if low {
                1u32
            } else {
                0u32
            }
        }) << low_loc,
        mask == !(3u32 << low_loc),
        result == (bv & mask) | target,
    ensures
        get_bit!(result, low_loc) == low,
        get_bit!(result, add(low_loc, 1)) == high,
        forall|loc2: u32|
            #![auto]
            loc2 < 32 && loc2 != low_loc && loc2 != add(low_loc, 1) ==> get_bit!(result, loc2)
                == get_bit!(bv, loc2),
{
}

fn set_two_bit_exec(bv: u32, low_loc: u32, high: bool, low: bool) -> (ret: u32)
    requires
        low_loc < 31,
    ensures
        get_bit!(ret, low_loc) == low,
        get_bit!(ret, add(low_loc, 1)) == high,
        forall|loc2: u32|
            #![auto]
            loc2 < 32 && loc2 != low_loc && loc2 != add(low_loc, 1) ==> get_bit!(ret, loc2)
                == get_bit!(bv, loc2),
{
    let target: u32 = (if high {
        if low {
            3u32
        } else {
            2u32
        }
    } else {
        if low {
            1u32
        } else {
            0u32
        }
    }) << low_loc;
    let mask: u32 = !(3u32 << low_loc);
    let result: u32 = (bv & mask) | target;
    proof {
        set_two_bit_proof(bv, target, mask, result, low_loc, high, low);
    }
    result
}

fn set_color(bucket: u32, high: bool, low: bool, i: u32, ghost_bucket: Seq<Color>) -> (new_bucket:
    u32)
    requires
        i < 16,
        bucket_view(bucket) =~= ghost_bucket,
    ensures
        bucket_view(new_bucket) =~= ghost_bucket.update(i as int, color_view(high, low)),
{
    let new_bucket = set_two_bit_exec(bucket, 2 * i, high, low);
    assert(color_view(high, low) == color_view(
        get_bit!(new_bucket, add(mul(2, i), 1)),
        get_bit!(new_bucket, mul(2, i)),
    ));
    new_bucket
}

#[verifier::bit_vector]
proof fn get_color_proof(bv: u32, index: u32, v: u32)
    requires
        v == 3u32 & (bv >> mul(index, 2)),
    ensures
        v < 4u32,
        v == 3 ==> get_bit!(bv, mul(index, 2)) && get_bit!(bv, add(mul(index, 2), 1)),
        v == 2 ==> !get_bit!(bv, mul(index, 2)) && get_bit!(bv, add(mul(index, 2), 1)),
        v == 1 ==> get_bit!(bv, mul(index, 2)) && !get_bit!(bv, add(mul(index, 2), 1)),
        v == 0 ==> !get_bit!(bv, mul(index, 2)) && !get_bit!(bv, add(mul(index, 2), 1)),
{
}

fn get_color(bv: u32, index: u32) -> (c: Color)
    requires
        index < 15,
    ensures
        c == color_view(get_bit!(bv, add(mul(2, index), 1)), get_bit!(bv, mul(2, index))),
{
    let v: u32 = 3u32 & (bv >> index * 2);
    proof {
        get_color_proof(bv, index, v);
    }
    let c = if v == 0 {
        Color::Undefined
    } else if v == 1 {
        Color::Black
    } else if v == 2 {
        Color::Gray
    } else {
        Color::White
    };
    c
}

} // verus!
