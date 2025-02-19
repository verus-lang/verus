// examples of using `OverflowingU32` and `OverflowingU64`
use vstd::prelude::*;
use vstd::arithmetic::overflow::*;

verus! {

fn overflowable_u64_constants()
{
    let w = OverflowableU64::new(0xFFFFFFFFFFFFFFFF);
    let x = w.add(1);
    assert(x.is_overflowed());
    assert(x.view() == 0x10000000000000000);

    let y = OverflowableU64::new(0x8000000000000000);
    let z = y.mul(2);
    assert(z.is_overflowed());
    assert(z.view() == 0x10000000000000000);
}

fn overflowable_u64_calculations(a: u64, b: u64, c: u64, d: u64) -> (result: Option<u64>)
    ensures
        match result {
            Some(v) => v == a * b + c * d,
            None => a * b + c * d > u64::MAX,
        }
{
    let a_times_b = OverflowableU64::new(a).mul(b);
    let c_times_d = OverflowableU64::new(c).mul(d);
    let sum_of_products = a_times_b.add_overflowable_u64(&c_times_d);
    if sum_of_products.is_overflowed() {
        assert(a * b + c * d > u64::MAX);
        None
    }
    else {
        let i: u64 = sum_of_products.unwrap();
        assert(i == a * b + c * d);
        Some(i)
    }
}

fn overflowable_u32_constants()
{
    let w = OverflowableU32::new(0xFFFFFFFF);
    let x = w.add(9);
    assert(x.is_overflowed());
    assert(x.view() == 0x100000008);

    let y = OverflowableU32::new(0x40000000);
    let z = y.mul(8);
    assert(z.is_overflowed());
    assert(z.view() == 0x200000000);
}

fn overflowable_u32_calculations(a: u32, b: u32, c: u32, d: u32, e: u32) -> (result: Option<u32>)
    ensures
        match result {
            Some(v) => v == a * b + c * d + e,
            None => a * b + c * d + e > u32::MAX,
        }
{
    let a_times_b = OverflowableU32::new(a).mul(b);
    let c_times_d = OverflowableU32::new(c).mul(d);
    let sum_of_products = a_times_b.add_overflowable_u32(&c_times_d);
    let f = sum_of_products.add(e);
    f.to_option()
}

} // verus!
fn main() {}
