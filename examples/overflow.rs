// examples of using `CheckedU32` and `CheckedU64`
use vstd::prelude::*;
use vstd::arithmetic::overflow::*;

verus! {

fn checked_u64_constants()
{
    let w = CheckedU64::new(0xFFFFFFFFFFFFFFFF);
    let x = w.add_value(1);
    assert(x.is_overflowed());
    assert(x.view() == 0x10000000000000000);

    let y = CheckedU64::new(0x8000000000000000);
    let z = y.mul_value(2);
    assert(z.is_overflowed());
    assert(z.view() == 0x10000000000000000);
}

fn checked_u64_calculations(a: u64, b: u64, c: u64, d: u64) -> (result: Option<u64>)
    ensures
        match result {
            Some(v) => v == a * b + c * d,
            None => a * b + c * d > u64::MAX,
        }
{
    let a_times_b = CheckedU64::new(a).mul_value(b);
    let c_times_d = CheckedU64::new(c).mul_value(d);
    let sum_of_products = a_times_b.add_checked(&c_times_d);
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

fn checked_u32_constants()
{
    let w = CheckedU32::new(0xFFFFFFFF);
    let x = w.add_value(9);
    assert(x.is_overflowed());
    assert(x.view() == 0x100000008);

    let y = CheckedU32::new(0x40000000);
    let z = y.mul_value(8);
    assert(z.is_overflowed());
    assert(z.view() == 0x200000000);
}

fn checked_u32_calculations(a: u32, b: u32, c: u32, d: u32, e: u32) -> (result: Option<u32>)
    ensures
        match result {
            Some(v) => v == a * b + c * d + e,
            None => a * b + c * d + e > u32::MAX,
        }
{
    let a_times_b = CheckedU32::new(a).mul_value(b);
    let c_times_d = CheckedU32::new(c).mul_value(d);
    let sum_of_products = a_times_b.add_checked(&c_times_d);
    let f = sum_of_products.add_value(e);
    f.to_option()
}

} // verus!
fn main() {}
