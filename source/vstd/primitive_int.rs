use super::prelude::*;

verus! {

// #[cfg_attr(rustc_diagnostic_item = "verus::vstd::PrimitiveInt")]
// #[cfg_attr(verus_keep_ghost, verifier::sealed)]
pub trait PrimitiveInt {

}

impl PrimitiveInt for u8 {

}

impl PrimitiveInt for u16 {

}

impl PrimitiveInt for u32 {

}

impl PrimitiveInt for u64 {

}

impl PrimitiveInt for u128 {

}

impl PrimitiveInt for usize {

}

impl PrimitiveInt for i8 {

}

impl PrimitiveInt for i16 {

}

impl PrimitiveInt for i32 {

}

impl PrimitiveInt for i64 {

}

impl PrimitiveInt for i128 {

}

impl PrimitiveInt for isize {

}

} // verus!
