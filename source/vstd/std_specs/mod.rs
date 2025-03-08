#[cfg(feature = "alloc")]
pub mod alloc;

pub mod atomic;
pub mod bits;
pub mod clone;
pub mod control_flow;
pub mod core;

#[cfg(all(feature = "alloc", feature = "std"))]
pub mod hash;

pub mod num;
pub mod option;
pub mod range;
pub mod result;

#[cfg(feature = "alloc")]
pub mod vec;

#[cfg(feature = "alloc")]
pub mod vecdeque;

#[cfg(feature = "alloc")]
pub mod smart_ptrs;

// This struct is a hack that exists purely to create
// a rustdoc page dedicated to 'assume_specification' specs
pub struct VstdSpecsForRustStdLib;
