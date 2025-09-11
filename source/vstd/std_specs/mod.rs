#[cfg(feature = "alloc")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod alloc;

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod atomic;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod bits;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod borrow;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod clone;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod cmp;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod control_flow;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod core;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod ops;

#[cfg(all(feature = "alloc", feature = "std"))]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod hash;

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod num;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod option;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod range;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod result;

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod slice;

#[cfg(feature = "alloc")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod vec;

#[cfg(feature = "alloc")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod vecdeque;

#[cfg(feature = "alloc")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod smart_ptrs;

// This struct is a hack that exists purely to create
// a rustdoc page dedicated to 'assume_specification' specs
pub struct VstdSpecsForRustStdLib;
