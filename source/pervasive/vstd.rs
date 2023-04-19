//! The "standard library" for [Verus](https://github.com/verus-lang/verus).
//! Contains various utilities and datatypes for proofs,
//! as well as runtime functionality with specifications.
//! For an introduction to Verus, see [the tutorial](https://verus-lang.github.io/verus/guide/).

#![feature(stmt_expr_attributes)]
#![feature(negative_impls)]
#![feature(register_tool)]
#![feature(rustc_attrs)]
#![feature(unboxed_closures)]

#![allow(unused_parens)]
#![allow(rustdoc::invalid_rust_codeblocks)]

pub mod pervasive;
pub mod bytes;
pub mod calc_macro;
pub mod map;
pub mod option;
pub mod result;
pub mod seq;
pub mod seq_lib;
pub mod set;
pub mod set_lib;
pub mod slice;
pub mod cell;
pub mod invariant;
pub mod atomic;
pub mod atomic_ghost;
pub mod modes;
pub mod multiset;
pub mod function;
pub mod state_machine_internal;
#[cfg(not(feature = "non_std"))]
pub mod thread;
#[cfg(not(feature = "no_global_allocator"))] 
pub mod ptr;
#[cfg(not(feature = "no_global_allocator"))] 
pub mod string;
#[cfg(not(feature = "no_global_allocator"))] 
pub mod vec;

// Re-exports all pervasive types, traits, and functions that are commonly used or replace
// regular `core` or `std` definitions.
pub mod prelude;
