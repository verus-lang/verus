//! The "standard library" for [Verus](https://github.com/verus-lang/verus).
//! Contains various utilities and datatypes for proofs,
//! as well as runtime functionality with specifications.
//! For an introduction to Verus, see [the tutorial](https://verus-lang.github.io/verus/guide/).
#![cfg_attr(not(feature = "std"), no_std)]
#![allow(unused_parens)]
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_attributes)]
#![allow(rustdoc::invalid_rust_codeblocks)]
#![cfg_attr(verus_keep_ghost, feature(core_intrinsics))]
#![cfg_attr(any(verus_keep_ghost, feature = "allocator"), feature(allocator_api))]
#![cfg_attr(verus_keep_ghost, feature(step_trait))]
#![cfg_attr(verus_keep_ghost, feature(ptr_metadata))]
#![cfg_attr(verus_keep_ghost, feature(strict_provenance_atomic_ptr))]
#![cfg_attr(verus_keep_ghost, feature(freeze))]
#![cfg_attr(verus_keep_ghost, feature(derive_clone_copy))]
#![cfg_attr(all(feature = "alloc", verus_keep_ghost), feature(liballoc_internals))]
#![cfg_attr(verus_keep_ghost, feature(new_range_api))]
#![feature(slice_index_methods)]

#![feature(unsized_fn_params)]
#[cfg(feature = "alloc")]
extern crate alloc;

#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod arithmetic;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod array;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod atomic;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod atomic_ghost;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod bits;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod bytes;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod calc_macro;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod cell;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod compute;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod float;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod function;
#[cfg(all(feature = "alloc", feature = "std"))]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod hash_map;
#[cfg(all(feature = "alloc", feature = "std"))]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod hash_set;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod invariant;
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod laws_cmp;
#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod laws_eq;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod layout;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod logatom;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod map;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod map_lib;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod math;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod modes;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod multiset;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod multiset_lib;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod pcm;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod pcm_lib;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod pervasive;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod proph;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod raw_ptr;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod primitive_int;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod endian;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod relations;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod rwlock;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod seq;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod seq_lib;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod set;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod set_lib;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod shared;
#[cfg(feature = "alloc")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod simple_pptr;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod slice;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod state_machine_internal;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod storage_protocol;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod string;
#[cfg(feature = "std")]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod thread;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod tokens;
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod view;

#[cfg(verus_keep_ghost)]
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod std_specs;

// Re-exports all vstd types, traits, and functions that are commonly used or replace
// regular `core` or `std` definitions.
#[stable(feature = "needed_for_compilation", since = "1.88.0")]
pub mod prelude;

use prelude::*;

verus! {

#[cfg_attr(verus_keep_ghost, verifier::broadcast_use_by_default_when_this_crate_is_imported)]
pub broadcast group group_vstd_default {
    //
    // basic Verus math, types, and features
    //
    seq::group_seq_axioms,
    seq_lib::group_seq_lib_default,
    map::group_map_axioms,
    set::group_set_axioms,
    set_lib::group_set_lib_default,
    multiset::group_multiset_axioms,
    compute::all_spec_ensures,
    function::group_function_axioms,
    laws_eq::group_laws_eq,
    laws_cmp::group_laws_cmp,
    //
    // Rust types
    //
    slice::group_slice_axioms,
    array::group_array_axioms,
    string::group_string_axioms,
    raw_ptr::group_raw_ptr_axioms,
    layout::group_layout_axioms,
    //
    // core std_specs
    //
    std_specs::range::group_range_axioms,
    std_specs::bits::group_bits_axioms,
    std_specs::control_flow::group_control_flow_axioms,
    std_specs::slice::group_slice_axioms,
    //
    // std_specs for alloc (with or without std)
    //
    #[cfg(feature = "alloc")]
    std_specs::vec::group_vec_axioms,
    #[cfg(feature = "alloc")]
    std_specs::vecdeque::group_vec_dequeue_axioms,
    //
    // std_specs for alloc + std
    //
    #[cfg(all(feature = "alloc", feature = "std"))]
    std_specs::hash::group_hash_axioms,
}

} // verus!
// This allows us to use `$crate::vstd` or `crate::vstd` to refer to vstd
// both in verus_verify_core mode (vstd is a module) and out (vstd is a crate)
#[cfg(not(verus_verify_core))]
#[doc(hidden)]
pub use crate as vstd;
