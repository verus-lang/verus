#![no_std]
#![allow(internal_features)]
#![cfg_attr(
    verus_keep_ghost,
    feature(rustc_attrs),
    feature(negative_impls),
    feature(unboxed_closures),
    feature(fn_traits),
    feature(register_tool),
    feature(tuple_trait),
    register_tool(verus),
    register_tool(verifier)
)]

use core::marker::PhantomData;

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::admit"]
#[verifier::proof]
pub fn admit() {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::no_method_body"]
#[verifier::proof]
pub fn no_method_body() -> ! {
    unimplemented!()
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::requires"]
#[verifier::proof]
pub fn requires<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::ensures"]
#[verifier::proof]
pub fn ensures<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of spec function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::recommends"]
#[verifier::proof]
pub fn recommends<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of loop body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::invariant_except_break"]
#[verifier::proof]
pub fn invariant_except_break<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of loop body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::invariant"]
#[verifier::proof]
pub fn invariant<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::decreases"]
#[verifier::proof]
pub fn decreases<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
// decrease_when is automatically added to list of recommends
#[cfg(verus_keep_ghost)]
#[verifier::proof]
#[rustc_diagnostic_item = "verus::builtin::decreases_when"]
pub fn decreases_when(_b: bool) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::decreases_by"]
#[verifier::proof]
pub fn decreases_by<F>(_f: F) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::recommends_by"]
#[verifier::proof]
pub fn recommends_by<F>(_f: F) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::extra_dependency"]
#[verifier::proof]
pub fn extra_dependency<F>(_f: F) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::opens_invariants_none"]
#[verifier::proof]
pub fn opens_invariants_none() {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::opens_invariants_any"]
#[verifier::proof]
pub fn opens_invariants_any() {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::opens_invariants"]
#[verifier::proof]
pub fn opens_invariants<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::opens_invariants_except"]
#[verifier::proof]
pub fn opens_invariants_except<A>(_a: A) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::no_unwind"]
#[verifier::proof]
pub fn no_unwind() {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::no_unwind_when"]
#[verifier::proof]
pub fn no_unwind_when(_b: bool) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::reveal_hide"]
#[verifier::proof]
pub fn reveal_hide_(_f: fn(), _n: u32) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::reveal_hide_internal_path"]
pub fn reveal_hide_internal_path_<A>(_x: A) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::imply"]
#[verifier::spec]
pub fn imply(_b1: bool, _b2: bool) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::forall"]
#[verifier::spec]
pub fn forall<A>(_a: A) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::exists"]
#[verifier::spec]
pub fn exists<A>(_a: A) -> bool {
    unimplemented!();
}

// choose(|x: t| P(x))
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::choose"]
#[verifier::spec]
pub fn choose<A, F: Fn(A) -> bool>(_f: F) -> A {
    unimplemented!()
}

// let (x1, ..., xn): (t1, ..., tn) = choose_tuple(|x1: t1, ..., xn: tn| P(x1, ..., xn));
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::choose_tuple"]
#[verifier::spec]
pub fn choose_tuple<A, F>(_f: F) -> A {
    unimplemented!()
}

// used by with_triggers! macro
// example: forall with three triggers [f(x), g(y)], [h(x, y)], [m(y, x)]:
//   forall( |x: int, y: int| with_triggers(  ( (f(x), g(y)), (h(x, y),), (m(y, x),) )  ,  body  ) )
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::with_triggers"]
#[verifier::spec]
pub fn with_triggers<A, B>(_triggers_tuples: A, body: B) -> B {
    body
}

// example: forall with three triggers [f(x), g(y)], [h(x, y)], [m(y, x)]:
//   forall(|x: int, y: int| with_triggers!([f(x), g(y)], [h(x, y)], [m(y, x)] => body))
#[macro_export]
macro_rules! with_triggers {
    ( $([ $($term:expr),* ]),* => $body:expr) => {
        {
            with_triggers(( $( ( $( $term, )* ), )* ), $body)
        }
    }
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::equal"]
#[verifier::spec]
pub fn equal<A>(_: A, _: A) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::ext_equal"]
#[verifier::spec]
pub fn ext_equal<A>(_: A, _: A) -> bool {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::ext_equal_deep"]
#[verifier::spec]
pub fn ext_equal_deep<A>(_: A, _: A) -> bool {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::old"]
#[verifier::spec]
pub fn old<A>(_: A) -> A {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::is_variant"]
#[verifier::spec]
pub fn is_variant<Adt>(_a: Adt, _variant: &str) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::get_variant_field"]
#[verifier::spec]
pub fn get_variant_field<Adt, Field>(_a: Adt, _variant: &str, _field: &str) -> Field {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::get_union_field"]
#[verifier::spec]
pub fn get_union_field<Adt, Field>(_a: Adt, _field: &str) -> Field {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::assume_"]
#[verifier::proof]
pub fn assume_(_: bool) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::assert_"]
#[verifier::proof]
pub fn assert_(_: bool) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::assert_by"]
#[verifier::proof]
pub fn assert_by(_: bool, _: ()) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::assert_by_compute"]
#[verifier::proof]
pub fn assert_by_compute(_: bool) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::assert_by_compute_only"]
#[verifier::proof]
pub fn assert_by_compute_only(_: bool) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::assert_nonlinear_by"]
#[verifier::proof]
pub fn assert_nonlinear_by(_: ()) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::assert_bitvector_by"]
#[verifier::proof]
pub fn assert_bitvector_by(_: ()) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::assert_forall_by"]
#[verifier::proof]
pub fn assert_forall_by<A>(_a: A) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::assert_bit_vector"]
#[verifier::proof]
pub fn assert_bit_vector(_: bool) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::use_type_invariant"]
#[verifier::proof]
pub fn use_type_invariant<A>(_a: A) {
    unimplemented!();
}

//
// Ghost, Tracked
//

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::builtin::Ghost")]
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types_in_ground_variants(A))]
pub struct Ghost<A> {
    phantom: PhantomData<A>,
}

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::builtin::Tracked")]
#[cfg_attr(verus_keep_ghost, verifier::external_body)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types_in_ground_variants(A))]
pub struct Tracked<A> {
    phantom: PhantomData<A>,
}

impl<A> Ghost<A> {
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::Ghost::view"]
    #[verifier::spec]
    pub fn view(self) -> A {
        unimplemented!()
    }

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::Ghost::new"]
    #[verifier::spec]
    #[verifier::external_body]
    pub fn new(_a: A) -> Ghost<A> {
        Ghost { phantom: PhantomData }
    }

    #[doc(hidden)]
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    #[inline(always)]
    pub const fn assume_new() -> Self {
        Ghost { phantom: PhantomData }
    }

    // The argument here is used as part of a trick to avoid
    // type inference errors when erasing code.

    #[doc(hidden)]
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    #[inline(always)]
    pub const fn assume_new_fallback(_: fn() -> A) -> Self {
        Ghost { phantom: PhantomData }
    }

    // note that because we return #[verifier::spec], not #[verifier::exec], we do not implement the Borrow trait
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::Ghost::borrow"]
    #[verifier::spec]
    #[verifier::external_body]
    pub fn borrow(&self) -> &A {
        unimplemented!()
    }

    // note that because we return #[verifier::spec], not #[verifier::exec], we do not implement the BorrowMut trait
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::Ghost::borrow_mut"]
    #[verifier::proof]
    #[verifier::external]
    pub fn borrow_mut(#[verifier::proof] &mut self) -> &mut A {
        unimplemented!()
    }
}

impl<A> Tracked<A> {
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::Tracked::view"]
    #[verifier::spec]
    pub fn view(self) -> A {
        unimplemented!()
    }

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::Tracked::new"]
    #[verifier::proof]
    #[verifier::external_body]
    pub fn new(#[verifier::proof] _a: A) -> Tracked<A> {
        Tracked { phantom: PhantomData }
    }

    #[doc(hidden)]
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    #[inline(always)]
    pub const fn assume_new() -> Self {
        Tracked { phantom: PhantomData }
    }

    #[doc(hidden)]
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    #[inline(always)]
    pub const fn assume_new_fallback(_: fn() -> A) -> Self {
        Tracked { phantom: PhantomData }
    }

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::Tracked::get"]
    #[verifier::proof]
    #[verifier::external_body]
    #[verifier::returns(proof)]
    pub fn get(#[verifier::proof] self) -> A {
        unimplemented!()
    }

    // note that because we return #[verifier::proof], not #[verifier::exec], we do not implement the Borrow trait
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::Tracked::borrow"]
    #[verifier::proof]
    #[verifier::external_body]
    #[verifier::returns(proof)]
    pub fn borrow(#[verifier::proof] &self) -> &A {
        unimplemented!()
    }

    // note that because we return #[verifier::proof], not #[verifier::exec], we do not implement the BorrowMut trait
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::Tracked::borrow_mut"]
    #[verifier::proof]
    #[verifier::external_body]
    #[verifier::returns(proof)]
    pub fn borrow_mut(#[verifier::proof] &mut self) -> &mut A {
        unimplemented!()
    }
}

impl<A> Clone for Ghost<A> {
    #[cfg_attr(verus_keep_ghost, verifier::external_body)]
    #[inline(always)]
    fn clone(&self) -> Self {
        Ghost { phantom: PhantomData }
    }
}

impl<A> Copy for Ghost<A> {}

impl<A: Copy> Clone for Tracked<A> {
    #[cfg_attr(verus_keep_ghost, verifier::external_body)]
    #[inline(always)]
    fn clone(&self) -> Self {
        Tracked { phantom: PhantomData }
    }
}

impl<A: Copy> Copy for Tracked<A> {}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::ghost_exec"]
#[verifier::external_body]
pub fn ghost_exec<A>(#[verifier::spec] _a: A) -> Ghost<A> {
    Ghost::assume_new()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::tracked_exec"]
#[verifier::external_body]
pub fn tracked_exec<A>(#[verifier::proof] _a: A) -> Tracked<A> {
    Tracked::assume_new()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::tracked_exec_borrow"]
#[verifier::external_body]
pub fn tracked_exec_borrow<'a, A>(#[verifier::proof] _a: &'a A) -> &'a Tracked<A> {
    // TODO: implement this (using unsafe) or mark function as ghost (if supported by Rust)
    unimplemented!();
}

//
// int and nat
//

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::builtin::int")]
#[allow(non_camel_case_types)]
#[derive(Clone, Copy)]
pub struct int;

// TODO: we should eventually be able to remove this and other int/nat ops,
// since we now have SpecAdd, etc.
impl core::ops::Add for int {
    type Output = Self;
    fn add(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl core::ops::Sub for int {
    type Output = Self;
    fn sub(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl core::ops::Mul for int {
    type Output = Self;
    fn mul(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl core::ops::Div for int {
    type Output = Self;
    fn div(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl core::ops::Rem for int {
    type Output = Self;
    fn rem(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl core::ops::Neg for int {
    type Output = Self;
    fn neg(self) -> Self::Output {
        unimplemented!()
    }
}

impl PartialEq for int {
    fn eq(&self, _other: &Self) -> bool {
        unimplemented!()
    }
}

impl Eq for int {}

impl core::cmp::PartialOrd for int {
    fn partial_cmp(&self, _other: &Self) -> Option<core::cmp::Ordering> {
        unimplemented!()
    }
}

impl core::cmp::Ord for int {
    fn cmp(&self, _other: &Self) -> core::cmp::Ordering {
        unimplemented!()
    }
}

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::builtin::nat")]
#[allow(non_camel_case_types)]
#[derive(Clone, Copy)]
pub struct nat;

impl core::ops::Add for nat {
    type Output = Self;
    fn add(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl core::ops::Sub for nat {
    type Output = Self;
    fn sub(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl core::ops::Mul for nat {
    type Output = Self;
    fn mul(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl core::ops::Div for nat {
    type Output = Self;
    fn div(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl core::ops::Rem for nat {
    type Output = Self;
    fn rem(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl PartialEq for nat {
    fn eq(&self, _other: &Self) -> bool {
        unimplemented!()
    }
}

impl Eq for nat {}

impl core::cmp::PartialOrd for nat {
    fn partial_cmp(&self, _other: &Self) -> Option<core::cmp::Ordering> {
        unimplemented!()
    }
}

impl core::cmp::Ord for nat {
    fn cmp(&self, _other: &Self) -> core::cmp::Ordering {
        unimplemented!()
    }
}

//
// Structural
//

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::builtin::Structural")]
pub trait Structural {
    #[doc(hidden)]
    fn assert_receiver_is_structural(&self) -> () {}
}

#[doc(hidden)]
pub struct AssertParamIsStructural<T: Structural + ?Sized> {
    _field: core::marker::PhantomData<T>,
}

macro_rules! impl_structural {
    ($($t:ty)*) => {
        $(
            impl Structural for $t { }
        )*
    }
}

impl_structural! {
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
    // TODO: support f32 f64 ?
    bool char
}

pub struct NoCopy {}
#[cfg(verus_keep_ghost)]
impl !Copy for NoCopy {}

#[cfg(verus_keep_ghost)]
struct NoSyncSend {}
#[cfg(verus_keep_ghost)]
impl !Sync for NoSyncSend {}
#[cfg(verus_keep_ghost)]
impl !Send for NoSyncSend {}

// TODO: remove this when !Sync, !Send are supported by stable Rust
#[cfg(not(verus_keep_ghost))]
struct NoSyncSend {
    _no_send_sync: core::marker::PhantomData<*const ()>,
}

// Used by state_machine_macros codegen
#[doc(hidden)]
#[allow(dead_code)]
pub struct SyncSendIfSyncSend<T> {
    no_sync_send: NoSyncSend,
    t: core::marker::PhantomData<T>,
}

unsafe impl<T: Sync + Send> Sync for SyncSendIfSyncSend<T> {}
unsafe impl<T: Sync + Send> Send for SyncSendIfSyncSend<T> {}

// Used by Invariant lib

#[doc(hidden)]
#[allow(dead_code)]
pub struct SendIfSend<T> {
    no_sync_send: NoSyncSend,
    t: core::marker::PhantomData<T>,
}

unsafe impl<T: Send> Send for SendIfSend<T> {}

#[doc(hidden)]
#[allow(dead_code)]
pub struct SyncSendIfSend<T> {
    no_sync_send: NoSyncSend,
    t: core::marker::PhantomData<T>,
}

unsafe impl<T: Send> Sync for SyncSendIfSend<T> {}
unsafe impl<T: Send> Send for SyncSendIfSend<T> {}

impl<T> SyncSendIfSend<T> {
    #[cfg(verus_keep_ghost)]
    pub fn assume_new() -> Self {
        SyncSendIfSend { no_sync_send: NoSyncSend {}, t: PhantomData }
    }
    #[cfg(not(verus_keep_ghost))]
    pub fn assume_new() -> Self {
        SyncSendIfSend {
            no_sync_send: NoSyncSend { _no_send_sync: Default::default() },
            t: PhantomData,
        }
    }
}

#[doc(hidden)]
#[allow(dead_code)]
pub struct AlwaysSyncSend<T> {
    t: core::marker::PhantomData<T>,
}

unsafe impl<T> Sync for AlwaysSyncSend<T> {}
unsafe impl<T> Send for AlwaysSyncSend<T> {}

impl<T> AlwaysSyncSend<T> {
    pub fn assume_new() -> Self {
        AlwaysSyncSend { t: PhantomData }
    }
}

//
// Integers
//

// Marker for integer types (i8 ... u128, isize, usize, nat, int)
// so that we get reasonable type error messages when someone uses a non-Integer type
// in an arithmetic operation.
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::builtin::Integer")]
#[cfg_attr(verus_keep_ghost, verifier::sealed)]
pub unsafe trait Integer: Copy {
    const CONST_DEFAULT: Self;
}
unsafe impl Integer for u8 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
unsafe impl Integer for u16 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
unsafe impl Integer for u32 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
unsafe impl Integer for u64 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
unsafe impl Integer for u128 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
unsafe impl Integer for usize {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
unsafe impl Integer for i8 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
unsafe impl Integer for i16 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
unsafe impl Integer for i32 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
unsafe impl Integer for i64 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
unsafe impl Integer for i128 {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
unsafe impl Integer for isize {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = 0;
}
unsafe impl Integer for int {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = int;
}
unsafe impl Integer for nat {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = nat;
}
unsafe impl Integer for char {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = ' ';
}

pub unsafe trait Boolean: Copy {
    const CONST_DEFAULT: Self;
}
unsafe impl Boolean for bool {
    #[cfg_attr(verus_keep_ghost, verifier::external)]
    const CONST_DEFAULT: Self = false;
}

// spec literals of the form "33", which could have any Integer type
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::spec_literal_integer"]
#[allow(non_camel_case_types)]
#[verifier::spec]
pub const fn spec_literal_integer<
    hint_please_add_suffix_on_literal_like_100u32_or_100int_or_100nat: Integer,
>(
    _s: &str,
) -> hint_please_add_suffix_on_literal_like_100u32_or_100int_or_100nat {
    hint_please_add_suffix_on_literal_like_100u32_or_100int_or_100nat::CONST_DEFAULT
}

// spec literals of the form "33int",
// or spec literals in positions syntactically expected to be int (e.g. in "x + 33")
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::spec_literal_int"]
#[verifier::spec]
pub const fn spec_literal_int(_s: &str) -> int {
    int
}

// spec literals of the form "33nat"
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::spec_literal_nat"]
#[verifier::spec]
pub const fn spec_literal_nat(_s: &str) -> nat {
    nat
}

// Fixed-width add
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::add"]
#[verifier::spec]
pub const fn add<IntegerType: Integer>(_left: IntegerType, _right: IntegerType) -> IntegerType {
    IntegerType::CONST_DEFAULT
}

// Fixed-width sub
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::sub"]
#[verifier::spec]
pub const fn sub<IntegerType: Integer>(_left: IntegerType, _right: IntegerType) -> IntegerType {
    IntegerType::CONST_DEFAULT
}

// Fixed-width mul
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::mul"]
#[verifier::spec]
pub const fn mul<IntegerType: Integer>(_left: IntegerType, _right: IntegerType) -> IntegerType {
    IntegerType::CONST_DEFAULT
}

// represent "expr as typ", including converting to and from int and nat
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::spec_cast_integer"]
#[verifier::spec]
pub const fn spec_cast_integer<From: Copy, To: Integer>(_from: From) -> To {
    To::CONST_DEFAULT
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::spec_eq"]
#[verifier::spec]
pub fn spec_eq<Lhs, Rhs>(_lhs: Lhs, _rhs: Rhs) -> bool {
    unimplemented!()
}

pub trait SpecOrd<Rhs = Self> {
    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecOrd::spec_lt"]
    #[verifier::spec]
    fn spec_lt(self, rhs: Rhs) -> bool;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecOrd::spec_le"]
    #[verifier::spec]
    fn spec_le(self, rhs: Rhs) -> bool;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecOrd::spec_gt"]
    #[verifier::spec]
    fn spec_gt(self, rhs: Rhs) -> bool;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecOrd::spec_ge"]
    #[verifier::spec]
    fn spec_ge(self, rhs: Rhs) -> bool;
}

pub trait SpecNeg {
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecNeg::spec_neg"]
    #[verifier::spec]
    fn spec_neg(self) -> Self::Output;
}

pub trait SpecAdd<Rhs = Self> {
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecAdd::spec_add"]
    #[verifier::spec]
    fn spec_add(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecSub<Rhs = Self> {
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecSub::spec_sub"]
    #[verifier::spec]
    fn spec_sub(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecMul<Rhs = Self> {
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecMul::spec_mul"]
    #[verifier::spec]
    fn spec_mul(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecEuclideanDiv<Rhs = Self> {
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecEuclideanDiv::spec_euclidean_div"]
    #[verifier::spec]
    fn spec_euclidean_div(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecEuclideanMod<Rhs = Self> {
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecEuclideanMod::spec_euclidean_mod"]
    #[verifier::spec]
    fn spec_euclidean_mod(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecBitAnd<Rhs = Self> {
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecBitAnd::spec_bitand"]
    #[verifier::spec]
    fn spec_bitand(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecBitOr<Rhs = Self> {
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecBitOr::spec_bitor"]
    #[verifier::spec]
    fn spec_bitor(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecBitXor<Rhs = Self> {
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecBitXor::spec_bitxor"]
    #[verifier::spec]
    fn spec_bitxor(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecShl<Rhs = Self> {
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecShl::spec_shl"]
    #[verifier::spec]
    fn spec_shl(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecShr<Rhs = Self> {
    type Output;

    #[cfg(verus_keep_ghost)]
    #[rustc_diagnostic_item = "verus::builtin::SpecShr::spec_shr"]
    #[verifier::spec]
    fn spec_shr(self, rhs: Rhs) -> Self::Output;
}

// Chained inequalities x <= y < z
pub struct SpecChain {
    data: PhantomData<int>,
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::spec_chained_value"]
#[verifier::spec]
pub fn spec_chained_value<IntegerType: Integer>(_a: IntegerType) -> SpecChain {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::spec_chained_le"]
#[verifier::spec]
pub fn spec_chained_le<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::spec_chained_lt"]
#[verifier::spec]
pub fn spec_chained_lt<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::spec_chained_ge"]
#[verifier::spec]
pub fn spec_chained_ge<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::spec_chained_gt"]
#[verifier::spec]
pub fn spec_chained_gt<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::spec_chained_cmp"]
#[verifier::spec]
pub fn spec_chained_cmp(_chain: SpecChain) -> bool {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::spec_chained_eq"]
#[verifier::spec]
pub fn spec_chained_eq<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

macro_rules! impl_ord {
    ([$($t:ty)*]) => {
        $(
            impl<Rhs: Integer> SpecOrd<Rhs> for $t {
                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn spec_lt(self, _rhs: Rhs) -> bool {
                    unimplemented!()
                }

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn spec_le(self, _rhs: Rhs) -> bool {
                    unimplemented!()
                }

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn spec_gt(self, _rhs: Rhs) -> bool {
                    unimplemented!()
                }

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn spec_ge(self, _rhs: Rhs) -> bool {
                    unimplemented!()
                }
            }
        )*
    }
}

macro_rules! impl_unary_op {
    ($trt:ident, $fun:ident, $ret:ty, [$($t:ty)*]) => {
        $(
            impl $trt for $t {
                type Output = $ret;

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn $fun(self) -> Self::Output {
                    unimplemented!()
                }
            }
        )*
    }
}

macro_rules! impl_binary_op {
    ($trt:ident, $fun:ident, $ret:ty, [$($t:ty)*]) => {
        $(
            impl<Rhs: Integer> $trt<Rhs> for $t {
                type Output = $ret;

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn $fun(self, _rhs: Rhs) -> Self::Output {
                    unimplemented!()
                }
            }
        )*
    }
}

macro_rules! impl_binary_op_nat {
    ($trt:ident, $fun:ident, $ret:ty, [$($t:ty)*]) => {
        $(
            impl $trt<$t> for nat {
                type Output = $ret;

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn $fun(self, _rhs: $t) -> Self::Output {
                    unimplemented!()
                }
            }
        )*
    }
}

macro_rules! impl_binary_op_rhs {
    ($trt:ident, $fun:ident, $rhs: ty, $ret:ty, [$($t:ty)*]) => {
        $(
            impl $trt<$rhs> for $t {
                type Output = $ret;

                #[cfg(verus_keep_ghost)]
                #[verifier::spec]
                fn $fun(self, _rhs: $rhs) -> Self::Output {
                    unimplemented!()
                }
            }
        )*
    }
}

impl_ord!([
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
    char
]);

impl_unary_op!(SpecNeg, spec_neg, int, [
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op!(SpecAdd, spec_add, int, [
    int
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_nat!(SpecAdd, spec_add, nat, [nat]);

impl_binary_op_nat!(SpecAdd, spec_add, int, [
    int
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op!(SpecSub, spec_sub, int, [
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op!(SpecMul, spec_mul, int, [
    int
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_nat!(SpecMul, spec_mul, nat, [nat]);

impl_binary_op_nat!(SpecMul, spec_mul, int, [
    int
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_rhs!(SpecEuclideanDiv, spec_euclidean_div, Self, Self, [
    int nat
    usize u8 u16 u32 u64 u128
]);

impl_binary_op_rhs!(SpecEuclideanDiv, spec_euclidean_div, Self, int, [
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_rhs!(SpecEuclideanMod, spec_euclidean_mod, Self, Self, [
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_rhs!(SpecBitAnd, spec_bitand, Self, Self, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_rhs!(SpecBitOr, spec_bitor, Self, Self, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_rhs!(SpecBitXor, spec_bitxor, Self, Self, [
    bool
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op!(SpecShl, spec_shl, Self, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op!(SpecShr, spec_shr, Self, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::strslice_is_ascii"]
#[verifier::spec]
pub fn strslice_is_ascii<A>(_a: A) -> bool {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::strslice_len"]
#[verifier::spec]
pub fn strslice_len<A>(_a: A) -> nat {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::strslice_get_char"]
#[verifier::spec]
pub fn strslice_get_char<A>(_a: A, _i: int) -> char {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::reveal_strlit"]
#[verifier::proof]
pub fn reveal_strlit<A>(_a: A) {
    unimplemented!()
}

#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::builtin::FnSpec")]
pub struct FnSpec<Args, Output> {
    phantom: PhantomData<(Args, Output)>,
}

#[cfg(verus_keep_ghost)]
impl<Args: core::marker::Tuple, Output> FnOnce<Args> for FnSpec<Args, Output> {
    type Output = Output;
    extern "rust-call" fn call_once(self, _: Args) -> <Self as FnOnce<Args>>::Output {
        todo!()
    }
}

#[cfg(verus_keep_ghost)]
impl<Args: core::marker::Tuple, Output> FnMut<Args> for FnSpec<Args, Output> {
    extern "rust-call" fn call_mut(&mut self, _: Args) -> <Self as FnOnce<Args>>::Output {
        todo!()
    }
}

#[cfg(verus_keep_ghost)]
impl<Args: core::marker::Tuple, Output> Fn<Args> for FnSpec<Args, Output> {
    extern "rust-call" fn call(&self, _: Args) -> <Self as FnOnce<Args>>::Output {
        todo!()
    }
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::closure_to_fn_spec"]
pub fn closure_to_fn_spec<Args: core::marker::Tuple, F: FnOnce<Args>>(
    _f: F,
) -> FnSpec<Args, F::Output> {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::call_requires"]
pub fn call_requires<Args: core::marker::Tuple, F: FnOnce<Args>>(_f: F, _args: Args) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::call_ensures"]
pub fn call_ensures<Args: core::marker::Tuple, F: FnOnce<Args>>(
    _f: F,
    _args: Args,
    _output: F::Output,
) -> bool {
    unimplemented!();
}

// Intrinsics defined in the AIR prelude related to word-sizes and bounded ints
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::unsigned_max"]
pub fn unsigned_max(_word_bits: nat) -> nat {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::signed_min"]
pub fn signed_min(_word_bits: nat) -> nat {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::signed_max"]
pub fn signed_max(_word_bits: nat) -> nat {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::arch_word_bits"]
pub fn arch_word_bits() -> nat {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::is_smaller_than"]
pub fn is_smaller_than<A, B>(_: A, _: B) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::is_smaller_than_lexicographic"]
pub fn is_smaller_than_lexicographic<A, B>(_: A, _: B) -> bool {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::is_smaller_than_recursive_function_field"]
pub fn is_smaller_than_recursive_function_field<A, B>(_: A, _: B) -> bool {
    unimplemented!();
}

#[macro_export]
#[cfg(not(verus_verify_core))]
macro_rules! decreases_to_internal {
    ($($x:expr),* $(,)? => $($y:expr),* $(,)?) => {
        $crate::is_smaller_than_lexicographic(($($y,)*), ($($x,)*))
    }
}

/// decreases_to!(b => a) means that height(a) < height(b), so that b can decrease to a
/// in decreases clauses.
/// decreases_to!(b1, ..., bn => a1, ..., am) can compare lexicographically ordered values,
/// which can be useful when making assertions about decreases clauses.
/// Notes:
/// - decreases_to! desugars to a call to is_smaller_than_lexicographic.
/// - you can write #[trigger](decreases_to!(b => a)) to trigger on height(a).
///   (in the SMT encoding, height is a function call and is a useful trigger,
///   while is_smaller_than/is_smaller_than_lexicographic is not a function call
///   and is not a useful trigger.)
#[macro_export]
#[cfg(not(verus_verify_core))]
macro_rules! decreases_to {
    ($($x:tt)*) => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::decreases_to_internal!($($x)*))
    };
}

#[macro_export]
#[cfg(verus_verify_core)]
macro_rules! decreases_to_internal {
    ($($x:expr),* $(,)? => $($y:expr),* $(,)?) => {
        $crate::builtin::is_smaller_than_lexicographic(($($y,)*), ($($x,)*))
    }
}

#[macro_export]
#[cfg(verus_verify_core)]
macro_rules! decreases_to {
    ($($x:tt)*) => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::builtin::decreases_to_internal!($($x)*))
    };
}

#[cfg(verus_verify_core)]
pub use decreases_to;
#[cfg(verus_verify_core)]
pub use decreases_to_internal;

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::infer_spec_for_loop_iter"]
#[verifier::spec]
pub fn infer_spec_for_loop_iter<A>(_: A, _print_hint: bool) -> Option<A> {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::global_size_of"]
#[verifier::spec]
pub const fn global_size_of<T>(_bytes: usize) {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::inline_air_stmt"]
#[verifier::proof]
pub fn inline_air_stmt(_s: &str) {
    unimplemented!()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::builtin::array_index"]
#[verifier::spec]
pub fn array_index<T, const N: usize>(_a: [T; N], _i: int) -> T {
    unimplemented!()
}
