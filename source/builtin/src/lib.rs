#![feature(rustc_attrs)]
#![feature(negative_impls)]

use std::marker::PhantomData;

#[proof]
pub fn admit() {
    unimplemented!();
}

// Can only appear at beginning of function body
#[proof]
pub fn no_method_body() -> ! {
    unimplemented!()
}

// Can only appear at beginning of function body
#[proof]
pub fn requires<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[proof]
pub fn ensures<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of spec function body
#[proof]
pub fn recommends<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of loop body
#[proof]
pub fn invariant<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[proof]
pub fn decreases<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
// decrease_when is automatically added to list of recommends
#[proof]
pub fn decreases_when(_b: bool) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[proof]
pub fn decreases_by<F>(_f: F) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[proof]
pub fn recommends_by<F>(_f: F) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[proof]
pub fn hide<F>(_f: F) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[proof]
pub fn extra_dependency<F>(_f: F) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[proof]
pub fn opens_invariants_none() {
    unimplemented!();
}

// Can only appear at beginning of function body
#[proof]
pub fn opens_invariants_any() {
    unimplemented!();
}

// Can only appear at beginning of function body
#[proof]
pub fn opens_invariants<A>(_a: A) {
    unimplemented!();
}

// Can only appear at beginning of function body
#[proof]
pub fn opens_invariants_except<A>(_a: A) {
    unimplemented!();
}

#[proof]
pub fn reveal<F>(_f: F) {
    unimplemented!();
}

#[proof]
pub fn reveal_with_fuel<F>(_f: F, _n: u32) {
    unimplemented!();
}

#[spec]
pub fn imply(_b1: bool, _b2: bool) -> bool {
    unimplemented!();
}

#[spec]
pub fn forall<A>(_a: A) -> bool {
    unimplemented!();
}

#[spec]
pub fn exists<A>(_a: A) -> bool {
    unimplemented!();
}

#[spec]
pub fn forall_arith<A>(_a: A) -> bool {
    unimplemented!();
}

// choose(|x: t| P(x))
#[spec]
pub fn choose<A, F: Fn(A) -> bool>(_f: F) -> A {
    unimplemented!()
}

// let (x1, ..., xn): (t1, ..., tn) = choose_tuple(|x1: t1, ..., xn: tn| P(x1, ..., xn));
#[spec]
pub fn choose_tuple<A, F>(_f: F) -> A {
    unimplemented!()
}

// used by with_triggers! macro
// example: forall with three triggers [f(x), g(y)], [h(x, y)], [m(y, x)]:
//   forall( |x: int, y: int| with_triggers(  ( (f(x), g(y)), (h(x, y),), (m(y, x),) )  ,  body  ) )
#[spec]
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

#[spec]
pub fn equal<A>(_: A, _: A) -> bool {
    unimplemented!();
}

#[spec]
pub fn old<A>(_: A) -> A {
    unimplemented!();
}

#[proof]
pub fn assert_by(_: bool, _: ()) {
    unimplemented!();
}

#[proof]
pub fn assert_nonlinear_by(_: ()) {
    unimplemented!();
}

#[proof]
pub fn assert_forall_by<A>(_a: A) {
    unimplemented!();
}

#[proof]
pub fn assert_bit_vector(_: bool) {
    unimplemented!();
}

// Used internally by erase.rs
#[spec]
pub fn internal_arbitrary<A>(_: u64) -> A {
    unimplemented!()
}

//
// Ghost, Tracked
//

#[verifier(external_body)]
pub struct Ghost<#[verifier(strictly_positive)] A> {
    phantom: PhantomData<A>,
}

#[verifier(external_body)]
pub struct Tracked<#[verifier(strictly_positive)] A> {
    phantom: PhantomData<A>,
}

impl<A> Ghost<A> {
    #[spec]
    pub fn view(self) -> A {
        unimplemented!()
    }

    #[spec]
    #[verifier(external_body)]
    pub fn new(_a: A) -> Ghost<A> {
        Ghost { phantom: PhantomData }
    }

    #[doc(hidden)]
    #[verifier(external)]
    #[inline(always)]
    pub fn assume_new() -> Self {
        Ghost { phantom: PhantomData }
    }

    // note that because we return #[spec], not #[exec], we do not implement the Borrow trait
    #[spec]
    #[verifier(external_body)]
    pub fn borrow(&self) -> &A {
        unimplemented!()
    }

    // note that because we return #[spec], not #[exec], we do not implement the BorrowMut trait
    #[proof]
    #[verifier(external)]
    pub fn borrow_mut(#[proof] &mut self) -> &mut A {
        unimplemented!()
    }
}

impl<A> Tracked<A> {
    #[spec]
    pub fn view(self) -> A {
        unimplemented!()
    }

    #[doc(hidden)]
    #[verifier(external)]
    #[inline(always)]
    pub fn assume_new() -> Self {
        Tracked { phantom: PhantomData }
    }

    #[proof]
    #[verifier(external_body)]
    #[verifier(returns(proof))]
    pub fn get(#[proof] self) -> A {
        unimplemented!()
    }

    // note that because we return #[proof], not #[exec], we do not implement the Borrow trait
    #[proof]
    #[verifier(external_body)]
    #[verifier(returns(proof))]
    pub fn borrow(#[proof] &self) -> &A {
        unimplemented!()
    }

    // note that because we return #[proof], not #[exec], we do not implement the BorrowMut trait
    #[proof]
    #[verifier(external_body)]
    #[verifier(returns(proof))]
    pub fn borrow_mut(#[proof] &mut self) -> &mut A {
        unimplemented!()
    }
}

impl<A> Clone for Ghost<A> {
    #[verifier(external_body)]
    #[inline(always)]
    fn clone(&self) -> Self {
        Ghost { phantom: PhantomData }
    }
}

impl<A> Copy for Ghost<A> {}

macro_rules! emit_phantom {
    ($x:ident) => {
        PhantomData
    };
}
macro_rules! split_tuple {
    /*
        #[inline(always)]
        pub fn tracked_split_tuple2<A1, A2>(_t: Tracked<(A1, A2)>) -> (Tracked<A1>, Tracked<A2>) {
            (Tracked { phantom: PhantomData }, Tracked { phantom: PhantomData })
        }
    */
    ($fun:ident, $typ:ident, [$($t:ident)*]) => {
        #[inline(always)]
        pub fn $fun
            <$( $t, )* >
            (_t: $typ<($( $t, )*)>)
            ->
            ($( $typ<$t>, )*) {
            ($( $typ { phantom: emit_phantom!($t) }, )*)
        }
    }
}
split_tuple!(ghost_split_tuple0, Ghost, []);
split_tuple!(ghost_split_tuple1, Ghost, [A1]);
split_tuple!(ghost_split_tuple2, Ghost, [A1 A2]);
split_tuple!(ghost_split_tuple3, Ghost, [A1 A2 A3]);
split_tuple!(ghost_split_tuple4, Ghost, [A1 A2 A3 A4]);
split_tuple!(ghost_split_tuple5, Ghost, [A1 A2 A3 A4 A5]);
split_tuple!(ghost_split_tuple6, Ghost, [A1 A2 A3 A4 A5 A6]);
split_tuple!(ghost_split_tuple7, Ghost, [A1 A2 A3 A4 A5 A6 A7]);
split_tuple!(ghost_split_tuple8, Ghost, [A1 A2 A3 A4 A5 A6 A7 A8]);
split_tuple!(tracked_split_tuple0, Tracked, []);
split_tuple!(tracked_split_tuple1, Tracked, [A1]);
split_tuple!(tracked_split_tuple2, Tracked, [A1 A2]);
split_tuple!(tracked_split_tuple3, Tracked, [A1 A2 A3]);
split_tuple!(tracked_split_tuple4, Tracked, [A1 A2 A3 A4]);
split_tuple!(tracked_split_tuple5, Tracked, [A1 A2 A3 A4 A5]);
split_tuple!(tracked_split_tuple6, Tracked, [A1 A2 A3 A4 A5 A6]);
split_tuple!(tracked_split_tuple7, Tracked, [A1 A2 A3 A4 A5 A6 A7]);
split_tuple!(tracked_split_tuple8, Tracked, [A1 A2 A3 A4 A5 A6 A7 A8]);

//
// int and nat
//

#[allow(non_camel_case_types)]
pub struct int;

// TODO: we should eventually be able to remove this and other int/nat ops,
// since we now have SpecAdd, etc.
impl std::ops::Add for int {
    type Output = Self;
    fn add(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Sub for int {
    type Output = Self;
    fn sub(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Mul for int {
    type Output = Self;
    fn mul(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Div for int {
    type Output = Self;
    fn div(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Rem for int {
    type Output = Self;
    fn rem(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Neg for int {
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

impl std::cmp::PartialOrd for int {
    fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        unimplemented!()
    }
}

impl std::cmp::Ord for int {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        unimplemented!()
    }
}

#[allow(non_camel_case_types)]
pub struct nat;

impl std::ops::Add for nat {
    type Output = Self;
    fn add(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Sub for nat {
    type Output = Self;
    fn sub(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Mul for nat {
    type Output = Self;
    fn mul(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Div for nat {
    type Output = Self;
    fn div(self, _other: Self) -> Self::Output {
        unimplemented!()
    }
}

impl std::ops::Rem for nat {
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

impl std::cmp::PartialOrd for nat {
    fn partial_cmp(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        unimplemented!()
    }
}

impl std::cmp::Ord for nat {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        unimplemented!()
    }
}

//
// Structural
//

// TODO(andreal) bake this into the compiler as a lang_item
#[rustc_diagnostic_item = "builtin::Structural"]
pub trait Structural {
    #[doc(hidden)]
    fn assert_receiver_is_structural(&self) -> () {}
}

#[doc(hidden)]
pub struct AssertParamIsStructural<T: Structural + ?Sized> {
    _field: std::marker::PhantomData<T>,
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

struct NoSyncSend {}
impl !Sync for NoSyncSend {}
impl !Send for NoSyncSend {}

// Used by state_machine_macros codegen
#[doc(hidden)]
#[allow(dead_code)]
pub struct SyncSendIfSyncSend<T> {
    no_sync_send: NoSyncSend,
    t: std::marker::PhantomData<T>,
}

unsafe impl<T: Sync + Send> Sync for SyncSendIfSyncSend<T> {}
unsafe impl<T: Sync + Send> Send for SyncSendIfSyncSend<T> {}

// Used by Invariant lib

#[doc(hidden)]
#[allow(dead_code)]
pub struct SendIfSend<T> {
    no_sync_send: NoSyncSend,
    t: std::marker::PhantomData<T>,
}

unsafe impl<T: Send> Send for SendIfSend<T> {}

#[doc(hidden)]
#[allow(dead_code)]
pub struct SyncSendIfSend<T> {
    no_sync_send: NoSyncSend,
    t: std::marker::PhantomData<T>,
}

unsafe impl<T: Send> Sync for SyncSendIfSend<T> {}
unsafe impl<T: Send> Send for SyncSendIfSend<T> {}

//
// Integers
//

// Marker for integer types (i8 ... u128, isize, usize, nat, int)
// so that we get reasonable type error messages when someone uses a non-Integer type
// in an arithmetic operation.
pub trait Integer {}
impl Integer for u8 {}
impl Integer for u16 {}
impl Integer for u32 {}
impl Integer for u64 {}
impl Integer for u128 {}
impl Integer for usize {}
impl Integer for i8 {}
impl Integer for i16 {}
impl Integer for i32 {}
impl Integer for i64 {}
impl Integer for i128 {}
impl Integer for isize {}
impl Integer for int {}
impl Integer for nat {}

// spec literals of the form "33", which could have any Integer type
#[allow(non_camel_case_types)]
#[spec]
pub fn spec_literal_integer<
    hint_please_add_suffix_on_literal_like_100u32_or_100int_or_100nat: Integer,
>(
    _s: &str,
) -> hint_please_add_suffix_on_literal_like_100u32_or_100int_or_100nat {
    unimplemented!()
}

// spec literals of the form "33int",
// or spec literals in positions syntactically expected to be int (e.g. in "x + 33")
#[spec]
pub fn spec_literal_int(_s: &str) -> int {
    unimplemented!()
}

// spec literals of the form "33nat"
#[spec]
pub fn spec_literal_nat(_s: &str) -> nat {
    unimplemented!()
}

// Fixed-width add
#[spec]
pub fn add<IntegerType: Integer>(_left: IntegerType, _right: IntegerType) -> IntegerType {
    unimplemented!()
}

// Fixed-width sub
#[spec]
pub fn sub<IntegerType: Integer>(_left: IntegerType, _right: IntegerType) -> IntegerType {
    unimplemented!()
}

// Fixed-width mul
#[spec]
pub fn mul<IntegerType: Integer>(_left: IntegerType, _right: IntegerType) -> IntegerType {
    unimplemented!()
}

// represent "expr as typ", including converting to and from int and nat
#[spec]
pub fn spec_cast_integer<From: Integer, To: Integer>(_from: From) -> To {
    unimplemented!()
}

#[spec]
pub fn spec_eq<Lhs: Structural, Rhs: Structural>(_lhs: Lhs, _rhs: Rhs) -> bool {
    unimplemented!()
}

pub trait SpecOrd<Rhs = Self> {
    #[spec]
    fn spec_lt(self, rhs: Rhs) -> bool;
    #[spec]
    fn spec_le(self, rhs: Rhs) -> bool;
    #[spec]
    fn spec_gt(self, rhs: Rhs) -> bool;
    #[spec]
    fn spec_ge(self, rhs: Rhs) -> bool;
}

pub trait SpecNeg {
    type Output;
    #[spec]
    fn spec_neg(self) -> Self::Output;
}

pub trait SpecAdd<Rhs = Self> {
    type Output;
    #[spec]
    fn spec_add(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecSub<Rhs = Self> {
    type Output;
    #[spec]
    fn spec_sub(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecMul<Rhs = Self> {
    type Output;
    #[spec]
    fn spec_mul(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecEuclideanDiv<Rhs = Self> {
    type Output;
    #[spec]
    fn spec_euclidean_div(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecEuclideanMod<Rhs = Self> {
    type Output;
    #[spec]
    fn spec_euclidean_mod(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecBitAnd<Rhs = Self> {
    type Output;
    #[spec]
    fn spec_bitand(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecBitOr<Rhs = Self> {
    type Output;
    #[spec]
    fn spec_bitor(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecBitXor<Rhs = Self> {
    type Output;
    #[spec]
    fn spec_bitxor(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecShl<Rhs = Self> {
    type Output;
    #[spec]
    fn spec_shl(self, rhs: Rhs) -> Self::Output;
}

pub trait SpecShr<Rhs = Self> {
    type Output;
    #[spec]
    fn spec_shr(self, rhs: Rhs) -> Self::Output;
}

// Chained inequalities x <= y < z
pub struct SpecChain {
    data: std::marker::PhantomData<int>,
}

#[spec]
pub fn spec_chained_value<IntegerType: Integer>(_a: IntegerType) -> SpecChain {
    unimplemented!()
}

#[spec]
pub fn spec_chained_le<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

#[spec]
pub fn spec_chained_lt<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

#[spec]
pub fn spec_chained_ge<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

#[spec]
pub fn spec_chained_gt<IntegerType: Integer>(_left: SpecChain, _right: IntegerType) -> SpecChain {
    unimplemented!()
}

#[spec]
pub fn spec_chained_cmp(_chain: SpecChain) -> bool {
    unimplemented!()
}

macro_rules! impl_ord {
    ([$($t:ty)*]) => {
        $(
            impl<Rhs: Integer> SpecOrd<Rhs> for $t {
                #[spec]
                fn spec_lt(self, _rhs: Rhs) -> bool {
                    unimplemented!()
                }
                #[spec]
                fn spec_le(self, _rhs: Rhs) -> bool {
                    unimplemented!()
                }
                #[spec]
                fn spec_gt(self, _rhs: Rhs) -> bool {
                    unimplemented!()
                }
                #[spec]
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
                #[spec]
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
                #[spec]
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
                #[spec]
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
                #[spec]
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

impl_binary_op_nat!(SpecAdd, spec_add, nat, [
    nat
    usize u8 u16 u32 u64 u128
]);

impl_binary_op_nat!(SpecAdd, spec_add, int, [
    int
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

impl_binary_op_nat!(SpecMul, spec_mul, nat, [
    nat
    usize u8 u16 u32 u64 u128
]);

impl_binary_op_nat!(SpecMul, spec_mul, int, [
    int
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

impl_binary_op_rhs!(SpecShl, spec_shl, Self, Self, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

impl_binary_op_rhs!(SpecShr, spec_shr, Self, Self, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);
