#![feature(rustc_attrs)]
#![feature(negative_impls)]

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

#[allow(non_camel_case_types)]
pub struct int;

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
