#![feature(rustc_attrs)]

#[proof]
pub fn admit() {
    unimplemented!();
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
#[proof]
pub fn hide<F>(_f: F) {
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
pub fn choose<A, F: Fn(A) -> bool>(_f: F) -> A {
    unimplemented!()
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

impl std::ops::BitAnd for int {
    type Output = Self;
    fn bitand(self, _other: Self) -> Self::Output {
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
