/// This file defines the `CheckedU32` and `CheckedU64` structs and
/// their associated methods. They handle `u32` and `u64` values that
/// can overflow. Each struct includes a ghost value representing the
/// true `nat` value (not subject to overflow), so that the `view`
/// function can provide that true value.
///
/// It's a fully verified library, i.e., it contains no trusted code.
///
/// Here are some examples using `CheckedU64`. (See
/// `rust_verify/example/overflow.rs` for more examples, including
/// ones for the analogous `CheckedU32`.)
///
/// ```
/// fn test1()
/// {
///     let w = CheckedU64::new(0xFFFFFFFFFFFFFFFF);
///     let x = w.add(1);
///     assert(x.is_overflowed());
///     assert(x.view() == 0x10000000000000000);
///
///     let y = CheckedU64::new(0x8000000000000000);
///     let z = y.mul(2);
///     assert(z.is_overflowed());
///     assert(z.view() == 0x10000000000000000);
/// }
///
/// fn test2(a: u64, b: u64, c: u64, d: u64) -> (e: Option<u64>)
///     ensures
///         match e {
///             Some(v) => v == a * b + c * d,
///             None => a * b + c * d > u64::MAX,
///         }
/// {
///     let a_times_b = CheckedU64::new(a).mul(b);
///     let c_times_d = CheckedU64::new(c).mul(d);
///     let sum_of_products = a_times_b.add_checked_u64(&c_times_d);
///     if sum_of_products.is_overflowed() {
///         assert(a * b + c * d > u64::MAX);
///         None
///     }
///     else {
///         let i: u64 = sum_of_products.unwrap();
///         assert(i == a * b + c * d);
///         Some(i)
///     }
/// }
/// ```
#[allow(unused_imports)]
use super::super::prelude::*;
#[allow(unused_imports)]
use super::super::view::View;
#[allow(unused_imports)]
#[cfg(verus_keep_ghost)]
use super::div_mod::{
    lemma_div_is_ordered_by_denominator, lemma_div_plus_one, lemma_fundamental_div_mod,
    lemma_mod_division_less_than_divisor,
};
#[allow(unused_imports)]
#[cfg(verus_keep_ghost)]
use super::mul::{lemma_mul_by_zero_is_zero, lemma_mul_inequality, lemma_mul_is_commutative};
#[allow(unused_imports)]
use super::*;

verus! {

/// This struct represents a `u64` value that can overflow. The `i` field
/// is a ghost value that represents the true value, while the `v` field
/// is `None` when the value has overflowed and `Some(x)` when the value
/// `x` fits in a `u64`.
pub struct CheckedU64 {
    i: Ghost<nat>,
    v: Option<u64>,
}

/// The view of an `CheckedU64` instance is the true value of the instance.
impl View for CheckedU64 {
    type V = nat;

    closed spec fn view(&self) -> nat {
        self.i@
    }
}

impl Clone for CheckedU64 {
    /// Clones the `CheckedU64` instance.
    /// Ensures the cloned instance has the same value as the original.
    exec fn clone(&self) -> (result: Self)
        ensures
            result@ == self@,
    {
        proof {
            use_type_invariant(self);
        }
        Self { i: self.i, v: self.v }
    }
}

impl CheckedU64 {
    /// This is the internal type invariant for an `CheckedU64`.
    /// It ensures the key invariant that relates `i` and `v`.
    #[verifier::type_invariant]
    spec fn well_formed(self) -> bool {
        match self.v {
            Some(v) => self.i@ == v,
            None => self.i@ > u64::MAX,
        }
    }

    /// Creates a new `CheckedU64` instance from a `u64` value.
    /// Ensures the internal representation matches the provided value.
    pub closed spec fn spec_new(v: u64) -> CheckedU64 {
        CheckedU64 { i: Ghost(v as nat), v: Some(v) }
    }

    /// Creates a new `CheckedU64` instance from a `u64` value.
    /// Ensures the internal representation matches the provided value.
    #[verifier::when_used_as_spec(spec_new)]
    pub exec fn new(v: u64) -> (result: Self)
        ensures
            result@ == v,
    {
        Self { i: Ghost(v as nat), v: Some(v) }
    }

    /// Creates a new `CheckedU64` instance with an overflowed value.
    /// Requires the provided value to be greater than `u64::MAX`.
    /// Ensures the internal representation matches the provided value.
    pub exec fn new_overflowed(Ghost(i): Ghost<int>) -> (result: Self)
        requires
            i > u64::MAX,
        ensures
            result@ == i,
    {
        Self { i: Ghost(i as nat), v: None }
    }

    /// Checks if the `CheckedU64` instance is overflowed.
    /// Returns true if the value is greater than `u64::MAX`.
    pub open spec fn spec_is_overflowed(&self) -> bool {
        self@ > u64::MAX
    }

    /// Checks if the `CheckedU64` instance is overflowed.
    /// Returns true if the value is greater than `u64::MAX`.
    #[verifier::when_used_as_spec(spec_is_overflowed)]
    pub exec fn is_overflowed(&self) -> (result: bool)
        ensures
            result == self.spec_is_overflowed(),
    {
        proof { use_type_invariant(self) }
        self.v.is_none()
    }

    /// Unwraps the `CheckedU64` instance to get the `u64` value.
    /// Requires the instance to not be overflowed.
    /// Ensures the returned value matches the internal representation.
    pub exec fn unwrap(&self) -> (result: u64)
        requires
            !self.is_overflowed(),
        ensures
            result == self@,
    {
        proof { use_type_invariant(self) }
        self.v.unwrap()
    }

    /// Converts the `CheckedU64` instance to an `Option<u64>`.
    /// Ensures the returned option matches the internal representation.
    pub exec fn to_option(&self) -> (result: Option<u64>)
        ensures
            match result {
                Some(v) => self@ == v && v <= u64::MAX,
                None => self@ > u64::MAX,
            },
    {
        proof {
            use_type_invariant(self);
        }
        self.v
    }

    /// Adds a `u64` value to the `CheckedU64` instance.
    /// Ensures the resulting value matches the sum of the internal representation and the provided value.
    #[inline]
    pub exec fn add(&self, v2: u64) -> (result: Self)
        ensures
            result@ == self@ + v2,
    {
        proof {
            use_type_invariant(&self);
        }
        let i: Ghost<nat> = Ghost((&self@ + v2) as nat);
        match self.v {
            Some(v1) => Self { i, v: v1.checked_add(v2) },
            None => Self { i, v: None },
        }
    }

    /// Adds another `CheckedU64` instance to the current instance.
    /// Ensures the resulting value matches the sum of the internal representations of both instances.
    #[inline]
    pub exec fn add_checked_u64(&self, v2: &CheckedU64) -> (result: Self)
        ensures
            result@ == self@ + v2@,
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(v2);
        }
        let i: Ghost<nat> = Ghost((self@ + v2@) as nat);
        match (self.v, v2.v) {
            (Some(n1), Some(n2)) => Self { i, v: n1.checked_add(n2) },
            _ => Self { i, v: None },
        }
    }

    /// Multiplies the `CheckedU64` instance by a `u64` value.
    /// Ensures the resulting value matches the product of the internal representation and the provided value.
    #[inline]
    pub exec fn mul(&self, v2: u64) -> (result: Self)
        ensures
            result@ == self@ as int * v2 as int,
    {
        proof {
            use_type_invariant(self);
        }
        let i: Ghost<nat> = Ghost((self@ * v2) as nat);
        match self.v {
            Some(n1) => Self { i, v: n1.checked_mul(v2) },
            None => {
                if v2 == 0 {
                    assert(i@ == 0) by {
                        lemma_mul_by_zero_is_zero(self@ as int);
                    }
                    Self { i, v: Some(0) }
                } else {
                    assert(self@ * v2 >= self@ * 1 == self@) by {
                        lemma_mul_inequality(1, v2 as int, self@ as int);
                        lemma_mul_is_commutative(self@ as int, v2 as int);
                    }
                    Self { i, v: None }
                }
            },
        }
    }

    /// Multiplies the `CheckedU64` instance by another `CheckedU64` instance.
    /// Ensures the resulting value matches the product of the internal representations of both instances.
    #[inline]
    pub exec fn mul_checked_u64(&self, v2: &Self) -> (result: Self)
        ensures
            result@ == self@ as int * v2@ as int,
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(v2);
        }
        let i: Ghost<nat> = Ghost((self@ * v2@) as nat);
        match (self.v, v2.v) {
            (Some(n1), Some(n2)) => Self { i, v: n1.checked_mul(n2) },
            (Some(n1), None) => {
                if n1 == 0 {
                    assert(i@ == 0) by {
                        lemma_mul_by_zero_is_zero(v2@ as int);
                    }
                    Self { i, v: Some(0) }
                } else {
                    assert(self@ * v2@ >= 1 * v2@ == v2@) by {
                        lemma_mul_inequality(1, self@ as int, v2@ as int);
                    }
                    Self { i, v: None }
                }
            },
            (None, Some(n2)) => {
                if n2 == 0 {
                    assert(i@ == 0) by {
                        lemma_mul_by_zero_is_zero(self@ as int);
                    }
                    Self { i, v: Some(0) }
                } else {
                    assert(self@ * n2 >= self@ * 1 == self@) by {
                        lemma_mul_inequality(1, n2 as int, self@ as int);
                        lemma_mul_is_commutative(self@ as int, n2 as int);
                    }
                    Self { i, v: None }
                }
            },
            (None, None) => {
                assert(self@ * v2@ > u64::MAX) by {
                    lemma_mul_inequality(1, self@ as int, v2@ as int);
                }
                Self { i, v: None }
            },
        }
    }
}

/// This struct represents a `u32` value that can overflow. The `i` field
/// is a ghost value that represents the true value, while the `v` field
/// is `None` when the value has overflowed and `Some(x)` when the value
/// `x` fits in a `u32`.
pub struct CheckedU32 {
    i: Ghost<nat>,
    v: Option<u32>,
}

/// The view of an `CheckedU32` instance is the true value of the instance.
impl View for CheckedU32 {
    type V = nat;

    closed spec fn view(&self) -> nat {
        self.i@
    }
}

impl Clone for CheckedU32 {
    /// Clones the `CheckedU32` instance.
    /// Ensures the cloned instance has the same value as the original.
    exec fn clone(&self) -> (result: Self)
        ensures
            result@ == self@,
    {
        proof {
            use_type_invariant(self);
        }
        Self { i: self.i, v: self.v }
    }
}

impl CheckedU32 {
    /// This is the internal type invariant for an `CheckedU32`.
    /// It ensures the key invariant that relates `i` and `v`.
    #[verifier::type_invariant]
    spec fn well_formed(self) -> bool {
        match self.v {
            Some(v) => self.i@ == v,
            None => self.i@ > u32::MAX,
        }
    }

    /// Creates a new `CheckedU32` instance from a `u32` value.
    /// Ensures the internal representation matches the provided value.
    pub closed spec fn spec_new(v: u32) -> CheckedU32 {
        CheckedU32 { i: Ghost(v as nat), v: Some(v) }
    }

    /// Creates a new `CheckedU32` instance from a `u32` value.
    /// Ensures the internal representation matches the provided value.
    #[verifier::when_used_as_spec(spec_new)]
    pub exec fn new(v: u32) -> (result: Self)
        ensures
            result@ == v,
    {
        Self { i: Ghost(v as nat), v: Some(v) }
    }

    /// Creates a new `CheckedU32` instance with an overflowed value.
    /// Requires the provided value to be greater than `u32::MAX`.
    /// Ensures the internal representation matches the provided value.
    pub exec fn new_overflowed(Ghost(i): Ghost<int>) -> (result: Self)
        requires
            i > u32::MAX,
        ensures
            result@ == i,
    {
        Self { i: Ghost(i as nat), v: None }
    }

    /// Checks if the `CheckedU32` instance is overflowed.
    /// Returns true if the value is greater than `u32::MAX`.
    pub open spec fn spec_is_overflowed(&self) -> bool {
        self@ > u32::MAX
    }

    /// Checks if the `CheckedU32` instance is overflowed.
    /// Returns true if the value is greater than `u32::MAX`.
    #[verifier::when_used_as_spec(spec_is_overflowed)]
    pub exec fn is_overflowed(&self) -> (result: bool)
        ensures
            result == self.spec_is_overflowed(),
    {
        proof { use_type_invariant(self) }
        self.v.is_none()
    }

    /// Unwraps the `CheckedU32` instance to get the `u32` value.
    /// Requires the instance to not be overflowed.
    /// Ensures the returned value matches the internal representation.
    pub exec fn unwrap(&self) -> (result: u32)
        requires
            !self.is_overflowed(),
        ensures
            result == self@,
    {
        proof { use_type_invariant(self) }
        self.v.unwrap()
    }

    /// Converts the `CheckedU32` instance to an `Option<u32>`.
    /// Ensures the returned option matches the internal representation.
    pub exec fn to_option(&self) -> (result: Option<u32>)
        ensures
            match result {
                Some(v) => self@ == v && v <= u32::MAX,
                None => self@ > u32::MAX,
            },
    {
        proof {
            use_type_invariant(self);
        }
        self.v
    }

    /// Adds a `u32` value to the `CheckedU32` instance.
    /// Ensures the resulting value matches the sum of the internal representation and the provided value.
    #[inline]
    pub exec fn add(&self, v2: u32) -> (result: Self)
        ensures
            result@ == self@ + v2,
    {
        proof {
            use_type_invariant(&self);
        }
        let i: Ghost<nat> = Ghost((&self@ + v2) as nat);
        match self.v {
            Some(v1) => Self { i, v: v1.checked_add(v2) },
            None => Self { i, v: None },
        }
    }

    /// Adds another `CheckedU32` instance to the current instance.
    /// Ensures the resulting value matches the sum of the internal representations of both instances.
    #[inline]
    pub exec fn add_checked_u32(&self, v2: &CheckedU32) -> (result: Self)
        ensures
            result@ == self@ + v2@,
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(v2);
        }
        let i: Ghost<nat> = Ghost((self@ + v2@) as nat);
        match (self.v, v2.v) {
            (Some(n1), Some(n2)) => Self { i, v: n1.checked_add(n2) },
            _ => Self { i, v: None },
        }
    }

    /// Multiplies the `CheckedU32` instance by a `u32` value.
    /// Ensures the resulting value matches the product of the internal representation and the provided value.
    #[inline]
    pub exec fn mul(&self, v2: u32) -> (result: Self)
        ensures
            result@ == self@ as int * v2 as int,
    {
        proof {
            use_type_invariant(self);
        }
        let i: Ghost<nat> = Ghost((self@ * v2) as nat);
        match self.v {
            Some(n1) => Self { i, v: n1.checked_mul(v2) },
            None => {
                if v2 == 0 {
                    assert(i@ == 0) by {
                        lemma_mul_by_zero_is_zero(self@ as int);
                    }
                    Self { i, v: Some(0) }
                } else {
                    assert(self@ * v2 >= self@ * 1 == self@) by {
                        lemma_mul_inequality(1, v2 as int, self@ as int);
                        lemma_mul_is_commutative(self@ as int, v2 as int);
                    }
                    Self { i, v: None }
                }
            },
        }
    }

    /// Multiplies the `CheckedU32` instance by another `CheckedU32` instance.
    /// Ensures the resulting value matches the product of the internal representations of both instances.
    #[inline]
    pub exec fn mul_checked_u32(&self, v2: &Self) -> (result: Self)
        ensures
            result@ == self@ as int * v2@ as int,
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(v2);
        }
        let i: Ghost<nat> = Ghost((self@ * v2@) as nat);
        match (self.v, v2.v) {
            (Some(n1), Some(n2)) => Self { i, v: n1.checked_mul(n2) },
            (Some(n1), None) => {
                if n1 == 0 {
                    assert(i@ == 0) by {
                        lemma_mul_by_zero_is_zero(v2@ as int);
                    }
                    Self { i, v: Some(0) }
                } else {
                    assert(self@ * v2@ >= 1 * v2@ == v2@) by {
                        lemma_mul_inequality(1, self@ as int, v2@ as int);
                    }
                    Self { i, v: None }
                }
            },
            (None, Some(n2)) => {
                if n2 == 0 {
                    assert(i@ == 0) by {
                        lemma_mul_by_zero_is_zero(self@ as int);
                    }
                    Self { i, v: Some(0) }
                } else {
                    assert(self@ * n2 >= self@ * 1 == self@) by {
                        lemma_mul_inequality(1, n2 as int, self@ as int);
                        lemma_mul_is_commutative(self@ as int, n2 as int);
                    }
                    Self { i, v: None }
                }
            },
            (None, None) => {
                assert(self@ * v2@ > u32::MAX) by {
                    lemma_mul_inequality(1, self@ as int, v2@ as int);
                }
                Self { i, v: None }
            },
        }
    }
}

} // verus!
