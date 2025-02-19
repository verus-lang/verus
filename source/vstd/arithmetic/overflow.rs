/// This file defines the `OverflowableU32` and `OverflowableU64`
/// structs and their associated methods to handle `u32` and `u64`
/// values that can overflow. Each struct includes a ghost value
/// representing the true value (not subject to overflow), so that the
/// `view` function can provide the true value.
///
/// Here are some examples using `OverflowableU64`. (The type
/// `OverflowableU32` can be used analogously.)
///
/// ```
/// fn test1()
/// {
///     let w = OverflowableU64::new(0xFFFFFFFFFFFFFFFF);
///     let x = w.add(1);
///     assert(x.is_overflowed());
///     assert(x.view() == 0x10000000000000000);
///
///     let y = OverflowableU64::new(0x8000000000000000);
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
///     let a_times_b = OverflowableU64::new(a).mul(b);
///     let c_times_d = OverflowableU64::new(c).mul(d);
///     let sum_of_products = a_times_b.add_overflowable_u64(&c_times_d);
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
use builtin::*;
use builtin_macros::*;
#[cfg(verus_keep_ghost)]
use super::div_mod::{
    lemma_div_is_ordered_by_denominator, lemma_div_plus_one, lemma_fundamental_div_mod,
    lemma_mod_division_less_than_divisor,
};
#[cfg(verus_keep_ghost)]
use super::mul::{
    lemma_mul_by_zero_is_zero, lemma_mul_inequality, lemma_mul_is_commutative,
};
use super::super::prelude::*;
use super::super::view::View;

verus! {

/// This struct represents a `u64` value that can overflow. The `i` field
/// is a ghost value that represents the true value, while the `v` field
/// is `None` when the value has overflowed and `Some(x)` when the value
/// `x` fits in a `u64`.
pub struct OverflowableU64 {
    i: Ghost<nat>,
    v: Option<u64>,
}

/// The view of an `OverflowableU64` instance is the true value of the instance.
impl View for OverflowableU64 {
    type V = nat;

    closed spec fn view(&self) -> nat {
        self.i@
    }
}

impl Clone for OverflowableU64 {
    /// Clones the `OverflowableU64` instance.
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

impl OverflowableU64 {
    /// This is the internal type invariant for an `OverflowableU64`.
    /// It ensures the key invariant that relates `i` and `v`.
    #[verifier::type_invariant]
    spec fn well_formed(self) -> bool {
        match self.v {
            Some(v) => self.i@ == v,
            None => self.i@ > u64::MAX,
        }
    }

    /// Creates a new `OverflowableU64` instance from a `u64` value.
    /// Ensures the internal representation matches the provided value.
    pub closed spec fn spec_new(v: u64) -> OverflowableU64 {
        OverflowableU64 { i: Ghost(v as nat), v: Some(v) }
    }

    /// Creates a new `OverflowableU64` instance from a `u64` value.
    /// Ensures the internal representation matches the provided value.
    #[verifier::when_used_as_spec(spec_new)]
    pub exec fn new(v: u64) -> (result: Self)
        ensures
            result@ == v,
    {
        Self { i: Ghost(v as nat), v: Some(v) }
    }

    /// Creates a new `OverflowableU64` instance with an overflowed value.
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

    /// Checks if the `OverflowableU64` instance is overflowed.
    /// Returns true if the value is greater than `u64::MAX`.
    pub open spec fn spec_is_overflowed(&self) -> bool {
        self@ > u64::MAX
    }

    /// Checks if the `OverflowableU64` instance is overflowed.
    /// Returns true if the value is greater than `u64::MAX`.
    #[verifier::when_used_as_spec(spec_is_overflowed)]
    pub exec fn is_overflowed(&self) -> (result: bool)
        ensures
            result == self.spec_is_overflowed(),
    {
        proof { use_type_invariant(self) }
        self.v.is_none()
    }

    /// Unwraps the `OverflowableU64` instance to get the `u64` value.
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

    /// Converts the `OverflowableU64` instance to an `Option<u64>`.
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

    /// Adds a `u64` value to the `OverflowableU64` instance.
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
        if self.v.is_none() || v2 > u64::MAX - self.v.unwrap() {
            assert(i@ > u64::MAX);
            Self { i, v: None }
        } else {
            Self { i, v: Some(self.v.unwrap() + v2) }
        }
    }

    /// Adds another `OverflowableU64` instance to the current instance.
    /// Ensures the resulting value matches the sum of the internal representations of both instances.
    #[inline]
    pub exec fn add_overflowable_u64(&self, v2: &OverflowableU64) -> (result: Self)
        ensures
            result@ == self@ + v2@,
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(v2);
        }
        let i: Ghost<nat> = Ghost((self@ + v2@) as nat);
        if self.is_overflowed() || v2.is_overflowed() || self.v.unwrap() > u64::MAX
            - v2.v.unwrap() {
            assert(i@ > u64::MAX);
            Self { i, v: None }
        } else {
            Self { i, v: Some(self.v.unwrap() + v2.v.unwrap()) }
        }
    }

    /// Multiplies the `OverflowableU64` instance by a `u64` value.
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
        if v2 == 0 {
            assert(i@ == 0) by {
                lemma_mul_by_zero_is_zero(self@ as int);
            }
            Self { i, v: Some(0) }
        } else if self.is_overflowed() {
            assert(self@ * v2 >= self@ * 1 == self@) by {
                lemma_mul_inequality(1, v2 as int, self@ as int);
                lemma_mul_is_commutative(self@ as int, v2 as int);
            }
            Self { i, v: None }
        } else if self.v.unwrap() > u64::MAX / v2 {
            // To make sure the multiplication won't overflow, we compare `self.v` to
            // `u64::MAX / v2`. If it's greater, we can prove that it will overflow
            // so we don't need to do the multiplication.
            proof {
                assert(self@ >= self.v.unwrap() >= u64::MAX / v2 + 1);
                assert(self@ >= (u64::MAX + v2) / v2 as int) by {
                    lemma_div_plus_one(u64::MAX as int, v2 as int);
                }
                assert(v2 * ((u64::MAX + v2) / (v2 as int)) == u64::MAX + v2 - ((u64::MAX + v2) % (
                v2 as int))) by {
                    lemma_fundamental_div_mod(u64::MAX + v2, v2 as int);
                }
                assert(v2 * ((u64::MAX + v2) / (v2 as int)) > u64::MAX) by {
                    assert(0 <= (u64::MAX + v2) % (v2 as int) < v2) by {
                        lemma_mod_division_less_than_divisor(u64::MAX + v2, v2 as int);
                    }
                }
                assert(self@ * v2 >= ((u64::MAX + v2) / (v2 as int)) * v2) by {
                    lemma_mul_inequality((u64::MAX + v2) / (v2 as int), self@ as int, v2 as int);
                }
                assert(self@ * v2 > u64::MAX);
            }
            Self { i, v: None }
        } else {
            // If `self.v <= u64::MAX / v2`, then we can prove the multiplication
            // won't overflow.
            proof {
                assert(self.v.unwrap() * v2 <= (u64::MAX / v2) * v2) by {
                    lemma_mul_inequality(
                        self.v.unwrap() as int,
                        u64::MAX as int / v2 as int,
                        v2 as int,
                    );
                }
                assert((u64::MAX / v2) * v2 == u64::MAX - u64::MAX % v2) by {
                    lemma_fundamental_div_mod(u64::MAX as int, v2 as int);
                }
                assert((u64::MAX / v2) * v2 <= u64::MAX) by {
                    lemma_mod_division_less_than_divisor(u64::MAX as int, v2 as int);
                }
            }
            Self { i, v: Some(self.v.unwrap() * v2) }
        }
    }

    /// Multiplies the `OverflowableU64` instance by another `OverflowableU64` instance.
    /// Ensures the resulting value matches the product of the internal representations of both instances.
    #[inline]
    pub exec fn mul_overflowable_u64(&self, v2: &Self) -> (result: Self)
        ensures
            result@ == self@ as int * v2@ as int,
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(v2);
        }
        let i: Ghost<nat> = Ghost(self@ * v2@);
        if v2.is_overflowed() {
            if self.v.is_some() && self.v.unwrap() == 0 {
                assert(i@ == 0) by {
                    lemma_mul_by_zero_is_zero(v2@ as int);
                }
                Self { i, v: Some(0) }
            } else {
                assert(i@ > u64::MAX) by {
                    lemma_mul_inequality(1, self@ as int, v2@ as int);
                }
                Self { i, v: None }
            }
        } else {
            self.mul(v2.v.unwrap())
        }
    }
}

/// This struct represents a `u32` value that can overflow. The `i` field
/// is a ghost value that represents the true value, while the `v` field
/// is `None` when the value has overflowed and `Some(x)` when the value
/// `x` fits in a `u32`.
pub struct OverflowableU32 {
    i: Ghost<nat>,
    v: Option<u32>,
}

/// The view of an `OverflowableU32` instance is the true value of the instance.
impl View for OverflowableU32 {
    type V = nat;

    closed spec fn view(&self) -> nat {
        self.i@
    }
}

impl Clone for OverflowableU32 {
    /// Clones the `OverflowableU32` instance.
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

impl OverflowableU32 {
    /// This is the internal type invariant for an `OverflowableU32`.
    /// It ensures the key invariant that relates `i` and `v`.
    #[verifier::type_invariant]
    spec fn well_formed(self) -> bool {
        match self.v {
            Some(v) => self.i@ == v,
            None => self.i@ > u32::MAX,
        }
    }

    /// Creates a new `OverflowableU32` instance from a `u32` value.
    /// Ensures the internal representation matches the provided value.
    pub closed spec fn spec_new(v: u32) -> OverflowableU32 {
        OverflowableU32 { i: Ghost(v as nat), v: Some(v) }
    }

    /// Creates a new `OverflowableU32` instance from a `u32` value.
    /// Ensures the internal representation matches the provided value.
    #[verifier::when_used_as_spec(spec_new)]
    pub exec fn new(v: u32) -> (result: Self)
        ensures
            result@ == v,
    {
        Self { i: Ghost(v as nat), v: Some(v) }
    }

    /// Creates a new `OverflowableU32` instance with an overflowed value.
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

    /// Checks if the `OverflowableU32` instance is overflowed.
    /// Returns true if the value is greater than `u32::MAX`.
    pub open spec fn spec_is_overflowed(&self) -> bool {
        self@ > u32::MAX
    }

    /// Checks if the `OverflowableU32` instance is overflowed.
    /// Returns true if the value is greater than `u32::MAX`.
    #[verifier::when_used_as_spec(spec_is_overflowed)]
    pub exec fn is_overflowed(&self) -> (result: bool)
        ensures
            result == self.spec_is_overflowed(),
    {
        proof { use_type_invariant(self) }
        self.v.is_none()
    }

    /// Unwraps the `OverflowableU32` instance to get the `u32` value.
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

    /// Converts the `OverflowableU32` instance to an `Option<u32>`.
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

    /// Adds a `u32` value to the `OverflowableU32` instance.
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
        if self.v.is_none() || v2 > u32::MAX - self.v.unwrap() {
            assert(i@ > u32::MAX);
            Self { i, v: None }
        } else {
            Self { i, v: Some(self.v.unwrap() + v2) }
        }
    }

    /// Adds another `OverflowableU32` instance to the current instance.
    /// Ensures the resulting value matches the sum of the internal representations of both instances.
    #[inline]
    pub exec fn add_overflowable_u32(&self, v2: &OverflowableU32) -> (result: Self)
        ensures
            result@ == self@ + v2@,
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(v2);
        }
        let i: Ghost<nat> = Ghost((self@ + v2@) as nat);
        if self.is_overflowed() || v2.is_overflowed() || self.v.unwrap() > u32::MAX
            - v2.v.unwrap() {
            assert(i@ > u32::MAX);
            Self { i, v: None }
        } else {
            Self { i, v: Some(self.v.unwrap() + v2.v.unwrap()) }
        }
    }

    /// Multiplies the `OverflowableU32` instance by a `u32` value.
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
        if v2 == 0 {
            assert(i@ == 0) by {
                lemma_mul_by_zero_is_zero(self@ as int);
            }
            Self { i, v: Some(0) }
        } else if self.is_overflowed() {
            assert(self@ * v2 >= self@ * 1 == self@) by {
                lemma_mul_inequality(1, v2 as int, self@ as int);
                lemma_mul_is_commutative(self@ as int, v2 as int);
            }
            Self { i, v: None }
        } else if self.v.unwrap() > u32::MAX / v2 {
            // To make sure the multiplication won't overflow, we compare `self.v` to
            // `u32::MAX / v2`. If it's greater, we can prove that it will overflow
            // so we don't need to do the multiplication.
            proof {
                assert(self@ >= self.v.unwrap() >= u32::MAX / v2 + 1);
                assert(self@ >= (u32::MAX + v2) / v2 as int) by {
                    lemma_div_plus_one(u32::MAX as int, v2 as int);
                }
                assert(v2 * ((u32::MAX + v2) / (v2 as int)) == u32::MAX + v2 - ((u32::MAX + v2) % (
                v2 as int))) by {
                    lemma_fundamental_div_mod(u32::MAX + v2, v2 as int);
                }
                assert(v2 * ((u32::MAX + v2) / (v2 as int)) > u32::MAX) by {
                    assert(0 <= (u32::MAX + v2) % (v2 as int) < v2) by {
                        lemma_mod_division_less_than_divisor(u32::MAX + v2, v2 as int);
                    }
                }
                assert(self@ * v2 >= ((u32::MAX + v2) / (v2 as int)) * v2) by {
                    lemma_mul_inequality((u32::MAX + v2) / (v2 as int), self@ as int, v2 as int);
                }
                assert(self@ * v2 > u32::MAX);
            }
            Self { i, v: None }
        } else {
            // If `self.v <= u32::MAX / v2`, then we can prove the multiplication
            // won't overflow.
            proof {
                assert(self.v.unwrap() * v2 <= (u32::MAX / v2) * v2) by {
                    lemma_mul_inequality(
                        self.v.unwrap() as int,
                        u32::MAX as int / v2 as int,
                        v2 as int,
                    );
                }
                assert((u32::MAX / v2) * v2 == u32::MAX - u32::MAX % v2) by {
                    lemma_fundamental_div_mod(u32::MAX as int, v2 as int);
                }
                assert((u32::MAX / v2) * v2 <= u32::MAX) by {
                    lemma_mod_division_less_than_divisor(u32::MAX as int, v2 as int);
                }
            }
            Self { i, v: Some(self.v.unwrap() * v2) }
        }
    }

    /// Multiplies the `OverflowableU32` instance by another `OverflowableU32` instance.
    /// Ensures the resulting value matches the product of the internal representations of both instances.
    #[inline]
    pub exec fn mul_overflowable_u32(&self, v2: &Self) -> (result: Self)
        ensures
            result@ == self@ as int * v2@ as int,
    {
        proof {
            use_type_invariant(self);
            use_type_invariant(v2);
        }
        let i: Ghost<nat> = Ghost(self@ * v2@);
        if v2.is_overflowed() {
            if self.v.is_some() && self.v.unwrap() == 0 {
                assert(i@ == 0) by {
                    lemma_mul_by_zero_is_zero(v2@ as int);
                }
                Self { i, v: Some(0) }
            } else {
                assert(i@ > u32::MAX) by {
                    lemma_mul_inequality(1, self@ as int, v2@ as int);
                }
                Self { i, v: None }
            }
        } else {
            self.mul(v2.v.unwrap())
        }
    }
}

} // verus!
