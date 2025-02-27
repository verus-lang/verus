/// This file defines structs `CheckedU8`, `CheckedU16`, etc. and
/// their associated methods to handle `u8`, `u16`, etc. values that
/// can overflow. Each struct includes a ghost value representing the
/// true value (not subject to overflow), so that the `view` function
/// can provide the true value.
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
///     let x = w.add_value(1);
///     assert(x.is_overflowed());
///     assert(x.view() == 0x10000000000000000);
///
///     let y = CheckedU64::new(0x8000000000000000);
///     let z = y.mul_value(2);
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
///     let a_times_b = CheckedU64::new(a).mul_value(b);
///     let c_times_d = CheckedU64::new(c).mul_value(d);
///     let sum_of_products = a_times_b.add_checked(&c_times_d);
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
use super::mul::{lemma_mul_by_zero_is_zero, lemma_mul_inequality, lemma_mul_is_commutative};
#[allow(unused_imports)]
use super::*;
macro_rules! checked_uint_gen {
    // This macro should be instantiated with the following parameters:
    //
    // $uty - The name of the `std` unsigned integer, e.g., `u64`
    // $cty - The name of the checked struct to create, e.g., `CheckedU64`
    ($uty: ty, $cty: ty) => {
        verus! {

            /// This struct represents a `$uty` value that can overflow. The `i` field
            /// is a ghost value that represents the true value, while the `v` field
            /// is `None` when the value has overflowed and `Some(x)` when the value
            /// `x` fits in a `$uty`.
            pub struct $cty {
                i: Ghost<nat>,
                v: Option<$uty>,
            }

            /// The view of an `$cty` instance is the true value of the instance.
            impl View for $cty
            {
                type V = nat;

                closed spec fn view(&self) -> nat
                {
                    self.i@
                }
            }

            impl Clone for $cty {
                /// Clones the `$cty` instance.
                /// Ensures the cloned instance has the same value as the original.
                exec fn clone(&self) -> (result: Self)
                    ensures
                        result@ == self@
                {
                    proof { use_type_invariant(self); }
                    Self{ i: self.i, v: self.v }
                }
            }

            impl $cty {
                /// This is the internal type invariant for an `$cty`.
                /// It ensures the key invariant that relates `i` and `v`.
                #[verifier::type_invariant]
                spec fn well_formed(self) -> bool
                {
                    match self.v {
                        Some(v) => self.i@ == v,
                        None => self.i@ > $uty::MAX,
                    }
                }

                /// Creates a new `$cty` instance from a `$uty` value.
                /// Ensures the internal representation matches the provided value.
                pub closed spec fn spec_new(v: $uty) -> $cty
                {
                    $cty{ i: Ghost(v as nat), v: Some(v) }
                }

                /// Creates a new `$cty` instance from a `$uty` value.
                /// Ensures the internal representation matches the provided value.
                #[verifier::when_used_as_spec(spec_new)]
                pub exec fn new(v: $uty) -> (result: Self)
                    ensures
                        result@ == v,
                {
                    Self{ i: Ghost(v as nat), v: Some(v) }
                }

                /// Creates a new `$cty` instance with an overflowed value.
                /// Requires the provided value to be greater than `$uty::MAX`.
                /// Ensures the internal representation matches the provided value.
                pub exec fn new_overflowed(Ghost(i): Ghost<int>) -> (result: Self)
                    requires
                        i > $uty::MAX,
                    ensures
                        result@ == i,
                {
                    Self{ i: Ghost(i as nat), v: None }
                }

                /// Checks if the `$cty` instance is overflowed.
                /// Returns true if the value is greater than `$uty::MAX`.
                pub open spec fn spec_is_overflowed(&self) -> bool
                {
                    self@ > $uty::MAX
                }

                /// Checks if the `$cty` instance is overflowed.
                /// Returns true if the value is greater than `$uty::MAX`.
                #[verifier::when_used_as_spec(spec_is_overflowed)]
                pub exec fn is_overflowed(&self) -> (result: bool)
                    ensures
                        result == self.spec_is_overflowed()
                {
                    proof { use_type_invariant(self) }
                    self.v.is_none()
                }

                /// Unwraps the `$cty` instance to get the `$uty` value.
                /// Requires the instance to not be overflowed.
                /// Ensures the returned value matches the internal representation.
                pub exec fn unwrap(&self) -> (result: $uty)
                    requires
                        !self.is_overflowed(),
                    ensures
                        result == self@,
                {
                    proof { use_type_invariant(self) }
                    self.v.unwrap()
                }

                /// Converts the `$cty` instance to an `Option<$uty>`.
                /// Ensures the returned option matches the internal representation.
                pub exec fn to_option(&self) -> (result: Option<$uty>)
                    ensures
                        match result {
                            Some(v) => self@ == v && v <= $uty::MAX,
                            None => self@ > $uty::MAX,
                        }
                {
                    proof { use_type_invariant(self); }
                    self.v
                }

                /// Adds a `$uty` value to the `$cty` instance.
                /// Ensures the resulting value matches the sum of
                /// the internal representation and the provided
                /// value.
                #[inline]
                pub exec fn add_value(&self, v2: $uty) -> (result: Self)
                    ensures
                        result@ == self@ + v2,
                {
                    proof {
                        use_type_invariant(&self);
                    }
                    let i: Ghost<nat> = Ghost((&self@ + v2) as nat);
                    match self.v {
                        Some(v1) => Self{ i, v: v1.checked_add(v2) },
                        None => Self{ i, v: None },
                    }
                }

                /// Adds another `$cty` instance to the current
                /// instance. Ensures the resulting value matches
                /// the sum of the internal representations of
                /// both instances.
                #[inline]
                pub exec fn add_checked(&self, v2: &$cty) -> (result: Self)
                    ensures
                        result@ == self@ + v2@,
                {
                    proof {
                        use_type_invariant(self);
                        use_type_invariant(v2);
                    }
                    match v2.v {
                        Some(n) => self.add_value(n),
                        None => {
                            let i: Ghost<nat> = Ghost((self@ + v2@) as nat);
                            Self{ i, v: None }
                        }
                    }
                }

                /// Multiplies the `$cty` instance by a `$uty`
                /// value. Ensures the resulting value matches the
                /// product of the internal representation and the
                /// provided value.
                #[inline]
                pub exec fn mul_value(&self, v2: $uty) -> (result: Self)
                    ensures
                        result@ == self@ as int * v2 as int,
                {
                    proof {
                        use_type_invariant(self);
                    }
                    let i: Ghost<nat> = Ghost((self@ * v2) as nat);
                    match self.v {
                        Some(n1) => Self{ i, v: n1.checked_mul(v2) },
                        None => {
                            if v2 == 0 {
                                assert(i@ == 0) by {
                                    lemma_mul_by_zero_is_zero(self@ as int);
                                }
                                Self{ i, v: Some(0) }
                            }
                            else {
                                assert(self@ * v2 >= self@ * 1 == self@) by {
                                    lemma_mul_inequality(1, v2 as int, self@ as int);
                                    lemma_mul_is_commutative(self@ as int, v2 as int);
                                }
                                Self{ i, v: None }
                            }
                        },
                    }
                }

                /// Multiplies the `$cty` instance by another `$cty` instance.
                /// Ensures the resulting value matches the product of the internal
                /// representations of both instances.
                #[inline]
                pub exec fn mul_checked(&self, v2: &Self) -> (result: Self)
                    ensures
                        result@ == self@ as int * v2@ as int,
                {
                    proof {
                        use_type_invariant(self);
                        use_type_invariant(v2);
                    }
                    let i: Ghost<nat> = Ghost((self@ * v2@) as nat);
                    match v2.v {
                        Some(n) => self.mul_value(n),
                        None => {
                            match self.v {
                                Some(n1) => {
                                    if n1 == 0 {
                                        assert(i@ == 0) by {
                                            lemma_mul_by_zero_is_zero(v2@ as int);
                                        }
                                        Self{ i, v: Some(0) }
                                    }
                                    else {
                                        assert(self@ * v2@ >= 1 * v2@ == v2@) by {
                                            lemma_mul_inequality(1, self@ as int, v2@ as int);
                                        }
                                        Self{ i, v: None }
                                    }
                                },
                                None => {
                                    assert(self@ * v2@ > $uty::MAX) by {
                                        lemma_mul_inequality(1, self@ as int, v2@ as int);
                                    }
                                    Self{ i, v: None }
                                },
                            }
                        }
                    }
                }
            }
        }
    };
}

checked_uint_gen!(u8, CheckedU8);
checked_uint_gen!(u16, CheckedU16);
checked_uint_gen!(u32, CheckedU32);
checked_uint_gen!(u64, CheckedU64);
checked_uint_gen!(u128, CheckedU128);
checked_uint_gen!(usize, CheckedUsize);
