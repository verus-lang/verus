#![allow(unused_imports)]
use super::super::prelude::*;

use core::cmp::Ordering;

macro_rules! num_specs {
    ($uN: ty, $iN: ty, $modname_u:ident, $modname_i:ident, $range:expr) => {
        verus! {

        // Unsigned ints (u8, u16, etc.)

        // Put in separate module to avoid name collisions.
        // Names don't matter - the user uses the stdlib functions.
        mod $modname_u {
            use super::*;

            pub assume_specification[<$uN as Clone>::clone](x: &$uN) -> (res: $uN)
                ensures res == x;

            impl super::super::cmp::PartialEqSpecImpl for $uN {
                open spec fn obeys_eq_spec() -> bool {
                    true
                }

                open spec fn eq_spec(&self, other: &$uN) -> bool {
                    *self == *other
                }
            }

            impl super::super::cmp::PartialOrdSpecImpl for $uN {
                open spec fn obeys_partial_cmp_spec() -> bool {
                    true
                }

                open spec fn partial_cmp_spec(&self, other: &$uN) -> Option<Ordering> {
                    if *self < *other {
                        Some(Ordering::Less)
                    } else if *self > *other {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Equal)
                    }
                }
            }

            impl super::super::cmp::OrdSpecImpl for $uN {
                open spec fn obeys_cmp_spec() -> bool {
                    true
                }

                open spec fn cmp_spec(&self, other: &$uN) -> Ordering {
                    if *self < *other {
                        Ordering::Less
                    } else if *self > *other {
                        Ordering::Greater
                    } else {
                        Ordering::Equal
                    }
                }
            }

            pub assume_specification[<$uN as PartialEq<$uN>>::eq](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as PartialEq<$uN>>::ne](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as Ord>::cmp](x: &$uN, y: &$uN) -> Ordering;

            pub assume_specification[<$uN as PartialOrd<$uN>>::partial_cmp](x: &$uN, y: &$uN) -> Option<Ordering>;

            pub assume_specification[<$uN as PartialOrd<$uN>>::lt](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as PartialOrd<$uN>>::le](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as PartialOrd<$uN>>::gt](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as PartialOrd<$uN>>::ge](x: &$uN, y: &$uN) -> bool;

            #[verifier::allow_in_spec]
            pub assume_specification[<$uN>::wrapping_add](x: $uN, y: $uN) -> $uN
                returns (
                    if x + y > <$uN>::MAX {
                        (x + y - $range) as $uN
                    } else {
                        (x + y) as $uN
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$uN>::wrapping_add_signed](x: $uN, y: $iN) -> $uN
                returns (
                    if x + y > <$uN>::MAX {
                        (x + y - $range) as $uN
                    } else if x + y < 0 {
                        (x + y + $range) as $uN
                    } else {
                        (x + y) as $uN
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$uN>::wrapping_sub](x: $uN, y: $uN) -> $uN
                returns (
                    if x - y < 0 {
                        (x - y + $range) as $uN
                    } else {
                        (x - y) as $uN
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$uN>::wrapping_mul](x: $uN, y: $uN) -> $uN
                returns ((x as nat * y as nat) % $range as nat) as $uN;

            #[verifier::allow_in_spec]
            pub assume_specification[<$uN>::checked_add](x: $uN, y: $uN) -> Option<$uN>
                returns (
                    if x + y > <$uN>::MAX {
                        None
                    } else {
                        Some((x + y) as $uN)
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$uN>::checked_add_signed](x: $uN, y: $iN) -> Option<$uN>
                returns (
                    if x + y > <$uN>::MAX || x + y < 0 {
                        None
                    } else {
                        Some((x + y) as $uN)
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$uN>::checked_sub](x: $uN, y: $uN) -> Option<$uN>
                returns (
                    if x - y < 0 {
                        None
                    } else {
                        Some((x - y) as $uN)
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$uN>::checked_mul](x: $uN, y: $uN) -> Option<$uN>
                returns (
                    if x * y > <$uN>::MAX {
                        None
                    } else {
                        Some((x * y) as $uN)
                    }
                );

            pub open spec fn checked_div(x: $uN, y: $uN) -> Option<$uN> {
                if y == 0 {
                    None
                } else {
                    Some(x / y)
                }
            }

            #[verifier::when_used_as_spec(checked_div)]
            pub assume_specification[<$uN>::checked_div](lhs: $uN, rhs: $uN) -> (result: Option<$uN>)
                ensures
                    result == checked_div(lhs, rhs);

            #[verifier::when_used_as_spec(checked_div)]
            pub assume_specification[<$uN>::checked_div_euclid](lhs: $uN, rhs: $uN) -> (result: Option<$uN>)
                ensures
                    // checked_div is the same as checked_div_euclid for unsigned ints
                    result == checked_div(lhs, rhs);

            #[verifier::allow_in_spec]
            pub assume_specification[<$uN>::is_multiple_of](x: $uN, y: $uN) -> bool
                returns (
                    if y == 0 { x == 0 } else { x % y == 0 }
                );
        }

        // Signed ints (i8, i16, etc.)

        mod $modname_i {
            use super::*;

            pub assume_specification[<$iN as Clone>::clone](x: &$iN) -> (res: $iN)
                ensures res == x;

            impl super::super::cmp::PartialEqSpecImpl for $iN {
                open spec fn obeys_eq_spec() -> bool {
                    true
                }

                open spec fn eq_spec(&self, other: &$iN) -> bool {
                    *self == *other
                }
            }

            impl super::super::cmp::PartialOrdSpecImpl for $iN {
                open spec fn obeys_partial_cmp_spec() -> bool {
                    true
                }

                open spec fn partial_cmp_spec(&self, other: &$iN) -> Option<Ordering> {
                    if *self < *other {
                        Some(Ordering::Less)
                    } else if *self > *other {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Equal)
                    }
                }
            }

            impl super::super::cmp::OrdSpecImpl for $iN {
                open spec fn obeys_cmp_spec() -> bool {
                    true
                }

                open spec fn cmp_spec(&self, other: &$iN) -> Ordering {
                    if *self < *other {
                        Ordering::Less
                    } else if *self > *other {
                        Ordering::Greater
                    } else {
                        Ordering::Equal
                    }
                }
            }

            pub assume_specification[<$iN as PartialEq<$iN>>::eq](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as PartialEq<$iN>>::ne](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as Ord>::cmp](x: &$iN, y: &$iN) -> Ordering;

            pub assume_specification[<$iN as PartialOrd<$iN>>::partial_cmp](x: &$iN, y: &$iN) -> Option<Ordering>;

            pub assume_specification[<$iN as PartialOrd<$iN>>::lt](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as PartialOrd<$iN>>::le](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as PartialOrd<$iN>>::gt](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as PartialOrd<$iN>>::ge](x: &$iN, y: &$iN) -> bool;

            #[verifier::allow_in_spec]
            pub assume_specification[<$iN>::wrapping_add](x: $iN, y: $iN) -> $iN
                returns (
                    if x + y > <$iN>::MAX {
                        (x + y - $range) as $iN
                    } else if x + y < <$iN>::MIN {
                        (x + y + $range) as $iN
                    } else {
                        (x + y) as $iN
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$iN>::wrapping_add_unsigned](x: $iN, y: $uN) -> $iN
                returns (
                    if x + y > <$iN>::MAX {
                        (x + y - $range) as $iN
                    } else {
                        (x + y) as $iN
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$iN>::wrapping_sub](x: $iN, y: $iN) -> (res: $iN)
                returns (
                    if x - y > <$iN>::MAX {
                        (x - y - $range) as $iN
                    } else if x - y < <$iN>::MIN {
                        (x - y + $range) as $iN
                    } else {
                        (x - y) as $iN
                    }
                );

            pub open spec fn signed_crop(x: int) -> $iN {
                if (x % ($range as int)) > (<$iN>::MAX as int) {
                    ((x % ($range as int)) - $range) as $iN
                } else {
                    (x % ($range as int)) as $iN
                }
            }

            #[verifier::allow_in_spec]
            pub assume_specification[<$iN>::wrapping_mul](x: $iN, y: $iN) -> $iN
                returns signed_crop(x * y);

            #[verifier::allow_in_spec]
            pub assume_specification[<$iN>::checked_add](x: $iN, y: $iN) -> Option<$iN>
                returns (
                    if x + y > <$iN>::MAX || x + y < <$iN>::MIN {
                        None
                    } else {
                        Some((x + y) as $iN)
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$iN>::checked_add_unsigned](x: $iN, y: $uN) -> Option<$iN>
                returns (
                    if x + y > <$iN>::MAX {
                        None
                    } else {
                        Some((x + y) as $iN)
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$uN>::saturating_add](x: $uN, y: $uN) -> $uN
                returns (
                    if x + y > <$uN>::MAX {
                        <$uN>::MAX
                    } else {
                        (x + y) as $uN
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$uN>::saturating_sub](x: $uN, y: $uN) -> $uN
                returns (
                    if x - y < <$uN>::MIN {
                        <$uN>::MIN
                    } else {
                        (x - y) as $uN
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$iN>::checked_sub](x: $iN, y: $iN) -> Option<$iN>
                returns (
                    if x - y > <$iN>::MAX || x - y < <$iN>::MIN {
                        None
                    } else {
                        Some((x - y) as $iN)
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$iN>::checked_sub_unsigned](x: $iN, y: $uN) -> Option<$iN>
                returns (
                    if x - y < <$iN>::MIN {
                        None
                    } else {
                        Some((x - y) as $iN)
                    }
                );

            #[verifier::allow_in_spec]
            pub assume_specification[<$iN>::checked_mul](x: $iN, y: $iN) -> Option<$iN>
                returns (
                    if x * y > <$iN>::MAX || x * y < <$iN>::MIN {
                        None
                    } else {
                        Some((x * y) as $iN)
                    }
                );
        }

        }
    };
}

num_specs!(u8, i8, u8_specs, i8_specs, 0x100);
num_specs!(u16, i16, u16_specs, i16_specs, 0x1_0000);
num_specs!(u32, i32, u32_specs, i32_specs, 0x1_0000_0000);
num_specs!(u64, i64, u64_specs, i64_specs, 0x1_0000_0000_0000_0000);
num_specs!(u128, i128, u128_specs, i128_specs, 0x1_0000_0000_0000_0000_0000_0000_0000_0000);
num_specs!(usize, isize, usize_specs, isize_specs, (usize::MAX - usize::MIN + 1));

verus! {

// TODO move all these into the num_specs! macro to handle them for other integer widths
// == u32 methods ==
pub assume_specification[ u32::checked_rem ](lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures
        rhs == 0 ==> result is None,
        rhs != 0 ==> result == Some((lhs % rhs) as u32),
;

pub assume_specification[ u32::checked_rem_euclid ](lhs: u32, rhs: u32) -> (result: Option<u32>)
    ensures
        rhs == 0 ==> result is None,
        rhs != 0 ==> result == Some((lhs % rhs) as u32),
;

// == i32 methods ==
pub assume_specification[ i32::checked_div ](lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result is None,
        ({
            let x = lhs as int;
            let d = rhs as int;
            let output = if x == 0 {
                0
            } else if x > 0 && d > 0 {
                x / d
            } else if x < 0 && d < 0 {
                ((x * -1) / (d * -1))
            } else if x < 0 {
                ((x * -1) / d) * -1
            } else {  // d < 0
                (x / (d * -1)) * -1
            };
            if output < i32::MIN || output > i32::MAX {
                result is None
            } else {
                result == Some(output as i32)
            }
        }),
;

pub assume_specification[ i32::checked_div_euclid ](lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result is None,
        lhs / rhs < i32::MIN || lhs / rhs > i32::MAX ==> result is None,
        i32::MIN <= lhs / rhs <= i32::MAX ==> result == Some((lhs / rhs) as i32),
;

pub assume_specification[ i32::checked_rem ](lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result is None,
        ({
            let x = lhs as int;
            let d = rhs as int;
            let output = if x == 0 {
                0
            } else if x > 0 && d > 0 {
                x % d
            } else if x < 0 && d < 0 {
                ((x * -1) % (d * -1)) * -1
            } else if x < 0 {
                ((x * -1) % d) * -1
            } else {  // d < 0
                x % (d * -1)
            };
            if output < i32::MIN || output > i32::MAX {
                result is None
            } else {
                result == Some(output as i32)
            }
        }),
;

pub assume_specification[ i32::checked_rem_euclid ](lhs: i32, rhs: i32) -> (result: Option<i32>)
    ensures
        rhs == 0 ==> result is None,
        lhs % rhs < i32::MIN || lhs % rhs > i32::MAX ==> result is None,
        i32::MIN <= lhs % rhs <= i32::MAX ==> result == Some((lhs % rhs) as i32),
;

} // verus!
