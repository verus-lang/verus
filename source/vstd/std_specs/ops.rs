#![allow(unused_imports)]

/// Defines the specifications for operator traits.
///
/// This file specifies the behavior of operator traits for integers when the trait method is invoked.
/// To maintain flexibility in defining postconditions, this specification does not enforce them.
/// However, preconditions for some operator trait method are required to prevent overflow and underflow.
///
/// - For primitive integer types, the expression `lhs $op rhs` is directly handled by the verifier
///   without relying on trait specifications defined here, avoiding additional trigger costs.
///   However, calling `lhs.add(rhs)` or T::add(lhs, rhs) will trigger the corresponding trait method
/// - If an operator is overloaded for a custom type, both `lhs $op rhs` and `lhs.add(rhs)` invoke the
///   corresponding trait method for verification.
///   and its preconditions are enforced.
/// - To allow users to specify preconditions for trait methods, preconditions can be defined in
///   the `Spec${Op}Requires` trait for types within the target crate.
/// - For types defined in external crates, preconditions must be specified using an axiom to define
///   the uninterpreted `spec_${op}_requires`, which is easy to cause contradict axioms and should be
///   avoided when possible.
use super::super::prelude::*;

verus! {

pub broadcast group group_ops_axioms {
    axiom_add_requires,
    axiom_sub_requires,
    axiom_shl_requires,
    axiom_mul_requires,
    axiom_div_requires,
    axiom_rem_requires,
    axiom_shr_requires,
    group_integer_ops_call_requires,
}

} // verus!
macro_rules! def_bin_ops_spec {
    ($trait:path, $extrait: ident, $fun:ident, $spec_trait:ident, $spec_requires:ident, $axiom_requires:ident, $axiom_call_requires:ident) => {
        builtin_macros::verus! {
            /// Define the pre-condition for the operator trait.
            /// This is used since the preconditions of trait methods must be set in the trait definition.
            /// spec_{op}_requires(..) ==> call_requires(...)
            pub uninterp spec fn $spec_requires<Lhs, Rhs>(v: Lhs, rhs: Rhs) -> bool;

            /// This is a workaround to allow the pre-condition to be defined outside the trait,
            /// without writing axiom for spec_{op}_requires.
            /// Spec{Op}Requires::spec_requires(...) <==> spec_{op}_requires(...)
            pub trait $spec_trait<Rhs>: Sized {
                open spec fn $spec_requires(self, rhs: Rhs) -> bool {true}
            }

            #[verifier::external_trait_specification]
            pub trait $extrait<Rhs> {
                type ExternalTraitSpecificationFor: $trait<Rhs>;

                type Output;
                fn $fun(self, rhs: Rhs) -> (ret: Self::Output)
                where Self: Sized
                requires $spec_requires::<Self, Rhs>(self, rhs);
            }

            pub broadcast proof fn $axiom_requires<Lhs, Rhs>(lhs: Lhs, rhs: Rhs)
            where
                Lhs: $spec_trait<Rhs>,
            ensures
                #![trigger $spec_requires(lhs, rhs)]
                $spec_requires(lhs, rhs) == Lhs::$spec_requires(lhs, rhs),
            {
                admit()
            }

            pub proof fn $axiom_call_requires<Lhs, Rhs>(lhs: Lhs, rhs: Rhs)
            where
                Lhs: $spec_trait<Rhs> + $trait<Rhs>,
            ensures
                #![trigger call_requires(Lhs::$fun, (lhs, rhs))]
                Lhs::$spec_requires(lhs, rhs) ==> call_requires(Lhs::$fun, (lhs, rhs)),
            {
                $axiom_requires(lhs, rhs);
            }
        }
};
}

verus! {

#[verifier::external_trait_specification]
pub trait ExNot {
    type ExternalTraitSpecificationFor: core::ops::Not;

    type Output;

    fn not(self) -> Self::Output where Self: Sized;
}

} // verus!
verus! {

#[verifier::external_trait_specification]
pub trait ExBitAnd<Rhs> {
    type ExternalTraitSpecificationFor: core::ops::BitAnd<Rhs>;

    type Output;

    fn bitand(self, other: Rhs) -> Self::Output where Self: Sized;
}

} // verus!
def_bin_ops_spec!(
    core::ops::Add,
    ExAdd,
    add,
    SpecAddRequires,
    spec_add_requires,
    axiom_add_requires,
    axiom_add_call_requires
);

def_bin_ops_spec!(
    core::ops::Sub,
    ExSub,
    sub,
    SpecSubRequires,
    spec_sub_requires,
    axiom_sub_requires,
    axiom_sub_call_requires
);

def_bin_ops_spec!(
    core::ops::Rem,
    ExRem,
    rem,
    SpecRemRequires,
    spec_rem_requires,
    axiom_rem_requires,
    axiom_rem_call_requires
);

def_bin_ops_spec!(
    core::ops::Mul,
    ExMul,
    mul,
    SpecMulRequires,
    spec_mul_requires,
    axiom_mul_requires,
    axiom_mul_call_requires
);

def_bin_ops_spec!(
    core::ops::Div,
    ExDiv,
    div,
    SpecDivRequires,
    spec_div_requires,
    axiom_div_requires,
    axiom_div_call_requires
);

def_bin_ops_spec!(
    core::ops::Shl,
    ExShl,
    shl,
    SpecShlRequires,
    spec_shl_requires,
    axiom_shl_requires,
    axiom_shl_call_requires
);

def_bin_ops_spec!(
    core::ops::Shr,
    ExShr,
    shr,
    SpecShrRequires,
    spec_shr_requires,
    axiom_shr_requires,
    axiom_shr_call_requires
);

macro_rules! def_bop_specs {
    ($tr: path, $func: ident, $op:tt, [$($typ:ty)*]) => {
        verus! {
        $(
            pub assume_specification[<$typ as $tr<$typ>>::$func ](a: $typ, b: $typ) -> (ret: $typ)
            ensures
                ret == (a $op b);
        )*
    }
    };
}

macro_rules! def_uop_axioms {
    ($tr: path, $fun: ident, $op:tt, [$($typ:ty)*]) => {
        verus!{
        $(
            pub assume_specification[ <$typ as $tr>::$fun ](a: $typ) -> (ret: $typ)
            ensures
                ret == ($op a);
        )*
    }
    };
}

def_bop_specs!(core::ops::Add, add, +, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_specs!(core::ops::Sub, sub, -, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_specs!(core::ops::Mul, mul, *, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_specs!(core::ops::Div, div, /, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_specs!(core::ops::Rem, rem, %, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_specs!(core::ops::BitAnd, bitand, &, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_specs!(core::ops::Shl, shl, <<, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_specs!(core::ops::Shr, shr, >>, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_uop_axioms!(core::ops::Not, not, !, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

macro_rules! def_call_requires_axiom {
    ($typ:ty, $mname: ident) => {
        verus!{
        impl SpecAddRequires<$typ> for $typ {
            #[verifier(inline)]
            open spec fn spec_add_requires(self, rhs: $typ) -> bool {
                (self + rhs) as $typ == (self + rhs)
            }
        }

        impl SpecSubRequires<$typ> for $typ {
            #[verifier(inline)]
            open spec fn spec_sub_requires(self, rhs: $typ) -> bool {
                (self - rhs) as $typ == (self - rhs)
            }
        }


        impl SpecRemRequires<$typ> for $typ {
            #[verifier(inline)]
            open spec fn spec_rem_requires(self, rhs: $typ) -> bool {
                rhs != 0
            }
        }

        impl SpecDivRequires<$typ> for $typ {
            #[verifier(inline)]
            open spec fn spec_div_requires(self, rhs: $typ) -> bool {
                rhs != 0
            }
        }

        impl SpecMulRequires<$typ> for $typ {
            #[verifier(inline)]
            open spec fn spec_mul_requires(self, rhs: $typ) -> bool {
                self * rhs == (self * rhs) as $typ
            }
        }

        impl SpecShlRequires<$typ> for $typ {
            #[verifier(inline)]
            open spec fn spec_shl_requires(self, rhs: $typ) -> bool {
                rhs <= $typ::BITS
            }
        }

        impl SpecShrRequires<$typ> for $typ {
            #[verifier(inline)]
            open spec fn spec_shr_requires(self, rhs: $typ) -> bool {
                rhs <= $typ::BITS
            }
        }

        mod $mname {
        use super::*;
        // Triggered by call_requires since we may not call spec_xxx_requires direcly.
        pub broadcast proof fn add_op_call_requires(a: $typ, b: $typ)
        ensures
            a.spec_add_requires(b) ==> #[trigger]call_requires(<$typ as core::ops::Add>::add, (a, b)),
        {
            axiom_add_requires(a, b);
        }

        pub broadcast proof fn sub_op_call_requires(a: $typ, b: $typ)
        ensures
            a.spec_sub_requires(b) ==> #[trigger]call_requires(<$typ as core::ops::Sub>::sub, (a, b)),
        {
            axiom_sub_requires(a, b);
        }

        pub broadcast proof fn mul_op_call_requires(a: $typ, b: $typ)
        ensures
            a.spec_mul_requires(b) ==> #[trigger]call_requires(<$typ as core::ops::Mul>::mul, (a, b)),
        {
            axiom_mul_requires(a, b);
        }

        pub broadcast proof fn rem_op_call_requires(a: $typ, b: $typ)
        ensures
            a.spec_rem_requires(b) ==> #[trigger]call_requires(<$typ as core::ops::Rem>::rem, (a, b)),
        {
            axiom_rem_requires(a, b);
        }

        pub broadcast proof fn div_op_call_requires(a: $typ, b: $typ)
        ensures
            a.spec_div_requires(b) ==> #[trigger]call_requires(<$typ as core::ops::Div>::div, (a, b)),
        {
            axiom_div_requires(a, b);
        }

        pub broadcast proof fn shr_op_call_requires(a: $typ, b: $typ)
        ensures
            a.spec_shr_requires(b) ==> #[trigger]call_requires(<$typ as core::ops::Shr>::shr, (a, b)),
        {
            axiom_shr_requires(a, b);
        }

        pub broadcast proof fn shl_op_call_requires(a: $typ, b: $typ)
        ensures
            a.spec_shr_requires(b) ==> #[trigger]call_requires(<$typ as core::ops::Shl>::shl, (a, b)),
        {
            axiom_shl_requires(a, b);
        }

        pub broadcast group $mname {
            add_op_call_requires,
            sub_op_call_requires,
            mul_op_call_requires,
            div_op_call_requires,
            rem_op_call_requires,
            shl_op_call_requires,
            shr_op_call_requires,
        }
    }
    }
    };
}

macro_rules! def_call_requires_axioms {
    ($group_op_requires: ident, [$($typ:ty, $mname: ident)*])  => {
        $(
            def_call_requires_axiom!($typ, $mname);
        )*
        verus!{
            pub broadcast group $group_op_requires {
                $(
                    $mname::$mname,
                )*
            }
        }
    }
}

def_call_requires_axioms! {group_integer_ops_call_requires, [
    usize, axiom_usize_op_requires
    u8, axiom_u8_op_requires
    u16, axiom_u16_op_requires
    u32, axiom_u32_op_requires
    u64, axiom_u64_op_requires
    isize, axiom_isize_op_requires
    i8, axiom_i8_op_requires
    i16, axiom_i16_op_requires
    i32, axiom_i32_op_requires
    i64, axiom_i64_op_requires
]
}
