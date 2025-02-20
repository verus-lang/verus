#![allow(unused_imports)]
use super::super::prelude::*;

verus! {

pub broadcast group group_ops_axioms {
    axiom_add_requires,
    axiom_add,
    axiom_sub_requires,
    axiom_sub,
    axiom_bitand_requires,
    axiom_bitand,
    axiom_not,
}

} // verus!
macro_rules! def_uop_spec {
    ($trait:path, $extrait: ident, $fun:ident, $spec_trait:ident, $spec_ensures:ident, $axiom_ensures:ident) => {
        builtin_macros::verus! {
            pub open spec fn $spec_ensures<T, Output>(v: T, ret: Output) -> bool;

            #[verifier::external_trait_specification]
            pub trait $extrait {
                type ExternalTraitSpecificationFor: $trait;

                type Output;
                fn $fun(self) -> (ret: Self::Output)
                where Self: Sized
                ensures $spec_ensures::<_, Self::Output>(self, ret),
                ;
            }

            pub trait $spec_trait: Sized {
                type Output;
                open spec fn $spec_ensures(v: Self, ret: Self::Output) -> bool {true}
            }

            pub broadcast proof fn $axiom_ensures<T>(v: T, ret: T::Output)
            where
                T: $spec_trait
            ensures
                T::$spec_ensures(v, ret) == #[trigger]$spec_ensures(v, ret),
            {
                admit()
            }
        }
};
}

macro_rules! def_bin_ops_spec {
    ($trait:path, $extrait: ident, $fun:ident, $spec_trait:ident, $spec_requires:ident, $spec_ensures:ident, $axiom_requires:ident, $axiom_ensures:ident) => {
        builtin_macros::verus! {
            pub open spec fn $spec_ensures<T, Rhs, Output>(v: T, rhs: Rhs, ret: Output)-> bool;

            pub open spec fn $spec_requires<T, Rhs>(v: T, rhs: Rhs) -> bool;

            pub trait $spec_trait<Rhs>: Sized {
                type Output;
                open spec fn $spec_ensures(v: Self, rhs: Rhs, ret: Self::Output) -> bool {true}
                open spec fn $spec_requires(v: Self, rhs: Rhs) -> bool {true}
            }

            #[verifier::external_trait_specification]
            pub trait $extrait<Rhs> {
                type ExternalTraitSpecificationFor: $trait<Rhs>;

                type Output;
                fn $fun(self, rhs: Rhs) -> (ret: Self::Output)
                where Self: Sized
                requires $spec_requires(self, rhs),
                ensures $spec_ensures(self, rhs, ret) // Please Impl SpecXXOp before exec operator trait.
                ;
            }

            pub broadcast proof fn $axiom_ensures<T, Rhs>(v: T, rhs: Rhs, ret: T::Output)
            where
                T: $spec_trait<Rhs>
            ensures
                (#[trigger]$spec_ensures(v, rhs, ret)) == T::$spec_ensures(v, rhs, ret)
            {
                admit()
            }

            pub broadcast proof fn $axiom_requires<T, Rhs>(v: T, rhs: Rhs)
            where
                T: $spec_trait<Rhs>
            ensures
                (#[trigger]$spec_requires(v, rhs)) == T::$spec_requires(v, rhs),
            {
                admit()
            }
        }
};
}

def_uop_spec!(core::ops::Not, ExNot, not, SpecNotOp, spec_not_ensures, axiom_not);
def_bin_ops_spec!(
    core::ops::Add,
    ExAdd,
    add,
    SpecAddOp,
    spec_add_requires,
    spec_add_ensures,
    axiom_add_requires,
    axiom_add
);

def_bin_ops_spec!(
    core::ops::Sub,
    ExSub,
    sub,
    SpecSubOp,
    spec_sub_requires,
    spec_sub_ensures,
    axiom_sub_requires,
    axiom_sub
);

def_bin_ops_spec!(
    core::ops::Rem,
    ExRem,
    rem,
    SpecRemOp,
    spec_rem_requires,
    spec_rem_ensures,
    axiom_rem_requires,
    axiom_rem
);

def_bin_ops_spec!(
    core::ops::Mul,
    ExMul,
    mul,
    SpecMulOp,
    spec_mul_requires,
    spec_mul_ensures,
    axiom_mul_requires,
    axiom_mul
);

def_bin_ops_spec!(
    core::ops::Div,
    ExDiv,
    div,
    SpecDivOp,
    spec_div_requires,
    spec_div_ensures,
    axiom_div_requires,
    axiom_div
);

def_bin_ops_spec!(
    core::ops::BitAnd,
    ExBitAdd,
    bitand,
    SpecBitAndOp,
    spec_bitand_requires,
    spec_bitand_ensures,
    axiom_bitand_requires,
    axiom_bitand
);

def_bin_ops_spec!(
    core::ops::Shl,
    ExShl,
    shl,
    SpecShlOp,
    spec_shl_requires,
    spec_shl_ensures,
    axiom_shl_requires,
    axiom_shl
);

def_bin_ops_spec!(
    core::ops::Shr,
    ExShr,
    shr,
    SpecShrOp,
    spec_shr_requires,
    spec_shr_ensures,
    axiom_shr_requires,
    axiom_shr
);

macro_rules! def_bop_spec {
    ($typ:ty, $rtyp:ty, $otyp: ty, $op:tt, $spec_ensures:ident, $spec_requires:ident, $spec_tr:ident) => {
        verus! {
            impl $spec_tr<$rtyp> for $typ {
                type Output = $otyp;

                #[verifier(inline)]
                open spec fn $spec_requires(v: Self, rhs: $rtyp) -> bool {
                    (v $op rhs) as $otyp == (v $op rhs)
                }

                #[verifier(inline)]
                open spec fn $spec_ensures(v: Self, rhs: $rtyp, ret: $otyp) -> bool {
                    ret == (v $op rhs)
                }
            }
        }
    };
}

macro_rules! def_bop_specs {
    ($spec_tr:ident, $spec_ensures:ident, $spec_requires:ident,$op:tt, [$($typ:ty)*])  => {
        $(
            def_bop_spec!($typ, $typ, $typ, $op, $spec_ensures, $spec_requires, $spec_tr);
        )*
    }
}

macro_rules! def_uop_axiom {
    ($spec_tr: ident, $spec_ensures:ident, $typ:ty, $otyp: ty, $op:tt) => {
        verus! {
            impl $spec_tr for $typ {
                type Output = $otyp;

                #[verifier(inline)]
                open spec fn $spec_ensures(v: $typ, ret: $otyp) -> bool {
                    ret == ($op v)
                }
            }
        }
    };
}

macro_rules! def_uop_axioms {
    ($tr: ident, $fun:ident, $op:tt, [$($typ:ty)*])  => {
        $(
            def_uop_axiom!($tr, $fun, $typ, $typ, $op);
        )*
    }
}

def_bop_specs!(SpecAddOp, spec_add_ensures, spec_add_requires, +, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);
def_bop_specs!(SpecSubOp, spec_sub_ensures, spec_sub_requires, -, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_specs!(SpecRemOp, spec_rem_ensures, spec_rem_requires, %, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_bop_specs!(SpecBitAndOp, spec_bitand_ensures,spec_bitand_requires, &, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

def_uop_axioms!(SpecNotOp, spec_not_ensures, !, [
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);
