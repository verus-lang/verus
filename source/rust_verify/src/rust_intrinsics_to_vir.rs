use crate::util::spanned_typed_new;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{Expr, ExprX, IntRange, IntegerTypeBoundKind, Mode, Typ, TypX, UnaryOpr};

pub(crate) fn int_intrinsic_constant_to_vir(span: Span, typ: &Typ, f_name: &str) -> Option<Expr> {
    let mk_expr = |x: ExprX| spanned_typed_new(span, &typ, x);

    let lit_expr = |u: u128| Some(mk_expr(ExprX::Const(vir::ast_util::const_int_from_u128(u))));

    let lit_expr_i = |i: i128| Some(mk_expr(ExprX::Const(vir::ast_util::const_int_from_i128(i))));

    let arch_bits = || {
        let arg = spanned_typed_new(
            span,
            &Arc::new(TypX::Int(IntRange::Int)),
            ExprX::Const(vir::ast_util::const_int_from_u128(0)),
        );

        let kind = IntegerTypeBoundKind::ArchWordBits;

        return mk_expr(ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, Mode::Exec), arg));
    };

    let arch_bound = |kind| {
        return Some(mk_expr(ExprX::UnaryOpr(
            UnaryOpr::IntegerTypeBound(kind, Mode::Exec),
            arch_bits(),
        )));
    };

    match f_name {
        // MIN
        "core::num::<impl u8>::MIN" => lit_expr(0),
        "core::num::<impl u16>::MIN" => lit_expr(0),
        "core::num::<impl u32>::MIN" => lit_expr(0),
        "core::num::<impl u64>::MIN" => lit_expr(0),
        "core::num::<impl u128>::MIN" => lit_expr(0),
        "core::num::<impl usize>::MIN" => lit_expr(0),

        "core::num::<impl i8>::MIN" => lit_expr_i(i8::MIN.into()),
        "core::num::<impl i16>::MIN" => lit_expr_i(i16::MIN.into()),
        "core::num::<impl i32>::MIN" => lit_expr_i(i32::MIN.into()),
        "core::num::<impl i64>::MIN" => lit_expr_i(i64::MIN.into()),
        "core::num::<impl i128>::MIN" => lit_expr_i(i128::MIN),
        "core::num::<impl isize>::MIN" => arch_bound(IntegerTypeBoundKind::SignedMin),

        // MAX
        "core::num::<impl u8>::MAX" => lit_expr(u8::MAX.into()),
        "core::num::<impl u16>::MAX" => lit_expr(u16::MAX.into()),
        "core::num::<impl u32>::MAX" => lit_expr(u32::MAX.into()),
        "core::num::<impl u64>::MAX" => lit_expr(u64::MAX.into()),
        "core::num::<impl u128>::MAX" => lit_expr(u128::MAX),
        "core::num::<impl usize>::MAX" => arch_bound(IntegerTypeBoundKind::UnsignedMax),

        "core::num::<impl i8>::MAX" => lit_expr_i(i8::MAX.into()),
        "core::num::<impl i16>::MAX" => lit_expr_i(i16::MAX.into()),
        "core::num::<impl i32>::MAX" => lit_expr_i(i32::MAX.into()),
        "core::num::<impl i64>::MAX" => lit_expr_i(i64::MAX.into()),
        "core::num::<impl i128>::MAX" => lit_expr_i(i128::MAX),
        "core::num::<impl isize>::MAX" => arch_bound(IntegerTypeBoundKind::SignedMax),

        // BITS
        "core::num::<impl u8>::BITS" => lit_expr(u8::BITS.into()),
        "core::num::<impl u16>::BITS" => lit_expr(u16::BITS.into()),
        "core::num::<impl u32>::BITS" => lit_expr(u32::BITS.into()),
        "core::num::<impl u64>::BITS" => lit_expr(u64::BITS.into()),
        "core::num::<impl u128>::BITS" => lit_expr(u128::BITS.into()),
        "core::num::<impl usize>::BITS" => Some(arch_bits()),

        "core::num::<impl i8>::BITS" => lit_expr_i(i8::BITS.into()),
        "core::num::<impl i16>::BITS" => lit_expr_i(i16::BITS.into()),
        "core::num::<impl i32>::BITS" => lit_expr_i(i32::BITS.into()),
        "core::num::<impl i64>::BITS" => lit_expr_i(i64::BITS.into()),
        "core::num::<impl i128>::BITS" => lit_expr_i(i128::BITS.into()),
        "core::num::<impl isize>::BITS" => Some(arch_bits()),

        _ => None,
    }
}
