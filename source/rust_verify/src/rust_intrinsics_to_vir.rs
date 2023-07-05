use crate::{
    context::Context,
    verus_items::{self, RustIntConst, RustIntIntrinsicItem, RustIntType},
};
use rustc_span::def_id::DefId;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{Expr, ExprX, IntRange, IntegerTypeBoundKind, Mode, Typ, TypX, UnaryOpr};

pub(crate) fn int_intrinsic_constant_to_vir(
    ctxt: &Context,
    span: Span,
    typ: &Typ,
    id: DefId,
) -> Option<Expr> {
    let mk_expr = |x: ExprX| ctxt.spanned_typed_new(span, &typ, x);

    let lit_expr = |u: u128| Some(mk_expr(ExprX::Const(vir::ast_util::const_int_from_u128(u))));

    let lit_expr_i = |i: i128| Some(mk_expr(ExprX::Const(vir::ast_util::const_int_from_i128(i))));

    let arch_bits = || {
        let arg = ctxt.spanned_typed_new(
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

    let rust_item = verus_items::get_rust_item(ctxt.tcx, id);
    use verus_items::RustItem::IntIntrinsic;
    use RustIntConst::*;
    match rust_item {
        // MIN
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U8, Min))) => lit_expr(0),
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U16, Min))) => lit_expr(0),
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U32, Min))) => lit_expr(0),
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U64, Min))) => lit_expr(0),
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U128, Min))) => lit_expr(0),
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::USize, Min))) => lit_expr(0),

        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I8, Min))) => {
            lit_expr_i(i8::MIN.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I16, Min))) => {
            lit_expr_i(i16::MIN.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I32, Min))) => {
            lit_expr_i(i32::MIN.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I64, Min))) => {
            lit_expr_i(i64::MIN.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I128, Min))) => lit_expr_i(i128::MIN),
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::ISize, Min))) => {
            arch_bound(IntegerTypeBoundKind::SignedMin)
        }

        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U8, Max))) => lit_expr(u8::MAX.into()),
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U16, Max))) => {
            lit_expr(u16::MAX.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U32, Max))) => {
            lit_expr(u32::MAX.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U64, Max))) => {
            lit_expr(u64::MAX.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U128, Max))) => lit_expr(u128::MAX),
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::USize, Max))) => {
            arch_bound(IntegerTypeBoundKind::UnsignedMax)
        }

        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I8, Max))) => {
            lit_expr_i(i8::MAX.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I16, Max))) => {
            lit_expr_i(i16::MAX.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I32, Max))) => {
            lit_expr_i(i32::MAX.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I64, Max))) => {
            lit_expr_i(i64::MAX.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I128, Max))) => lit_expr_i(i128::MAX),
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::ISize, Max))) => {
            arch_bound(IntegerTypeBoundKind::SignedMax)
        }

        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U8, Bits))) => {
            lit_expr(u8::BITS.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U16, Bits))) => {
            lit_expr(u16::BITS.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U32, Bits))) => {
            lit_expr(u32::BITS.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U64, Bits))) => {
            lit_expr(u64::BITS.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::U128, Bits))) => {
            lit_expr(u128::BITS.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::USize, Bits))) => Some(arch_bits()),

        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I8, Bits))) => {
            lit_expr_i(i8::BITS.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I16, Bits))) => {
            lit_expr_i(i16::BITS.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I32, Bits))) => {
            lit_expr_i(i32::BITS.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I64, Bits))) => {
            lit_expr_i(i64::BITS.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::I128, Bits))) => {
            lit_expr_i(i128::BITS.into())
        }
        Some(IntIntrinsic(RustIntIntrinsicItem(RustIntType::ISize, Bits))) => Some(arch_bits()),

        _ => None,
    }
}
