use air::ast::Ident;
use regex::Regex;
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::def_id::DefId;
use std::{collections::HashMap, sync::Arc};

// The names returned by this are intended exclusively for matching in `get_rust_item`
fn ty_to_stable_string_partial<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: &rustc_middle::ty::Ty<'_>,
) -> Option<String> {
    Some(match ty.kind() {
        TyKind::Bool => format!("bool"),
        TyKind::Char => format!("char"),
        TyKind::Int(t) => format!("{}", t.name_str()),
        TyKind::Uint(t) => format!("{}", t.name_str()),
        TyKind::Float(t) => format!("{}", t.name_str()),
        TyKind::RawPtr(ref ty, ref tm) => format!(
            "*{} {}",
            match tm {
                rustc_ast::Mutability::Mut => "mut",
                rustc_ast::Mutability::Not => "const",
            },
            ty_to_stable_string_partial(tcx, ty)?,
        ),
        TyKind::Ref(_r, ty, mutbl) => format!(
            "&{} {}",
            match mutbl {
                rustc_ast::Mutability::Mut => "mut",
                rustc_ast::Mutability::Not => "const",
            },
            ty_to_stable_string_partial(tcx, ty)?,
        ),
        TyKind::Never => format!("!"),
        TyKind::Tuple(ref tys) => format!(
            "({})",
            tys.iter()
                .map(|ty| ty_to_stable_string_partial(tcx, &ty))
                .collect::<Option<Vec<_>>>()?
                .join(",")
        ),
        TyKind::Param(ref param_ty) => format!("{}", param_ty.name.as_str()),
        TyKind::Adt(def, _substs) => {
            return Some(def_id_to_stable_rust_path(tcx, def.did())?);
        }
        TyKind::Str => format!("str"),
        TyKind::Array(ty, sz) => {
            format!("[{}; {}]", ty_to_stable_string_partial(tcx, &ty)?, sz)
        }
        TyKind::Slice(ty) => format!("[{}]", ty_to_stable_string_partial(tcx, &ty)?),
        _ => return None,
    })
}

/// NOTE: do not use this to determine if something is a well known / rust lang item
/// use verus_items::get_rust_item instead
pub(crate) fn def_id_to_stable_rust_path<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<String> {
    let def_path = tcx.def_path(def_id);
    let mut segments: Vec<String> = Vec::with_capacity(def_path.data.len());
    let crate_name = tcx.crate_name(def_path.krate);
    segments.push(crate_name.to_ident_string());
    let mut one_impl_block_in_path = false;
    for d in def_path.data.iter() {
        use rustc_hir::definitions::DefPathData;
        match &d.data {
            DefPathData::ValueNs(symbol) | DefPathData::TypeNs(symbol) => {
                segments.push(symbol.to_string())
            }
            DefPathData::Ctor => segments.push(vir::def::RUST_DEF_CTOR.to_string()),
            DefPathData::Impl => {
                if one_impl_block_in_path {
                    return None;
                }
                one_impl_block_in_path = true;
                let self_ty = tcx.type_of(tcx.parent(def_id)).skip_binder();
                let path = ty_to_stable_string_partial(tcx, &self_ty)?;
                segments.clear();
                segments.push(path);
            }
            DefPathData::ForeignMod => {
                // this segment can be ignored
            }
            _ => return None,
        }
    }
    Some(segments.join("::"))
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum SpecItem {
    Admit,
    Assume,
    NoMethodBody,
    Requires,
    Recommends,
    Ensures,
    Returns,
    InvariantExceptBreak,
    Invariant,
    Decreases,
    DecreasesWhen,
    DecreasesBy,
    RecommendsBy,
    OpensInvariantsNone,
    OpensInvariantsAny,
    OpensInvariants,
    OpensInvariantsExcept,
    OpensInvariantsSet,
    NoUnwind,
    NoUnwindWhen,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum QuantItem {
    Forall,
    Exists,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum DirectiveItem {
    ExtraDependency,
    RevealHide,
    RevealHideInternalPath,
    RevealStrlit,
    InlineAirStmt,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum ExprItem {
    Choose,
    ChooseTuple,
    Old,
    GetVariantField,
    GetUnionField,
    IsVariant,
    ArrayIndex,
    F32ToBits,
    F64ToBits,
    StrSliceLen,
    StrSliceGetChar,
    StrSliceIsAscii,
    ArchWordBits,
    ClosureToFnSpec,
    ClosureToFnProof,
    SignedMin,
    SignedMax,
    UnsignedMax,
    IsSmallerThan,
    IsSmallerThanLexicographic,
    IsSmallerThanRecursiveFunctionField,
    DefaultEnsures,
    InferSpecForLoopIter,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum CompilableOprItem {
    Implies,
    // SmartPtrNew,
    GhostExec,
    GhostNew,
    TrackedNew,
    TrackedExec,
    TrackedExecBorrow,
    TrackedGet,
    TrackedBorrow,
    TrackedBorrowMut,
    // GhostSplitTuple,
    // TrackedSplitTuple,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum ArithItem {
    BuiltinAdd,
    BuiltinSub,
    BuiltinMul,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum EqualityItem {
    Equal,
    SpecEq,
    ExtEqual,
    ExtEqualDeep,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum SpecOrdItem {
    Le,
    Ge,
    Lt,
    Gt,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum SpecArithItem {
    Add,
    Sub,
    Mul,
    EuclideanOrRealDiv,
    EuclideanMod,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum SpecBitwiseItem {
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum BinaryOpItem {
    Arith(ArithItem),
    Equality(EqualityItem),
    SpecOrd(SpecOrdItem),
    SpecArith(SpecArithItem),
    SpecBitwise(SpecBitwiseItem),
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum ChainedItem {
    Value,
    Le,
    Lt,
    Ge,
    Gt,
    Cmp,
    Eq,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum AssertItem {
    Assert,
    AssertBy,
    AssertByCompute,
    AssertByComputeOnly,
    AssertNonlinearBy,
    AssertBitvectorBy,
    AssertForallBy,
    AssertBitVector,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum SpecLiteralItem {
    Integer,
    Int,
    Nat,
    Decimal,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum SpecGhostTrackedItem {
    GhostView,
    GhostBorrow,
    GhostBorrowMut,
    TrackedView,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum UnaryOpItem {
    SpecLiteral(SpecLiteralItem),
    SpecNeg,
    SpecCastInteger,
    SpecCastReal,
    SpecGhostTracked(SpecGhostTrackedItem),
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum OpenInvariantBlockItem {
    OpenLocalInvariantBegin,
    OpenAtomicInvariantBegin,
    OpenInvariantEnd,
}

#[derive(PartialEq, Eq, Debug, Clone, Hash)]
pub(crate) enum InvariantItem {
    AtomicInvariantNamespace,
    AtomicInvariantInv,
    LocalInvariantNamespace,
    LocalInvariantInv,
    CreateOpenInvariantCredit,
    SpendOpenInvariantCredit,
    SpendOpenInvariantCreditInProof,
}

#[derive(PartialEq, Eq, Debug, Clone, Hash)]
pub(crate) enum SetItem {
    Empty,
    Full,
    Contains,
    SubsetOf,
    Insert,
    Remove,
}

#[derive(PartialEq, Eq, Debug, Clone, Hash)]
pub(crate) enum VstdItem {
    SeqFn(vir::interpreter::SeqFn),
    SetFn(SetItem),
    Invariant(InvariantItem),
    ExecNonstaticCall,
    ProofNonstaticCall,
    ArrayIndexGet,
    ArrayAsSlice,
    ArrayFillForCopyTypes,
    SpecArrayUpdate,
    SliceIndexGet,
    SpecSliceUpdate,
    SpecSliceLen,
    SpecSliceIndex,
    CastPtrToThinPtr,
    CastArrayPtrToSlicePtr,
    CastPtrToUsize,
    VecIndex,
    VecIndexMut,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum MarkerItem {
    Structural,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum BuiltinTypeItem {
    Int,
    Nat,
    Real,
    FnSpec,
    Ghost,
    Tracked,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum BuiltinTraitItem {
    Integer,
    Sealed,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum BuiltinFunctionItem {
    CallRequires,
    CallEnsures,
    ConstrainType,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum GlobalItem {
    SizeOf,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
#[allow(non_camel_case_types)]
pub(crate) enum ExternalItem {
    FnProof,
    FOpts,
    FnProofReq,
    FnProofEns,
    ProofFnOnce,
    ProofFnMut,
    ProofFn,
    Trk,
    RqEn,
}

#[derive(PartialEq, Eq, Debug, Clone, Hash)]
pub(crate) enum VerusItem {
    Spec(SpecItem),
    Quant(QuantItem),
    Directive(DirectiveItem),
    Expr(ExprItem),
    CompilableOpr(CompilableOprItem),
    BinaryOp(BinaryOpItem),
    UnaryOp(UnaryOpItem),
    Chained(ChainedItem),
    Assert(AssertItem),
    UseTypeInvariant,
    WithTriggers,
    OpenInvariantBlock(OpenInvariantBlockItem),
    Vstd(VstdItem, Option<Ident>),
    Marker(MarkerItem),
    BuiltinType(BuiltinTypeItem),
    BuiltinTrait(BuiltinTraitItem),
    BuiltinFunction(BuiltinFunctionItem),
    Global(GlobalItem),
    External(ExternalItem),
    HasResolved,
    HasResolvedUnsized,
    MutRefCurrent,
    MutRefFuture,
    Final,
    AfterBorrow,
    ErasedGhostValue,
    DummyCapture(DummyCaptureItem),
}

#[derive(PartialEq, Eq, Debug, Clone, Hash)]
pub(crate) enum DummyCaptureItem {
    Struct,
    New,
    Consume,
}

#[rustfmt::skip]
fn verus_items_map() -> Vec<(&'static str, VerusItem)> {
    vec![
        ("verus::verus_builtin::admit",                   VerusItem::Spec(SpecItem::Admit)),
        ("verus::verus_builtin::assume_",                 VerusItem::Spec(SpecItem::Assume)),
        ("verus::verus_builtin::no_method_body",          VerusItem::Spec(SpecItem::NoMethodBody)),
        ("verus::verus_builtin::requires",                VerusItem::Spec(SpecItem::Requires)),
        ("verus::verus_builtin::recommends",              VerusItem::Spec(SpecItem::Recommends)),
        ("verus::verus_builtin::ensures",                 VerusItem::Spec(SpecItem::Ensures)),
        ("verus::verus_builtin::returns",                 VerusItem::Spec(SpecItem::Returns)),
        ("verus::verus_builtin::invariant_except_break",  VerusItem::Spec(SpecItem::InvariantExceptBreak)),
        ("verus::verus_builtin::invariant",               VerusItem::Spec(SpecItem::Invariant)),
        ("verus::verus_builtin::decreases",               VerusItem::Spec(SpecItem::Decreases)),
        ("verus::verus_builtin::decreases_when",          VerusItem::Spec(SpecItem::DecreasesWhen)),
        ("verus::verus_builtin::decreases_by",            VerusItem::Spec(SpecItem::DecreasesBy)),
        ("verus::verus_builtin::recommends_by",           VerusItem::Spec(SpecItem::RecommendsBy)),
        ("verus::verus_builtin::opens_invariants_none",   VerusItem::Spec(SpecItem::OpensInvariantsNone)),
        ("verus::verus_builtin::opens_invariants_any",    VerusItem::Spec(SpecItem::OpensInvariantsAny)),
        ("verus::verus_builtin::opens_invariants",        VerusItem::Spec(SpecItem::OpensInvariants)),
        ("verus::verus_builtin::opens_invariants_except", VerusItem::Spec(SpecItem::OpensInvariantsExcept)),
        ("verus::verus_builtin::opens_invariants_set",    VerusItem::Spec(SpecItem::OpensInvariantsSet)),

        ("verus::verus_builtin::no_unwind",               VerusItem::Spec(SpecItem::NoUnwind)),
        ("verus::verus_builtin::no_unwind_when",          VerusItem::Spec(SpecItem::NoUnwindWhen)),

        ("verus::verus_builtin::forall",                  VerusItem::Quant(QuantItem::Forall)),
        ("verus::verus_builtin::exists",                  VerusItem::Quant(QuantItem::Exists)),

        ("verus::verus_builtin::extra_dependency",        VerusItem::Directive(DirectiveItem::ExtraDependency)),
        ("verus::verus_builtin::reveal_hide",             VerusItem::Directive(DirectiveItem::RevealHide)),
        ("verus::verus_builtin::reveal_hide_internal_path", VerusItem::Directive(DirectiveItem::RevealHideInternalPath)),
        ("verus::verus_builtin::reveal_strlit",           VerusItem::Directive(DirectiveItem::RevealStrlit)),
        ("verus::verus_builtin::inline_air_stmt",         VerusItem::Directive(DirectiveItem::InlineAirStmt)),

        ("verus::verus_builtin::choose",                  VerusItem::Expr(ExprItem::Choose)),
        ("verus::verus_builtin::choose_tuple",            VerusItem::Expr(ExprItem::ChooseTuple)),
        ("verus::verus_builtin::old",                     VerusItem::Expr(ExprItem::Old)),
        ("verus::verus_builtin::get_variant_field",       VerusItem::Expr(ExprItem::GetVariantField)),
        ("verus::verus_builtin::get_union_field",         VerusItem::Expr(ExprItem::GetUnionField)),
        ("verus::verus_builtin::is_variant",              VerusItem::Expr(ExprItem::IsVariant)),
        ("verus::verus_builtin::array_index",             VerusItem::Expr(ExprItem::ArrayIndex)),
        ("verus::verus_builtin::f32_to_bits",             VerusItem::Expr(ExprItem::F32ToBits)),
        ("verus::verus_builtin::f64_to_bits",             VerusItem::Expr(ExprItem::F64ToBits)),
        ("verus::verus_builtin::strslice_len",            VerusItem::Expr(ExprItem::StrSliceLen)),
        ("verus::verus_builtin::strslice_get_char",       VerusItem::Expr(ExprItem::StrSliceGetChar)),
        ("verus::verus_builtin::strslice_is_ascii",       VerusItem::Expr(ExprItem::StrSliceIsAscii)),
        ("verus::verus_builtin::arch_word_bits",          VerusItem::Expr(ExprItem::ArchWordBits)),
        ("verus::verus_builtin::closure_to_fn_spec",      VerusItem::Expr(ExprItem::ClosureToFnSpec)),
        ("verus::verus_builtin::closure_to_fn_proof",     VerusItem::Expr(ExprItem::ClosureToFnProof)),
        ("verus::verus_builtin::signed_min",              VerusItem::Expr(ExprItem::SignedMin)),
        ("verus::verus_builtin::signed_max",              VerusItem::Expr(ExprItem::SignedMax)),
        ("verus::verus_builtin::unsigned_max",            VerusItem::Expr(ExprItem::UnsignedMax)),
        ("verus::verus_builtin::is_smaller_than",         VerusItem::Expr(ExprItem::IsSmallerThan)),
        ("verus::verus_builtin::is_smaller_than_lexicographic", VerusItem::Expr(ExprItem::IsSmallerThanLexicographic)),
        ("verus::verus_builtin::is_smaller_than_recursive_function_field", VerusItem::Expr(ExprItem::IsSmallerThanRecursiveFunctionField)),
        ("verus::verus_builtin::default_ensures",         VerusItem::Expr(ExprItem::DefaultEnsures)),
        ("verus::verus_builtin::infer_spec_for_loop_iter", VerusItem::Expr(ExprItem::InferSpecForLoopIter)),

        ("verus::verus_builtin::imply",                   VerusItem::CompilableOpr(CompilableOprItem::Implies)),
        // TODO ("verus::verus_builtin::smartptr_new",    VerusItem::CompilableOpr(CompilableOprItem::SmartPtrNew)),
        ("verus::verus_builtin::ghost_exec",              VerusItem::CompilableOpr(CompilableOprItem::GhostExec)),
        ("verus::verus_builtin::Ghost::new",              VerusItem::CompilableOpr(CompilableOprItem::GhostNew)),
        ("verus::verus_builtin::Tracked::new",            VerusItem::CompilableOpr(CompilableOprItem::TrackedNew)),
        ("verus::verus_builtin::tracked_exec",            VerusItem::CompilableOpr(CompilableOprItem::TrackedExec)),
        ("verus::verus_builtin::tracked_exec_borrow",     VerusItem::CompilableOpr(CompilableOprItem::TrackedExecBorrow)),
        ("verus::verus_builtin::Tracked::get",            VerusItem::CompilableOpr(CompilableOprItem::TrackedGet)),
        ("verus::verus_builtin::Tracked::borrow",         VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrow)),
        ("verus::verus_builtin::Tracked::borrow_mut",     VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrowMut)),

        ("verus::verus_builtin::add",                     VerusItem::BinaryOp(BinaryOpItem::Arith(ArithItem::BuiltinAdd))),
        ("verus::verus_builtin::sub",                     VerusItem::BinaryOp(BinaryOpItem::Arith(ArithItem::BuiltinSub))),
        ("verus::verus_builtin::mul",                     VerusItem::BinaryOp(BinaryOpItem::Arith(ArithItem::BuiltinMul))),

        ("verus::verus_builtin::equal",                   VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::Equal))),
        ("verus::verus_builtin::spec_eq",                 VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::SpecEq))),
        ("verus::verus_builtin::ext_equal",               VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::ExtEqual))),
        ("verus::verus_builtin::ext_equal_deep",          VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::ExtEqualDeep))),

        ("verus::verus_builtin::SpecOrd::spec_le",        VerusItem::BinaryOp(BinaryOpItem::SpecOrd(SpecOrdItem::Le))),
        ("verus::verus_builtin::SpecOrd::spec_ge",        VerusItem::BinaryOp(BinaryOpItem::SpecOrd(SpecOrdItem::Ge))),
        ("verus::verus_builtin::SpecOrd::spec_lt",        VerusItem::BinaryOp(BinaryOpItem::SpecOrd(SpecOrdItem::Lt))),
        ("verus::verus_builtin::SpecOrd::spec_gt",        VerusItem::BinaryOp(BinaryOpItem::SpecOrd(SpecOrdItem::Gt))),

        ("verus::verus_builtin::SpecAdd::spec_add",       VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::Add))),
        ("verus::verus_builtin::SpecSub::spec_sub",       VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::Sub))),
        ("verus::verus_builtin::SpecMul::spec_mul",       VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::Mul))),
        ("verus::verus_builtin::SpecEuclideanOrRealDiv::spec_euclidean_or_real_div", VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::EuclideanOrRealDiv))),
        ("verus::verus_builtin::SpecEuclideanMod::spec_euclidean_mod", VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::EuclideanMod))),

        ("verus::verus_builtin::SpecBitAnd::spec_bitand", VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::BitAnd))),
        ("verus::verus_builtin::SpecBitOr::spec_bitor",   VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::BitOr))),
        ("verus::verus_builtin::SpecBitXor::spec_bitxor", VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::BitXor))),
        ("verus::verus_builtin::SpecShl::spec_shl",       VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::Shl))),
        ("verus::verus_builtin::SpecShr::spec_shr",       VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::Shr))),

        ("verus::verus_builtin::spec_chained_value",      VerusItem::Chained(ChainedItem::Value)),
        ("verus::verus_builtin::spec_chained_le",         VerusItem::Chained(ChainedItem::Le)),
        ("verus::verus_builtin::spec_chained_lt",         VerusItem::Chained(ChainedItem::Lt)),
        ("verus::verus_builtin::spec_chained_ge",         VerusItem::Chained(ChainedItem::Ge)),
        ("verus::verus_builtin::spec_chained_gt",         VerusItem::Chained(ChainedItem::Gt)),
        ("verus::verus_builtin::spec_chained_cmp",        VerusItem::Chained(ChainedItem::Cmp)),
        ("verus::verus_builtin::spec_chained_eq",         VerusItem::Chained(ChainedItem::Eq)),

        ("verus::verus_builtin::assert_",                 VerusItem::Assert(AssertItem::Assert)),
        ("verus::verus_builtin::assert_by",               VerusItem::Assert(AssertItem::AssertBy)),
        ("verus::verus_builtin::assert_by_compute",       VerusItem::Assert(AssertItem::AssertByCompute)),
        ("verus::verus_builtin::assert_by_compute_only",  VerusItem::Assert(AssertItem::AssertByComputeOnly)),
        ("verus::verus_builtin::assert_nonlinear_by",     VerusItem::Assert(AssertItem::AssertNonlinearBy)),
        ("verus::verus_builtin::assert_bitvector_by",     VerusItem::Assert(AssertItem::AssertBitvectorBy)),
        ("verus::verus_builtin::assert_forall_by",        VerusItem::Assert(AssertItem::AssertForallBy)),
        ("verus::verus_builtin::assert_bit_vector",       VerusItem::Assert(AssertItem::AssertBitVector)),
        ("verus::verus_builtin::use_type_invariant",      VerusItem::UseTypeInvariant),

        ("verus::verus_builtin::with_triggers",           VerusItem::WithTriggers),

        ("verus::verus_builtin::spec_literal_integer",    VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(SpecLiteralItem::Integer))),
        ("verus::verus_builtin::spec_literal_int",        VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(SpecLiteralItem::Int))),
        ("verus::verus_builtin::spec_literal_nat",        VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(SpecLiteralItem::Nat))),
        ("verus::verus_builtin::spec_literal_decimal",    VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(SpecLiteralItem::Decimal))),
        ("verus::verus_builtin::SpecNeg::spec_neg",       VerusItem::UnaryOp(UnaryOpItem::SpecNeg)),
        ("verus::verus_builtin::spec_cast_integer",       VerusItem::UnaryOp(UnaryOpItem::SpecCastInteger)),
        ("verus::verus_builtin::spec_cast_real"   ,       VerusItem::UnaryOp(UnaryOpItem::SpecCastReal)),
        ("verus::verus_builtin::Ghost::view",             VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostView))),
        ("verus::verus_builtin::Ghost::borrow",           VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostBorrow))),
        ("verus::verus_builtin::Ghost::borrow_mut",       VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostBorrowMut))),
        ("verus::verus_builtin::Tracked::view",           VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::TrackedView))),

        ("verus::verus_builtin::erased_ghost_value",      VerusItem::ErasedGhostValue),
        ("verus::verus_builtin::DummyCapture",            VerusItem::DummyCapture(DummyCaptureItem::Struct)),
        ("verus::verus_builtin::dummy_capture_new",       VerusItem::DummyCapture(DummyCaptureItem::New)),
        ("verus::verus_builtin::dummy_capture_consume",   VerusItem::DummyCapture(DummyCaptureItem::Consume)),

        ("verus::vstd::invariant::open_atomic_invariant_begin", VerusItem::OpenInvariantBlock(OpenInvariantBlockItem::OpenAtomicInvariantBegin)),
        ("verus::vstd::invariant::open_local_invariant_begin",  VerusItem::OpenInvariantBlock(OpenInvariantBlockItem::OpenLocalInvariantBegin)),
        ("verus::vstd::invariant::open_invariant_end",          VerusItem::OpenInvariantBlock(OpenInvariantBlockItem::OpenInvariantEnd)),

        ("verus::vstd::seq::Seq::empty",       VerusItem::Vstd(VstdItem::SeqFn(vir::interpreter::SeqFn::Empty   ), Some(Arc::new("seq::Seq::empty"      .to_owned())))),
        ("verus::vstd::seq::Seq::new",         VerusItem::Vstd(VstdItem::SeqFn(vir::interpreter::SeqFn::New     ), Some(Arc::new("seq::Seq::new"        .to_owned())))),
        ("verus::vstd::seq::Seq::push",        VerusItem::Vstd(VstdItem::SeqFn(vir::interpreter::SeqFn::Push    ), Some(Arc::new("seq::Seq::push"       .to_owned())))),
        ("verus::vstd::seq::Seq::update",      VerusItem::Vstd(VstdItem::SeqFn(vir::interpreter::SeqFn::Update  ), Some(Arc::new("seq::Seq::update"     .to_owned())))),
        ("verus::vstd::seq::Seq::subrange",    VerusItem::Vstd(VstdItem::SeqFn(vir::interpreter::SeqFn::Subrange), Some(Arc::new("seq::Seq::subrange"   .to_owned())))),
        ("verus::vstd::seq::Seq::add",         VerusItem::Vstd(VstdItem::SeqFn(vir::interpreter::SeqFn::Add     ), Some(Arc::new("seq::Seq::add"        .to_owned())))),
        ("verus::vstd::seq::Seq::len",         VerusItem::Vstd(VstdItem::SeqFn(vir::interpreter::SeqFn::Len     ), Some(Arc::new("seq::Seq::len"        .to_owned())))),
        ("verus::vstd::seq::Seq::index",       VerusItem::Vstd(VstdItem::SeqFn(vir::interpreter::SeqFn::Index   ), Some(Arc::new("seq::Seq::index"      .to_owned())))),
        ("verus::vstd::seq::Seq::ext_equal",   VerusItem::Vstd(VstdItem::SeqFn(vir::interpreter::SeqFn::ExtEqual), Some(Arc::new("seq::Seq::ext_equal"  .to_owned())))),
        ("verus::vstd::seq::Seq::last",        VerusItem::Vstd(VstdItem::SeqFn(vir::interpreter::SeqFn::Last    ), Some(Arc::new("seq::Seq::last"       .to_owned())))),

        ("verus::vstd::set::Set::empty",     VerusItem::Vstd(VstdItem::SetFn(SetItem::Empty),    Some(Arc::new("set::Set::empty".to_owned())))),
        ("verus::vstd::set::Set::full",      VerusItem::Vstd(VstdItem::SetFn(SetItem::Full),     Some(Arc::new("set::Set::full".to_owned())))),
        ("verus::vstd::set::Set::contains",  VerusItem::Vstd(VstdItem::SetFn(SetItem::Contains), Some(Arc::new("set::Set::contains".to_owned())))),
        ("verus::vstd::set::Set::subset_of", VerusItem::Vstd(VstdItem::SetFn(SetItem::SubsetOf), Some(Arc::new("set::Set::subset_of".to_owned())))),
        ("verus::vstd::set::Set::insert",    VerusItem::Vstd(VstdItem::SetFn(SetItem::Insert),   Some(Arc::new("set::Set::insert".to_owned())))),
        ("verus::vstd::set::Set::remove",    VerusItem::Vstd(VstdItem::SetFn(SetItem::Remove),   Some(Arc::new("set::Set::remove".to_owned())))),

        ("verus::vstd::invariant::AtomicInvariant::namespace",           VerusItem::Vstd(VstdItem::Invariant(InvariantItem::AtomicInvariantNamespace       ), Some(Arc::new("invariant::AtomicInvariant::namespace"          .to_owned())))),
        ("verus::vstd::invariant::AtomicInvariant::inv",                 VerusItem::Vstd(VstdItem::Invariant(InvariantItem::AtomicInvariantInv             ), Some(Arc::new("invariant::AtomicInvariant::inv"                .to_owned())))),
        ("verus::vstd::invariant::LocalInvariant::namespace",            VerusItem::Vstd(VstdItem::Invariant(InvariantItem::LocalInvariantNamespace        ), Some(Arc::new("invariant::LocalInvariant::namespace"           .to_owned())))),
        ("verus::vstd::invariant::LocalInvariant::inv",                  VerusItem::Vstd(VstdItem::Invariant(InvariantItem::LocalInvariantInv              ), Some(Arc::new("invariant::LocalInvariant::inv"                 .to_owned())))),
        ("verus::vstd::invariant::create_open_invariant_credit",         VerusItem::Vstd(VstdItem::Invariant(InvariantItem::CreateOpenInvariantCredit      ), Some(Arc::new("invariant::create_open_invariant_credit"        .to_owned())))),
        ("verus::vstd::invariant::spend_open_invariant_credit",          VerusItem::Vstd(VstdItem::Invariant(InvariantItem::SpendOpenInvariantCredit       ), Some(Arc::new("invariant::spend_open_invariant_credit"         .to_owned())))),
        ("verus::vstd::invariant::spend_open_invariant_credit_in_proof", VerusItem::Vstd(VstdItem::Invariant(InvariantItem::SpendOpenInvariantCreditInProof), Some(Arc::new("invariant::spend_open_invariant_credit_in_proof".to_owned())))),
        ("verus::vstd::vstd::exec_nonstatic_call", VerusItem::Vstd(VstdItem::ExecNonstaticCall, Some(Arc::new("pervasive::exec_nonstatic_call".to_owned())))),
        ("verus::vstd::vstd::proof_nonstatic_call", VerusItem::Vstd(VstdItem::ProofNonstaticCall, Some(Arc::new("pervasive::proof_nonstatic_call".to_owned())))),

        ("verus::vstd::std_specs::vec::vec_index", VerusItem::Vstd(VstdItem::VecIndex, Some(Arc::new("std_specs::vec::vec_index".to_owned())))),
        ("verus::vstd::std_specs::vec::vec_index_mut", VerusItem::Vstd(VstdItem::VecIndexMut, Some(Arc::new("std_specs::vec::vec_index_mut".to_owned())))),
        ("verus::vstd::array::array_index_get", VerusItem::Vstd(VstdItem::ArrayIndexGet, Some(Arc::new("array::array_index_get".to_owned())))),
        ("verus::vstd::array::array_as_slice", VerusItem::Vstd(VstdItem::ArrayAsSlice, Some(Arc::new("array::array_as_slice".to_owned())))),
        ("verus::vstd::array::array_fill_for_copy_types", VerusItem::Vstd(VstdItem::ArrayFillForCopyTypes, Some(Arc::new("array::array_fill_for_copy_types".to_owned())))),
        ("verus::vstd::array::spec_array_update", VerusItem::Vstd(VstdItem::SpecArrayUpdate, Some(Arc::new("array::spec_array_update".to_owned())))),
        ("verus::vstd::slice::slice_index_get", VerusItem::Vstd(VstdItem::SliceIndexGet, Some(Arc::new("slice::slice_index_get".to_owned())))),
        ("verus::vstd::slice::spec_slice_update", VerusItem::Vstd(VstdItem::SpecSliceUpdate, Some(Arc::new("slice::spec_slice_update".to_owned())))),
        ("verus::vstd::slice::spec_slice_len", VerusItem::Vstd(VstdItem::SpecSliceLen, Some(Arc::new("slice::spec_slice_len".to_owned())))),
        ("verus::vstd::slice::spec_slice_index", VerusItem::Vstd(VstdItem::SpecSliceIndex, Some(Arc::new("slice::spec_slice_index".to_owned())))),
        ("verus::vstd::raw_ptr::cast_ptr_to_thin_ptr", VerusItem::Vstd(VstdItem::CastPtrToThinPtr, Some(Arc::new("raw_ptr::cast_ptr_to_thin_ptr".to_owned())))),
        ("verus::vstd::raw_ptr::cast_array_ptr_to_slice_ptr", VerusItem::Vstd(VstdItem::CastArrayPtrToSlicePtr, Some(Arc::new("raw_ptr::cast_array_ptr_to_slice_ptr".to_owned())))),
        ("verus::vstd::raw_ptr::cast_ptr_to_usize", VerusItem::Vstd(VstdItem::CastPtrToUsize, Some(Arc::new("raw_ptr::cast_ptr_to_usize".to_owned())))),
            // SeqFn(vir::interpreter::SeqFn::Last    ))),

        ("verus::verus_builtin::Structural",              VerusItem::Marker(MarkerItem::Structural)),

        ("verus::verus_builtin::int",                     VerusItem::BuiltinType(BuiltinTypeItem::Int)),
        ("verus::verus_builtin::nat",                     VerusItem::BuiltinType(BuiltinTypeItem::Nat)),
        ("verus::verus_builtin::real",                    VerusItem::BuiltinType(BuiltinTypeItem::Real)),
        ("verus::verus_builtin::FnSpec",                  VerusItem::BuiltinType(BuiltinTypeItem::FnSpec)),
        ("verus::verus_builtin::Ghost",                   VerusItem::BuiltinType(BuiltinTypeItem::Ghost)),
        ("verus::verus_builtin::Tracked",                 VerusItem::BuiltinType(BuiltinTypeItem::Tracked)),

        ("verus::verus_builtin::Integer",                 VerusItem::BuiltinTrait(BuiltinTraitItem::Integer)),
        ("verus::verus_builtin::private::Sealed",         VerusItem::BuiltinTrait(BuiltinTraitItem::Sealed)),

        ("verus::verus_builtin::call_requires", VerusItem::BuiltinFunction(BuiltinFunctionItem::CallRequires)),
        ("verus::verus_builtin::call_ensures",  VerusItem::BuiltinFunction(BuiltinFunctionItem::CallEnsures)),
        ("verus::verus_builtin::constrain_type",          VerusItem::BuiltinFunction(BuiltinFunctionItem::ConstrainType)),
        
        ("verus::verus_builtin::global_size_of", VerusItem::Global(GlobalItem::SizeOf)),

        ("verus::verus_builtin::FnProof",          VerusItem::External(ExternalItem::FnProof)),
        ("verus::verus_builtin::FOpts",   VerusItem::External(ExternalItem::FOpts)),
        ("verus::verus_builtin::ProofFnReqEnsDef::req", VerusItem::External(ExternalItem::FnProofReq)),
        ("verus::verus_builtin::ProofFnReqEnsDef::ens", VerusItem::External(ExternalItem::FnProofEns)),
        ("verus::verus_builtin::ProofFnOnce",      VerusItem::External(ExternalItem::ProofFnOnce)),
        ("verus::verus_builtin::ProofFnMut",       VerusItem::External(ExternalItem::ProofFnMut)),
        ("verus::verus_builtin::ProofFn",          VerusItem::External(ExternalItem::ProofFn)),
        ("verus::verus_builtin::Trk",              VerusItem::External(ExternalItem::Trk)),
        ("verus::verus_builtin::RqEn",             VerusItem::External(ExternalItem::RqEn)),
        ("verus::verus_builtin::has_resolved",     VerusItem::HasResolved),
        ("verus::verus_builtin::has_resolved_unsized",     VerusItem::HasResolvedUnsized),
        ("verus::verus_builtin::mut_ref_current",  VerusItem::MutRefCurrent),
        ("verus::verus_builtin::mut_ref_future",   VerusItem::MutRefFuture),
        ("verus::verus_builtin::fin",              VerusItem::Final),
        ("verus::verus_builtin::after_borrow",     VerusItem::AfterBorrow),
    ]
}

pub(crate) struct VerusItems {
    pub(crate) id_to_name: HashMap<DefId, VerusItem>,
    pub(crate) name_to_id: HashMap<VerusItem, DefId>,
}

pub(crate) fn from_diagnostic_items(
    diagnostic_items: &rustc_hir::diagnostic_items::DiagnosticItems,
) -> VerusItems {
    let verus_item_map: HashMap<&str, VerusItem> =
        verus_items_map().iter().map(|(k, v)| (*k, v.clone())).collect();
    let diagnostic_name_to_id = &diagnostic_items.name_to_id;
    let mut id_to_name: HashMap<DefId, VerusItem> = HashMap::new();
    let mut name_to_id: HashMap<VerusItem, DefId> = HashMap::new();
    for (name, id) in diagnostic_name_to_id {
        let name = name.as_str();
        if name.starts_with("verus::verus_builtin") || name.starts_with("verus::vstd") {
            if let Some(item) = verus_item_map.get(name) {
                id_to_name.insert(id.clone(), item.clone());
                name_to_id.insert(item.clone(), id.clone());
            } else {
                panic!("unexpected verus diagnostic item {}", name);
            }
        }
    }
    VerusItems { id_to_name, name_to_id }
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub(crate) enum RustIntType {
    U8,
    U16,
    U32,
    U64,
    U128,
    USize,

    I8,
    I16,
    I32,
    I64,
    I128,
    ISize,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub(crate) enum RustIntConst {
    Min,
    Max,
    Bits,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub(crate) struct RustIntIntrinsicItem(pub(crate) RustIntType, pub(crate) RustIntConst);

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub(crate) enum RustItem {
    Panic,
    Box,
    Fn,
    FnOnce,
    FnMut,
    Drop,
    Sized,
    Copy,
    Send,
    Sync,
    Clone,
    StructuralPartialEq,
    Eq,
    PartialEq,
    Ord,
    PartialOrd,
    Hash,
    Default,
    Debug,
    Rc,
    Arc,
    BoxNew,
    ArcNew,
    RcNew,
    CloneClone,
    CloneFrom,
    IntIntrinsic(RustIntIntrinsicItem),
    AllocGlobal,
    Allocator,
    TryTraitBranch,
    ResidualTraitFromResidual,
    IntoIterFn,
    ManuallyDrop,
    PhantomData,
    Destruct,
    SliceSealed,
    Vec,
}

pub(crate) fn get_rust_item<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<RustItem> {
    // if tcx.parent(def_id) == partial_eq {
    if tcx.lang_items().panic_fn() == Some(def_id) {
        return Some(RustItem::Panic);
    }
    if tcx.lang_items().owned_box() == Some(def_id) {
        return Some(RustItem::Box);
    }
    if tcx.lang_items().fn_trait() == Some(def_id) {
        return Some(RustItem::Fn);
    }
    if tcx.lang_items().fn_mut_trait() == Some(def_id) {
        return Some(RustItem::FnMut);
    }
    if tcx.lang_items().fn_once_trait() == Some(def_id) {
        return Some(RustItem::FnOnce);
    }
    if tcx.lang_items().drop_trait() == Some(def_id) {
        return Some(RustItem::Drop);
    }
    if tcx.lang_items().structural_peq_trait() == Some(def_id) {
        return Some(RustItem::StructuralPartialEq);
    }
    if tcx.lang_items().eq_trait() == Some(def_id) {
        return Some(RustItem::PartialEq);
    }
    if tcx.lang_items().branch_fn() == Some(def_id) {
        return Some(RustItem::TryTraitBranch);
    }
    if tcx.lang_items().from_residual_fn() == Some(def_id) {
        return Some(RustItem::ResidualTraitFromResidual);
    }
    if tcx.lang_items().into_iter_fn() == Some(def_id) {
        return Some(RustItem::IntoIterFn);
    }
    if tcx.lang_items().manually_drop() == Some(def_id) {
        return Some(RustItem::ManuallyDrop);
    }
    if tcx.lang_items().phantom_data() == Some(def_id) {
        return Some(RustItem::PhantomData);
    }
    if tcx.lang_items().destruct_trait() == Some(def_id) {
        return Some(RustItem::Destruct);
    }
    if tcx.lang_items().partial_ord_trait() == Some(def_id) {
        return Some(RustItem::PartialOrd);
    }
    let rust_path = def_id_to_stable_rust_path(tcx, def_id);
    let rust_path = rust_path.as_ref().map(|x| x.as_str());
    get_rust_item_str(rust_path)
}

#[allow(dead_code)]
pub(crate) fn get_rust_item_path(rust_path: &vir::ast::Path) -> Option<RustItem> {
    get_rust_item_str(Some(&vir::ast_util::path_as_friendly_rust_name(rust_path)))
}

pub(crate) fn get_rust_item_str(rust_path: Option<&str>) -> Option<RustItem> {
    // We could use rust's diagnostic_items for these, but they are only defined when cfg(not(test))
    // and they may get changed without us noticing, so we are using paths instead
    if rust_path == Some("core::cmp::Eq") {
        return Some(RustItem::Eq);
    }
    if rust_path == Some("alloc::rc::Rc") {
        return Some(RustItem::Rc);
    }
    if rust_path == Some("alloc::sync::Arc") {
        return Some(RustItem::Arc);
    }

    if rust_path == Some("alloc::boxed::Box::new") {
        return Some(RustItem::BoxNew);
    }
    if rust_path == Some("alloc::sync::Arc::new") {
        return Some(RustItem::ArcNew);
    }
    if rust_path == Some("alloc::rc::Rc::new") {
        return Some(RustItem::RcNew);
    }

    if rust_path == Some("core::marker::Sized") {
        return Some(RustItem::Sized);
    }
    if rust_path == Some("core::marker::Send") {
        return Some(RustItem::Send);
    }
    if rust_path == Some("core::marker::Sync") {
        return Some(RustItem::Sync);
    }
    if rust_path == Some("core::marker::Copy") {
        return Some(RustItem::Copy);
    }
    if rust_path == Some("core::clone::Clone") {
        return Some(RustItem::Clone);
    }
    if rust_path == Some("core::clone::Clone::clone") {
        return Some(RustItem::CloneClone);
    }
    if rust_path == Some("core::clone::Clone::clone_from") {
        return Some(RustItem::CloneFrom);
    }

    if rust_path == Some("alloc::alloc::Global") {
        return Some(RustItem::AllocGlobal);
    }
    if rust_path == Some("core::alloc::Allocator") {
        return Some(RustItem::Allocator);
    }
    if rust_path == Some("core::slice::index::private_slice_index::Sealed") {
        return Some(RustItem::SliceSealed);
    }
    if rust_path == Some("core::fmt::Debug") {
        return Some(RustItem::Debug);
    }
    if rust_path == Some("core::hash::Hash") {
        return Some(RustItem::Hash);
    }
    if rust_path == Some("core::default::Default") {
        return Some(RustItem::Default);
    }
    if rust_path == Some("core::cmp::Ord") {
        return Some(RustItem::Ord);
    }
    if rust_path == Some("alloc::vec::Vec") {
        return Some(RustItem::Vec);
    }

    if let Some(rust_path) = rust_path {
        static NUM_RE: std::sync::OnceLock<Regex> = std::sync::OnceLock::new();
        let num_re =
            NUM_RE.get_or_init(|| Regex::new(r"^([A-Za-z0-9_]+)::(MIN|MAX|BITS)").unwrap());
        if let Some(captures) = num_re.captures(rust_path) {
            let ty_name = captures.get(1).expect("invalid int intrinsic regex");
            let const_name = captures.get(2).expect("invalid int intrinsic regex");
            use RustIntType::*;
            let ty = match ty_name.as_str() {
                "u8" => Some(U8),
                "u16" => Some(U16),
                "u32" => Some(U32),
                "u64" => Some(U64),
                "u128" => Some(U128),
                "usize" => Some(USize),

                "i8" => Some(I8),
                "i16" => Some(I16),
                "i32" => Some(I32),
                "i64" => Some(I64),
                "i128" => Some(I128),
                "isize" => Some(ISize),

                _ => None,
            };
            return ty.map(|ty| {
                let const_ = match const_name.as_str() {
                    "MIN" => RustIntConst::Min,
                    "MAX" => RustIntConst::Max,
                    "BITS" => RustIntConst::Bits,

                    _ => panic!("unexpected int const"),
                };
                RustItem::IntIntrinsic(RustIntIntrinsicItem(ty, const_))
            });
        }
    }

    None
}
