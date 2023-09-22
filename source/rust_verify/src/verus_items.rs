use air::ast::Ident;
use regex::Regex;
use rustc_middle::ty::{DefIdTree, TyCtxt, TyKind};
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
        TyKind::RawPtr(ref tm) => format!(
            "*{} {}",
            match tm.mutbl {
                rustc_ast::Mutability::Mut => "mut",
                rustc_ast::Mutability::Not => "const",
            },
            ty_to_stable_string_partial(tcx, &tm.ty)?,
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
    Invariant,
    InvariantEnsures,
    Decreases,
    DecreasesWhen,
    DecreasesBy,
    RecommendsBy,
    OpensInvariantsNone,
    OpensInvariantsAny,
    OpensInvariants,
    OpensInvariantsExcept,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum QuantItem {
    Forall,
    ForallArith,
    Exists,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum DirectiveItem {
    ExtraDependency,
    RevealHide,
    RevealHideInternalPath,
    RevealStrlit,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum ExprItem {
    Choose,
    ChooseTuple,
    Old,
    GetVariantField,
    IsVariant,
    StrSliceLen,
    StrSliceGetChar,
    StrSliceIsAscii,
    ArchWordBits,
    ClosureToFnSpec,
    SignedMin,
    SignedMax,
    UnsignedMax,
    IsSmallerThan,
    IsSmallerThanLexicographic,
    IsSmallerThanRecursiveFunctionField,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum CompilableOprItem {
    Implies,
    // SmartPtrNew,
    NewStrLit,
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
    EuclideanDiv,
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
}

#[derive(PartialEq, Eq, Debug, Clone, Hash)]
pub(crate) enum PervasiveItem {
    StrSlice,
    SeqFn(vir::interpreter::SeqFn),
    Invariant(InvariantItem),
    ExecNonstaticCall,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum MarkerItem {
    Structural,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum BuiltinTypeItem {
    Int,
    Nat,
    FnSpec,
    Ghost,
    Tracked,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum BuiltinFunctionItem {
    FnWithSpecificationRequires,
    FnWithSpecificationEnsures,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub(crate) enum BuiltinTraitItem {
    FnWithSpecification,
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
    WithTriggers,
    OpenInvariantBlock(OpenInvariantBlockItem),
    Pervasive(PervasiveItem, Option<Ident>),
    Marker(MarkerItem),
    BuiltinType(BuiltinTypeItem),
    BuiltinFunction(BuiltinFunctionItem),
    BuiltinTrait(BuiltinTraitItem),
}

#[rustfmt::skip]
fn verus_items_map() -> Vec<(&'static str, VerusItem)> {
    vec![
        ("verus::builtin::admit",                   VerusItem::Spec(SpecItem::Admit)),
        ("verus::builtin::assume_",                 VerusItem::Spec(SpecItem::Assume)),
        ("verus::builtin::no_method_body",          VerusItem::Spec(SpecItem::NoMethodBody)),
        ("verus::builtin::requires",                VerusItem::Spec(SpecItem::Requires)),
        ("verus::builtin::recommends",              VerusItem::Spec(SpecItem::Recommends)),
        ("verus::builtin::ensures",                 VerusItem::Spec(SpecItem::Ensures)),
        ("verus::builtin::invariant",               VerusItem::Spec(SpecItem::Invariant)),
        ("verus::builtin::invariant_ensures",       VerusItem::Spec(SpecItem::InvariantEnsures)),
        ("verus::builtin::decreases",               VerusItem::Spec(SpecItem::Decreases)),
        ("verus::builtin::decreases_when",          VerusItem::Spec(SpecItem::DecreasesWhen)),
        ("verus::builtin::decreases_by",            VerusItem::Spec(SpecItem::DecreasesBy)),
        ("verus::builtin::recommends_by",           VerusItem::Spec(SpecItem::RecommendsBy)),
        ("verus::builtin::opens_invariants_none",   VerusItem::Spec(SpecItem::OpensInvariantsNone)),
        ("verus::builtin::opens_invariants_any",    VerusItem::Spec(SpecItem::OpensInvariantsAny)),
        ("verus::builtin::opens_invariants",        VerusItem::Spec(SpecItem::OpensInvariants)),
        ("verus::builtin::opens_invariants_except", VerusItem::Spec(SpecItem::OpensInvariantsExcept)),

        ("verus::builtin::forall",                  VerusItem::Quant(QuantItem::Forall)),
        ("verus::builtin::exists",                  VerusItem::Quant(QuantItem::Exists)),
        ("verus::builtin::forall_arith",            VerusItem::Quant(QuantItem::ForallArith)),

        ("verus::builtin::extra_dependency",        VerusItem::Directive(DirectiveItem::ExtraDependency)),
        ("verus::builtin::reveal_hide",             VerusItem::Directive(DirectiveItem::RevealHide)),
        ("verus::builtin::reveal_hide_internal_path", VerusItem::Directive(DirectiveItem::RevealHideInternalPath)),
        ("verus::builtin::reveal_strlit",           VerusItem::Directive(DirectiveItem::RevealStrlit)),

        ("verus::builtin::choose",                  VerusItem::Expr(ExprItem::Choose)),
        ("verus::builtin::choose_tuple",            VerusItem::Expr(ExprItem::ChooseTuple)),
        ("verus::builtin::old",                     VerusItem::Expr(ExprItem::Old)),
        ("verus::builtin::get_variant_field",       VerusItem::Expr(ExprItem::GetVariantField)),
        ("verus::builtin::is_variant",              VerusItem::Expr(ExprItem::IsVariant)),
        ("verus::builtin::strslice_len",            VerusItem::Expr(ExprItem::StrSliceLen)),
        ("verus::builtin::strslice_get_char",       VerusItem::Expr(ExprItem::StrSliceGetChar)),
        ("verus::builtin::strslice_is_ascii",       VerusItem::Expr(ExprItem::StrSliceIsAscii)),
        ("verus::builtin::arch_word_bits",          VerusItem::Expr(ExprItem::ArchWordBits)),
        ("verus::builtin::closure_to_fn_spec",      VerusItem::Expr(ExprItem::ClosureToFnSpec)),
        ("verus::builtin::signed_min",              VerusItem::Expr(ExprItem::SignedMin)),
        ("verus::builtin::signed_max",              VerusItem::Expr(ExprItem::SignedMax)),
        ("verus::builtin::unsigned_max",            VerusItem::Expr(ExprItem::UnsignedMax)),
        ("verus::builtin::is_smaller_than",         VerusItem::Expr(ExprItem::IsSmallerThan)),
        ("verus::builtin::is_smaller_than_lexicographic", VerusItem::Expr(ExprItem::IsSmallerThanLexicographic)),
        ("verus::builtin::is_smaller_than_recursive_function_field", VerusItem::Expr(ExprItem::IsSmallerThanRecursiveFunctionField)),

        ("verus::builtin::imply",                   VerusItem::CompilableOpr(CompilableOprItem::Implies)),
        // TODO ("verus::builtin::smartptr_new",    VerusItem::CompilableOpr(CompilableOprItem::SmartPtrNew)),
        // TODO: replace with builtin:
        ("verus::pervasive::string::new_strlit",    VerusItem::CompilableOpr(CompilableOprItem::NewStrLit)),
        ("verus::builtin::ghost_exec",              VerusItem::CompilableOpr(CompilableOprItem::GhostExec)),
        ("verus::builtin::Ghost::new",              VerusItem::CompilableOpr(CompilableOprItem::GhostNew)),
        ("verus::builtin::Tracked::new",            VerusItem::CompilableOpr(CompilableOprItem::TrackedNew)),
        ("verus::builtin::tracked_exec",            VerusItem::CompilableOpr(CompilableOprItem::TrackedExec)),
        ("verus::builtin::tracked_exec_borrow",     VerusItem::CompilableOpr(CompilableOprItem::TrackedExecBorrow)),
        ("verus::builtin::Tracked::get",            VerusItem::CompilableOpr(CompilableOprItem::TrackedGet)),
        ("verus::builtin::Tracked::borrow",         VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrow)),
        ("verus::builtin::Tracked::borrow_mut",     VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrowMut)),

        ("verus::builtin::add",                     VerusItem::BinaryOp(BinaryOpItem::Arith(ArithItem::BuiltinAdd))),
        ("verus::builtin::sub",                     VerusItem::BinaryOp(BinaryOpItem::Arith(ArithItem::BuiltinSub))),
        ("verus::builtin::mul",                     VerusItem::BinaryOp(BinaryOpItem::Arith(ArithItem::BuiltinMul))),

        ("verus::builtin::equal",                   VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::Equal))),
        ("verus::builtin::spec_eq",                 VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::SpecEq))),
        ("verus::builtin::ext_equal",               VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::ExtEqual))),
        ("verus::builtin::ext_equal_deep",          VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::ExtEqualDeep))),

        ("verus::builtin::SpecOrd::spec_le",        VerusItem::BinaryOp(BinaryOpItem::SpecOrd(SpecOrdItem::Le))),
        ("verus::builtin::SpecOrd::spec_ge",        VerusItem::BinaryOp(BinaryOpItem::SpecOrd(SpecOrdItem::Ge))),
        ("verus::builtin::SpecOrd::spec_lt",        VerusItem::BinaryOp(BinaryOpItem::SpecOrd(SpecOrdItem::Lt))),
        ("verus::builtin::SpecOrd::spec_gt",        VerusItem::BinaryOp(BinaryOpItem::SpecOrd(SpecOrdItem::Gt))),

        ("verus::builtin::SpecAdd::spec_add",       VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::Add))),
        ("verus::builtin::SpecSub::spec_sub",       VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::Sub))),
        ("verus::builtin::SpecMul::spec_mul",       VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::Mul))),
        ("verus::builtin::SpecEuclideanDiv::spec_euclidean_div", VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::EuclideanDiv))),
        ("verus::builtin::SpecEuclideanMod::spec_euclidean_mod", VerusItem::BinaryOp(BinaryOpItem::SpecArith(SpecArithItem::EuclideanMod))),

        ("verus::builtin::SpecBitAnd::spec_bitand", VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::BitAnd))),
        ("verus::builtin::SpecBitOr::spec_bitor",   VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::BitOr))),
        ("verus::builtin::SpecBitXor::spec_bitxor", VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::BitXor))),
        ("verus::builtin::SpecShl::spec_shl",       VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::Shl))),
        ("verus::builtin::SpecShr::spec_shr",       VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(SpecBitwiseItem::Shr))),

        ("verus::builtin::spec_chained_value",      VerusItem::Chained(ChainedItem::Value)),
        ("verus::builtin::spec_chained_le",         VerusItem::Chained(ChainedItem::Le)),
        ("verus::builtin::spec_chained_lt",         VerusItem::Chained(ChainedItem::Lt)),
        ("verus::builtin::spec_chained_ge",         VerusItem::Chained(ChainedItem::Ge)),
        ("verus::builtin::spec_chained_gt",         VerusItem::Chained(ChainedItem::Gt)),
        ("verus::builtin::spec_chained_cmp",        VerusItem::Chained(ChainedItem::Cmp)),
        ("verus::builtin::spec_chained_eq",         VerusItem::Chained(ChainedItem::Eq)),

        ("verus::builtin::assert_",                 VerusItem::Assert(AssertItem::Assert)),
        ("verus::builtin::assert_by",               VerusItem::Assert(AssertItem::AssertBy)),
        ("verus::builtin::assert_by_compute",       VerusItem::Assert(AssertItem::AssertByCompute)),
        ("verus::builtin::assert_by_compute_only",  VerusItem::Assert(AssertItem::AssertByComputeOnly)),
        ("verus::builtin::assert_nonlinear_by",     VerusItem::Assert(AssertItem::AssertNonlinearBy)),
        ("verus::builtin::assert_bitvector_by",     VerusItem::Assert(AssertItem::AssertBitvectorBy)),
        ("verus::builtin::assert_forall_by",        VerusItem::Assert(AssertItem::AssertForallBy)),
        ("verus::builtin::assert_bit_vector",       VerusItem::Assert(AssertItem::AssertBitVector)),

        ("verus::builtin::with_triggers",           VerusItem::WithTriggers),

        ("verus::builtin::spec_literal_integer",    VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(SpecLiteralItem::Integer))),
        ("verus::builtin::spec_literal_int",        VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(SpecLiteralItem::Int))),
        ("verus::builtin::spec_literal_nat",        VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(SpecLiteralItem::Nat))),
        ("verus::builtin::SpecNeg::spec_neg",       VerusItem::UnaryOp(UnaryOpItem::SpecNeg)),
        ("verus::builtin::spec_cast_integer",       VerusItem::UnaryOp(UnaryOpItem::SpecCastInteger)),
        ("verus::builtin::Ghost::view",             VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostView))),
        ("verus::builtin::Ghost::borrow",           VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostBorrow))),
        ("verus::builtin::Ghost::borrow_mut",       VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostBorrowMut))),
        ("verus::builtin::Tracked::view",           VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::TrackedView))),

        ("verus::pervasive::invariant::open_atomic_invariant_begin", VerusItem::OpenInvariantBlock(OpenInvariantBlockItem::OpenAtomicInvariantBegin)),
        ("verus::pervasive::invariant::open_local_invariant_begin",  VerusItem::OpenInvariantBlock(OpenInvariantBlockItem::OpenLocalInvariantBegin)),
        ("verus::pervasive::invariant::open_invariant_end",          VerusItem::OpenInvariantBlock(OpenInvariantBlockItem::OpenInvariantEnd)),

        ("verus::pervasive::string::StrSlice",      VerusItem::Pervasive(PervasiveItem::StrSlice, None)),
        ("verus::pervasive::seq::Seq::empty",       VerusItem::Pervasive(PervasiveItem::SeqFn(vir::interpreter::SeqFn::Empty   ), Some(Arc::new("seq::Seq::empty"      .to_owned())))),
        ("verus::pervasive::seq::Seq::new",         VerusItem::Pervasive(PervasiveItem::SeqFn(vir::interpreter::SeqFn::New     ), Some(Arc::new("seq::Seq::new"        .to_owned())))),
        ("verus::pervasive::seq::Seq::push",        VerusItem::Pervasive(PervasiveItem::SeqFn(vir::interpreter::SeqFn::Push    ), Some(Arc::new("seq::Seq::push"       .to_owned())))),
        ("verus::pervasive::seq::Seq::update",      VerusItem::Pervasive(PervasiveItem::SeqFn(vir::interpreter::SeqFn::Update  ), Some(Arc::new("seq::Seq::update"     .to_owned())))),
        ("verus::pervasive::seq::Seq::subrange",    VerusItem::Pervasive(PervasiveItem::SeqFn(vir::interpreter::SeqFn::Subrange), Some(Arc::new("seq::Seq::subrange"   .to_owned())))),
        ("verus::pervasive::seq::Seq::add",         VerusItem::Pervasive(PervasiveItem::SeqFn(vir::interpreter::SeqFn::Add     ), Some(Arc::new("seq::Seq::add"        .to_owned())))),
        ("verus::pervasive::seq::Seq::len",         VerusItem::Pervasive(PervasiveItem::SeqFn(vir::interpreter::SeqFn::Len     ), Some(Arc::new("seq::Seq::len"        .to_owned())))),
        ("verus::pervasive::seq::Seq::index",       VerusItem::Pervasive(PervasiveItem::SeqFn(vir::interpreter::SeqFn::Index   ), Some(Arc::new("seq::Seq::index"      .to_owned())))),
        ("verus::pervasive::seq::Seq::ext_equal",   VerusItem::Pervasive(PervasiveItem::SeqFn(vir::interpreter::SeqFn::ExtEqual), Some(Arc::new("seq::Seq::ext_equal"  .to_owned())))),
        ("verus::pervasive::seq::Seq::last",        VerusItem::Pervasive(PervasiveItem::SeqFn(vir::interpreter::SeqFn::Last    ), Some(Arc::new("seq::Seq::last"       .to_owned())))),
        ("verus::pervasive::invariant::AtomicInvariant::namespace", VerusItem::Pervasive(PervasiveItem::Invariant(InvariantItem::AtomicInvariantNamespace  ), Some(Arc::new("invariant::AtomicInvariant::namespace" .to_owned())))),
        ("verus::pervasive::invariant::AtomicInvariant::inv",       VerusItem::Pervasive(PervasiveItem::Invariant(InvariantItem::AtomicInvariantInv        ), Some(Arc::new("invariant::AtomicInvariant::inv"       .to_owned())))),
        ("verus::pervasive::invariant::LocalInvariant::namespace",  VerusItem::Pervasive(PervasiveItem::Invariant(InvariantItem::LocalInvariantNamespace   ), Some(Arc::new("invariant::LocalInvariant::namespace" .to_owned())))),
        ("verus::pervasive::invariant::LocalInvariant::inv",        VerusItem::Pervasive(PervasiveItem::Invariant(InvariantItem::LocalInvariantInv         ), Some(Arc::new("invariant::LocalInvariant::inv"       .to_owned())))),
        ("verus::pervasive::pervasive::exec_nonstatic_call", VerusItem::Pervasive(PervasiveItem::ExecNonstaticCall, Some(Arc::new("pervasive::exec_nonstatic_call".to_owned())))),
            // SeqFn(vir::interpreter::SeqFn::Last    ))),

        ("verus::builtin::Structural",              VerusItem::Marker(MarkerItem::Structural)),

        ("verus::builtin::int",                     VerusItem::BuiltinType(BuiltinTypeItem::Int)),
        ("verus::builtin::nat",                     VerusItem::BuiltinType(BuiltinTypeItem::Nat)),
        ("verus::builtin::FnSpec",                  VerusItem::BuiltinType(BuiltinTypeItem::FnSpec)),
        ("verus::builtin::Ghost",                   VerusItem::BuiltinType(BuiltinTypeItem::Ghost)),
        ("verus::builtin::Tracked",                 VerusItem::BuiltinType(BuiltinTypeItem::Tracked)),

        ("verus::builtin::FnWithSpecification::requires", VerusItem::BuiltinFunction(BuiltinFunctionItem::FnWithSpecificationRequires)),
        ("verus::builtin::FnWithSpecification::ensures",  VerusItem::BuiltinFunction(BuiltinFunctionItem::FnWithSpecificationEnsures)),

        ("verus::builtin::FnWithSpecification", VerusItem::BuiltinTrait(BuiltinTraitItem::FnWithSpecification)),
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
        if name.starts_with("verus::builtin") || name.starts_with("verus::pervasive") {
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
    StructuralEq,
    StructuralPartialEq,
    Eq,
    PartialEq,
    Rc,
    Arc,
    BoxNew,
    ArcNew,
    RcNew,
    Clone,
    IntIntrinsic(RustIntIntrinsicItem),
    AllocGlobal,
    TryTraitBranch,
    IntoIterFn,
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
    if tcx.lang_items().structural_teq_trait() == Some(def_id) {
        return Some(RustItem::StructuralEq);
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
    if tcx.lang_items().into_iter_fn() == Some(def_id) {
        return Some(RustItem::IntoIterFn);
    }

    let rust_path = def_id_to_stable_rust_path(tcx, def_id);
    let rust_path = rust_path.as_ref().map(|x| x.as_str());

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

    if rust_path == Some("core::clone::Clone::clone") {
        return Some(RustItem::Clone);
    }

    if rust_path == Some("alloc::alloc::Global") {
        return Some(RustItem::AllocGlobal);
    }

    if let Some(rust_path) = rust_path {
        let num_re = Regex::new(r"^([A-Za-z0-9_]+)::(MIN|MAX|BITS)").unwrap();
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
