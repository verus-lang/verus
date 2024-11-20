use rustc_infer::infer::InferCtxt;
use crate::rustc_infer::infer::TyCtxtInferExt;
use super::constraints::Info;
use rustc_span::Span;
use super::State;
use vir::ast::{Typ, TypX, Dt, Typs, TypDecoration, Primitive};
use std::collections::HashMap;
use rustc_middle::ty::{Ty, GenericArg, TyKind, AssocKind, AliasKind, AliasTy, UintTy, IntTy, InferTy, Term, TermKind, GenericParamDefKind, Const, ConstKind, ValTree, ScalarInt, ClauseKind};
use num_bigint::BigInt;
use rustc_middle::ty::GenericArgs;
use std::sync::Arc;
use vir::ast::IntRange;
use rustc_middle::ty::TyVid;
use super::unification_table::NodeClass;
use crate::verus_items::{VerusItem, BuiltinTypeItem};
use crate::rustc_middle::ty::new::Region;
use num_traits::cast::ToPrimitive;

// Functions to turn a VIR Typ into a rustc_middle::ty::Ty.
// This is needed for cases where we want to call into rustc machinery, e.g.,
// to solve traits or do method probing.
//
// Some of the functions here are only for finalized types (no inference vars)
// and some support inference vars. For the latter case, we handle an inference var
// as follows:
//
//  - If it's in the Known state, use the known type.
//  - Anything else, we translate it to an inference variable in the rustc InferCtxt.

struct ReverseTypeState<'tcx> {
    span: Span,
    id_map: HashMap<NodeClass, rustc_middle::ty::Ty<'tcx>>,
    infcx: InferCtxt<'tcx>,
}

impl<'a, 'tcx> State<'a, 'tcx> {
    pub fn finalized_vir_typs_to_generic_args(&self, typs: &Typs)
        -> &'tcx GenericArgs<'tcx>
    {
        let mut mid_args: Vec<GenericArg<'_>> = vec![];
        for t in typs.iter() {
            mid_args.push(GenericArg::from(self.vir_ty_to_middle_rec(&mut None, t)));
        }
        self.tcx.mk_args(&mid_args)
    }

    pub fn finalized_vir_typ_to_term(&self, typ: &Typ) -> Term<'tcx>
    {
        self.vir_ty_to_middle_rec(&mut None, typ)
    }

    pub fn vir_ty_to_middle(&self, span: Span, t: &Typ)
        -> (Term<'tcx>, InferCtxt<'tcx>)
    {
        let infcx = self.tcx.infer_ctxt().ignoring_regions().build();
        let mut r = Some(ReverseTypeState { infcx: infcx, span, id_map: HashMap::new() });
        let term = self.vir_ty_to_middle_rec(&mut r, t);
        (term, r.unwrap().infcx)
    }

    pub fn vir_typs_to_middle_args(&self, span: Span, typs: &Typs)
        -> (Vec<GenericArg<'tcx>>, InferCtxt<'tcx>, HashMap<TyVid, usize>)
    {
        let infcx = self.tcx.infer_ctxt().ignoring_regions().build();
        let mut r = Some(ReverseTypeState { infcx: infcx, span, id_map: HashMap::new() });
        let mut mid_args: Vec<GenericArg<'_>> = vec![];
        for typ in typs.iter() {
            let ty = self.vir_ty_to_middle_rec(&mut r, typ);
            mid_args.push(GenericArg::from(ty));
        }

        let r = r.unwrap();

        let mut h = HashMap::<TyVid, usize>::new();
        for (our_uid, rust_ty) in r.id_map.iter() {
            match rust_ty.kind() {
                TyKind::Infer(InferTy::TyVar(rust_ty_vid)) => {
                    h.insert(*rust_ty_vid, our_uid.0);
                }
                _ => unreachable!()
            }
        }

        (mid_args, r.infcx, h)
    }


    // TODO overflow checking
    fn vir_ty_to_middle_rec(&self, r: &mut Option<ReverseTypeState<'tcx>>, t: &Typ) -> Term<'tcx> {
        let tcx = self.tcx;
        match &**t {
            TypX::Datatype(Dt::Path(path), args, _) => {
                let def_id = crate::rust_to_vir_base::def_id_of_vir_path(path);
                let adt_def = tcx.adt_def(def_id);
                let mut mid_args: Vec<GenericArg<'_>> = vec![];
                for a in args.iter() {
                    mid_args.push(GenericArg::from(self.vir_ty_to_middle_rec(r, a)));
                }
                let args = self.tcx.mk_args(&mid_args);
                Term::from(tcx.mk_ty_from_kind(TyKind::Adt(adt_def, args)))
            }
            TypX::Primitive(Primitive::Array, args) => {
                assert!(args.len() == 2);
                let typ = self.vir_ty_to_middle_rec(r, &args[0]);
                let len = self.vir_ty_to_middle_rec(r, &args[1]);
                Term::from(tcx.mk_ty_from_kind(TyKind::Array(
                    expect_ty(typ),
                    expect_const(len),
                )))
            }
            TypX::Primitive(Primitive::Global, args) => {
                assert!(args.len() == 0);
                let p = vir::path!("alloc" => "alloc", "Global");
                let def_id = crate::rust_to_vir_base::def_id_of_vir_path(&p);
                let adt_def = tcx.adt_def(def_id);
                let args = self.tcx.mk_args(&[]);
                Term::from(tcx.mk_ty_from_kind(TyKind::Adt(adt_def, args)))
            }
            TypX::Decorate(TypDecoration::Ref, None, typ) => {
                Term::from(tcx.mk_ty_from_kind(TyKind::Ref(
                    Region::new_static(self.tcx),
                    expect_ty(self.vir_ty_to_middle_rec(r, typ)),
                    rustc_ast::Mutability::Not)))
            }
            TypX::Decorate(TypDecoration::Ghost, None, typ) => {
                self.adt_from_verus_item_1_arg(
                    VerusItem::BuiltinType(BuiltinTypeItem::Ghost),
                    expect_ty(self.vir_ty_to_middle_rec(r, typ)))
            }
            TypX::TypParam(t) => {
                *self.param_name_to_param_ty.get(t).unwrap()
            }
            TypX::ConstInt(i, int_range) => {
                let scalar = self.int_to_value_tree(i, *int_range);
                Term::from(Const::new(self.tcx,
                    ConstKind::Value(ValTree::Leaf(scalar)),
                    expect_ty(self.vir_ty_to_middle_rec(r, &Arc::new(TypX::Int(*int_range)))),
                ))
            }
            TypX::UnificationVar(i) => {
                let rstate: &mut ReverseTypeState<'tcx> = r.as_mut().unwrap();
                let node = self.unifier.get_class(*i);
                if let Info::Known(t) = &self.unifier[node].info {
                    self.vir_ty_to_middle_rec(r, t)
                } else {
                    if rstate.id_map.contains_key(&node) {
                        Term::from(rstate.id_map[&node])
                    } else {
                        let ty = rstate.infcx.next_ty_var(rustc_infer::infer::type_variable::TypeVariableOrigin { span: rstate.span, param_def_id: None });
                        rstate.id_map.insert(node, ty);
                        Term::from(ty)
                    }
                }
            }
            TypX::Projection { trait_typ_args, trait_path, name } => {
                let trait_def_id = crate::rust_to_vir_base::def_id_of_vir_path(trait_path);
                let mut mid_args: Vec<GenericArg<'_>> = vec![];
                for a in trait_typ_args.iter() {
                    mid_args.push(GenericArg::from(self.vir_ty_to_middle_rec(r, a)));
                }
                let assoc_item = self.tcx.associated_items(trait_def_id)
                      .find_by_name_and_kinds(self.tcx, rustc_span::symbol::Ident::from_str(&name),
                        &[AssocKind::Type], trait_def_id).unwrap();
                Term::from(tcx.mk_ty_from_kind(TyKind::Alias(
                    AliasKind::Projection,
                    AliasTy::new(self.tcx, assoc_item.def_id, mid_args))))
            }
            TypX::Int(ir) => Term::from(match ir {
                IntRange::U(8) => tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U8)),
                IntRange::U(16) => tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U16)),
                IntRange::U(32) => tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U32)),
                IntRange::U(64) => tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U64)),
                IntRange::U(128) => tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U128)),
                IntRange::USize => tcx.mk_ty_from_kind(TyKind::Uint(UintTy::Usize)),
                IntRange::I(8) => tcx.mk_ty_from_kind(TyKind::Int(IntTy::I8)),
                IntRange::I(16) => tcx.mk_ty_from_kind(TyKind::Int(IntTy::I16)),
                IntRange::I(32) => tcx.mk_ty_from_kind(TyKind::Int(IntTy::I32)),
                IntRange::I(64) => tcx.mk_ty_from_kind(TyKind::Int(IntTy::I64)),
                IntRange::I(128) => tcx.mk_ty_from_kind(TyKind::Int(IntTy::I128)),
                IntRange::ISize => tcx.mk_ty_from_kind(TyKind::Int(IntTy::Isize)),
                IntRange::Int => self.adt_from_verus_item(VerusItem::BuiltinType(BuiltinTypeItem::Int)),
                IntRange::Nat => self.adt_from_verus_item(VerusItem::BuiltinType(BuiltinTypeItem::Nat)),
                IntRange::Char => tcx.mk_ty_from_kind(TyKind::Char),
                IntRange::U(_) => unreachable!(),
                IntRange::I(_) => unreachable!(),
            }),
            TypX::Bool => Term::from(tcx.mk_ty_from_kind(TyKind::Bool)),
            _ => {
                dbg!(t);
                todo!();
            }
        }
    }

    fn adt_from_verus_item(&self, verus_item: VerusItem) -> Ty<'tcx> {
        let def_id = self.bctx.ctxt.verus_items.name_to_id.get(&verus_item).unwrap();
        let adt_def = self.tcx.adt_def(*def_id);
        self.tcx.mk_ty_from_kind(TyKind::Adt(adt_def, self.tcx.mk_args(&[])))
    }

    fn adt_from_verus_item_1_arg(&self, verus_item: VerusItem, ty: Ty<'tcx>) -> Term<'tcx> {
        let def_id = self.bctx.ctxt.verus_items.name_to_id.get(&verus_item).unwrap();
        let adt_def = self.tcx.adt_def(*def_id);
        Term::from(self.tcx.mk_ty_from_kind(TyKind::Adt(adt_def, self.tcx.mk_args(&[ty.into()]))))
    } 

    fn int_to_value_tree(&self, i: &BigInt, int_range: IntRange) -> ScalarInt {
        match int_range {
            IntRange::USize => {
                let j = i.to_u128().unwrap();
                ScalarInt::try_from_target_usize(j, self.tcx).unwrap()
            }
            _ => todo!(),
        }
    }
}

pub(crate) fn make_param_map<'tcx>(bctx: &crate::context::BodyCtxt<'tcx>) -> HashMap<vir::ast::Ident, Term<'tcx>> {
    let tcx = bctx.ctxt.tcx;
    let mut generics = tcx.generics_of(bctx.fun_id);
    let mut map: HashMap<vir::ast::Ident, Term<'tcx>> = HashMap::new();

    let param_env = bctx.ctxt.tcx.param_env(bctx.fun_id);

    loop {
        for param in generics.params.iter() {
            match &param.kind {
                GenericParamDefKind::Lifetime => { }
                GenericParamDefKind::Type { .. } => {
                    let ident = crate::rust_to_vir_base::generic_param_def_to_vir_name(param);
                    let param_ty = rustc_middle::ty::ParamTy::for_def(param);
                    let ty = tcx.mk_ty_from_kind(TyKind::Param(param_ty));
                    let term = Term::from(ty);
                    map.insert(Arc::new(ident), term);
                }
                GenericParamDefKind::Const { .. } => {
                    let ident = crate::rust_to_vir_base::generic_param_def_to_vir_name(param);
                    let param_const = rustc_middle::ty::ParamConst::for_def(param);

                    let mut this_cnst = None;
                    for clause in param_env.caller_bounds() {
                        if let ClauseKind::ConstArgHasType(cnst, _ty) = clause.kind().skip_binder() {
                            if let ConstKind::Param(pc) = cnst.kind() {
                                if pc.name == param_const.name {
                                    this_cnst = Some(cnst);
                                    break;
                                }
                            }
                        }
                    }

                    let term = Term::from(this_cnst.unwrap());
                    map.insert(Arc::new(ident), term);
                }
            }
        }
        match &generics.parent {
            Some(def_id) => { generics = tcx.generics_of(*def_id); }
            None => { break; }
        }
    }
    map
}

fn expect_ty<'tcx>(term: Term<'tcx>) -> Ty<'tcx> {
    match term.unpack() {
        TermKind::Ty(ty) => ty,
        TermKind::Const(_) => panic!("Verus internal error: expect_ty failed"),
    }
}

fn expect_const<'tcx>(term: Term<'tcx>) -> Const<'tcx> {
    match term.unpack() {
        TermKind::Ty(_) => panic!("Verus internal error: expect_const failed"),
        TermKind::Const(c) => c,
    }
}
