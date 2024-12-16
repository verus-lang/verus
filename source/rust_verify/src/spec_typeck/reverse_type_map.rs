use rustc_infer::infer::InferCtxt;
use crate::rustc_infer::infer::TyCtxtInferExt;
use super::unifier::Info;
use rustc_span::Span;
use super::State;
use vir::ast::{Typ, TypX, Dt, Typs};
use std::collections::HashMap;
use rustc_middle::ty::{Ty, GenericArg, TyKind, AssocKind, AliasKind, AliasTy, UintTy, InferTy};
use rustc_middle::ty::GenericArgs;
use std::sync::Arc;
use vir::ast::IntRange;
use rustc_middle::ty::TyVid;
use super::unification_table::NodeClass;

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

    pub fn finalized_vir_typ_to_typ(&self, typ: &Typ) -> Ty<'tcx>
    {
        self.vir_ty_to_middle_rec(&mut None, typ)
    }

    pub fn vir_ty_to_middle(&self, span: Span, t: &Typ)
        -> (Ty<'tcx>, InferCtxt<'tcx>)
    {
        let infcx = self.tcx.infer_ctxt().ignoring_regions().build();
        let mut r = Some(ReverseTypeState { infcx: infcx, span, id_map: HashMap::new() });
        let ty = self.vir_ty_to_middle_rec(&mut r, t);
        (ty, r.unwrap().infcx)
    }

    pub fn vir_typs_to_middle_tys(&self, span: Span, typs: &Typs)
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
    fn vir_ty_to_middle_rec(&self, r: &mut Option<ReverseTypeState<'tcx>>, t: &Typ) -> Ty<'tcx> {
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
                tcx.mk_ty_from_kind(TyKind::Adt(adt_def, args))
            }
            TypX::TypParam(t) => {
                *self.param_name_to_param_ty.get(t).unwrap()
            }
            TypX::UnificationVar(i) => {
                let rstate: &mut ReverseTypeState<'tcx> = r.as_mut().unwrap();
                let node = self.unifier.get_class(*i);
                if let Info::Known(t) = &self.unifier[node].info {
                    self.vir_ty_to_middle_rec(r, t)
                } else {
                    if rstate.id_map.contains_key(&node) {
                        rstate.id_map[&node]
                    } else {
                        let ty = rstate.infcx.next_ty_var(rustc_infer::infer::type_variable::TypeVariableOrigin { span: rstate.span, param_def_id: None });
                        rstate.id_map.insert(node, ty);
                        ty
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
                tcx.mk_ty_from_kind(TyKind::Alias(
                    AliasKind::Projection,
                    AliasTy::new(self.tcx, assoc_item.def_id, mid_args)))
            }
            TypX::Int(IntRange::U(8)) => tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U8)),
            TypX::Bool => tcx.mk_ty_from_kind(TyKind::Bool),
            _ => {
                dbg!(t);
                todo!();
            }
        }
    }
}

pub(crate) fn make_param_map<'tcx>(bctx: &crate::context::BodyCtxt<'tcx>) -> HashMap<vir::ast::Ident, Ty<'tcx>> {
    let tcx = bctx.ctxt.tcx;
    let mut generics = tcx.generics_of(bctx.fun_id);
    let mut map: HashMap<vir::ast::Ident, Ty<'tcx>> = HashMap::new();
    loop {
        for param in generics.params.iter() {
            let ident = crate::rust_to_vir_base::generic_param_def_to_vir_name(param);
            let param_ty = rustc_middle::ty::ParamTy::for_def(param);
            let ty = tcx.mk_ty_from_kind(TyKind::Param(param_ty));
            map.insert(Arc::new(ident), ty);
        }
        match &generics.parent {
            Some(def_id) => { generics = tcx.generics_of(*def_id); }
            None => { break; }
        }
    }
    map
}
