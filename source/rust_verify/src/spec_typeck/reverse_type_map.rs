use rustc_infer::infer::InferCtxt;
use crate::rustc_infer::infer::TyCtxtInferExt;
use rustc_span::Span;
use super::State;
use vir::ast::{Typ, TypX, Dt, Typs};
use std::collections::HashMap;
use rustc_middle::ty::{Ty, GenericArg, TyKind};
use rustc_middle::ty::GenericArgs;

struct ReverseTypeState<'tcx> {
    span: Span,
    id_map: HashMap<usize, rustc_middle::ty::Ty<'tcx>>,
    infcx: InferCtxt<'tcx>,
}

impl<'a, 'tcx> State<'a, 'tcx> {
    pub fn finalized_vir_typs_to_generic_args(&mut self, typs: &Typs)
        -> &'tcx GenericArgs<'tcx>
    {
        let mut mid_args: Vec<GenericArg<'_>> = vec![];
        for t in typs.iter() {
            mid_args.push(GenericArg::from(self.vir_ty_to_middle_rec(&mut None, t)));
        }
        self.tcx.mk_args(&mid_args)
    }

    pub fn vir_ty_to_middle(&mut self, span: Span, t: &Typ)
        -> (Ty<'tcx>, InferCtxt<'tcx>)
    {
        let infcx = self.tcx.infer_ctxt().ignoring_regions().build();
        let mut r = Some(ReverseTypeState { infcx: infcx, span, id_map: HashMap::new() });
        let ty = self.vir_ty_to_middle_rec(&mut r, t);
        (ty, r.unwrap().infcx)
    }

    fn vir_ty_to_middle_rec(&mut self, r: &mut Option<ReverseTypeState<'tcx>>, t: &Typ) -> Ty<'tcx> {
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
            TypX::UnificationVar(i) => {
                let r: &mut ReverseTypeState<'tcx> = r.as_mut().unwrap();
                let node = self.unifier.get_node(*i);
                if r.id_map.contains_key(&node) {
                    r.id_map[&node]
                } else {
                    let ty = r.infcx.next_ty_var(rustc_infer::infer::type_variable::TypeVariableOrigin { span: r.span, param_def_id: None });
                    r.id_map.insert(node, ty);
                    ty
                }
            }
            _ => todo!(),
        }
    }
}
