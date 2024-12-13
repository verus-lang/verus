use rustc_infer::infer::InferCtxt;
use crate::rustc_infer::infer::TyCtxtInferExt;
use rustc_span::Span;
use super::State;
use vir::ast::{Typ, TypX, Dt};

struct ReverseTypeState<'tcx> {
    infcx: InferCtxt<'tcx>,
    span: Span,
}

impl<'a, 'tcx> State<'a, 'tcx> {
    pub fn vir_ty_to_middle(&mut self, span: Span, t: &Typ)
        -> (rustc_middle::ty::Ty<'tcx>, InferCtxt<'tcx>)
    {
        let infcx = self.tcx.infer_ctxt().ignoring_regions().build();
        let mut r = ReverseTypeState { infcx, span };
        let ty = self.vir_ty_to_middle_rec(&mut r, t);
        (ty, r.infcx)
    }

    fn vir_ty_to_middle_rec(&mut self, r: &mut ReverseTypeState<'tcx>, t: &Typ) -> rustc_middle::ty::Ty<'tcx> {
        let tcx = self.tcx;
        match &**t {
            TypX::Datatype(Dt::Path(path), args, _) => {
                let def_id = crate::rust_to_vir_base::def_id_of_vir_path(path);
                let adt_def = tcx.adt_def(def_id);
                let mut mid_args: Vec<rustc_middle::ty::GenericArg<'_>> = vec![];
                for a in args.iter() {
                    mid_args.push(rustc_middle::ty::GenericArg::from(self.vir_ty_to_middle_rec(r, a)));
                }
                let args = self.tcx.mk_args(&mid_args);
                tcx.mk_ty_from_kind(rustc_middle::ty::TyKind::Adt(adt_def, args))
            }
            TypX::UnificationVar(i) => {
                r.infcx.next_ty_var(rustc_infer::infer::type_variable::TypeVariableOrigin { span: r.span, param_def_id: None })
                /*
                tcx.mk_ty_from_kind(rustc_middle::ty::TyKind::Infer(
                    rustc_middle::ty::InferTy::TyVar(
                      rustc_middle::ty::TyVid::from_usize(*i))))
                      */
            }
            _ => todo!(),
        }
    }
}
