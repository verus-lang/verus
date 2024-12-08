
pub fn check_ty<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    state: &mut State,
    ty: rustc_hir::hir::Ty,
) -> Result<Typ, VirErr> {
    match &ty.kind {
        TyKind::Slice(ty) => {
            let typ = check_ty(tcx, state, ty)?;
            let typs = Arc::new(vec![typ]);
            (Arc::new(TypX::Primitive(Primitive::Slice, typs)), false)
        }
        TyKind::Array(ty, array_len) => {
            let typ = check_ty(tcx, state, ty)?;
            let len = check_const(tcx, ty_len)?;
            let typs = Arc::new(vec![typ, len]);
            (Arc::new(TypX::Primitive(Primitive::Slice, typs)), false)
        }
        TyKind::Ptr(..) => todo!(),
        TyKind::Ref(..) => todo!(),
        TyKind::BareFn(..) => todo!(),
        TyKind::Never => todo(),
        TyKind::Tup(types) => {
            let mut typs = vec![];
            for t in types.iter() {
                typs.push(check_ty(tcx, state, t)?);
            }
            Ok(vir::ast_util::mk_tuple_typ(&Arc::new(typs)))
        }
        TyKind::Path(_qpath) => {
            /*match qpath {
                QPath::Resolved(
            }*/
            todo!()
        }
        TyKind::Infer => {
            Ok(state.unifier.new_unif_variable_type())
        }
        TyKind::InferDelegation(_, _)
        | TyKind::AnonAdt(..)
        | TyKind::OpaqueDef(..)
        | TyKind::TraitObject(..)
        | TyKind::Typeof(..)
        | TyKind::Err(..)
        | TyKind::Pat(..)
        => {
            unsupported_err!("type: {:?}", ty);
        }
    }
}
