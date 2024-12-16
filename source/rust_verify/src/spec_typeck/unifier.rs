use vir::ast::{Typ, TypX, VirErr, IntRange, Typs};
use super::State;
use std::sync::Arc;
use std::collections::HashSet;
use rustc_middle::ty::GenericArg;
use super::unification_table::NodeClass;

#[derive(Debug, Clone, Copy)]
pub enum UnknownInteger {
    /// Can be any *signed* integer type. Will default to 'int'
    Signed,
    /// Can be any integer type. Will default to 'nat'
    Any,
}

#[derive(Clone, Debug)]
pub enum Info {
    Unknown,
    UnknownInteger(UnknownInteger),
    Alias(Alias),
    Known(Typ),
}

#[derive(Clone, Debug)]
pub struct Entry {
    pub info: Info,
    pub final_typ: Option<Typ>,
}

#[derive(Clone, Debug)]
pub struct Alias {
    pub def_id: rustc_span::def_id::DefId,
    pub args: Typs,
}

#[derive(Clone)]
pub enum AliasOrTyp {
    Alias(Alias),
    Typ(Typ),
}

enum UnifyError {
    Error,
}

impl State<'_, '_> {
    // TODO overflow checking
    pub fn finish_unification(&mut self) -> Result<(), VirErr> {
        for i in 0 .. self.unifier.len() {
            if let Some(class) = self.unifier.is_root_of_class(i) {
               self.finish_rec(class);
            }
        }

        self.check_deferred_obligations();

        Ok(())
    }

    fn finish_rec(&mut self, node: NodeClass) {
        if self.unifier[node].final_typ.is_some() {
            return;
        }

        let typ = match &self.unifier[node].info {
            Info::Unknown => todo!(),
            Info::UnknownInteger(UnknownInteger::Any) => vir::ast_util::nat_typ(),
            Info::UnknownInteger(UnknownInteger::Signed) => vir::ast_util::int_typ(),
            Info::Alias(_) => todo!(),
            Info::Known(typ) => typ.clone(),
        };

        let t = vir::ast_visitor::map_typ_visitor_env(&typ, self, &|state: &mut Self, t: &Typ| {
            match &**t {
                TypX::UnificationVar(uid) => {
                    let node = state.unifier.get_node(*uid);
                    state.finish_rec(node);
                    Ok(state.unifier[node].final_typ.clone().unwrap())
                }
                TypX::Projection { .. } => {
                    todo!();
                }
                _ => Ok(t.clone())
            }
        }).unwrap();

        self.unifier[node].final_typ = Some(t);
    }

    pub(crate) fn check_deferred_obligations(&mut self) {
        let span = self.whole_span;

        use crate::rustc_infer::infer::TyCtxtInferExt;
        use crate::rustc_trait_selection::traits::TraitEngineExt;
        use crate::rustc_trait_selection::traits::error_reporting::TypeErrCtxtExt;
        use crate::rustc_middle::ty::ToPredicate;

        let infcx = self.tcx.infer_ctxt().ignoring_regions().build();
        let mut fulfillment_cx = <dyn rustc_trait_selection::traits::TraitEngine<'_>>::new(&infcx);

        let deferred_projection_obligations = std::mem::take(&mut self.deferred_projection_obligations);

        for (alias, typ) in deferred_projection_obligations.iter() {
            let typ = self.get_finished_typ(typ);
            let ty = self.finalized_vir_typ_to_typ(&typ);

            let mut mid_args: Vec<GenericArg<'_>> = vec![];
            for typ in alias.args.iter() {
                let typ = self.get_finished_typ(typ);
                let ty = self.finalized_vir_typ_to_typ(&typ);
                mid_args.push(GenericArg::from(ty));
            }

            let alias_ty = rustc_middle::ty::AliasTy::new(self.tcx, alias.def_id, mid_args);

            let pp = rustc_middle::ty::ProjectionPredicate {
                projection_ty: alias_ty,
                term: rustc_middle::ty::Term::from(ty),
            };
            let ck = rustc_middle::ty::ClauseKind::Projection(pp);
            let pk = rustc_middle::ty::PredicateKind::Clause(ck);
            let p: rustc_middle::ty::Predicate = pk.to_predicate(self.tcx);

            let cause = rustc_trait_selection::traits::ObligationCause::new(
                span,
                self.bctx.fun_id.expect_local(),
                rustc_trait_selection::traits::ObligationCauseCode::MiscObligation,
            );
            let obligation = rustc_trait_selection::traits::Obligation::new(
                self.tcx,
                cause,
                self.tcx.param_env(self.bctx.fun_id),
                p,
            );
            fulfillment_cx.register_predicate_obligation(&infcx, obligation);
        }

        let mut errors = fulfillment_cx.select_where_possible(&infcx);
        errors.append(&mut fulfillment_cx.collect_remaining_errors(&infcx));

        if errors.len() > 0 {
            let err_ctxt = infcx.err_ctxt();
            err_ctxt.report_fulfillment_errors(errors);
        }

        assert!(self.deferred_projection_obligations.len() == 0);
        todo!();
    }

    /// Get the final type with no unification variables.
    /// This must be called after `finish`
    pub fn get_finished_typ(&mut self, typ: &Typ) -> Typ {
        vir::ast_visitor::map_typ_visitor_env(typ, self, &|state: &mut Self, t: &Typ| {
            match &**t {
                TypX::UnificationVar(uid) => {
                    let node = state.unifier.get_node(*uid);
                    Ok(state.unifier[node].final_typ.clone().unwrap())
                }
                TypX::Projection { .. } => unreachable!(),
                _ => Ok(t.clone())
            }
        }).unwrap()
    }

    pub fn fresh_typ_with_info(&mut self, info: Info) -> Typ {
        let entry = Entry { info, final_typ: None };
        let uid = self.unifier.fresh_node(entry);
        Arc::new(TypX::UnificationVar(uid))
    }

    pub fn new_unknown_typ(&mut self) -> Typ {
        self.fresh_typ_with_info(Info::Unknown)
    }

    pub fn new_unknown_integer_typ(&mut self, u: UnknownInteger) -> Typ {
        self.fresh_typ_with_info(Info::UnknownInteger(u))
    }

    pub fn expect_integer(&mut self, _u2: &Typ) -> Result<(), VirErr> {
        todo!();
    }

    pub fn expect_integer_and_choose_int_range(&mut self, _u2: &Typ) -> Result<IntRange, VirErr> {
        todo!();
    }

    pub fn get_typ_with_concrete_head_if_possible(&mut self, t: &Typ) -> Typ {
        match &**t {
            TypX::UnificationVar(id) => {
                let node = self.unifier.get_node(*id);
                if matches!(&self.unifier[node].info, Info::Alias(_)) {
                    self.reduce_node_as_much_as_possible(node);
                }
                match &self.unifier[node].info {
                    Info::Known(known_typ) => known_typ.clone(),
                    _ => t.clone(),
                }
            }
            TypX::Projection { .. } => unreachable!(),
            _ => t.clone(),
        }
    }

    /// t1 can be used where t2 is expected
    /// for the most part this means types are exactly equal, except for
    /// some integer type coercions
    pub fn expect_allowing_coercion(&mut self, t1: &Typ, t2: &Typ) -> Result<(), VirErr> {
        let t1c = self.get_typ_with_concrete_head_if_possible(t1);
        let t2c = self.get_typ_with_concrete_head_if_possible(t2);

        match (&*t1c, &*t2c) {
            (TypX::Int(ir1), TypX::Int(ir2)) 
                if int_range_equal_or_implicit_coercion_ok(*ir1, *ir2)
            => {
                // we're good
                return Ok(());
            }
            _ => { }
        }

        let e = self.unify(t1, t2);
        match e {
            Ok(()) => Ok(()),
            Err(_ue) => {
                dbg!(&t1);
                dbg!(&t2);
                todo!()
            }
        }
    }

    pub fn expect_bool(&mut self, t1: &Typ) -> Result<(), VirErr> {
        self.expect_exact(t1, &vir::ast_util::bool_typ())
    }

    /// t1 can be used where t2 is expected
    /// for the most part this means types are exactly equal, except for
    /// some integer type coercions
    pub fn expect_exact(&mut self, t1: &Typ, t2: &Typ) -> Result<(), VirErr> {
        let e = self.unify(t1, t2);
        match e {
            Ok(()) => Ok(()),
            Err(_ue) => {
                dbg!(t1);
                dbg!(t2);
                panic!("expect_exact");
            }
        }
    }

    // TODO overflow checking
    fn unify(&mut self, typ1: &Typ, typ2: &Typ) -> Result<(), UnifyError> {
        match (&**typ1, &**typ2) {
            (TypX::UnificationVar(id1), TypX::UnificationVar(id2)) => {
                let node1 = self.unifier.get_node(*id1);
                let node2 = self.unifier.get_node(*id2);
                if node1 != node2 {
                    let (merged_info, recurse_tys) = merge_info(
                        &self.unifier[node1].info,
                        &self.unifier[node2].info);
                    self.unifier.merge_nodes(node1, node2, Entry { info: merged_info, final_typ: None });

                    if let Some((rt1, rt2)) = recurse_tys {
                        self.unify(&rt1, &rt2)?;
                    }

                    Ok(())
                } else {
                    Ok(())
                }
            }
            (TypX::UnificationVar(uid), _) | (_, TypX::UnificationVar(uid)) => {
                let (typ, uvar_on_left) = if matches!(&**typ1, TypX::UnificationVar(_)) {
                    (typ2, true)
                } else {
                    (typ1, false)
                };

                let node = self.unifier.get_node(*uid);
                match &self.unifier[node].info {
                    Info::Unknown => {
                        self.unifier[node].info = Info::Known(typ.clone());
                        Ok(())
                    }
                    Info::UnknownInteger(u) => {
                        if is_definitely_integer_type(typ, *u) {
                            self.unifier[node].info = Info::Known(typ.clone());
                        } else {
                            todo!();
                        }
                        Ok(())
                    }
                    Info::Known(known_typ) => {
                        if uvar_on_left {
                            self.unify(&known_typ.clone(), typ)
                        } else {
                            self.unify(typ, &known_typ.clone())
                        }
                    }
                    Info::Alias(alias) => {
                        self.deferred_projection_obligations.push((alias.clone(), typ.clone()));
                        self.unifier[node].info = Info::Known(typ.clone());
                        Ok(())
                    }
                }
            }
            (_ty1, _ty2) => {
                self.unify_heads(typ1, typ2)
            }
        }
    }

    // This is the part of `unify` that just checks the head type matches and recurses.
    // Fancy logic dealing with unification vars & projections should go in `unify`
    fn unify_heads(&mut self, t1: &Typ, t2: &Typ) -> Result<(), UnifyError> {
        match (&**t1, &**t2) {
            (TypX::Bool, TypX::Bool) => Ok(()),
            (TypX::Int(ir1), TypX::Int(ir2)) => {
                if ir1 == ir2 {
                    Ok(())
                } else {
                    Err(UnifyError::Error)
                }
            }
            (TypX::SpecFn(args1, ret1), TypX::SpecFn(args2, ret2)) => {
                if args1.len() != args2.len() {
                    Err(UnifyError::Error)
                } else {
                    for (a1, a2) in args1.iter().zip(args2.iter()) {
                        self.unify(a1, a2)?;
                    }
                    self.unify(ret1, ret2)?;
                    Ok(())
                }
            }
            (TypX::AnonymousClosure(_args1, _ret1, id1), TypX::AnonymousClosure(_args2, _ret2, id2)) => {
                if id1 == id2 {
                    Ok(())
                } else {
                    Err(UnifyError::Error)
                }
            }
            (TypX::FnDef(..), TypX::FnDef(..)) => {
                todo!()
            }
            (TypX::Datatype(dt1, args1, _impl_paths1),
                TypX::Datatype(dt2, args2, _impl_paths2))
            => {
                if dt1 == dt2 && args1.len() == args2.len() {
                    for (a1, a2) in args1.iter().zip(args2.iter()) {
                        self.unify(a1, a2)?;
                    }
                    Ok(())
                } else {
                    Err(UnifyError::Error)
                }
            }
            (TypX::Primitive(prim1, args1), TypX::Primitive(prim2, args2)) => {
                if prim1 == prim2 && args1.len() == args2.len() {
                    for (a1, a2) in args1.iter().zip(args2.iter()) {
                        self.unify(a1, a2)?;
                    }
                    Ok(())
                } else {
                    Err(UnifyError::Error)
                }
            }
            (TypX::Decorate(dec1, tda1, typ1), TypX::Decorate(dec2, tda2, typ2)) => {
                if dec1 != dec2 {
                    return Err(UnifyError::Error);
                }
                match (tda1, tda2) {
                    (None, None) => { }
                    (Some(vir::ast::TypDecorationArg { allocator_typ: tda1 }),
                     Some(vir::ast::TypDecorationArg { allocator_typ: tda2 })) => {
                        self.unify(tda1, tda2)?;
                    }
                    (None, Some(_)) | (Some(_), None) => unreachable!(),
                }
                self.unify(typ1, typ2)
            }
            (TypX::TypParam(id1), TypX::TypParam(id2)) => {
                if id1 == id2 {
                    Err(UnifyError::Error)
                } else {
                    Ok(())
                }
            }
            (TypX::ConstInt(a1), TypX::ConstInt(a2)) => {
                if a1 == a2 {
                    Err(UnifyError::Error)
                } else {
                    Ok(())
                }
            }

            (TypX::UnificationVar(..), _) => unreachable!(),
            (_, TypX::UnificationVar(..)) => unreachable!(),
            (TypX::Projection{..}, _) => unreachable!(),
            (_, TypX::Projection{..}) => unreachable!(),

            // for exhaustiveness checks
            (TypX::Bool, _)
            | (TypX::Int(_), _)
            | (TypX::SpecFn(..), _)
            | (TypX::AnonymousClosure(..), _)
            | (TypX::FnDef(..), _)
            | (TypX::Datatype(..), _)
            | (TypX::Primitive(..), _)
            | (TypX::Decorate(..), _)
            | (TypX::TypParam(..), _)
            | (TypX::ConstInt(..), _)
            => Err(UnifyError::Error),

            (TypX::Boxed(..), _)
            | (TypX::TypeId, _)
            | (TypX::Air(..), _) => unreachable!(),
        }
    }

    /*
    pub fn finalized_normalize(&mut self, typ: &Typ) -> Typ {
        //use crate::rustc_infer::infer::TyCtxtInferExt;
        let ty = self.finalized_vir_typ_to_typ(typ);

        //let param_env = self.tcx.param_env(self.bctx.fun_id);
        //let infcx = self.tcx.infer_ctxt().ignoring_regions().build();
        //let cause = rustc_infer::traits::ObligationCause::dummy();
        //let at = infcx.at(&cause, param_env);
        //let ty = &crate::rust_to_vir_base::clean_all_escaping_bound_vars(self.tcx, ty, param_env);
        //let norm = at.normalize(*ty);
        crate::rust_to_vir_base::mid_ty_to_vir(
            self.tcx,
            &self.bctx.ctxt.verus_items,
            self.bctx.fun_id,
            self.whole_span,
            &ty,
            false,
        ).unwrap()
    }
    */

    pub(crate) fn normalize_typ(&mut self, typ: &Typ) -> Typ {
        vir::ast_visitor::map_typ_visitor_env(typ, self, &|state: &mut Self, t: &Typ| {
            match &**t {
                TypX::Projection { trait_typ_args, trait_path, name } => {
                    let trait_def_id = crate::rust_to_vir_base::def_id_of_vir_path(trait_path);
                    let assoc_item = state.tcx.associated_items(trait_def_id)
                          .find_by_name_and_kinds(state.tcx, rustc_span::symbol::Ident::from_str(&name),
                            &[rustc_middle::ty::AssocKind::Type], trait_def_id).unwrap();
                    let alias = Alias {
                        def_id: assoc_item.def_id,
                        args: trait_typ_args.clone(),
                    };

                    Ok(state.fresh_typ_with_info(Info::Alias(alias)))
                }
                _ => Ok(t.clone()),
            }
        }).unwrap()
    }

    fn reduce_node_as_much_as_possible(&mut self, node: NodeClass) {
        let mut reachable = vec![node];
        let mut is_in_reachable = HashSet::<NodeClass>::new();
        is_in_reachable.insert(node);

        let mut idx = 0;
        while idx < reachable.len() {
            let n = reachable[idx];
            idx += 1;

            let typs: &[Typ] = match &self.unifier[n].info {
                Info::Alias(alias) => &alias.args,
                Info::Known(t) => &[t.clone()],
                Info::Unknown | Info::UnknownInteger(_) => &[]
            };
            for t in typs.iter() {
                vir::ast_visitor::typ_visitor_check(t, &mut |t| {
                    if let TypX::UnificationVar(v) = &**t {
                        let n = self.unifier.get_node(*v);
                        if !is_in_reachable.contains(&n) {
                            reachable.push(n);
                            is_in_reachable.insert(n);
                        }
                    }
                    Ok::<(), ()>(())
                }).unwrap();
            }
        }

        for node in reachable.iter().rev() {
            let node = *node;
            if matches!(&self.unifier[node].info, Info::Alias(_)) {
                self.reduce_one_node(node);
            }
        }

        /*
                let new_info = match self.reduce_alias(&alias.clone()) {
                    AliasOrTyp::Alias(new_alias) => Info::Alias(new_alias),
                    AliasOrTyp::Typ(typ) => Info::Known(typ),
                };
                self.unifier.info[node] = new_info;
            }
            _ => { }
        }
        */
    }

    fn reduce_one_node(&mut self, node: NodeClass) {
        if let Info::Alias(alias) = &self.unifier[node].info {
            let alias_or_typ = self.reduce_alias(alias);
            self.unifier[node].info = match alias_or_typ {
                AliasOrTyp::Alias(alias) => Info::Alias(alias),
                AliasOrTyp::Typ(t) => {
                    match &*t {
                        TypX::UnificationVar(_v) => todo!(),
                        _ => Info::Known(t),
                    }
                }
            };
        }
    }

    fn reduce_alias(&self, alias: &Alias) -> AliasOrTyp {
        use crate::rust_to_vir_base::mid_ty_to_vir;
        use crate::rust_to_vir_base::mid_ty_to_vir_ghost;
        use rustc_middle::ty::GenericArgKind;

        let (args, infcx, unif_map) = self.vir_typs_to_middle_tys(self.whole_span, &alias.args);
        let alias_ty = rustc_middle::ty::AliasTy::new(self.tcx, alias.def_id, args);
        let ty = self.tcx.mk_ty_from_kind(rustc_middle::ty::Alias(rustc_middle::ty::AliasKind::Projection, alias_ty));

        let param_env = self.tcx.param_env(self.bctx.fun_id);
        let cause = rustc_infer::traits::ObligationCause::dummy();
        let at = infcx.at(&cause, param_env);
        let ty = &crate::rust_to_vir_base::clean_all_escaping_bound_vars(self.tcx, ty, self.bctx.fun_id);
        use crate::rustc_trait_selection::traits::NormalizeExt;
        let norm = at.normalize(*ty);

        dbg!(ty);
        dbg!(&norm);

        let mut obligations = norm.obligations;

        let m_alias_or_ty = if let rustc_middle::ty::TyKind::Infer(t) = norm.value.kind() {
            let rustc_middle::ty::InferTy::TyVar(tyvid) = t else { unreachable!() };
            if unif_map.contains_key(tyvid) {
                MiddleAliasOrTy::Ty(norm.value)
            } else {
                MiddleAliasOrTy::Alias(
                    Self::get_alias_from_normalize_result(*tyvid, &mut obligations)
                )
            }
        } else {
            MiddleAliasOrTy::Ty(norm.value)
        };

        dbg!(&m_alias_or_ty);
        assert!(obligations.len() == 0);

        match m_alias_or_ty {
            MiddleAliasOrTy::Ty(ty) => {
                let typ = mid_ty_to_vir_ghost(self.tcx, &self.bctx.ctxt.verus_items, 
                    self.bctx.fun_id, self.whole_span, &ty, Some(&unif_map), false).unwrap().0;
                AliasOrTyp::Typ(typ)
            }
            MiddleAliasOrTy::Alias(alias) => {
                let mut typs = vec![];
                for arg in alias.args.iter() {
                    match arg.unpack() {
                        GenericArgKind::Type(ty) => {
                            let typ = mid_ty_to_vir_ghost(self.tcx, &self.bctx.ctxt.verus_items, 
                                self.bctx.fun_id, self.whole_span, &ty, Some(&unif_map), false).unwrap().0;
                            typs.push(typ);
                        }
                        _ => todo!()
                    }
                }
                AliasOrTyp::Alias(Alias { def_id: alias.def_id, args: Arc::new(typs) })
            }
        }


        //let selcx = rustc_trait_selection_verus_fork::traits::SelectionContext::new(

        //rustc_trait_selection_verus_fork::traits::project::project;
        //todo!();
        /*
        assert!(matches!(&**typ, TypX::Projection { .. }));

        use crate::rustc_trait_selection::traits::NormalizeExt;
        let (ty, infcx) = self.vir_ty_to_middle(self.whole_span, typ);

        let param_env = self.tcx.param_env(self.bctx.fun_id);
        let cause = rustc_infer::traits::ObligationCause::dummy();
        let at = infcx.at(&cause, param_env);
        let ty = &crate::rust_to_vir_base::clean_all_escaping_bound_vars(self.tcx, ty, self.bctx.fun_id);
        let norm = at.normalize(*ty); // TODO is normalize recursive?

        dbg!(&ty);
        dbg!(&norm.value);
        dbg!(&norm);
        let norm_typ = crate::rust_to_vir_base::mid_ty_to_vir(
            self.tcx,
            &self.bctx.ctxt.verus_items,
            self.bctx.fun_id,
            self.whole_span,
            &norm.value,
            false,
        ).unwrap();

        if !vir::ast_util::types_equal(typ, &norm_typ) {
            self.deferred_projection_obligations.push((typ.clone(), norm_typ.clone()));
        }

        norm_typ
        */
    }

    fn get_alias_from_normalize_result<'tcx>(
        tyvid: rustc_middle::ty::TyVid,
        obligations: &mut rustc_infer::traits::PredicateObligations<'tcx>)
        -> rustc_middle::ty::AliasTy<'tcx>
    {
        use rustc_middle::ty::PredicateKind;
        use rustc_middle::ty::ClauseKind;
        use rustc_middle::ty::TermKind;
        use rustc_middle::ty::TyKind;
        use rustc_middle::ty::InferTy;
        for i in 0 .. obligations.len() {
            let predicate = &obligations[i].predicate;
            if let PredicateKind::Clause(ClauseKind::Projection(projection_pred)) = predicate.kind().skip_binder() {
                if let TermKind::Ty(ty) = projection_pred.term.unpack() {
                    if let TyKind::Infer(infer_ty) = ty.kind() {
                        if *infer_ty == InferTy::TyVar(tyvid) {
                            let ma = projection_pred.projection_ty;
                            obligations.remove(i);
                            return ma;
                        }
                    }
                }
            }
        }
        panic!("get_alias_from_normalize_result failed");
    }
}

fn int_range_equal_or_implicit_coercion_ok(ir1: IntRange, ir2: IntRange) -> bool {
    if ir1 == ir2 {
        return true;
    }
    match (ir1, ir2) {
        (_, IntRange::Int) => true,
        (IntRange::U(_) | IntRange::USize, IntRange::Nat) => true,
        _ => false,
    }
}

fn merge_info(info1: &Info, info2: &Info) -> (Info, Option<(Typ, Typ)>) {
    match (info1, info2) {
        (Info::Unknown, info) => (info.clone(), None),
        (info, Info::Unknown) => (info.clone(), None),
        (Info::UnknownInteger(a), Info::UnknownInteger(b)) => (Info::UnknownInteger(a.join(*b)), None),
        (Info::Known(t1), Info::Known(t2)) => {
            let t = if matches!(&**t2, TypX::Projection { .. })
                && !matches!(&**t1, TypX::Projection { .. })
            {
                t1.clone()
            } else {
                t2.clone()
            };
            (Info::Known(t), Some((t1.clone(), t2.clone())))
        }
        (Info::UnknownInteger(u), Info::Known(t))
        | (Info::Known(t), Info::UnknownInteger(u))
        => { 
            if is_definitely_integer_type(t, *u) {
                (Info::Known(t.clone()), None)
            } else {
                todo!();
                //(Info::Contradiction, None)
            }
        }
        (Info::Alias(_), _) => todo!(),
        (_, Info::Alias(_)) => todo!(),
    }
}

impl UnknownInteger {
    fn join(self, b: UnknownInteger) -> UnknownInteger {
        match (self, b) {
            (UnknownInteger::Signed, _) => UnknownInteger::Signed,
            (_, UnknownInteger::Signed) => UnknownInteger::Signed,
            (UnknownInteger::Any, UnknownInteger::Any) => UnknownInteger::Any,
        }
    }
}

fn is_definitely_integer_type(t: &Typ, u: UnknownInteger) -> bool {
    match u {
        UnknownInteger::Any => {
            match &**t {
                TypX::Int(ir) => match ir {
                    IntRange::Int
                    | IntRange::Nat
                    | IntRange::U(_)
                    | IntRange::I(_)
                    | IntRange::USize
                    | IntRange::ISize => true,
                    IntRange::Char => false,
                }
                _ => false,
            }
        }
        UnknownInteger::Signed => {
            match &**t {
                TypX::Int(ir) => match ir {
                    IntRange::Int
                    | IntRange::I(_)
                    | IntRange::ISize => true,
                    IntRange::Nat
                    | IntRange::U(_)
                    | IntRange::USize => false,
                    IntRange::Char => false,
                }
                _ => false,
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum MiddleAliasOrTy<'tcx> {
    Alias(rustc_middle::ty::AliasTy<'tcx>),
    Ty(rustc_middle::ty::Ty<'tcx>),
}
