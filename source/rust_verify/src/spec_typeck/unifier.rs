use vir::ast::{Typ, TypX, VirErr, IntRange, Typs};
use vir::ast_util::{int_typ, nat_typ};
use super::State;
use std::sync::Arc;
use std::collections::HashSet;
use super::unification_table::NodeClass;

/// During type inference, we create type variables which are unified into equivalence
/// classes in the unification table (UnificationTable<Entry>).
/// Each equivalence class maps to some 'Entry' and with an 'info' field that tells us what
/// we know about that variable.
///
/// An `Info::Known` type should never be a lone inference variable. Inference variables
/// should be unified through the unification table instead.
/// The Known type can still have inference variables in arguments, e.g.,
///   ?1  -->  Known( SomeDatatype<?2, ?3> )
/// The Known type must have a "concrete head".
///
/// If cycles ever happen, it can cause infinite recursion, so we have to detect that case
/// and report an error.
///
/// ** Working with projections **
///
/// All types stored in info must be _normalized_.
/// This means no non-normalized TypX::Projection types.
/// (A Projection can be normalized if it uses a type param, like `T::AssocType` which has
/// obligations that must be met through a 'where' clause. We use rust's normalizer to tell
/// the difference.)
///
/// To normalize a type, all non-normalized projections are replaced with inference vars;
/// these vars can be mapped to the projections via Info::Projection. (The type arguments
/// in an Info::Projection should in turn be normalized.)
///
/// When we need concrete types, we attempt to reduce the projections as much as possible.
/// Ideally, Projections eventually become Known. If, at the end, we can't reduce all the
/// Projections to Known, then we have to error.
///
/// Also note there *can* be cycles of inference vars through the Projection types.
/// That isn't necessarily an error.

#[derive(Clone, Debug)]
pub enum Info {
    Unknown,
    UnknownInteger,
    Projection(Projection),
    Known(Typ),
}

#[derive(Clone, Debug)]
pub struct Entry {
    pub info: Info,
    /// The 'final_typ' is filled in at the end. It should have no inference variables
    /// and no non-normalized projection types.
    pub final_typ: Option<Typ>,
}

#[derive(Debug, Clone, Copy)]
pub enum IntOrNat {
    Int, Nat
}

#[derive(Clone, Debug)]
pub struct Projection {
    pub def_id: rustc_span::def_id::DefId,
    pub args: Typs,
}

#[derive(Clone)]
pub enum ProjectionOrTyp {
    Projection(Projection),
    Typ(Typ),
}

enum UnifyError {
    Error,
}

impl State<'_, '_> {
    /// Finish unification, solve all projections, concretize everything.
    /// Error if there any unresolved vars or 
    ///
    /// This should be called after all constraints are in.

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
            Info::UnknownInteger => vir::ast_util::int_typ(),
            Info::Projection(_) => todo!(),
            Info::Known(typ) => typ.clone(),
        };

        let t = vir::ast_visitor::map_typ_visitor_env(&typ, self, &|state: &mut Self, t: &Typ| {
            match &**t {
                TypX::UnificationVar(uid) => {
                    let node = state.unifier.get_class(*uid);
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

    /// Get the final type with no unification variables.
    /// This must be called after `finish_unification`
    pub fn get_finished_typ(&mut self, typ: &Typ) -> Typ {
        vir::ast_visitor::map_typ_visitor_env(typ, self, &|state: &mut Self, t: &Typ| {
            match &**t {
                TypX::UnificationVar(uid) => {
                    let node = state.unifier.get_class(*uid);
                    Ok(state.unifier[node].final_typ.clone().unwrap())
                }
                TypX::Projection { .. } => unreachable!(),
                _ => Ok(t.clone())
            }
        }).unwrap()
    }

    /////////////////////////////////////////////////////////////////////
    ///////// Utilities to be called by the main type-checking logic

    pub fn fresh_typ_with_info(&mut self, info: Info) -> Typ {
        let entry = Entry { info, final_typ: None };
        let uid = self.unifier.fresh_node(entry);
        Arc::new(TypX::UnificationVar(uid))
    }

    pub fn new_unknown_typ(&mut self) -> Typ {
        self.fresh_typ_with_info(Info::Unknown)
    }

    pub fn new_unknown_integer_typ(&mut self) -> Typ {
        self.fresh_typ_with_info(Info::UnknownInteger)
    }

    /// Require the given type to be an integer
    pub fn expect_integer(&mut self, t: &Typ) -> Result<(), VirErr> {
        match &**t {
            TypX::Int(
              IntRange::Int
              | IntRange::Nat
              | IntRange::U(_)
              | IntRange::I(_)
              | IntRange::USize
              | IntRange::ISize) => Ok(()),
            TypX::UnificationVar(id) => {
                let node = self.unifier.get_class(*id);
                match &self.unifier[node].info {
                    Info::Known(t) => self.expect_integer(&t.clone()),
                    Info::UnknownInteger => Ok(()),
                    Info::Projection(_) => todo!(),
                    Info::Unknown => {
                        self.unifier[node].info = Info::UnknownInteger;
                        Ok(())
                    }
                }
            }
            _ => todo!(),
        }
    }

    /// Require the given type to be bool
    pub fn expect_bool(&mut self, t1: &Typ) -> Result<(), VirErr> {
        self.expect_exact(t1, &vir::ast_util::bool_typ())
    }

    pub fn get_typ_with_concrete_head_if_possible(&mut self, t: &Typ) -> Result<Typ, VirErr> {
        match &**t {
            TypX::UnificationVar(id) => {
                let node = self.unifier.get_class(*id);
                if matches!(&self.unifier[node].info, Info::Projection(_)) {
                    self.reduce_node_as_much_as_possible(node)?;
                }
                match &self.unifier[node].info {
                    Info::Known(known_typ) => Ok(known_typ.clone()),
                    _ => Ok(t.clone()),
                }
            }
            _ => Ok(t.clone()),
        }
    }

    /// t1 can be used where t2 is expected
    /// for the most part this means types are exactly equal, except for
    /// some integer type coercions
    pub fn expect_allowing_coercion(&mut self, t1: &Typ, t2: &Typ) -> Result<(), VirErr> {
        let t1c = self.get_typ_with_concrete_head_if_possible(t1)?;
        let t2c = self.get_typ_with_concrete_head_if_possible(t2)?;

        match (&*t1c, &*t2c) {
            (TypX::Int(ir1), TypX::Int(ir2)) 
                if int_range_equal_or_implicit_coercion_ok(*ir1, *ir2)
            => {
                // we're good
                return Ok(());
            }
            _ => { }
        }

        self.expect_exact(t1, t2)
    }

    /// expect t1 to match t2 exactly
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

    /////////////////////////////////////////////////////////////////////
    ///////// The unification

    // TODO overflow checking
    fn unify(&mut self, typ1: &Typ, typ2: &Typ) -> Result<(), UnifyError> {
        match (&**typ1, &**typ2) {
            (TypX::UnificationVar(id1), TypX::UnificationVar(id2)) => {
                let node1 = self.unifier.get_class(*id1);
                let node2 = self.unifier.get_class(*id2);
                if node1 != node2 {
                    let (merged_info, recurse_tys) = merge_info(
                        &self.unifier[node1].info,
                        &self.unifier[node2].info);
                    self.unifier.merge_classes(node1, node2, Entry { info: merged_info, final_typ: None });

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

                let node = self.unifier.get_class(*uid);
                match &self.unifier[node].info {
                    Info::Unknown => {
                        self.unifier[node].info = Info::Known(typ.clone());
                        Ok(())
                    }
                    Info::UnknownInteger => {
                        if is_definitely_integer_type(typ) {
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
                    Info::Projection(projection) => {
                        self.deferred_projection_obligations.push((projection.clone(), typ.clone()));
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

    /////////////////////////////////////////////////////////////////////
    ///////// "Normalize" types.

    /// Normalize the type by removing all the projection types.
    /// This doesn't attempt to reduce the projections, just instantiates new
    /// inference vars for them.
    /// This should be called after performing substitution into some item.
    pub(crate) fn normalize_typ(&mut self, typ: &Typ) -> Typ {
        vir::ast_visitor::map_typ_visitor_env(typ, self, &|state: &mut Self, t: &Typ| {
            match &**t {
                TypX::Projection { trait_typ_args, trait_path, name } => {
                    let trait_def_id = crate::rust_to_vir_base::def_id_of_vir_path(trait_path);
                    let assoc_item = state.tcx.associated_items(trait_def_id)
                          .find_by_name_and_kinds(state.tcx, rustc_span::symbol::Ident::from_str(&name),
                            &[rustc_middle::ty::AssocKind::Type], trait_def_id).unwrap();
                    let projection = Projection {
                        def_id: assoc_item.def_id,
                        args: trait_typ_args.clone(),
                    };

                    Ok(state.fresh_typ_with_info(Info::Projection(projection)))
                }
                _ => Ok(t.clone()),
            }
        }).unwrap()
    }

    /// Same as above, but if the root of the given type is a Projection,
    /// it returns a 'ProjectionOrTyp::Projection' rather than making an inference var.
    pub(crate) fn normalize_typ_or_proj(&mut self, typ: &Typ) -> ProjectionOrTyp {
        match &**typ {
            TypX::Projection { trait_typ_args, trait_path, name } => {
                let mut ts = vec![];
                for t in trait_typ_args.iter() {
                    ts.push(self.normalize_typ(t));
                }
                let trait_def_id = crate::rust_to_vir_base::def_id_of_vir_path(trait_path);
                let assoc_item = self.tcx.associated_items(trait_def_id)
                      .find_by_name_and_kinds(self.tcx, rustc_span::symbol::Ident::from_str(&name),
                        &[rustc_middle::ty::AssocKind::Type], trait_def_id).unwrap();
                ProjectionOrTyp::Projection(Projection {
                    def_id: assoc_item.def_id,
                    args: Arc::new(ts),
                })
            }
            _ => {
                ProjectionOrTyp::Typ(self.normalize_typ(typ))
            }
        }
    }

    /////////////////////////////////////////////////////////////////////
    ///////// Attempt to solve projections

    fn reduce_node_as_much_as_possible(&mut self, node: NodeClass) -> Result<(), VirErr> {
        // TODO need a better approach here

        let mut reachable = vec![node];
        let mut is_in_reachable = HashSet::<NodeClass>::new();
        is_in_reachable.insert(node);

        let mut idx = 0;
        while idx < reachable.len() {
            let n = reachable[idx];
            idx += 1;

            let typs: &[Typ] = match &self.unifier[n].info {
                Info::Unknown => &[],
                Info::UnknownInteger => &[],
                Info::Projection(projection) => &projection.args,
                Info::Known(t) => &[t.clone()],
            };
            for t in typs.iter() {
                vir::ast_visitor::typ_visitor_check(t, &mut |t| {
                    if let TypX::UnificationVar(v) = &**t {
                        let n = self.unifier.get_class(*v);
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
            if matches!(&self.unifier[node].info, Info::Projection(_)) {
                self.reduce_one_node(node)?;
            }
        }

        Ok(())

        /*
                let new_info = match self.reduce_projection(&projection.clone()) {
                    ProjectionOrTyp::Projection(new_projection) => Info::Projection(new_projection),
                    ProjectionOrTyp::Typ(typ) => Info::Known(typ),
                };
                self.unifier.info[node] = new_info;
            }
            _ => { }
        }
        */
    }

    fn reduce_one_node(&mut self, node: NodeClass) -> Result<(), VirErr> {
        if let Info::Projection(projection) = &self.unifier[node].info {
            let projection_or_typ_opt = self.reduce_projection_once(&projection.clone())?;
            if let Some((projection_or_typ, unifs)) = projection_or_typ_opt {
                self.unifier[node].info = match projection_or_typ {
                    ProjectionOrTyp::Projection(projection) => Info::Projection(projection),
                    ProjectionOrTyp::Typ(t) => {
                        match &*t {
                            TypX::UnificationVar(_v) => todo!(),
                            _ => Info::Known(t),
                        }
                    }
                };
                for (t1, t2) in unifs.unifications.iter() {
                    self.expect_exact(t1, t2)?;
                }
            }
        }
        Ok(())
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
        (Info::UnknownInteger, Info::UnknownInteger) => (Info::UnknownInteger, None),
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
        (Info::UnknownInteger, Info::Known(t))
        | (Info::Known(t), Info::UnknownInteger)
        => { 
            if is_definitely_integer_type(t) {
                (Info::Known(t.clone()), None)
            } else {
                todo!();
            }
        }
        (Info::Projection(_), _) => todo!(),
        (_, Info::Projection(_)) => todo!(),
    }
}

fn is_definitely_integer_type(t: &Typ) -> bool {
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
