use crate::ast::{FieldOpr, Typ, UnaryOp, UnaryOpr, VarIdent, TypX};
use crate::def::Spanned;
use crate::messages::Span;
use crate::sst::{
    BinaryOp, Dest, Exp, ExpX, LocalDecl, LocalDeclKind, Pars, Stm, StmX, Stms, UniqueIdent,
};
use crate::sst_to_air::{try_unbox, apply_field};
use crate::poly::typ_is_poly;
use crate::sst_visitor::exp_visitor_check;
use air::ast::{ExprX, Ident, StmtX};
use air::scope_map::ScopeMap;
use indexmap::map::Entry;
use indexmap::{IndexMap, IndexSet};
use std::collections::HashMap;
use std::sync::Arc;
use vir_macros::ToDebugSNode;

fn to_ident_set(input: &IndexSet<UniqueIdent>) -> IndexSet<VarIdent> {
    let mut output = IndexSet::new();
    for item in input {
        output.insert(item.clone());
    }
    output
}

// Compute:
// - which variables have definitely been assigned to up to each statement
// - which variables have been modified within each statement
pub type AssignMap = IndexMap<*const Spanned<StmX>, IndexSet<VarIdent>>;

pub(crate) fn get_loc_var(exp: &Exp) -> UniqueIdent {
    match &exp.x {
        ExpX::Loc(x) => get_loc_var(x),
        ExpX::Unary(UnaryOp::MutRefCurrent, x) => get_loc_var(x),
        ExpX::UnaryOpr(UnaryOpr::Field { .. }, x) => get_loc_var(x),
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), x) => get_loc_var(x),
        ExpX::Binary(BinaryOp::Index(..), x, _idx) => get_loc_var(x),
        ExpX::VarLoc(x) => x.clone(),
        _ => panic!("lhs {:?} unsupported", exp),
    }
}

/// If this Stm node performs a (non-init) assignment, add it to the map.
/// Shallow: does not recurse into sub-nodes.
pub(crate) fn stm_get_mutations_shallow(stm: &Stm, m: &mut HashMap<VarIdent, Span>) {
    // TODO: checking args can be removed after new-mut-ref is permanent
    match &stm.x {
        StmX::Call { args, .. } => {
            for arg in args.iter() {
                if let ExpX::Loc(_) = &arg.x {
                    let v = get_loc_var(arg);
                    m.insert(v, arg.span.clone());
                }
            }
        }
        _ => {}
    }

    match &stm.x {
        StmX::Call { dest: Some(dest), .. } | StmX::Assign { lhs: dest, .. } => {
            let Dest { dest, is_init } = dest;
            if !*is_init {
                let v = get_loc_var(dest);
                m.insert(v, stm.span.clone());
            }
        }
        StmX::Call { dest: None, .. }
        | StmX::Assert(..)
        | StmX::AssertBitVector { .. }
        | StmX::AssertQuery { .. }
        | StmX::AssertCompute(..)
        | StmX::Assume(..)
        | StmX::Fuel(..)
        | StmX::RevealString(..)
        | StmX::DeadEnd(..)
        | StmX::Return { .. }
        | StmX::BreakOrContinue { .. }
        | StmX::If(..)
        | StmX::Loop { .. }
        | StmX::OpenInvariant(..)
        | StmX::ClosureInner { .. }
        | StmX::Air(..)
        | StmX::Block(..) => {}
    }
}

/// If there's an assignment associated with this Stm (shallowly), return it.
/// There can be at most one (in new-mut-ref, they no longer appear in calls)
pub(crate) fn stm_get_assignment_shallow(stm: &Stm) -> Option<&Exp> {
    match &stm.x {
        StmX::Call { dest: Some(dest), .. } | StmX::Assign { lhs: dest, .. } => {
            let Dest { dest, is_init: _ } = dest;
            Some(dest)
        }
        StmX::Call { dest: None, .. }
        | StmX::Assert(..)
        | StmX::AssertBitVector { .. }
        | StmX::AssertQuery { .. }
        | StmX::AssertCompute(..)
        | StmX::Assume(..)
        | StmX::Fuel(..)
        | StmX::RevealString(..)
        | StmX::DeadEnd(..)
        | StmX::Return { .. }
        | StmX::BreakOrContinue { .. }
        | StmX::If(..)
        | StmX::Loop { .. }
        | StmX::OpenInvariant(..)
        | StmX::ClosureInner { .. }
        | StmX::Air(..)
        | StmX::Block(..) => None,
    }
}

/// Find any assignment that overlaps the given loc if it exists
pub(crate) fn find_overlapping_assignment(stm: &Stm, loc: &Exp) -> Option<Span> {
    crate::sst_visitor::stm_visitor_check(&stm, &mut |stm| match stm_get_assignment_shallow(stm) {
        Some(assigned_loc) if locs_may_overlap(assigned_loc, loc) => Err(stm.span.clone()),
        _ => Ok(()),
    })
    .err()
}

pub(crate) fn locs_may_overlap(loc1: &Exp, loc2: &Exp) -> bool {
    let loc1 = match &loc1.x {
        ExpX::Loc(loc1) => loc1,
        _ => loc1,
    };
    let loc2 = match &loc2.x {
        ExpX::Loc(loc2) => loc2,
        _ => loc2,
    };

    fn get_depth(e: &Exp) -> (usize, &VarIdent) {
        let mut e = e;
        let mut d = 0;
        loop {
            match &e.x {
                ExpX::Var(x) | ExpX::VarLoc(x) => {
                    return (d, x);
                }
                ExpX::Unary(UnaryOp::MutRefCurrent, x) => {
                    e = x;
                }
                ExpX::UnaryOpr(UnaryOpr::Field { .. }, x) => {
                    e = x;
                }
                ExpX::Binary(BinaryOp::Index(..), x, _idx) => {
                    e = x;
                }
                _ => panic!("lhs {:?} unsupported", e),
            }
            d += 1;
        }
    }

    fn skip(e: &Exp, d: usize) -> &Exp {
        let mut e = e;
        for _i in 0..d {
            match &e.x {
                ExpX::Unary(UnaryOp::MutRefCurrent, x) => {
                    e = x;
                }
                ExpX::UnaryOpr(UnaryOpr::Field { .. }, x) => {
                    e = x;
                }
                ExpX::Binary(BinaryOp::Index(..), x, _idx) => {
                    e = x;
                }
                _ => unreachable!(),
            }
        }
        e
    }

    let (d1, x1) = get_depth(loc1);
    let (d2, x2) = get_depth(loc2);
    if x1 != x2 {
        return false;
    }

    let mut loc1 = loc1;
    let mut loc2 = loc2;
    if d1 > d2 {
        loc1 = skip(loc1, d1 - d2);
    } else if d2 > d1 {
        loc2 = skip(loc2, d2 - d1);
    }

    loop {
        match (&loc1.x, &loc2.x) {
            (ExpX::Unary(UnaryOp::MutRefCurrent, x1), ExpX::Unary(UnaryOp::MutRefCurrent, x2)) => {
                loc1 = x1;
                loc2 = x2;
            }
            (
                ExpX::UnaryOpr(UnaryOpr::Field(FieldOpr { variant: v1, field: i1, .. }), x1),
                ExpX::UnaryOpr(UnaryOpr::Field(FieldOpr { variant: v2, field: i2, .. }), x2),
            ) => {
                if !(v1 == v2 && i1 == i2) {
                    return false;
                }
                loc1 = x1;
                loc2 = x2;
            }
            (
                ExpX::Binary(BinaryOp::Index(..), x1, _idx1),
                ExpX::Binary(BinaryOp::Index(..), x2, _idx2),
            ) => {
                loc1 = x1;
                loc2 = x2;
            }
            (ExpX::Var(_) | ExpX::VarLoc(_), ExpX::Var(_) | ExpX::VarLoc(_)) => {
                return true;
            }
            _ => panic!("locs_may_overlap failed"),
        }
    }
}

/// Fill in the AssignMap and add var information to all loops in the Stm
pub(crate) fn compute_assign_info(
    assign_map: &mut AssignMap,
    params: &Pars,
    local_decls: &[LocalDecl],
    stm: &Stm,
) -> Stm {
    let mut declared: IndexMap<UniqueIdent, Typ> = IndexMap::new();
    let mut assigned: IndexSet<UniqueIdent> = IndexSet::new();

    for param in params.iter() {
        // REVIEW: isn't this redundant with below?
        declared.insert(param.x.name.clone(), param.x.typ.clone());
        assigned.insert(param.x.name.clone());
    }

    for decl in local_decls.iter() {
        declared.insert(decl.ident.clone(), decl.typ.clone());
    }

    // REVIEW: This is needed because `stm_assign` doesn't otherwise pick up that these
    // decls get initialized; are there any other decls like that?
    for decl in local_decls.iter() {
        if matches!(decl.kind, LocalDeclKind::ExecClosureParam { .. }) {
            assigned.insert(decl.ident.clone());
        }
    }

    let mut _modified = HavocSet::new();
    let stm = stm_assign(assign_map, &declared, &mut assigned, &mut _modified, stm);

    // Second pass:

    let mut param_typs = vec![];
    for decl in local_decls.iter() {
        if matches!(decl.kind, LocalDeclKind::ExecClosureParam { .. } | LocalDeclKind::Param { .. })
        {
            param_typs.push((decl.ident.clone(), decl.typ.clone()));
        }
    }

    stm_mutations(&param_typs, &mut HavocSet::new(), &stm)
}

/// Fill in `typ_inv_vars` and `modified_vars` fields on all `Loop` nodes.
fn stm_assign(
    assign_map: &mut AssignMap,
    declared: &IndexMap<UniqueIdent, Typ>,
    assigned: &mut IndexSet<UniqueIdent>,
    modified: &mut HavocSet,
    stm: &Stm,
) -> Stm {
    let result = match &stm.x {
        StmX::Call {
            fun,
            resolved_method,
            mode,
            is_trait_default,
            typ_args,
            args,
            split,
            dest,
            assert_id,
            body,
        } => {
            if let Some(dest) = dest {
                let var: UniqueIdent = get_loc_var(&dest.dest);
                assigned.insert(var.clone());
                if !dest.is_init {
                    modified.insert(&dest.dest);
                }
            }
            for arg in args.iter() {
                // TODO: checking args can be removed after new-mut-ref is permanent

                // Search for any ExpX::Loc in the arg, which might be modified.
                // Given current limitations, I think the only way this can happen
                // is if either
                //    arg.x = ExpX::Loc(loc)
                // or
                //    arg.x = UnaryOpr(Box, ExpX::Loc(loc))

                exp_visitor_check::<(), _>(arg, &mut ScopeMap::new(), &mut |e, _| {
                    if let ExpX::Loc(loc) = &e.x {
                        modified.insert(loc);
                    }
                    Ok(())
                })
                .unwrap();
            }

            let body = body
                .as_ref()
                .map(|body_stm| stm_assign(assign_map, declared, assigned, modified, body_stm));

            stm.new_x(StmX::Call {
                fun: fun.clone(),
                resolved_method: resolved_method.clone(),
                mode: mode.clone(),
                is_trait_default: is_trait_default.clone(),
                typ_args: typ_args.clone(),
                args: args.clone(),
                split: split.clone(),
                dest: dest.clone(),
                assert_id: assert_id.clone(),
                body,
            })
        }
        StmX::AssertQuery { mode, typ_inv_exps, typ_inv_vars, body } => {
            assert!(typ_inv_vars.len() == 0);
            let vars = crate::sst_util::free_vars_exps(typ_inv_exps);
            let mode = *mode;
            let typ_inv_exps = Arc::new(vec![]);
            let typ_inv_vars = Arc::new(
                declared.clone().into_iter().filter(|(x, _)| vars.contains_key(x)).collect(),
            );
            let body = body.clone();
            stm.new_x(StmX::AssertQuery { mode, typ_inv_exps, typ_inv_vars, body })
        }
        StmX::Assert(..)
        | StmX::AssertBitVector { .. }
        | StmX::AssertCompute(..)
        | StmX::Assume(_)
        | StmX::Fuel(..)
        | StmX::RevealString(_)
        | StmX::Return { .. }
        | StmX::Air(_) => stm.clone(),
        StmX::Assign { lhs: Dest { dest, is_init }, rhs: _ } => {
            let var = get_loc_var(dest);
            assigned.insert(var.clone());
            if !is_init {
                modified.insert(dest);
            }
            stm.clone()
        }
        StmX::DeadEnd(s) => {
            let s = stm_assign(assign_map, declared, assigned, modified, s);
            Spanned::new(stm.span.clone(), StmX::DeadEnd(s))
        }
        StmX::BreakOrContinue { label: _, is_break: _ } => stm.clone(),
        StmX::ClosureInner { body, typ_inv_vars } => {
            let pre_modified = modified.clone();
            let pre_assigned = assigned.clone();
            let body = stm_assign(assign_map, declared, assigned, modified, body);
            *assigned = pre_assigned;
            *modified = pre_modified;

            Spanned::new(
                stm.span.clone(),
                StmX::ClosureInner { body, typ_inv_vars: typ_inv_vars.clone() },
            )
        }
        StmX::If(cond, lhs, rhs) => {
            let mut pre_assigned = assigned.clone();

            let lhs = stm_assign(assign_map, declared, assigned, modified, lhs);
            let lhs_assigned = assigned.clone();
            *assigned = pre_assigned.clone();

            let rhs = rhs.as_ref().map(|s| stm_assign(assign_map, declared, assigned, modified, s));
            let rhs_assigned = &assigned;

            for x in declared.keys() {
                if lhs_assigned.contains(x) && rhs_assigned.contains(x) && !pre_assigned.contains(x)
                {
                    pre_assigned.insert(x.clone());
                }
            }

            *assigned = pre_assigned;
            Spanned::new(stm.span.clone(), StmX::If(cond.clone(), lhs, rhs))
        }
        StmX::Loop {
            loop_isolation,
            is_for_loop,
            id,
            label,
            cond,
            body,
            invs,
            decrease,
            typ_inv_vars,
            modified_vars,
            au_branch_bool,
            pre_modified_params,
        } => {
            let mut inner_modified = HavocSet::new();
            let cond = if let Some((cond_stm, cond_exp)) = cond {
                let cond_stm =
                    stm_assign(assign_map, declared, assigned, &mut inner_modified, cond_stm);
                Some((cond_stm, cond_exp.clone()))
            } else {
                None
            };

            let pre_assigned = assigned.clone();
            let body = stm_assign(assign_map, declared, assigned, &mut inner_modified, body);
            *assigned = pre_assigned;

            assert!(modified_vars.is_none());

            let inner_modified = inner_modified.filter_by_declared(declared);
            modified.merge_with(&inner_modified);

            assert!(typ_inv_vars.len() == 0);
            let mut typ_inv_vars: Vec<(UniqueIdent, Typ)> = Vec::new();
            for x in assigned.iter() {
                typ_inv_vars.push((x.clone(), declared[x].clone()));
            }
            let loop_x = StmX::Loop {
                loop_isolation: *loop_isolation,
                is_for_loop: *is_for_loop,
                id: *id,
                label: label.clone(),
                cond,
                body,
                invs: invs.clone(),
                decrease: decrease.clone(),
                typ_inv_vars: Arc::new(typ_inv_vars),
                modified_vars: Some(Arc::new(inner_modified)),
                au_branch_bool: au_branch_bool.clone(),
                pre_modified_params: pre_modified_params.clone(),
            };
            Spanned::new(stm.span.clone(), loop_x)
        }
        StmX::OpenInvariant(body_stm) => {
            let body_stm = stm_assign(assign_map, declared, assigned, modified, body_stm);
            Spanned::new(stm.span.clone(), StmX::OpenInvariant(body_stm))
        }
        StmX::Block(stms) => {
            let mut pre_assigned = assigned.clone();
            let stms = stms_assign(assign_map, declared, assigned, modified, stms);
            for x in declared.keys() {
                if assigned.contains(x) && !pre_assigned.contains(x) {
                    pre_assigned.insert(x.clone());
                }
            }
            *assigned = pre_assigned;
            Spanned::new(stm.span.clone(), StmX::Block(stms))
        }
    };

    assign_map.insert(Arc::as_ptr(&result), to_ident_set(assigned));
    result
}

fn stms_assign(
    assign_map: &mut AssignMap,
    declared: &IndexMap<UniqueIdent, Typ>,
    assigned: &mut IndexSet<UniqueIdent>,
    modified: &mut HavocSet,
    stms: &Stms,
) -> Stms {
    let stms: Vec<Stm> =
        stms.iter().map(|s| stm_assign(assign_map, declared, assigned, modified, s)).collect();
    Arc::new(stms)
}

/// Fill in `pre_modified_params` on all Loop nodes.
/// This requires `modified_vars` to be filled in already
/// (i.e., `stm_assign` needs to be called first).
fn stm_mutations(param_typs: &[(VarIdent, Typ)], mutations: &mut HavocSet, stm: &Stm) -> Stm {
    match &stm.x {
        StmX::Assert(..)
        | StmX::AssertBitVector { .. }
        | StmX::AssertCompute(..)
        | StmX::Assume(_)
        | StmX::Fuel(..)
        | StmX::RevealString(_)
        | StmX::Return { .. }
        | StmX::BreakOrContinue { .. }
        | StmX::Air(_) => stm.clone(),
        StmX::Call {
            fun,
            resolved_method,
            mode,
            is_trait_default,
            typ_args,
            args,
            split,
            dest,
            assert_id,
            body,
        } => {
            if let Some(Dest { is_init: false, dest }) = dest {
                mutations.insert(dest);
            }

            let body = body.as_ref().map(|stm| stm_mutations(param_typs, mutations, stm));

            stm.new_x(StmX::Call {
                fun: fun.clone(),
                resolved_method: resolved_method.clone(),
                mode: mode.clone(),
                is_trait_default: is_trait_default.clone(),
                typ_args: typ_args.clone(),
                args: args.clone(),
                split: split.clone(),
                dest: dest.clone(),
                assert_id: assert_id.clone(),
                body,
            })
        }
        StmX::Assign { lhs, rhs: _ } => {
            if let Dest { is_init: false, dest } = lhs {
                mutations.insert(dest);
            }
            stm.clone()
        }
        StmX::AssertQuery { mode, typ_inv_exps, typ_inv_vars, body } => {
            let body = stm_mutations(param_typs, mutations, body);
            stm.new_x(StmX::AssertQuery {
                mode: *mode,
                typ_inv_exps: typ_inv_exps.clone(),
                typ_inv_vars: typ_inv_vars.clone(),
                body: body,
            })
        }
        StmX::DeadEnd(body) => {
            let mut m = mutations.clone();
            let body = stm_mutations(param_typs, &mut m, body);
            stm.new_x(StmX::DeadEnd(body))
        }
        StmX::If(cond, thn, None) => {
            let thn = stm_mutations(param_typs, mutations, thn);
            stm.new_x(StmX::If(cond.clone(), thn, None))
        }
        StmX::If(cond, thn, Some(els)) => {
            let mut thn_m = mutations.clone();
            let thn = stm_mutations(param_typs, &mut thn_m, thn);
            let els = stm_mutations(param_typs, mutations, els);
            mutations.merge_with(&thn_m);
            stm.new_x(StmX::If(cond.clone(), thn, Some(els)))
        }
        StmX::Loop {
            loop_isolation,
            is_for_loop,
            id,
            label,
            cond,
            body,
            invs,
            decrease,
            typ_inv_vars,
            modified_vars,
            pre_modified_params,
            au_branch_bool,
        } => {
            assert!(pre_modified_params.is_none());

            mutations.merge_with(&modified_vars.as_ref().unwrap());

            let cond = match cond {
                None => None,
                Some((cond_stm, cond_exp)) => {
                    let cond_stm = stm_mutations(param_typs, mutations, cond_stm);
                    Some((cond_stm, cond_exp.clone()))
                }
            };
            let body = stm_mutations(param_typs, mutations, body);

            let pre_modified_params = mutations.filter_by_params(param_typs);

            let loopx = StmX::Loop {
                loop_isolation: *loop_isolation,
                is_for_loop: *is_for_loop,
                id: *id,
                label: label.clone(),
                cond: cond,
                body: body,
                invs: invs.clone(),
                decrease: decrease.clone(),
                typ_inv_vars: typ_inv_vars.clone(),
                modified_vars: modified_vars.clone(),
                pre_modified_params: Some(Arc::new(pre_modified_params)),
                au_branch_bool: au_branch_bool.clone(),
            };
            stm.new_x(loopx)
        }
        StmX::OpenInvariant(body) => {
            let body = stm_mutations(param_typs, mutations, body);
            stm.new_x(StmX::OpenInvariant(body))
        }
        StmX::ClosureInner { body, typ_inv_vars } => {
            let body = stm_mutations(param_typs, mutations, body);
            stm.new_x(StmX::ClosureInner { body, typ_inv_vars: typ_inv_vars.clone() })
        }
        StmX::Block(stms) => {
            let mut v = vec![];
            for stm in stms.iter() {
                v.push(stm_mutations(param_typs, mutations, stm));
            }
            stm.new_x(StmX::Block(Arc::new(v)))
        }
    }
}

/// Represents a set of locations that need to be havoc'ed
#[derive(Clone, Debug, ToDebugSNode)]
pub struct HavocSet {
    pub vars: IndexMap<VarIdent, SublocationTree>,
}

/// Represents, for a given local, the set of sublocations that need havocing
#[derive(Clone, Debug, ToDebugSNode)]
pub struct SublocationTree {
    local: VarIdent,
    root: SublocationNode,
}

#[derive(Clone, Debug, ToDebugSNode)]
pub struct SublocationNode {
    typ: Typ,
    /// None means havoc this entire location
    children: Option<Vec<(ProjectionKind, SublocationNode)>>,
}

/// A single sublocation
#[derive(Clone, Debug)]
pub struct Sublocation {
    local: VarIdent,
    local_typ: Typ,
    projections: Vec<Projection>,
}

#[derive(Clone, Debug, ToDebugSNode)]
struct Projection {
    typ: Typ,
    kind: ProjectionKind,
}

#[derive(Clone, Debug, ToDebugSNode)]
enum ProjectionKind {
    MutRefCurrent,
    Field(FieldOpr),
}

impl HavocSet {
    fn new() -> Self {
        HavocSet { vars: IndexMap::new() }
    }

    fn insert(&mut self, loc: &Exp) {
        let subloc = loc_to_subloc(loc).0;

        match self.vars.entry(subloc.local.clone()) {
            Entry::Occupied(mut entry) => {
                entry.get_mut().merge_subloc(&subloc);
            }
            Entry::Vacant(entry) => {
                entry.insert(SublocationTree::from_subloc(&subloc));
            }
        }
    }

    /// Merge other into self
    fn merge_with(&mut self, other: &Self) {
        for (ident, other_tree) in other.vars.iter() {
            match self.vars.entry(ident.clone()) {
                Entry::Occupied(mut entry) => {
                    entry.get_mut().merge_tree(other_tree);
                }
                Entry::Vacant(entry) => {
                    entry.insert(other_tree.clone());
                }
            }
        }
    }

    fn filter_by_declared(&self, declared: &IndexMap<UniqueIdent, Typ>) -> HavocSet {
        let mut result = HavocSet { vars: IndexMap::new() };
        for (ident, entry) in self.vars.iter() {
            if declared.contains_key(ident) {
                result.vars.insert(ident.clone(), entry.clone());
            }
        }
        result
    }

    fn filter_by_params(&self, param_typs: &[(VarIdent, Typ)]) -> HavocSet {
        let mut result = HavocSet { vars: IndexMap::new() };
        for (ident, _typ) in param_typs.iter() {
            if let Some(entry) = self.vars.get(ident) {
                result.vars.insert(ident.clone(), entry.clone());
            }
        }
        result
    }

    pub(crate) fn emit_havocs(
        &self,
        ctx: &crate::context::Ctx,
        snapshot_name: &str,
        stmts: &mut Vec<air::ast::Stmt>,
    ) {
        for (_var, tree) in self.vars.iter() {
            tree.emit_havoc(ctx, snapshot_name, stmts);
        }
    }
}

fn loc_to_subloc(exp: &Exp) -> (Sublocation, bool) {
    match &exp.x {
        ExpX::Loc(e) => loc_to_subloc(e),
        ExpX::VarLoc(x) => (
            Sublocation { local: x.clone(), local_typ: exp.typ.clone(), projections: vec![] },
            false,
        ),
        ExpX::Unary(UnaryOp::MutRefCurrent, e) => {
            let (mut subloc, done) = loc_to_subloc(e);
            if !done {
                subloc
                    .projections
                    .push(Projection { typ: exp.typ.clone(), kind: ProjectionKind::MutRefCurrent });
            }
            (subloc, done)
        }
        ExpX::UnaryOpr(UnaryOpr::Field(field_opr), e) => {
            let (mut subloc, done) = loc_to_subloc(e);
            if !done {
                subloc.projections.push(Projection {
                    typ: exp.typ.clone(),
                    kind: ProjectionKind::Field(field_opr.clone()),
                });
            }
            (subloc, done)
        }
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), e) => loc_to_subloc(e),
        ExpX::Binary(BinaryOp::Index(..), e, _idx) => {
            let (subloc, _) = loc_to_subloc(e);
            (subloc, true)
        }
        _ => {
            panic!("loc_to_subloc got unexpected exp: {:?}", exp);
        }
    }
}

fn equiv_proj_kind(a: &ProjectionKind, b: &ProjectionKind) -> bool {
    match (a, b) {
        (ProjectionKind::MutRefCurrent, ProjectionKind::MutRefCurrent) => true,
        (ProjectionKind::Field(f1), ProjectionKind::Field(f2)) => {
            f1.variant == f2.variant && f1.field == f2.field
        }

        (ProjectionKind::MutRefCurrent, _) | (ProjectionKind::Field(_), _) => false,
    }
}

impl ProjectionKind {
    fn is_field(&self, variant: &Ident, field: &Ident) -> bool {
        match self {
            ProjectionKind::MutRefCurrent => false,
            ProjectionKind::Field(opr) => &opr.variant == variant && &opr.field == field,
        }
    }
}

impl SublocationTree {
    fn from_subloc(subloc: &Sublocation) -> SublocationTree {
        let mut tree = SublocationTree {
            local: subloc.local.clone(),
            root: SublocationNode { typ: subloc.local_typ.clone(), children: None },
        };
        let mut children_ref = &mut tree.root.children;
        for p in subloc.projections.iter() {
            *children_ref = Some(vec![(
                p.kind.clone(),
                SublocationNode { typ: p.typ.clone(), children: None },
            )]);
            children_ref = &mut children_ref.as_mut().unwrap()[0].1.children;
        }
        tree
    }

    fn merge_subloc(&mut self, subloc: &Sublocation) {
        let mut children_ref = &mut self.root.children;
        let mut fresh_path = false;
        for p in subloc.projections.iter() {
            match children_ref {
                Some(children_vec_ref) => {
                    let idx = children_vec_ref
                        .iter()
                        .position(|(kind, _)| equiv_proj_kind(&p.kind, kind));
                    match idx {
                        Some(idx) => {
                            children_ref = &mut children_vec_ref[idx].1.children;
                        }
                        None => {
                            let r = children_vec_ref.push_mut((
                                p.kind.clone(),
                                SublocationNode { typ: p.typ.clone(), children: None },
                            ));
                            children_ref = &mut r.1.children;
                            fresh_path = true;
                        }
                    }
                }
                None => {
                    if fresh_path {
                        *children_ref = Some(vec![(
                            p.kind.clone(),
                            SublocationNode { typ: p.typ.clone(), children: None },
                        )]);
                        children_ref = &mut children_ref.as_mut().unwrap()[0].1.children;
                    } else {
                        return;
                    }
                }
            }
        }
        *children_ref = None;
    }

    fn merge_tree(&mut self, other: &Self) {
        Self::merge_children_lists(&mut self.root.children, &other.root.children);
    }

    fn merge_children_lists(
        a: &mut Option<Vec<(ProjectionKind, SublocationNode)>>,
        b: &Option<Vec<(ProjectionKind, SublocationNode)>>,
    ) {
        let Some(children1) = a else {
            return;
        };
        let Some(children2) = b else {
            *a = None;
            return;
        };

        for (b_kind, b_node) in children2.iter() {
            let idx = children1.iter().position(|(kind, _)| equiv_proj_kind(&b_kind, kind));
            match idx {
                Some(idx) => {
                    Self::merge_children_lists(&mut children1[idx].1.children, &b_node.children);
                }
                None => {
                    children1.push((b_kind.clone(), b_node.clone()));
                }
            }
        }
    }

    fn emit_havoc(
        &self,
        ctx: &crate::context::Ctx,
        snapshot_name: &str,
        stmts: &mut Vec<air::ast::Stmt>,
    ) {
        let uid = crate::def::suffix_local_unique_id(&self.local);
        stmts.push(Arc::new(StmtX::Havoc(uid.clone())));

        let typ = &self.root.typ;
        let typ_inv = crate::sst_to_air::typ_invariant(ctx, typ, &air::ast_util::ident_var(&uid));
        if let Some(expr) = typ_inv {
            stmts.push(Arc::new(StmtX::Assume(expr)));
        }

        let old_var = Arc::new(ExprX::Old(crate::def::snapshot_ident(snapshot_name), uid.clone()));
        let new_var = air::ast_util::string_var(&uid);
        let mut equalities = vec![];
        Self::gather_preserved_locations(ctx, &self.root, &old_var, &new_var, &mut equalities);
        for (e1, e2) in equalities.into_iter() {
            let eq = Arc::new(ExprX::Binary(air::ast::BinaryOp::Eq, e1, e2));
            stmts.push(Arc::new(StmtX::Assume(eq)));
        }
    }

    fn gather_preserved_locations(
        ctx: &crate::context::Ctx,
        node: &SublocationNode,
        loc1: &air::ast::Expr,
        loc2: &air::ast::Expr,
        out: &mut Vec<(air::ast::Expr, air::ast::Expr)>,
    ) {
        let Some(children) = &node.children else {
            // everything is havoc'ed; nothing to preserve
            return;
        };

        match &children[0].0 {
            ProjectionKind::MutRefCurrent => {
                assert!(children.len() == 1);
                let future = Arc::new(crate::def::MUT_REF_FUTURE.to_string());
                let f1 = Arc::new(ExprX::Apply(future.clone(), Arc::new(vec![loc1.clone()])));
                let f2 = Arc::new(ExprX::Apply(future.clone(), Arc::new(vec![loc2.clone()])));
                out.push((f1, f2));

                let current = Arc::new(crate::def::MUT_REF_CURRENT.to_string());
                let c1 = Arc::new(ExprX::Apply(current.clone(), Arc::new(vec![loc1.clone()])));
                let c2 = Arc::new(ExprX::Apply(current.clone(), Arc::new(vec![loc2.clone()])));

                Self::gather_preserved_locations(ctx, &children[0].1, &c1, &c2, out);
            }
            ProjectionKind::Field(first_field_opr) => {
                let datatype = &ctx.datatype_map[&first_field_opr.datatype];
                if datatype.x.variants.len() > 1 {
                    // TODO: should handle enums too
                    return;
                }
                let variant = &datatype.x.variants[0];
                for field in variant.fields.iter() {
                    let mut f1 = loc1.clone();
                    let mut f2 = loc2.clone();
                    let mut base_typ = &node.typ;

                    if let TypX::Boxed(native_typ) = &*node.typ
                        && !typ_is_poly(ctx, native_typ)
                    {
                        f1 = try_unbox(ctx, f1, native_typ).expect("try_unbox");
                        f2 = try_unbox(ctx, f2, native_typ).expect("try_unbox");
                        base_typ = native_typ;
                    }

                    let f1 = apply_field(
                        ctx,
                        f1,
                        base_typ,
                        &datatype.x.name,
                        &variant.name,
                        &field.name,
                    );
                    let f2 = apply_field(
                        ctx,
                        f2,
                        base_typ,
                        &datatype.x.name,
                        &variant.name,
                        &field.name,
                    );

                    match children
                        .iter()
                        .position(|(kind, _)| kind.is_field(&variant.name, &field.name))
                    {
                        Some(idx) => {
                            Self::gather_preserved_locations(ctx, &children[idx].1, &f1, &f2, out);
                        }
                        None => {
                            out.push((f1, f2));
                        }
                    }
                }
            }
        }
    }
}
