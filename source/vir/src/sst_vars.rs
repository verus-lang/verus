use crate::ast::{BinaryOp, Typ, UnaryOp, UnaryOpr, VarIdent};
use crate::def::Spanned;
use crate::messages::Span;
use crate::sst::{Dest, Exp, ExpX, LocalDecl, LocalDeclKind, Pars, Stm, StmX, Stms, UniqueIdent};
use crate::sst_visitor::exp_visitor_check;
use air::ast::{ExprX, StmtX};
use air::scope_map::ScopeMap;
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

pub(crate) fn get_loc_var_typ(exp: &Exp) -> (UniqueIdent, Typ, bool) {
    match &exp.x {
        ExpX::Unary(UnaryOp::MutRefCurrent, inner) => match &inner.x {
            ExpX::VarLoc(x) => (x.clone(), inner.typ.clone(), true),
            _ => get_loc_var_typ(inner),
        },
        ExpX::Loc(x) => get_loc_var_typ(x),
        ExpX::UnaryOpr(UnaryOpr::Field { .. }, x) => get_loc_var_typ(x),
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), x) => get_loc_var_typ(x),
        ExpX::Binary(BinaryOp::Index(..), x, _idx) => get_loc_var_typ(x),
        ExpX::VarLoc(x) => (x.clone(), exp.typ.clone(), false),
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
        StmX::Call { args, dest, .. } => {
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
            stm.clone()
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
        StmX::Call { dest, .. } => {
            if let Some(Dest { is_init: false, dest }) = dest {
                mutations.insert(dest);
            }
            stm.clone()
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
    pub vars: IndexMap<VarIdent, (Typ, HavocVar)>,
}

/// Represents, for a given local, the set of sublocations that need havocing
/// At present, the granularity is only
/// "all" or "just the 'current' field of a mutable reference",
/// but in principle we could track individual fields of a tuple/struct.
#[derive(Clone, Debug, ToDebugSNode, Copy)]
pub enum HavocVar {
    All,
    Current,
}

impl HavocSet {
    fn new() -> Self {
        HavocSet { vars: IndexMap::new() }
    }

    fn insert(&mut self, loc: &Exp) {
        let (ident, typ, mut_ref_cur) = get_loc_var_typ(loc);

        let hvar = if mut_ref_cur { HavocVar::Current } else { HavocVar::All };

        match self.vars.get(&ident) {
            Some((typ, h2)) => {
                self.vars.insert(ident, (typ.clone(), h2.join(&hvar)));
            }
            None => {
                self.vars.insert(ident, (typ, hvar));
            }
        }
    }

    /// Merge other into self
    fn merge_with(&mut self, other: &Self) {
        for (ident, (typ, hvar)) in other.vars.iter() {
            match self.vars.get(ident) {
                Some((typ, h2)) => {
                    self.vars.insert(ident.clone(), (typ.clone(), h2.join(hvar)));
                }
                None => {
                    self.vars.insert(ident.clone(), (typ.clone(), hvar.clone()));
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
        for (var, (typ, havoc_var)) in self.vars.iter() {
            havoc_var.emit_havoc(ctx, var, typ, snapshot_name, stmts);
        }
    }
}

impl HavocVar {
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (HavocVar::Current, HavocVar::Current) => HavocVar::Current,
            _ => HavocVar::All,
        }
    }

    fn emit_havoc(
        &self,
        ctx: &crate::context::Ctx,
        var: &VarIdent,
        typ: &Typ,
        snapshot_name: &str,
        stmts: &mut Vec<air::ast::Stmt>,
    ) {
        let uid = crate::def::suffix_local_unique_id(&var);
        stmts.push(Arc::new(StmtX::Havoc(uid.clone())));

        let typ_inv = crate::sst_to_air::typ_invariant(ctx, typ, &air::ast_util::ident_var(&uid));
        if let Some(expr) = typ_inv {
            stmts.push(Arc::new(StmtX::Assume(expr)));
        }

        match self {
            HavocVar::All => {}
            HavocVar::Current => {
                // If only the 'current' is havoc'ed, we need to preserve the future:
                let old_var =
                    Arc::new(ExprX::Old(crate::def::snapshot_ident(snapshot_name), uid.clone()));
                let new_var = air::ast_util::string_var(&uid);
                let future = Arc::new(crate::def::MUT_REF_FUTURE.to_string());
                let old_future = Arc::new(ExprX::Apply(future.clone(), Arc::new(vec![old_var])));
                let new_future = Arc::new(ExprX::Apply(future, Arc::new(vec![new_var])));
                let eq = Arc::new(ExprX::Binary(air::ast::BinaryOp::Eq, old_future, new_future));
                stmts.push(Arc::new(StmtX::Assume(eq)));
            }
        }
    }
}
