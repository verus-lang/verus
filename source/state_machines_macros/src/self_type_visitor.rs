use crate::ast::{
    MonoidElt, ShardableType, SpecialOp, SplitKind, SubIdx, Transition, TransitionStmt, SM,
};
use crate::to_token_stream::get_self_ty_turbofish_path;
use syn_verus::punctuated::Punctuated;
use syn_verus::token;
use syn_verus::visit_mut;
use syn_verus::visit_mut::VisitMut;
use syn_verus::{Expr, Ident, Pat, Path, PathSegment, Type};

/// If the user ever uses 'Self' in a transition, then change it out for the explicit
/// self type so that it's safe to use these expressions and types in other places
/// outside the generated `State` impl.

pub fn replace_self_sm(sm: &mut SM) {
    let path = get_self_ty_turbofish_path(&*sm);
    for trans in sm.transitions.iter_mut() {
        match trans {
            Transition { name: _, kind: _, params, body } => {
                for param in params.iter_mut() {
                    replace_self_type(&mut param.ty, &path);
                }
                replace_self_ts(body, &path);
            }
        }
    }
    for field in sm.fields.iter_mut() {
        replace_self_shardable_type(&mut field.stype, &path);
    }
}

fn replace_self_shardable_type(stype: &mut ShardableType, path: &Path) {
    match stype {
        ShardableType::Variable(ty) => {
            replace_self_type(ty, path);
        }
        ShardableType::Constant(ty) => {
            replace_self_type(ty, path);
        }
        ShardableType::NotTokenized(ty) => {
            replace_self_type(ty, path);
        }
        ShardableType::Option(ty) => {
            replace_self_type(ty, path);
        }
        ShardableType::PersistentOption(ty) => {
            replace_self_type(ty, path);
        }
        ShardableType::Set(ty) => {
            replace_self_type(ty, path);
        }
        ShardableType::PersistentSet(ty) => {
            replace_self_type(ty, path);
        }
        ShardableType::Map(key, val) => {
            replace_self_type(key, path);
            replace_self_type(val, path);
        }
        ShardableType::PersistentMap(key, val) => {
            replace_self_type(key, path);
            replace_self_type(val, path);
        }
        ShardableType::Multiset(ty) => {
            replace_self_type(ty, path);
        }
        ShardableType::StorageOption(ty) => {
            replace_self_type(ty, path);
        }
        ShardableType::StorageMap(key, val) => {
            replace_self_type(key, path);
            replace_self_type(val, path);
        }
        ShardableType::Count => {}
        ShardableType::PersistentCount => {}
        ShardableType::Bool => {}
        ShardableType::PersistentBool => {}
    }
}

fn replace_self_ts(ts: &mut TransitionStmt, path: &Path) {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter_mut() {
                replace_self_ts(t, path);
            }
        }
        TransitionStmt::Split(_, split_kind, es) => {
            match split_kind {
                SplitKind::Let(pat, ty, _lk, e) => {
                    replace_self_pat(pat, path);
                    match ty {
                        None => {}
                        Some(ty) => replace_self_type(ty, path),
                    }
                    replace_self_expr(e, path);
                }
                SplitKind::If(cond) => {
                    replace_self_expr(cond, path);
                }
                SplitKind::Match(match_e, arms) => {
                    replace_self_expr(match_e, path);
                    for arm in arms.iter_mut() {
                        replace_self_pat(&mut arm.pat, path);
                        match &mut arm.guard {
                            Some((_, guard_e)) => {
                                replace_self_expr(&mut **guard_e, path);
                            }
                            None => {}
                        }
                    }
                }
                SplitKind::Special(_f, op, _proof, pat_opt) => {
                    replace_self_op(op, path);
                    match pat_opt {
                        None => {}
                        Some(pat) => {
                            replace_self_pat(pat, path);
                        }
                    }
                }
            }
            for e in es {
                replace_self_ts(e, path);
            }
        }
        TransitionStmt::Require(_, e) => {
            replace_self_expr(e, path);
        }
        TransitionStmt::Assert(_, e, _proof) => {
            replace_self_expr(e, path);
        }
        TransitionStmt::SubUpdate(_, _f, subs, e) => {
            for sub in subs {
                match sub {
                    SubIdx::Field(_ident) => {}
                    SubIdx::Idx(e) => {
                        replace_self_expr(e, path);
                    }
                }
            }
            replace_self_expr(e, path);
        }
        TransitionStmt::Update(_, _f, e) | TransitionStmt::Initialize(_, _f, e) => {
            replace_self_expr(e, path);
        }
        TransitionStmt::PostCondition(_, e) => {
            replace_self_expr(e, path);
        }
    }
}

fn replace_self_op(op: &mut SpecialOp, path: &Path) {
    match &mut op.elt {
        MonoidElt::True => {}
        MonoidElt::OptionSome(None) => {}
        MonoidElt::OptionSome(Some(e))
        | MonoidElt::SingletonMultiset(e)
        | MonoidElt::SingletonSet(e)
        | MonoidElt::General(e)
        | MonoidElt::SingletonKV(e, None) => {
            replace_self_expr(e, path);
        }
        MonoidElt::SingletonKV(e1, Some(e2)) => {
            replace_self_expr(e1, path);
            replace_self_expr(e2, path);
        }
    }
}

fn replace_self_expr(e: &mut Expr, subst_path: &Path) {
    let mut sv = SelfVisitor { subst_path };
    sv.visit_expr_mut(e);
}

fn replace_self_type(ty: &mut Type, subst_path: &Path) {
    let mut sv = SelfVisitor { subst_path };
    sv.visit_type_mut(ty);
}

fn replace_self_pat(p: &mut Pat, subst_path: &Path) {
    let mut sv = SelfVisitor { subst_path };
    sv.visit_pat_mut(p);
}

struct SelfVisitor<'a> {
    subst_path: &'a Path,
}

impl<'a> VisitMut for SelfVisitor<'a> {
    fn visit_path_mut(&mut self, path: &mut Path) {
        if path.leading_colon.is_none() && path.segments[0].ident.to_string() == "Self" {
            let orig_span = path.segments[0].ident.span();
            let mut segments = Punctuated::<PathSegment, token::Colon2>::new();
            for seg in self.subst_path.segments.iter() {
                let mut seg = seg.clone();
                seg.ident = Ident::new(&seg.ident.to_string(), orig_span);
                segments.push(seg);
            }
            for seg in path.segments.iter().skip(1) {
                segments.push(seg.clone());
            }
            path.segments = segments;
        }

        visit_mut::visit_path_mut(self, path)
    }
}
