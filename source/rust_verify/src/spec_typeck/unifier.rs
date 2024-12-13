use vir::ast::{Typ, TypX, VirErr, IntRange};
use super::State;
use std::sync::Arc;

#[derive(Clone)]
enum Info {
    Unknown,
    UnknownIntegerType,
    Known(Typ),
    Contradiction,
}

struct UFNode {
    parent: usize,
    rank: usize,
}

pub struct Unifier {
    uf_nodes: Vec<UFNode>,
    info: Vec<Info>,
    final_typs: Option<Vec<Option<Typ>>>,
}

enum UnifyError {
    Error,
}

impl Unifier {
    pub fn new() -> Self {
        Unifier {
            uf_nodes: vec![],
            info: vec![],
            final_typs: None,
        }
    }

    fn new_node(&mut self, info: Info) -> usize {
        assert!(self.final_typs.is_none());
        self.info.push(info);
        let me = self.uf_nodes.len();
        self.uf_nodes.push(UFNode { parent: me, rank: 0 });
        me
    }

    pub fn get_node(&mut self, i: usize) -> usize {
        if self.uf_nodes[i].parent == i {
            return i;
        }
        let root = self.get_node(self.uf_nodes[i].parent);
        self.uf_nodes[i].parent = root;
        return root;
    }

    fn merge_nodes(&mut self, i: usize, j: usize, info: Info) {
        assert!(self.final_typs.is_none());
        assert!(i != j);
        assert!(self.uf_nodes[i].parent == i);
        assert!(self.uf_nodes[j].parent == j);

        let new_node;
        if self.uf_nodes[i].rank > self.uf_nodes[j].rank {
            self.uf_nodes[j].parent = i;
            new_node = i;
        } else if self.uf_nodes[i].rank < self.uf_nodes[j].rank {
            self.uf_nodes[i].parent = j;
            new_node = j;
        } else {
            self.uf_nodes[j].parent = i;
            self.uf_nodes[j].rank += 1;
            new_node = i;
        }

        self.info[new_node] = info;
    }
}

impl State<'_, '_> {
    // TODO overflow checking
    pub fn finish_unification(&mut self) -> Result<(), VirErr> {
        self.unifier.final_typs = Some(vec![None; self.unifier.uf_nodes.len()]);

        for i in 0 .. self.unifier.uf_nodes.len() {
            if self.unifier.uf_nodes[i].parent == i {
               self.finish_rec(i);
            }
        }

        Ok(())
    }

    fn finish_rec(&mut self, i: usize) {
        if self.unifier.final_typs.as_ref().unwrap()[i].is_some() {
            return;
        }

        let typ = match &self.unifier.info[i] {
            Info::Unknown => todo!(),
            Info::UnknownIntegerType => vir::ast_util::int_typ(),
            Info::Known(typ) => typ.clone(),
            Info::Contradiction => todo!(),
        };

        let t = vir::ast_visitor::map_typ_visitor_env(&typ, self, &|state: &mut Self, t: &Typ| {
            match &**t {
                TypX::UnificationVar(uid) => {
                    let node = state.unifier.get_node(*uid);
                    state.finish_rec(node);
                    Ok(state.unifier.final_typs.as_ref().unwrap()[node].clone().unwrap())
                }
                _ => Ok(t.clone())
            }
        }).unwrap();

        self.unifier.final_typs.as_mut().unwrap()[i] = Some(t);
    }

    /// Get the final type with no unification variables.
    /// This must be called after `finish`
    pub fn get_finished_typ(&mut self, typ: &Typ) -> Typ {
        vir::ast_visitor::map_typ_visitor_env(typ, self, &|state: &mut Self, t: &Typ| {
            match &**t {
                TypX::UnificationVar(uid) => {
                    let node = state.unifier.get_node(*uid);
                    Ok(state.unifier.final_typs.as_ref().unwrap()[node].clone().unwrap())
                }
                _ => Ok(t.clone())
            }
        }).unwrap()
    }

    pub fn new_unknown_typ(&mut self) -> Typ {
        let uid = self.unifier.new_node(Info::Unknown);
        Arc::new(TypX::UnificationVar(uid))
    }

    pub fn new_unknown_integer_typ(&mut self) -> Typ {
        let uid = self.unifier.new_node(Info::UnknownIntegerType);
        Arc::new(TypX::UnificationVar(uid))
    }

    pub fn expect_integer(&mut self, _u2: &Typ) -> Result<(), VirErr> {
        todo!();
    }

    fn get_typ_if_known(&mut self, t: &Typ) -> Typ {
        match &**t {
            TypX::UnificationVar(id) => {
                let node = self.unifier.get_node(*id);
                match &self.unifier.info[node] {
                    Info::Known(known_typ) => known_typ.clone(),
                    _ => t.clone(),
                }
            }
            _ => t.clone(),
        }
    }

    /// t1 can be used where t2 is expected
    /// for the most part this means types are exactly equal, except for
    /// some integer type coercions
    pub fn expect_allowing_int_coercion(&mut self, t1: &Typ, t2: &Typ) -> Result<(), VirErr> {
        let t1c = self.get_typ_if_known(t1);
        let t2c = self.get_typ_if_known(t2);

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
                panic!("asdf");
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
                        &self.unifier.info[node1],
                        &self.unifier.info[node2]);
                    self.unifier.merge_nodes(node1, node2, merged_info);

                    if let Some((rt1, rt2)) = recurse_tys {
                        self.unify(&rt1, &rt2)?;
                    }

                    Ok(())
                } else {
                    Ok(())
                }
            }
            (TypX::UnificationVar(id1), _ty2) => {
                let node = self.unifier.get_node(*id1);
                let (new_info, recurse_typ) = merge_info_concrete(&self.unifier.info[node], typ2);
                self.unifier.info[node] = new_info;

                if let Some(rt1) = recurse_typ {
                    self.unify(&rt1, typ2)?;
                }
                Ok(())
            }
            (_ty1, TypX::UnificationVar(id2)) => {
                let node = self.unifier.get_node(*id2);
                let (new_info, recurse_typ) = merge_info_concrete(&self.unifier.info[node], typ1);
                self.unifier.info[node] = new_info;

                if let Some(rt2) = recurse_typ {
                    self.unify(typ1, &rt2)?;
                }
                Ok(())
            }
            (_ty1, _ty2) => {
                self.unify_heads(typ1, typ2)
            }
        }
    }

    // This is the part of `unify` that just checks the head type matches and recurses.
    // Fancy logic dealing with unification vars should go in `unify`
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
            (TypX::Projection { .. }, _) => todo!(),
            (_, TypX::Projection { .. }) => todo!(),
            (TypX::ConstInt(a1), TypX::ConstInt(a2)) => {
                if a1 == a2 {
                    Err(UnifyError::Error)
                } else {
                    Ok(())
                }
            }

            (TypX::UnificationVar(..), _) => unreachable!(),
            (_, TypX::UnificationVar(..)) => unreachable!(),

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
        (_, Info::Contradiction) => (Info::Contradiction, None),
        (Info::Contradiction, _) => (Info::Contradiction, None),
        (Info::UnknownIntegerType, Info::UnknownIntegerType) => (Info::UnknownIntegerType, None),
        (Info::Known(t1), Info::Known(t2)) => {
            (Info::Known(t2.clone()), Some((t1.clone(), t2.clone())))
        }
        (Info::UnknownIntegerType, Info::Known(t))
        | (Info::Known(t), Info::UnknownIntegerType)
        => { 
            if is_definitely_integer_type(t) {
                (Info::Known(t.clone()), None)
            } else {
                (Info::Contradiction, None)
            }
        }
    }
}

fn merge_info_concrete(info1: &Info, t2: &Typ) -> (Info, Option<Typ>) {
    match info1 {
        Info::Unknown => (Info::Known(t2.clone()), None),
        Info::Contradiction => (Info::Contradiction, None),
        Info::Known(t1) => (Info::Known(t1.clone()), Some(t1.clone())),
        Info::UnknownIntegerType => {
            if is_definitely_integer_type(t2) {
                (Info::Known(t2.clone()), None)
            } else {
                (Info::Contradiction, None)
            }
        }
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
