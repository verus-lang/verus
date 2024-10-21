/*!
Handles monomorphization, where we produce specialized code from a polymorphic function.

For example, if we have
```no_run
spec fn f<A>(a: A) -> A { ... }

proof fn proof1<B>(b: B) {
  let x = f(b);
  let y = f(true);
}
```
we need to generate two functions, `(f Poly Poly)`, and `(f bool bool)` in the
emitted SMT code. This is done to meet 3 design criteria:
1. We want to verify a function exactly once, so we cannot specialize `proof1`
    on demand every time someone calls it.
2. We want to leverage SMT solver's capability as much as possible. Coercing a
primitive type such as `bool` or `int` to poly, even though we know `f(bool)` is
specialized, hinders this.
3. We want to ensure the generated AIR code can be type-checked by AIR.
 */
use crate::ast::{Fun, Dt};
use crate::ast::Idents;
use crate::ast::IntRange;
use crate::ast::Primitive;
use crate::ast_util::n_types_equal;
use crate::sst::{CallFun, Exp, ExpX, KrateSstX, Stm};
use crate::sst_util::{subst_exp, subst_typ};
use crate::sst_visitor::{self, Visitor};
use crate::{
    ast::{Ident, Typ, TypX, Typs},
    sst::{FunctionSst, KrateSst},
};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use crate::sst::{Par, ParX};
use crate::def::Spanned;

/**
This stores one instance of specialization of a particular function. This
structure handles deduplication of essentially isomorphic call sites.
 */
#[derive(Debug, Hash)]
pub struct Specialization {
    pub typs: Typs,
}
impl Specialization {
    pub fn empty() -> Self {
        Self { typs: Arc::new(vec![]) }
    }
    pub fn from_exp(exp: &ExpX) -> Option<(&Fun, Self)> {
        let ExpX::Call(CallFun::Fun(fun, _) | CallFun::Recursive(fun), typs, _) = exp else {
            return None;
        };
        let result = Self { typs: typs.clone() };
        Some((fun, result))
    }

    fn mangle_path(path: &Dt) -> String {
        match path {
            Dt::Path(path) => {
                path.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("")
            }
            Dt::Tuple(i) => i.to_string(),
        }
    }

    fn mangle_type_name_inner(typ: &TypX) -> String {
        let mut suffix = String::new();
        match typ {
            TypX::Bool => {
                suffix += "_bool";
            }
            TypX::Int(range) => match range {
                IntRange::Int => suffix += "_int",
                IntRange::Nat => suffix += "_nat",
                IntRange::U(bits) => suffix += &format!("_u{bits}"),
                IntRange::I(bits) => suffix += &format!("_i{bits}"),
                IntRange::USize => suffix += "_usize",
                IntRange::ISize => suffix += "_isize",
                IntRange::Char => suffix += "char",
            },
            TypX::SpecFn(_, _) => {
                suffix += "_spec"; // Example for SpecFn
            }
            TypX::AnonymousClosure(_, _, _) => {
                suffix += "_ac"; // Example for AnonymousClosure
            }
            TypX::FnDef(_, _, _) => {
                suffix += "_fn"; // Example for FnDef
            }
            TypX::Datatype(dt, typs, _) => {
                suffix += "_data"; // Example for Datatype
                suffix += &Self::mangle_path(dt);
                for typ in typs.iter() {
                    suffix += &Self::mangle_type_name_inner(&*typ)
                }
            }
            TypX::Primitive(p, typs) => {
                suffix += "_prim"; // Example for Primitive
                match p {
                    Primitive::Array => {
                        suffix += "A";
                    }
                    Primitive::Slice => {
                        suffix += "S";
                    }
                    Primitive::StrSlice => {
                        suffix += "Ss";
                    }
                    Primitive::Ptr => {
                        suffix += "P";
                    }
                    Primitive::Global => {
                        suffix += "G";
                    }
                }
                for typ in typs.iter() {
                    suffix += &Self::mangle_type_name_inner(&*typ)
                }
            }
            TypX::Decorate(_, _, typ) => {
                suffix += "_de";
                suffix += &Self::mangle_type_name_inner(&*typ)
            }
            TypX::Boxed(_) => {
                suffix += "_box"; // Example for Boxed
            }
            TypX::TypParam(ref ident) => {
                suffix += "_x";
                suffix += ident.as_ref();
            }
            TypX::Projection { .. } => {
                suffix += "_proj"; // Example for Projection
            }
            TypX::TypeId => {
                suffix += "_tid";
            }
            TypX::ConstInt(ref big_int) => {
                suffix += "_ci";
                suffix += &big_int.to_string();
            }
            TypX::Air(_) => {
                suffix += "_a";
            }
        }
        suffix
    }
    fn mangle_type_name(typ: &TypX) -> Ident {
        let name = Self::mangle_type_name_inner(typ);
        let l = name.len();
        Arc::new(format!("_M{l}{name}"))
    }

    pub fn transform_ident(&self, ident: Ident) -> Ident {
        if self.typs.is_empty() {
            return ident;
        }
        let mut suffix = String::new();
        for typ in self.typs.iter() {
            suffix += &Self::mangle_type_name(&*typ);
        }

        Arc::new(ident.as_ref().clone() + &suffix)
    }

    pub fn transform_par(&self, typ_params: &Idents, par: &Par) -> Par {
        if self.typs.is_empty() {
            return par.clone();
        }
        let mut trait_typ_substs: HashMap<Ident, Typ> = HashMap::new();
        assert!(typ_params.len() == self.typs.len());
        for (x, t) in typ_params.iter().zip(self.typs.iter()) {
            trait_typ_substs.insert(x.clone(), t.clone());
        }
        Arc::new(Spanned {
            span: par.span.clone(), // Assuming `par` has a `span` field that needs to be copied
            x: ParX {
            name: par.x.name.clone(),
            typ: self.transform_typ(typ_params, &par.x.typ),
            mode: par.x.mode,
            is_mut: par.x.is_mut,
            purpose: par.x.purpose
            },

        })

    }

    pub fn transform_typ(&self, typ_params: &Idents,typ: &Typ) -> Typ {
        if self.typs.is_empty() {
            return typ.clone();
        }
        let mut trait_typ_substs: HashMap<Ident, Typ> = HashMap::new();
        assert!(typ_params.len() == self.typs.len());
        for (x, t) in typ_params.iter().zip(self.typs.iter()) {
            trait_typ_substs.insert(x.clone(), t.clone());
        }
        let new_typ  = subst_typ(&trait_typ_substs, typ);
        new_typ
    }
  

    pub fn transform_exp(&self, typ_params: &Idents, ex: &Exp) -> Exp {
        if self.typs.is_empty() {
            return ex.clone();
        }
        let mut trait_typ_substs: HashMap<Ident, Typ> = HashMap::new();
        assert!(typ_params.len() == self.typs.len());
        for (x, t) in typ_params.iter().zip(self.typs.iter()) {
            trait_typ_substs.insert(x.clone(), t.clone());
        }
        let new_body_exp = subst_exp(&trait_typ_substs, &HashMap::new(), ex);
        new_body_exp
    }

    pub fn comment(&self) -> String {
        format!(" specialized to {:?}", &self.typs)
    }
}
impl PartialEq for Specialization {
    fn eq(&self, other: &Self) -> bool {
        n_types_equal(&self.typs, &other.typs)
    }
}
impl Eq for Specialization {}

/**
Utility for walking through the expression tree.

This must be doubly recursive on both expressions and statements, hence its
structure mirrors `StmExpVisitorDfs`.
 */
struct SpecializationVisitor {
    invocations: Vec<(Fun, Specialization)>,
    params: Vec<Ident>,
}
impl SpecializationVisitor {
    fn new() -> Self {
        Self { invocations: vec![], params: vec![] }
    }
}
impl Visitor<sst_visitor::Walk, (), sst_visitor::NoScoper> for SpecializationVisitor {
    fn visit_exp(&mut self, exp: &Exp) -> Result<(), ()> {
        if let Some((fun, spec)) = Specialization::from_exp(&exp.x) {
            self.invocations.push((fun.clone(), spec))
        }
        self.visit_exp_rec(exp)
    }
    fn visit_stm(&mut self, stm: &Stm) -> Result<(), ()> {
        self.visit_stm_rec(stm)
    }
}

pub(crate) fn collect_specializations_from_function(
    function: &FunctionSst,
) -> Vec<(Fun, Specialization)> {
    let mut visitor = SpecializationVisitor::new();
    for h in function.x.typ_params.iter() {
        visitor.params.push(h.clone());
    }
    visitor.visit_function(function).unwrap();
    visitor.invocations
}
/**
Collect all polymorphic function invocations in a module
 */
pub fn mono_krate_for_module(krate: &KrateSst) -> HashMap<Fun, HashSet<Specialization>> {
    let mut invocations: HashMap<Fun, HashSet<Specialization>> = HashMap::new();
    let KrateSstX { functions, .. } = &**krate;
    for f in functions.iter() {
        for (fun, spec) in collect_specializations_from_function(f).into_iter() {
            invocations.entry(fun).or_insert_with(HashSet::new).insert(spec);
        }
    }
    invocations
}
