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
use crate::ast::Fun;
use crate::ast_util::n_types_equal;
use crate::sst::{CallFun, Exp, ExpX, KrateSstX, Stm};
use crate::sst_visitor::{self, Visitor};
use crate::{
    ast::{Ident, TypX, Typs, Typ},
    sst::{FunctionSst, KrateSst},
};
use std::collections::{HashMap, HashSet};
use crate::ast::Idents;
use std::sync::Arc;
use crate::sst_util::{subst_exp};
use crate::ast::Primitive;
use crate::ast::IntRange;

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

    pub fn get_type_name(typ: Typ) -> Ident {
        let mut suffix = String::new();
        match &*typ {
            TypX::Bool => {
                suffix += "_bool";
            }
            TypX::Int(range) => {
                match range {
                    IntRange::Int => suffix +="_int",
                    IntRange::Nat => suffix += "_nat",
                    IntRange::U(bits) => suffix += &format!("_unsigned_{}", bits),
                    IntRange::I(bits) => suffix += &format!("_signed_{}", bits),
                    IntRange::USize => suffix += "_rustusize",
                    IntRange::ISize => suffix += "_rustisze",
                    IntRange::Char => suffix += "char",
                }
            }
            TypX::Tuple(typs) => {
                suffix += "tuple"; 
                for typ in typs.iter() {
                    suffix += &Self::get_type_name(typ.clone())
                }
            }
            TypX::SpecFn(_, _) => {
                suffix += "_specfn"; // Example for SpecFn
            }
            TypX::AnonymousClosure(_, _, _) => {
                suffix += "_anon_closure"; // Example for AnonymousClosure
            }
            TypX::FnDef(_, _, _) => {
                suffix += "_fn_def"; // Example for FnDef
            }
            TypX::Datatype(path, typs, _) => {
                suffix += "_datatype"; // Example for Datatype
                for id in path.segments.iter() {
                    suffix += id;
                }
                for typ in typs.iter() {
                    suffix += &Self::get_type_name(typ.clone())
                }
            }
            TypX::Primitive(p, typs) => {
                suffix += "_primitive_"; // Example for Primitive
                match p {
                    Primitive::Array => {
                        suffix += "_array";
                    }
                    Primitive::Slice => {
                        suffix += "_slice";
                    }
                    Primitive::StrSlice => {
                        suffix += "_strslice";
                    }
                    Primitive::Ptr => {
                        suffix += "_ptr";
                    }
                    Primitive::Global => {
                        suffix += "_global";
                    }
                }
                for typ in typs.iter() {
                    suffix += &Self::get_type_name(typ.clone())
                }
            }
            TypX::Decorate(_, _, typ) => {
                suffix += "_decorate";
                suffix += &Self::get_type_name(typ.clone())
            }
            TypX::Boxed(_) => {
                suffix += "_boxed"; // Example for Boxed
            }
            TypX::TypParam(ref ident) => {
                suffix += "_";
                suffix += ident.as_ref();
            }
            TypX::Projection { .. } => {
                suffix += "_projection"; // Example for Projection
            }
            TypX::TypeId => {
                suffix += "_type_id"; 
            }
            TypX::ConstInt(ref big_int) => {
                suffix += "_const_int";
                suffix += &big_int.to_string();
            }
            TypX::Air(_) => {
                suffix += "_air"; 
            }

        }
        Arc::new(suffix)

    }

    pub fn transform_ident(&self, ident: Ident) -> Ident {
        if self.typs.is_empty() {
            return ident;
        }
        let mut suffix = String::new();
        for typ in self.typs.iter() {
            suffix += &Self::get_type_name(typ.clone());
        }
    
        Arc::new(ident.as_ref().clone() + &suffix)
    }

    pub fn transform_exp(&self, typ_params: &Idents,  ex: &Exp) -> Exp {
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
        Self { invocations: vec![],
                params: vec![] }
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
