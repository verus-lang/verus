//! This module checks for conflicts between trait implementations so that Verus
//! does not generate contradictory axioms for conflicting implementations.
//! For example, these would be conflicting and would result in contradictory axioms:
//!   impl T for bool { spec fn f() -> int { 3 } }
//!   impl T for bool { spec fn f() -> int { 4 } }
//! In principle, this is redundant, because rustc already checks for conflicts and will
//! flag this example as conflicting.  However, it is prudent to double-check more directly
//! that Verus's axioms won't be contradictory, in case Verus's VIR/AST model of Rust's traits
//! ever gets out of sync with rustc's conflict checking.
//! This has happened before (see https://github.com/verus-lang/verus/issues/1094 ),
//! and given the complexity of Rust traits, it could happen again.
//! (See, for example, "fn is_sized" in rustc_middle/src/ty/util.rs, which talks about how the result
//! of is_sized "... can be an over-approximation in generic contexts, where one can have
//! strange rules like `<T as Foo<'static>>::Bar: Sized` ...".)
//! If Verus's model gets out of sync (because, for example, the VIR/AST model ignores lifetime
//! variables), it's better to detect the conflict and halt than to generate unsound axioms.
//! This may mean that Verus rejects some trait implementations that Rust accepts,
//! since Verus's slightly abstracted model of the trait implementations means that
//! implementations that are distinct in the original Rust code might get mapped onto overlapping
//! implementations in the VIR/AST model.

//! To perform the conflict checking, we reuse rustc's trait conflict checker,
//! but we run rustc's trait conflict checker on code generated from Verus's VIR/AST model of the
//! trait implementations rather than on the original trait implementations.
//! This module generates trait declarations and trait implementations from Verus's VIR/AST model,
//! which are fed back to rustc as part of the code generated by lifetime.rs.

use crate::lifetime_ast::*;
use crate::lifetime_generate::*;
use crate::verus_items::RustItem;
use std::collections::{HashMap, HashSet};
use vir::ast::{
    AssocTypeImpl, Dt, GenericBoundX, GenericBounds, Ident, Path, Primitive, TypDecoration,
    TypDecorationArg,
};

// General purpose type to represent various types, where N comes from the TypNum enum:
//   struct C<const N: usize, A>(A);
// For example, Ptr<bool> is represented as C<TypNum::Ptr, bool>.
#[derive(Copy, Clone)]
enum TypNum {
    SpecFn,
    Slice,
    StrSlice,
    Ptr,
    Ref,
    MutRef,
    Box,
    Rc,
    Arc,
    Ghost,
    Tracked,
    Never,
    ConstPtr,
    Global,
    SharedRef,
}

fn gen_num_typ(n: TypNum, ts: Vec<Typ>) -> Typ {
    let t1 = Box::new(TypX::Primitive((n as isize).to_string()));
    // types are unsized, so tuple elements must be boxed:
    let box_name = Id::new(IdKind::Builtin, 0, "Box".to_owned());
    let ts = ts
        .into_iter()
        .map(|t| Box::new(TypX::Datatype(box_name.clone(), Vec::new(), vec![t])))
        .collect();
    let t2 = Box::new(TypX::Tuple(ts));
    Box::new(TypX::Datatype(Id::new(IdKind::Builtin, 0, "C".to_owned()), vec![], vec![t1, t2]))
}

// This should generate a type that is one-to-one mapped to the result of sst_to_air::typ_to_ids.
// All generated types are unsized, and we treat Sized/?Sized explicitly rather than relying on
// Rust's complex conventions for Sized.
fn gen_typ(state: &mut State, typ: &vir::ast::Typ) -> Typ {
    match &**typ {
        vir::ast::TypX::Bool | vir::ast::TypX::Int(..) => {
            Box::new(TypX::Primitive(vir::ast_util::typ_to_diagnostic_str(typ)))
        }
        vir::ast::TypX::Datatype(Dt::Tuple(_), ts, _) => {
            let ts = gen_typs(state, ts);
            // types are unsized, so tuple elements must be boxed:
            let box_name = Id::new(IdKind::Builtin, 0, "Box".to_owned());
            let ts = ts
                .into_iter()
                .map(|t| Box::new(TypX::Datatype(box_name.clone(), Vec::new(), vec![t])))
                .collect();
            Box::new(TypX::Tuple(ts))
        }
        vir::ast::TypX::SpecFn(ts, t) => gen_num_typ(
            TypNum::SpecFn,
            vec![Box::new(TypX::Tuple(gen_typs(state, ts))), gen_typ(state, t)],
        ),
        vir::ast::TypX::AnonymousClosure(..) => {
            panic!("unexpected closure in trait type argument")
        }
        vir::ast::TypX::FnDef(..) => {
            panic!("unexpected function definition in trait type argument")
        }
        vir::ast::TypX::Datatype(Dt::Path(path), typs, _) => {
            Box::new(TypX::Datatype(state.datatype_name(path), vec![], gen_typs(state, typs)))
        }
        vir::ast::TypX::Primitive(Primitive::Array, ts) => {
            assert!(ts.len() == 2);
            Box::new(TypX::Datatype(
                Id::new(IdKind::Builtin, 0, "Arr".to_owned()),
                vec![],
                gen_typs(state, ts),
            ))
        }
        vir::ast::TypX::Primitive(prim, ts) => {
            let n = match prim {
                Primitive::Array => unreachable!(),
                Primitive::Slice => TypNum::Slice,
                Primitive::StrSlice => TypNum::StrSlice,
                Primitive::Ptr => TypNum::Ptr,
                Primitive::Global => TypNum::Global,
                Primitive::SharedRef => TypNum::SharedRef,
            };
            gen_num_typ(n, gen_typs(state, ts))
        }
        vir::ast::TypX::Decorate(d, targ, t) => {
            let n = match d {
                TypDecoration::Ref => TypNum::Ref,
                TypDecoration::MutRef => TypNum::MutRef,
                TypDecoration::Box => TypNum::Box,
                TypDecoration::Rc => TypNum::Rc,
                TypDecoration::Arc => TypNum::Arc,
                TypDecoration::Ghost => TypNum::Ghost,
                TypDecoration::Tracked => TypNum::Tracked,
                TypDecoration::Never => TypNum::Never,
                TypDecoration::ConstPtr => TypNum::ConstPtr,
            };
            let mut ts = vec![t.clone()];
            match targ {
                None => {}
                Some(TypDecorationArg { allocator_typ }) => {
                    ts.push(allocator_typ.clone());
                }
            }
            gen_num_typ(n, gen_typs(state, &ts))
        }
        vir::ast::TypX::Boxed(t) => gen_typ(state, t),
        vir::ast::TypX::TypParam(x) => {
            if x == &vir::def::trait_self_type_param() {
                Box::new(TypX::TraitSelf)
            } else {
                Box::new(TypX::TypParam(state.typ_param(x.to_string(), None)))
            }
        }
        vir::ast::TypX::Projection { trait_typ_args, trait_path, name } => {
            let self_typ = gen_typ(state, &trait_typ_args[0]);
            let args = gen_typ_slice(state, &trait_typ_args[1..]);
            let path = state.trait_name(trait_path);
            let trait_as_datatype = Box::new(TypX::Datatype(path, Vec::new(), args));
            let name = state.typ_param(name.to_string(), None);
            Box::new(TypX::Projection { self_typ, trait_as_datatype, name, assoc_typ_args: vec![] })
        }
        vir::ast::TypX::ConstInt(i) => Box::new(TypX::Primitive(i.to_string())),
        vir::ast::TypX::ConstBool(b) => Box::new(TypX::Primitive(b.to_string())),
        vir::ast::TypX::TypeId | vir::ast::TypX::Air(..) => {
            panic!("internal error: unexpected type")
        }
    }
}

fn gen_typs(state: &mut State, typs: &Vec<vir::ast::Typ>) -> Vec<Typ> {
    typs.iter().map(|t| gen_typ(state, t)).collect()
}

fn gen_typ_slice(state: &mut State, typs: &[vir::ast::Typ]) -> Vec<Typ> {
    typs.iter().map(|t| gen_typ(state, t)).collect()
}

fn gen_generics(
    state: &mut State,
    typ_params: &Vec<Ident>,
    typ_bounds: &GenericBounds,
) -> (Vec<GenericParam>, Vec<GenericBound>) {
    let mut generic_params: Vec<GenericParam> = Vec::new();
    let mut generic_bounds: Vec<GenericBound> = Vec::new();
    let mut const_typs: HashMap<String, Typ> = HashMap::new();
    for b in typ_bounds.iter() {
        match &**b {
            GenericBoundX::Trait(path, typs) => {
                let rust_item = crate::verus_items::get_rust_item_path(path);
                let typ = gen_typ(state, &typs[0]);
                let bound = match rust_item {
                    Some(RustItem::Sized) => Bound::Sized,
                    _ => {
                        let args = gen_typ_slice(state, &typs[1..]);
                        let trait_path = state.trait_name(&path);
                        Bound::Trait { trait_path, args, equality: None }
                    }
                };
                generic_bounds.push(GenericBound { typ, bound_vars: vec![], bound });
            }
            GenericBoundX::TypEquality(path, typs, x, eq_typ) => {
                let typ = gen_typ(state, &typs[0]);
                let args = gen_typ_slice(state, &typs[1..]);
                let eq_typ = gen_typ(state, eq_typ);
                let trait_path = state.trait_name(&path);
                let x = state.typ_param(x.to_string(), None);
                let equality = Some((x, vec![], eq_typ));
                let bound = Bound::Trait { trait_path, args, equality };
                generic_bounds.push(GenericBound { typ, bound_vars: vec![], bound });
            }
            GenericBoundX::ConstTyp(c, typ) => {
                if let vir::ast::TypX::TypParam(x) = &**c {
                    const_typs.insert(x.to_string(), gen_typ(state, typ));
                } else {
                    panic!("unexpected constant");
                }
            }
        }
    }
    for x in typ_params {
        generic_params.push(GenericParam {
            name: state.typ_param(x.to_string(), None),
            const_typ: const_typs.get(&x.to_string()).cloned(),
        });
    }
    (generic_params, generic_bounds)
}

pub(crate) fn gen_check_trait_impl_conflicts(
    spans: &crate::spans::SpanContext,
    vir_crate: &vir::ast::Krate,
    state: &mut State,
) {
    state.restart_names();

    for d in &vir_crate.datatypes {
        let Dt::Path(path) = &d.x.name else {
            panic!("Verus internal error: gen_check_trait_impl_conflicts expects Dt::Path");
        };

        let (generic_params, generic_bounds) = gen_generics(
            state,
            &d.x.typ_params.iter().map(|(x, _)| x.clone()).collect(),
            &d.x.typ_bounds,
        );
        let mut fields: Vec<Typ> = Vec::new();
        for p in generic_params.iter() {
            if p.const_typ.is_none() {
                // types are unsized, so fields must be boxed:
                let box_name = Id::new(IdKind::Builtin, 0, "Box".to_owned());
                let t = Box::new(TypX::TypParam(p.name.clone()));
                fields.push(Box::new(TypX::Datatype(box_name, Vec::new(), vec![t])));
            }
        }
        let decl = DatatypeDecl {
            name: state.datatype_name(path),
            span: spans.from_air_span(&d.span, None),
            generic_params,
            generic_bounds,
            datatype: Box::new(Datatype::Struct(Fields::Pos(fields))),
        };
        state.datatype_decls.push(decl);
    }

    let mut used_traits: HashSet<Path> = HashSet::new();
    let mut used_assoc_typs: HashSet<(Path, Ident)> = HashSet::new();
    for t in &vir_crate.traits {
        let (t_params, mut t_bounds) = gen_generics(
            state,
            &t.x.typ_params.iter().map(|(x, _)| x.clone()).collect(),
            &t.x.typ_bounds,
        );
        let (a_params, mut a_bounds) = gen_generics(state, &t.x.assoc_typs, &t.x.assoc_typs_bounds);
        used_traits.insert(t.x.name.clone());
        for a in t.x.assoc_typs.iter() {
            used_assoc_typs.insert((t.x.name.clone(), a.clone()));
        }
        let name = state.trait_name(&t.x.name);
        let mut assoc_typs: Vec<(Id, Vec<GenericParam>, Vec<GenericBound>)> = Vec::new();
        for x in &a_params {
            let (bounds_x, bounds_other) =
                crate::lifetime_emit::simplify_assoc_typ_bounds(&name, &x.name, a_bounds);
            a_bounds = bounds_other;
            assoc_typs.push((x.name.clone(), vec![], bounds_x));
        }
        t_bounds.extend(a_bounds);
        let decl =
            TraitDecl { name, generic_params: t_params, generic_bounds: t_bounds, assoc_typs };
        state.trait_decls.push(decl);
    }

    let mut impl_path_to_assoc_typs: HashMap<Path, Vec<AssocTypeImpl>> = HashMap::new();
    for i in &vir_crate.trait_impls {
        let prev = impl_path_to_assoc_typs.insert(i.x.impl_path.clone(), vec![]);
        assert!(prev.is_none());
    }
    for a in &vir_crate.assoc_type_impls {
        if let Some(entry) = impl_path_to_assoc_typs.get_mut(&a.x.impl_path) {
            entry.push(a.clone());
        }
    }

    for i in &vir_crate.trait_impls {
        if !used_traits.contains(&i.x.trait_path) {
            continue;
        }
        let span = spans.from_air_span(&i.span, None);
        let (generic_params, generic_bounds) =
            gen_generics(state, &*i.x.typ_params, &i.x.typ_bounds);
        let self_typ = gen_typ(state, &i.x.trait_typ_args[0]);
        let trait_as_datatype = Box::new(TypX::Datatype(
            state.trait_name(&i.x.trait_path),
            vec![],
            gen_typ_slice(state, &i.x.trait_typ_args[1..]),
        ));
        let mut assoc_typs: Vec<(Id, Vec<GenericParam>, Typ)> = Vec::new();
        for a in &impl_path_to_assoc_typs[&i.x.impl_path] {
            if used_assoc_typs.contains(&(i.x.trait_path.clone(), a.x.name.clone())) {
                assoc_typs.push((
                    state.typ_param(a.x.name.to_string(), None),
                    vec![],
                    gen_typ(state, &a.x.typ),
                ));
            }
        }
        let trait_polarity = rustc_middle::ty::ImplPolarity::Positive;
        let decl = TraitImpl {
            span,
            self_typ,
            generic_params,
            generic_bounds,
            trait_as_datatype,
            assoc_typs,
            trait_polarity,
            is_clone: false,
        };
        state.trait_impls.push(decl);
    }
}
