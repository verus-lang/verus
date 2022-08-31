use crate::ast::{Datatype, FunctionKind, GenericBoundX, Ident, Krate, Path, Typ, TypX, VirErr};
use crate::ast_util::{err_str, err_string, path_as_rust_name};
use crate::context::GlobalCtx;
use crate::recursion::Node;
use crate::scc::Graph;
use air::ast::Span;
use air::errors::ErrorLabel;
use std::collections::HashMap;
use std::sync::Arc;

// To enable decreases clauses on datatypes while treating the datatypes as inhabited in specs,
// we need to make sure that the datatypes have base cases, not just inductive cases.
// This also checks that there is at least one variant, so that spec matches are safe.
fn check_well_founded(
    datatypes: &HashMap<Path, Datatype>,
    datatypes_well_founded: &mut HashMap<Path, bool>,
    path: &Path,
) -> Result<bool, VirErr> {
    if let Some(well_founded) = datatypes_well_founded.get(path) {
        // return true ==> definitely well founded
        // return false ==> not yet known to be well founded; still in process
        return Ok(*well_founded);
    }
    datatypes_well_founded.insert(path.clone(), false);
    let datatype = &datatypes[path];
    'variants: for variant in datatype.x.variants.iter() {
        for field in variant.a.iter() {
            let (typ, _, _) = &field.a;
            if !check_well_founded_typ(datatypes, datatypes_well_founded, typ)? {
                // inductive case
                continue 'variants;
            }
        }
        // Found a base case variant
        datatypes_well_founded.insert(path.clone(), true);
        return Ok(true);
    }
    // No base cases found, only inductive cases
    err_str(&datatype.span, "datatype must have at least one non-recursive variant")
}

fn check_well_founded_typ(
    datatypes: &HashMap<Path, Datatype>,
    datatypes_well_founded: &mut HashMap<Path, bool>,
    typ: &Typ,
) -> Result<bool, VirErr> {
    match &**typ {
        TypX::Bool | TypX::Int(_) | TypX::TypParam(_) | TypX::Lambda(..) | TypX::StrSlice => {
            Ok(true)
        }
        TypX::Boxed(_) | TypX::TypeId | TypX::Air(_) => {
            panic!("internal error: unexpected type in check_well_founded_typ")
        }
        TypX::Tuple(typs) => {
            // tuples are just datatypes and therefore have a height in decreases clauses,
            // so we need to include them in the well foundedness checks
            for typ in typs.iter() {
                if !check_well_founded_typ(datatypes, datatypes_well_founded, typ)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        TypX::Datatype(path, _) => {
            // note: we don't care about the type arguments here,
            // because datatype heights in decreases clauses are oblivious to the type arguments.
            // (e.g. in enum List { Cons(Foo<List>) }, Cons is considered a base case because
            // the height of Foo<List> is unrelated to the height of List)
            check_well_founded(datatypes, datatypes_well_founded, path)
        }
    }
}

struct CheckPositiveGlobal {
    datatypes: HashMap<Path, Datatype>,
    type_graph: Graph<Path>,
}

struct CheckPositiveLocal {
    span: Span,
    my_datatype: Path,
    tparams: HashMap<Ident, bool>,
}

// polarity = Some(true) for positive, Some(false) for negative, None for neither
fn check_positive_uses(
    global: &CheckPositiveGlobal,
    local: &CheckPositiveLocal,
    polarity: Option<bool>,
    typ: &Typ,
) -> Result<(), VirErr> {
    match &**typ {
        TypX::Bool => Ok(()),
        TypX::Int(..) => Ok(()),
        TypX::StrSlice => Ok(()),
        TypX::Lambda(ts, tr) => {
            /* REVIEW: we could track both positive and negative polarity,
               but strict positivity is more conservative
            let flip_polarity = match polarity {
                None => None,
                Some(b) => Some(!b),
            };
            */
            let flip_polarity = None; // strict positivity
            for t in ts.iter() {
                check_positive_uses(global, local, flip_polarity, t)?;
            }
            check_positive_uses(global, local, polarity, tr)?;
            Ok(())
        }
        TypX::Tuple(ts) => {
            for t in ts.iter() {
                check_positive_uses(global, local, polarity, t)?;
            }
            Ok(())
        }
        TypX::Datatype(path, ts) => {
            // Check path
            if path == &local.my_datatype
                || global.type_graph.get_scc_rep(&path)
                    == global.type_graph.get_scc_rep(&local.my_datatype)
            {
                match polarity {
                    Some(true) => {}
                    _ => {
                        return err_string(
                            &local.span,
                            format!(
                                "Type {} recursively uses type {} in a non-positive polarity",
                                path_as_rust_name(&local.my_datatype),
                                path_as_rust_name(path)
                            ),
                        );
                    }
                }
            }
            let typ_params = &global.datatypes[path].x.typ_params;
            for ((_, _, strictly_positive), t) in typ_params.iter().zip(ts.iter()) {
                let t_polarity = if *strictly_positive { Some(true) } else { None };
                check_positive_uses(global, local, t_polarity, t)?;
            }
            Ok(())
        }
        TypX::Boxed(t) => check_positive_uses(global, local, polarity, t),
        TypX::TypParam(x) => {
            let strictly_positive = local.tparams[x];
            match (strictly_positive, polarity) {
                (false, _) => Ok(()),
                (true, Some(true)) => Ok(()),
                (true, _) => err_string(
                    &local.span,
                    format!(
                        "Type parameter {} must be declared #[verifier(maybe_negative)] to be used in a non-positive position",
                        x
                    ),
                ),
            }
        }
        TypX::TypeId => Ok(()),
        TypX::Air(_) => Ok(()),
    }
}

pub(crate) fn check_recursive_types(krate: &Krate) -> Result<(), VirErr> {
    let mut type_graph: Graph<Path> = Graph::new();
    let mut datatypes: HashMap<Path, Datatype> = HashMap::new();
    let mut datatypes_well_founded: HashMap<Path, bool> = HashMap::new();

    // If datatype D1 has a field whose type mentions datatype D2, create a graph edge D1 --> D2
    for datatype in &krate.datatypes {
        datatypes.insert(datatype.x.path.clone(), datatype.clone());
        for variant in datatype.x.variants.iter() {
            for field in variant.a.iter() {
                let (typ, _, _) = &field.a;
                let ft = |type_graph: &mut Graph<Path>, t: &Typ| match &**t {
                    TypX::Datatype(path, _) => {
                        type_graph.add_edge(datatype.x.path.clone(), path.clone());
                        Ok(t.clone())
                    }
                    _ => Ok(t.clone()),
                };
                crate::ast_visitor::map_typ_visitor_env(typ, &mut type_graph, &ft).unwrap();
            }
        }
    }

    type_graph.compute_sccs();
    let global = CheckPositiveGlobal { datatypes, type_graph };

    for function in &krate.functions {
        let mut typ_params = function.x.typ_bounds.iter();
        if let FunctionKind::TraitMethodDecl { .. } = function.x.kind {
            let (self_name, _) = typ_params.next().expect("self type parameter");
            assert!(self_name == &crate::def::trait_self_type_param());
        }
        for (_name, bound) in typ_params {
            match (&**bound, &function.x.kind) {
                (GenericBoundX::Traits(ts), _) if ts.len() == 0 => {}
                (GenericBoundX::Traits(_), FunctionKind::Static)
                    if function.x.attrs.broadcast_forall =>
                {
                    // See the todo!() in func_to_air.rs
                    return err_str(
                        &function.span,
                        "not yet supported: bounds on broadcast_forall function type parameters",
                    );
                }
                (_, FunctionKind::Static) => {}
                _ => {
                    // REVIEW: when we support bounds on method type parameters,
                    // we'll need the appropriate termination checking.
                    return err_str(
                        &function.span,
                        "not yet supported: bounds on method type parameters",
                    );
                }
            }
        }
    }

    for tr in &krate.traits {
        for (_name, bound, _positive) in tr.x.typ_params.iter() {
            match &**bound {
                GenericBoundX::Traits(ts) if ts.len() == 0 => {}
                _ => {
                    // REVIEW: when we support bounds on trait type parameters,
                    // we'll need the appropriate termination checking.
                    // (e.g. by including traits in the datatype graph
                    // and checking bounded type variables occur in positive positions)
                    return err_str(&tr.span, "not yet supported: bounds on trait type parameters");
                }
            }
        }
    }

    for datatype in &krate.datatypes {
        let mut tparams: HashMap<Ident, bool> = HashMap::new();
        for (name, bound, positive) in datatype.x.typ_params.iter() {
            match &**bound {
                GenericBoundX::Traits(ts) if ts.len() == 0 => {}
                _ => {
                    // REVIEW: when we support bounds on datatype parameters,
                    // we'll need the appropriate termination checking.
                    return err_str(
                        &datatype.span,
                        "not yet supported: bounds on datatype parameters",
                    );
                }
            }
            tparams.insert(name.clone(), *positive);
        }
        let local = CheckPositiveLocal {
            span: datatype.span.clone(),
            my_datatype: datatype.x.path.clone(),
            tparams,
        };
        let _ =
            check_well_founded(&global.datatypes, &mut datatypes_well_founded, &datatype.x.path)?;
        for variant in datatype.x.variants.iter() {
            for field in variant.a.iter() {
                // Check that field type only uses SCC siblings in positive positions
                let (typ, _, _) = &field.a;
                check_positive_uses(&global, &local, Some(true), typ)?;
            }
        }
    }

    Ok(())
}

fn scc_error(krate: &Krate, head: &Node, nodes: &Vec<Node>) -> VirErr {
    let mut labels: Vec<ErrorLabel> = Vec::new();
    let mut spans: Vec<Span> = Vec::new();
    for node in nodes {
        let mut push = |node: &Node, span: Span| {
            if node == head {
                spans.push(span);
            } else {
                let msg = "may be part of cycle".to_string();
                labels.push(ErrorLabel { span, msg });
            }
        };
        match node {
            Node::Fun(fun) => {
                if let Some(f) = krate.functions.iter().find(|f| f.x.name == *fun) {
                    let span = f.span.clone();
                    push(node, span);
                }
            }
            Node::Trait(trait_path) => {
                if let Some(t) = krate.traits.iter().find(|t| t.x.name == *trait_path) {
                    let span = t.span.clone();
                    push(node, span);
                }
            }
            Node::DatatypeTraitBound { datatype, .. } => {
                if let Some(d) = krate.datatypes.iter().find(|d| d.x.path == *datatype) {
                    let span = d.span.clone();
                    push(node, span);
                }
            }
        }
    }
    let msg =
        "found a cyclic self-reference in a trait definition, which may result in nontermination"
            .to_string();
    Arc::new(air::errors::ErrorX { msg, spans, labels })
}

// Check for cycles in traits
pub fn check_traits(krate: &Krate, ctx: &GlobalCtx) -> Result<(), VirErr> {
    // It's possible to encode nontermination using trait methods.
    // For soundness, proof/spec functions must terminate, so we must check trait termination.
    // (REVIEW: we could be more lenient and allow cycles through exec functions.)

    // We use the approach taken by Coq and F* for type classes as inspiration.
    // These languages encode type classes and methods as datatypes and functions,
    // so that the termination checks for datatypes and functions guarantee termination
    // of traits and methods.
    // Suppose we have a trait (type class) T:
    //   trait T {
    //     fn f(x: Self, y: Self) -> bool;
    //     fn g(x: Self, y: Self) -> Self { requires(f(x, y)); };
    //   }
    // Coq/F* would encode this using a "dictionary" datatype:
    //   struct Dictionary_T<Self> {
    //     f: Fn(Self, Self) -> bool,
    //     g: Fn(Self, Self) -> Self { requires(f(x, y)); },
    //   }
    // (Note that this is a dependent record in Coq/F*, where g's type depends on f,
    // because g's requires clause mentions f.  Because of this, the order of the fields matters --
    // f must precede g in the record type.  Also notice that f and g do not recursively
    // take the dictionary as an argument -- it's f(Self, Self),
    // not f(Dictionary_T<Self>, Self, Self).)
    // An implementations of T for datatype D would then have to produce a value
    // of type Dictionary_T<D> containing the functions f and g:
    //   let dictionary_T_for_D_f = |x: D, y: D| -> bool { ... };
    //   let dictionary_T_for_D_g = |x: D, y: D| -> D { ... };
    //   let dictionary_T_for_D: Dictionary_T<D> = Dictionary_T {
    //     f: dictionary_T_for_D_f,
    //     g: dictionary_T_for_D_g,
    //   };
    // A trait bound A: T is treated as an argument of type Dictionary_T<A>.
    // In other words, we have to justify any instantiation of a trait bound A: T
    // by passing in a dictionary that represents the implementation of T for A.

    // Although we don't actually encode traits and methods as datatypes and functions,
    // we ensure termination by checking that it would be possible to encode traits and methods
    // as datatypes and functions.
    // So it must be possible to define the following in the following order, with no cycle:
    //   1) The trait T and the trait's method declarations
    //   2) Method implementations for any datatype D that implements T
    //   3) Uses of datatype D to satisfy the trait bound T (in Rust notation, D: T).

    // We extend the call graph to represent trait declarations (T) and datatypes implementing
    // traits (D: T) using Node::Trait(T) and Node::DatatypeTraitBound(D, T).
    // We add the following edges to the call graph (see recursion::expand_call_graph):
    //   - T --> f if the requires/ensures of T's method declarations call f
    //   - f --> T for any function f<A: T> with type parameter A: T
    //   - D: T --> T
    //   - f --> D: T where one of f's expressions instantiates A: T with D: T.
    //   - D: T --> f where f is one of D's methods that implements T
    // It is an error for Node::Trait(T) or Node::DatatypeTraitBound(D, T) to appear in a cycle in
    // the call graph.

    for scc in &ctx.func_call_sccs {
        let scc_nodes = ctx.func_call_graph.get_scc_nodes(scc);
        let count = scc_nodes.len();
        for node in scc_nodes.iter() {
            match node {
                Node::Fun(_) => {}
                _ if count == 1 => {}
                _ => {
                    return Err(scc_error(krate, node, &scc_nodes));
                }
            }
        }
    }
    Ok(())
}
