use crate::ast::{
    AcceptRecursiveType, Datatype, FunctionKind, GenericBoundX, Ident, Krate, Path, Trait, Typ,
    TypX, VirErr,
};
use crate::ast_util::{error, path_as_rust_name};
use crate::context::GlobalCtx;
use crate::recursion::Node;
use crate::scc::Graph;
use air::ast::Span;
use std::collections::{HashMap, HashSet};

// true means that the type is derived from a TypParam,
// which, for a datatype, means that the type can't be the datatype itself.
// (Example: in D<A> { ... x: A::X::Y, ... }, A::X::Y can't be D<...>.)
pub(crate) fn rooted_in_typ_param(typ: &Typ) -> bool {
    match &**typ {
        TypX::TypParam(_) => true,
        TypX::Projection { self_typ, .. } => rooted_in_typ_param(self_typ),
        _ => false,
    }
}

// To enable decreases clauses on datatypes while treating the datatypes as inhabited in specs,
// we need to make sure that the datatypes have base cases, not just inductive cases.
// This also checks that there is at least one variant, so that spec matches are safe.
// It also makes sure that (in the formal semantics) we can construct default values for
// datatypes that aren't just "bottom", so that the values can be pattern matched (see
// the OOPSLA 2023 paper and corresponding arXiv paper).
fn check_well_founded(
    datatypes: &HashMap<Path, Datatype>,
    datatypes_well_founded: &mut HashSet<Path>,
    path: &Path,
) -> bool {
    if datatypes_well_founded.contains(path) {
        return true;
    }
    if !datatypes.contains_key(path) {
        panic!("{:?}", path);
    }
    let datatype = &datatypes[path];
    let mut typ_param_accept: HashMap<Ident, AcceptRecursiveType> = HashMap::new();
    for (x, _, accept_rec) in datatype.x.typ_params.iter() {
        typ_param_accept.insert(x.clone(), *accept_rec);
    }
    'variants: for variant in datatype.x.variants.iter() {
        for field in variant.a.iter() {
            let (typ, _, _) = &field.a;
            if !check_well_founded_typ(datatypes, datatypes_well_founded, &typ_param_accept, typ) {
                // inductive case
                continue 'variants;
            }
        }
        // Found a base case variant
        datatypes_well_founded.insert(path.clone());
        return true;
    }
    // No base cases found, only inductive cases
    return false;
}

fn check_well_founded_typ(
    datatypes: &HashMap<Path, Datatype>,
    datatypes_well_founded: &mut HashSet<Path>,
    typ_param_accept: &HashMap<Ident, AcceptRecursiveType>,
    typ: &Typ,
) -> bool {
    match &**typ {
        TypX::Bool | TypX::Int(_) | TypX::ConstInt(_) | TypX::StrSlice | TypX::Char => true,
        TypX::Boxed(_) | TypX::TypeId | TypX::Air(_) => {
            panic!("internal error: unexpected type in check_well_founded_typ")
        }
        TypX::TypParam(x) => match typ_param_accept[x] {
            AcceptRecursiveType::Reject => true,
            AcceptRecursiveType::RejectInGround => true,
            AcceptRecursiveType::Accept => false,
        },
        TypX::Lambda(_, ret) => {
            // This supports decreases on fields of function type (e.g. for infinite maps)
            check_well_founded_typ(datatypes, datatypes_well_founded, typ_param_accept, ret)
        }
        TypX::Tuple(typs) => {
            // tuples are just datatypes and therefore have a height in decreases clauses,
            // so we need to include them in the well foundedness checks
            for typ in typs.iter() {
                if !check_well_founded_typ(datatypes, datatypes_well_founded, typ_param_accept, typ)
                {
                    return false;
                }
            }
            true
        }
        TypX::Datatype(path, targs) => {
            if !datatypes_well_founded.contains(path) {
                return false;
            }
            // For each targ:
            // - if the corresponding type parameter is Accept, accept the targ unconditionally
            // - otherwise, recurse on targ
            let tparams = &datatypes[path].x.typ_params;
            assert!(targs.len() == tparams.len());
            for (tparam, targ) in tparams.iter().zip(targs.iter()) {
                let (_, _, accept_rec) = tparam;
                if *accept_rec != AcceptRecursiveType::Accept {
                    if !check_well_founded_typ(
                        datatypes,
                        datatypes_well_founded,
                        typ_param_accept,
                        targ,
                    ) {
                        return false;
                    }
                }
            }
            true
        }
        TypX::Decorate(_, t) => {
            check_well_founded_typ(datatypes, datatypes_well_founded, typ_param_accept, t)
        }
        TypX::Projection { .. } if rooted_in_typ_param(typ) => true,
        TypX::Projection { .. } => false,
        TypX::AnonymousClosure(..) => {
            unimplemented!();
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
    tparams: HashMap<Ident, AcceptRecursiveType>,
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
        TypX::Char => Ok(()),
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
        TypX::AnonymousClosure(..) => {
            unimplemented!();
        }
        TypX::Tuple(ts) => {
            for t in ts.iter() {
                check_positive_uses(global, local, polarity, t)?;
            }
            Ok(())
        }
        TypX::Datatype(path, ts) => {
            // Check path
            if global.type_graph.in_same_scc(path, &local.my_datatype) {
                match polarity {
                    Some(true) => {}
                    _ => {
                        return error(
                            &local.span,
                            format!(
                                "Type {} recursively uses type {} in a non-positive position",
                                path_as_rust_name(&local.my_datatype),
                                path_as_rust_name(path)
                            ),
                        );
                    }
                }
            }
            let typ_params = &global.datatypes[path].x.typ_params;
            for ((_, _, accept_rec), t) in typ_params.iter().zip(ts.iter()) {
                let strictly_positive = *accept_rec != AcceptRecursiveType::Reject;
                let t_polarity =
                    if strictly_positive && polarity == Some(true) { Some(true) } else { None };
                check_positive_uses(global, local, t_polarity, t)?;
            }
            Ok(())
        }
        TypX::Decorate(_, t) => check_positive_uses(global, local, polarity, t),
        TypX::Boxed(t) => check_positive_uses(global, local, polarity, t),
        TypX::TypParam(x) => {
            let strictly_positive = local.tparams[x] != AcceptRecursiveType::Reject;
            match (strictly_positive, polarity) {
                (false, _) => Ok(()),
                (true, Some(true)) => Ok(()),
                (true, _) => error(
                    &local.span,
                    format!(
                        "Type parameter {} must be declared #[verifier::reject_recursive_types] to be used in a non-positive position",
                        x
                    ),
                ),
            }
        }
        TypX::Projection { .. } => {
            // If rooted_in_typ_param(typ), conservatively treat this like a type parameter
            // that isn't allowed in a non-positive position.
            // Otherwise, conservatively assume that the projection could be our own datatype,
            // which isn't allowed in a non-positive position.
            match polarity {
                Some(true) => Ok(()),
                _ => {
                    return error(
                        &local.span,
                        "Cannot use a projection type in a non-positive position",
                    );
                }
            }
        }
        TypX::TypeId => Ok(()),
        TypX::ConstInt(_) => Ok(()),
        TypX::Air(_) => Ok(()),
    }
}

pub(crate) fn build_datatype_graph(krate: &Krate) -> Graph<Path> {
    let mut type_graph: Graph<Path> = Graph::new();

    // If datatype D1 has a field whose type mentions datatype D2, create a graph edge D1 --> D2
    for datatype in &krate.datatypes {
        type_graph.add_node(datatype.x.path.clone());
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
    return type_graph;
}

pub(crate) fn check_recursive_types(krate: &Krate) -> Result<(), VirErr> {
    let type_graph = build_datatype_graph(krate);
    let mut datatypes: HashMap<Path, Datatype> = HashMap::new();
    let mut datatypes_well_founded: HashSet<Path> = HashSet::new();

    for datatype in &krate.datatypes {
        datatypes.insert(datatype.x.path.clone(), datatype.clone());
    }

    let global = CheckPositiveGlobal { datatypes, type_graph };

    for function in &krate.functions {
        let mut typ_params = function.x.typ_bounds.iter();
        if let FunctionKind::TraitMethodDecl { .. } = function.x.kind {
            let (self_name, _) = typ_params.next().expect("self type parameter");
            assert!(self_name == &crate::def::trait_self_type_param());
        }
        for (_name, bound) in typ_params {
            match &**bound {
                GenericBoundX::Traits(ts) if function.x.attrs.broadcast_forall && ts.len() != 0 => {
                    // See the todo!() in func_to_air.rs
                    return error(
                        &function.span,
                        "not yet supported: bounds on broadcast_forall function type parameters",
                    );
                }
                GenericBoundX::Traits(..) => {}
            }
        }
    }

    for tr in &krate.traits {
        for (_name, bound, _positive) in tr.x.typ_params.iter() {
            match &**bound {
                GenericBoundX::Traits(_) => {}
            }
        }
    }

    for datatype in &krate.datatypes {
        let mut tparams: HashMap<Ident, AcceptRecursiveType> = HashMap::new();
        for (name, bound, accept_rec) in datatype.x.typ_params.iter() {
            match &**bound {
                GenericBoundX::Traits(_) => {}
            }
            tparams.insert(name.clone(), *accept_rec);
        }
        let local = CheckPositiveLocal {
            span: datatype.span.clone(),
            my_datatype: datatype.x.path.clone(),
            tparams,
        };
        for variant in datatype.x.variants.iter() {
            for field in variant.a.iter() {
                // Check that field type only uses SCC siblings in positive positions
                let (typ, _, _) = &field.a;
                check_positive_uses(&global, &local, Some(true), typ)?;
            }
        }
    }

    let type_sccs = global.type_graph.sort_sccs();
    for scc in &type_sccs {
        let mut converged = false;
        loop {
            let count = datatypes_well_founded.len();
            for path in &global.type_graph.get_scc_nodes(scc) {
                let wf = check_well_founded(&global.datatypes, &mut datatypes_well_founded, path);
                if converged && !wf {
                    let span = &global.datatypes[path].span;
                    return error(span, "datatype must have at least one non-recursive variant");
                }
            }
            if converged {
                break;
            }
            converged = count == datatypes_well_founded.len();
        }
    }

    Ok(())
}

fn scc_error(krate: &Krate, head: &Node, nodes: &Vec<Node>) -> VirErr {
    let msg =
        "found a cyclic self-reference in a trait definition, which may result in nontermination"
            .to_string();
    let mut err = air::messages::error_bare(msg);
    for node in nodes {
        let mut push = |node: &Node, span: Span| {
            if node == head {
                err = err.primary_span(&span);
            } else {
                let msg = "may be part of cycle".to_string();
                err = err.secondary_label(&span, msg);
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
            Node::DatatypeTraitBound { self_typ, .. } => {
                if let TypX::Datatype(dt_path, _) = &**self_typ {
                    if let Some(d) = krate.datatypes.iter().find(|d| d.x.path == *dt_path) {
                        let span = d.span.clone();
                        push(node, span);
                    }
                }
            }
        }
    }
    err
}

pub(crate) fn add_trait_to_graph(call_graph: &mut Graph<Node>, trt: &Trait) {
    // For
    //   trait T<A1: U1, ..., An: Un>
    // Add T --> U1, ..., T --> Un edges (see comments below for more details.)
    let t_node = Node::Trait(trt.x.name.clone());
    for (_, bound, _) in trt.x.typ_params.iter() {
        let GenericBoundX::Traits(bounds) = &**bound;
        for u_path in bounds {
            let u_node = Node::Trait(u_path.clone());
            call_graph.add_edge(t_node.clone(), u_node);
        }
    }
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
    //     f: Fn(x: Self, y: Self) -> bool,
    //     g: Fn(x: Self, y: Self) -> Self { requires(f(x, y)); },
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
    // Note that we don't have nodes for datatypes D, because the datatype itself
    // does not carry its trait implementations -- the trait implementations D: T
    // are separate from D, and are needed only when we instantiate A: T with D: T,
    // not when we construct a value of type D.

    // To handle bounds on trait parameters like this:
    //   trait T<A: U> {
    //     fn f(x: Self, y: Self) -> bool;
    //     fn g(x: Self, y: Self) -> Self { requires(f(x, y)); };
    //   }
    // We can store a Dictionary_U inside Dictionary_T:
    //   struct Dictionary_T<Self, A> {
    //     a: Dictionary_U<A>,
    //     f: Fn(x: Self, y: Self) -> bool,
    //     g: Fn(x: Self, y: Self) -> Self { requires(f(x, y)); },
    //   }
    // This adds an edge:
    //   - T --> U
    // This also ensures that whenever A is used in f and g,
    // the dictionary a: Dictionary_U<A> is available.

    // For bounds on datatype parameters like this:
    //   struct D<A: U> {
    //     x: A,
    //   }
    // we don't do anything extra.  As stated above, D carries just its fields,
    // and nothing related to traits and dictionaries.

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
