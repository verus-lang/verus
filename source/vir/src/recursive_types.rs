use crate::ast::{
    AcceptRecursiveType, Datatype, FunctionKind, GenericBound, GenericBoundX, Ident, Idents, Krate,
    Path, Trait, Typ, TypX, VirErr,
};
use crate::ast_util::path_as_friendly_rust_name;
use crate::context::GlobalCtx;
use crate::messages::{error, Span};
use crate::recursion::Node;
use crate::scc::Graph;
use std::collections::{HashMap, HashSet};

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
    for (x, accept_rec) in datatype.x.typ_params.iter() {
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
        TypX::Bool
        | TypX::Int(_)
        | TypX::ConstInt(_)
        | TypX::StrSlice
        | TypX::Char
        | TypX::Primitive(_, _) => true,
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
        TypX::Datatype(path, targs, _) => {
            if !datatypes_well_founded.contains(path) {
                return false;
            }
            // For each targ:
            // - if the corresponding type parameter is Accept, accept the targ unconditionally
            // - otherwise, recurse on targ
            let tparams = &datatypes[path].x.typ_params;
            assert!(targs.len() == tparams.len());
            for (tparam, targ) in tparams.iter().zip(targs.iter()) {
                let (_, accept_rec) = tparam;
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
        TypX::Projection { .. } => {
            // Treat projection as AcceptRecursiveType::Reject,
            // and rely on type_graph to reject any cycles
            true
        }
        TypX::AnonymousClosure(..) => {
            unimplemented!();
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
// REVIEW: should we also have Trait(Path) here?
pub(crate) enum TypNode {
    Datatype(Path),
    TraitImpl(Path),
}

struct CheckPositiveGlobal {
    krate: Krate,
    datatypes: HashMap<Path, Datatype>,
    type_graph: Graph<TypNode>,
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
        TypX::Datatype(path, ts, impl_paths) => {
            // Check path
            let target_node = TypNode::Datatype(path.clone());
            let my_node = TypNode::Datatype(local.my_datatype.clone());
            if global.type_graph.in_same_scc(&target_node, &my_node) {
                match polarity {
                    Some(true) => {}
                    _ => {
                        return Err(error(
                            &local.span,
                            format!(
                                "Type {} recursively uses type {} in a non-positive position",
                                path_as_friendly_rust_name(&local.my_datatype),
                                path_as_friendly_rust_name(path)
                            ),
                        ));
                    }
                }
            }
            let typ_params = &global.datatypes[path].x.typ_params;
            for ((_, accept_rec), t) in typ_params.iter().zip(ts.iter()) {
                let strictly_positive = *accept_rec != AcceptRecursiveType::Reject;
                let t_polarity =
                    if strictly_positive && polarity == Some(true) { Some(true) } else { None };
                check_positive_uses(global, local, t_polarity, t)?;
            }
            for impl_path in impl_paths.iter() {
                // REVIEW: this check isn't actually about polarity; should it be somewhere else?
                let impl_node = TypNode::TraitImpl(impl_path.clone());
                if global.type_graph.in_same_scc(&impl_node, &my_node) {
                    let scc_rep = global.type_graph.get_scc_rep(&my_node);
                    let scc_nodes = global.type_graph.get_scc_nodes(&scc_rep);
                    return Err(type_scc_error(&global.krate, &my_node, &scc_nodes));
                }
            }
            Ok(())
        }
        TypX::Decorate(_, t) => check_positive_uses(global, local, polarity, t),
        TypX::Primitive(_, ts) => {
            for t in ts.iter() {
                check_positive_uses(global, local, polarity, t)?;
            }
            Ok(())
        }
        TypX::Boxed(t) => check_positive_uses(global, local, polarity, t),
        TypX::TypParam(x) => {
            let strictly_positive = local.tparams[x] != AcceptRecursiveType::Reject;
            match (strictly_positive, polarity) {
                (false, _) => Ok(()),
                (true, Some(true)) => Ok(()),
                (true, _) => Err(error(
                    &local.span,
                    format!(
                        "Type parameter {} must be declared #[verifier::reject_recursive_types] to be used in a non-positive position",
                        x
                    ),
                )),
            }
        }
        TypX::Projection { .. } => {
            // Treat projection as AcceptRecursiveType::Reject,
            // and rely on type_graph to reject any cycles
            Ok(())
        }
        TypX::TypeId => Ok(()),
        TypX::ConstInt(_) => Ok(()),
        TypX::Air(_) => Ok(()),
    }
}

// meant to be called from a type visitor
fn add_one_type_to_graph(type_graph: &mut Graph<TypNode>, src: &TypNode, typ: &Typ) {
    if let TypX::Datatype(path, _, impl_paths) = &**typ {
        type_graph.add_edge(src.clone(), TypNode::Datatype(path.clone()));
        for impl_path in impl_paths.iter() {
            type_graph.add_edge(src.clone(), TypNode::TraitImpl(impl_path.clone()));
        }
    }
}

pub(crate) fn build_datatype_graph(krate: &Krate) -> Graph<TypNode> {
    let mut type_graph: Graph<TypNode> = Graph::new();

    // If datatype D1 has a field whose type mentions datatype D2, create a graph edge D1 --> D2
    for datatype in &krate.datatypes {
        type_graph.add_node(TypNode::Datatype(datatype.x.path.clone()));
        let mut ft = |type_graph: &mut Graph<TypNode>, typ: &Typ| {
            add_one_type_to_graph(type_graph, &TypNode::Datatype(datatype.x.path.clone()), typ);
            Ok(typ.clone())
        };
        crate::ast_visitor::map_datatype_visitor_env(datatype, &mut type_graph, &mut ft).unwrap();
    }

    for a in &krate.assoc_type_impls {
        let src = TypNode::TraitImpl(a.x.impl_path.clone());
        for impl_path in a.x.impl_paths.iter() {
            let dst = TypNode::TraitImpl(impl_path.clone());
            type_graph.add_edge(src.clone(), dst);
        }

        let mut ft = |type_graph: &mut Graph<TypNode>, typ: &Typ| {
            add_one_type_to_graph(type_graph, &src, typ);
            Ok(typ.clone())
        };
        crate::ast_visitor::map_assoc_type_impl_visitor_env(a, &mut type_graph, &mut ft).unwrap();
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

    let global = CheckPositiveGlobal { krate: krate.clone(), datatypes, type_graph };

    for function in &krate.functions {
        if let FunctionKind::TraitMethodDecl { .. } = function.x.kind {
            assert!(&function.x.typ_params[0] == &crate::def::trait_self_type_param());
        }
    }

    for tr in &krate.traits {
        for bound in tr.x.typ_bounds.iter() {
            match &**bound {
                GenericBoundX::Trait(..) => {}
            }
        }
    }

    for datatype in &krate.datatypes {
        let mut tparams: HashMap<Ident, AcceptRecursiveType> = HashMap::new();
        for (name, accept_rec) in datatype.x.typ_params.iter() {
            tparams.insert(name.clone(), *accept_rec);
        }
        for bound in datatype.x.typ_bounds.iter() {
            match &**bound {
                GenericBoundX::Trait(..) => {}
            }
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
        for node in &global.type_graph.get_scc_nodes(scc) {
            match node {
                TypNode::TraitImpl(_) if global.type_graph.node_is_in_cycle(node) => {
                    return Err(type_scc_error(krate, node, &global.type_graph.get_scc_nodes(scc)));
                }
                _ => {}
            }
        }

        let mut converged = false;
        loop {
            let count = datatypes_well_founded.len();
            for node in &global.type_graph.get_scc_nodes(scc) {
                if let TypNode::Datatype(path) = node {
                    let wf =
                        check_well_founded(&global.datatypes, &mut datatypes_well_founded, path);
                    if converged && !wf {
                        let span = &global.datatypes[path].span;
                        return Err(error(
                            span,
                            "datatype must have at least one non-recursive variant",
                        ));
                    }
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

fn type_scc_error(krate: &Krate, head: &TypNode, nodes: &Vec<TypNode>) -> VirErr {
    let msg =
        "found a cyclic self-reference in a trait definition, which may result in nontermination"
            .to_string();
    let mut err = crate::messages::error_bare(msg);
    for node in nodes {
        let mut push = |node: &TypNode, span: Span| {
            if node == head {
                err = err.primary_span(&span);
            } else {
                let msg = "may be part of cycle".to_string();
                err = err.secondary_label(&span, msg);
            }
        };
        match node {
            TypNode::Datatype(path) => {
                if let Some(d) = krate.datatypes.iter().find(|t| t.x.path == *path) {
                    let span = d.span.clone();
                    push(node, span);
                }
            }
            TypNode::TraitImpl(impl_path) => {
                if let Some(t) = krate.trait_impls.iter().find(|t| t.x.impl_path == *impl_path) {
                    let span = t.span.clone();
                    push(node, span);
                }
            }
        }
    }
    err
}

fn scc_error(krate: &Krate, head: &Node, nodes: &Vec<Node>) -> VirErr {
    let msg =
        "found a cyclic self-reference in a trait definition, which may result in nontermination"
            .to_string();
    let mut err = crate::messages::error_bare(msg);
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
            Node::Datatype(path) => {
                if let Some(d) = krate.datatypes.iter().find(|t| t.x.path == *path) {
                    let span = d.span.clone();
                    push(node, span);
                }
            }
            Node::Trait(trait_path) => {
                if let Some(t) = krate.traits.iter().find(|t| t.x.name == *trait_path) {
                    let span = t.span.clone();
                    push(node, span);
                }
            }
            Node::TraitImpl(impl_path) => {
                if let Some(t) = krate.trait_impls.iter().find(|t| t.x.impl_path == *impl_path) {
                    let span = t.span.clone();
                    push(node, span);
                }
            }
        }
    }
    err
}

pub(crate) fn suppress_bound_in_trait_decl(
    trait_path: &Path,
    typ_params: &Idents,
    bound: &GenericBound,
) -> bool {
    // For a member f in a trait T<Self, A1, ..., An>, rustc introduces a bound T(Self, A1, ..., An)
    // into f.  When checking termination for the declaration of f, we disallow this bound,
    // since allowing this bound would allow f to refer to itself recursively, allowing nontermination.
    // (Conceptually, the bound would correspond to a dictionary giving f access to all of T's members,
    // including f itself.)
    // If we didn't suppress the bound, then the bound would add a cycle to the call graph that would
    // always cause a cycle and would cause the trait declaration to be rejected.
    // See the check_traits comments below (particularly the part about not passing T's dictionary into
    // T's own members).
    let GenericBoundX::Trait(bound_path, args) = &**bound;
    if trait_path == bound_path {
        assert!(args.len() == typ_params.len());
        for (typ_param, arg) in typ_params.iter().zip(args.iter()) {
            if let TypX::TypParam(bound_param) = &**arg {
                if typ_param == bound_param {
                    continue;
                }
            }
            return false;
        }
        true
    } else {
        false
    }
}

pub(crate) fn add_trait_to_graph(call_graph: &mut Graph<Node>, trt: &Trait) {
    // For
    //   trait T<...> where ...: U1(...), ..., ...: Un(...)
    // Add T --> U1, ..., T --> Un edges (see comments below for more details.)
    let t_path = &trt.x.name;
    let t_node = Node::Trait(t_path.clone());
    for bound in trt.x.typ_bounds.iter().chain(trt.x.assoc_typs_bounds.iter()) {
        let GenericBoundX::Trait(u_path, _) = &**bound;
        assert_ne!(t_path, u_path);
        let u_node = Node::Trait(u_path.clone());
        call_graph.add_edge(t_node.clone(), u_node);
    }
}

pub(crate) fn add_trait_impl_to_graph(call_graph: &mut Graph<Node>, t: &crate::ast::TraitImpl) {
    // For
    //   trait T<...> where ...: U1(...), ..., ...: Un(...)
    //   impl T<t1...tn> for ... { ... }
    // Add necessary impl_T_for_* --> impl_Ui_for_* edges
    // This corresponds to instantiating the a: Dictionary_U<A> field in the comments below
    let src_node = Node::TraitImpl(t.x.impl_path.clone());
    for imp in t.x.trait_typ_arg_impls.iter() {
        if &t.x.impl_path != imp {
            call_graph.add_edge(src_node.clone(), Node::TraitImpl(imp.clone()));
        }
    }
    // Add impl_T_for_* --> T
    call_graph.add_edge(src_node, Node::Trait(t.x.trait_path.clone()));
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
    // not f(Dictionary_T<Self>, Self, Self).  In general, for a trait T<Self, A1, ... An>,
    // rustc introduces a bound T(Self, A1, ..., An), but we do not make this bound available
    // to the trait member declarations when checking recursion, since it would allow
    // nontermination.)
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
    // traits (D: T) using Node::Trait(T) and Node::TraitImpl(impl for D: T).
    // We add the following edges to the call graph (see recursion::expand_call_graph):
    //   - T --> f for any method f declared by T
    //   - f --> T for any function f<A: T> with type parameter A: T
    //     (more generally, f --> T for any function f with a where-bound T(...))
    //   - f --> T for any function f that implements a method of T in D: T
    //   - D: T --> T
    //     (more generally, trait_impl -> trait)
    //   - f --> D: T where one of f's expressions instantiates A: T with D: T.
    //     (more generally, f --> trait_impl when one of f's expressions uses trait_impl
    //     to satisfy a bound on A1...An)
    //   - D: T --> f where f is one of D's methods that implements T
    //     (more generally, trait_impl --> f when f is one of the methods in trait_impl implementing
    //     trait T)
    // It is an error for Node::Trait(T) or Node::TraitImpl(impl for D: T) to appear in a cycle in
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
    //     a: Dictionary_U<A>, // see add_trait_impl_to_graph
    //     f: Fn(x: Self, y: Self) -> bool,
    //     g: Fn(x: Self, y: Self) -> Self { requires(f(x, y)); },
    //   }
    // This adds an edge:
    //   - T --> U
    // This also ensures that whenever A is used in f and g,
    // the dictionary a: Dictionary_U<A> is available.

    // To handle bounds on Self like this:
    //   trait T: U {
    //     fn f(x: Self, y: Self) -> bool;
    //     fn g(x: Self, y: Self) -> Self { requires(f(x, y)); };
    //   }
    // We can store a Dictionary_U inside Dictionary_T:
    //   struct Dictionary_T<Self> {
    //     a: Dictionary_U<Self>,
    //     f: Fn(x: Self, y: Self) -> bool,
    //     g: Fn(x: Self, y: Self) -> Self { requires(f(x, y)); },
    //   }
    // This adds an edge, like for bounds on trait parameters:
    //   - T --> U
    // This also ensures that whenever Self is used in f and g,
    // the dictionary a: Dictionary_U<Self> is available.

    // To handle bounds on associated types:
    //   trait T {
    //     type Y: U;
    //     fn f(x: Self, y: Y) -> bool;
    //     fn g(x: Self, y: Y) -> Self { requires(f(x, y)); };
    //   }
    // We can store a Dictionary_U inside Dictionary_T:
    //   struct Dictionary_T<Self> {
    //     Y: Type, // an F* Type0
    //     a: Dictionary_U<Y>,
    //     f: Fn(x: Self, y: Y) -> bool,
    //     g: Fn(x: Self, y: Y) -> Self { requires(f(x, y)); },
    //   }
    // This adds an edge, like for bounds on trait parameters:
    //   - T --> U
    // This also ensures that whenever Y is used in f and g,
    // the dictionary a: Dictionary_U<Y> is available.

    // For bounds on datatype parameters like this:
    //   struct D<A: U> {
    //     x: A,
    //   }
    // we use separate type-only dictionaries to represent any associated types in U.
    // This allows us to split the termination checking into two phases:
    // 1) Check datatype definitions using type-only dictionaries
    // 2) Check function definitions using value dictionaries

    for scc in ctx.func_call_sccs.iter() {
        let scc_nodes = ctx.func_call_graph.get_scc_nodes(scc);
        for node in scc_nodes.iter() {
            match node {
                // handled by decreases checking:
                Node::Fun(_) => {}
                _ if ctx.func_call_graph.node_is_in_cycle(node) => {
                    return Err(scc_error(krate, node, &scc_nodes));
                }
                _ => {}
            }
        }
    }
    Ok(())
}
