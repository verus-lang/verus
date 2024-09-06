use crate::ast::{
    AcceptRecursiveType, Datatype, FunctionKind, GenericBound, GenericBoundX, Ident, Idents,
    ImplPath, Krate, Path, Trait, Typ, TypX, VirErr,
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
        for field in variant.fields.iter() {
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
        TypX::Bool | TypX::Int(_) | TypX::ConstInt(_) | TypX::Primitive(_, _) => true,
        TypX::Boxed(_) | TypX::TypeId | TypX::Air(_) => {
            panic!("internal error: unexpected type in check_well_founded_typ")
        }
        TypX::TypParam(x) => match typ_param_accept[x] {
            AcceptRecursiveType::Reject => true,
            AcceptRecursiveType::RejectInGround => true,
            AcceptRecursiveType::Accept => false,
        },
        TypX::SpecFn(_, ret) => {
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
        TypX::Decorate(_, _targ, t) => {
            // We don't need to check the allocator type argument
            // (We can consider it to be AcceptRecursiveType::Accept.
            // This is ok because, e.g., the spec-encoding of Box<T, Allocator> doesn't
            // depends on the spec-encoding of Allocator)
            check_well_founded_typ(datatypes, datatypes_well_founded, typ_param_accept, t)
        }
        TypX::Projection { .. } => {
            // Treat projection as AcceptRecursiveType::Reject,
            // and rely on type_graph to reject any cycles
            true
        }
        TypX::FnDef(_fun, _type_args, _res_fun) => {
            // I don't think there's any way to refer to explicitly refer to these types in
            // Rust code, so it shouldn't be possible to use on in a struct definition
            // or anything.
            // Though this type is basically a named singleton type, so
            // the correct result here would probably be `Ok(true)`
            panic!("FnDef type is not expected in struct definitions");
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
    TraitImpl(ImplPath),
    // This is used to replace an X --> Y edge with X --> SpanInfo --> Y edges
    // to give more precise span information than X or Y alone provide
    SpanInfo { span_infos_index: usize, text: String },
}

struct CheckPositiveGlobal {
    krate: Krate,
    datatypes: HashMap<Path, Datatype>,
    type_graph: Graph<TypNode>,
    span_infos: Vec<Span>,
}

struct CheckPositiveLocal {
    span: Span,
    my_datatype: Path,
    tparams: HashMap<Ident, AcceptRecursiveType>,
}

pub(crate) fn new_span_info_node(span_infos: &mut Vec<Span>, span: Span, text: String) -> Node {
    let node = Node::SpanInfo { span_infos_index: span_infos.len(), text };
    span_infos.push(span);
    node
}

fn new_span_info_typ_node(span_infos: &mut Vec<Span>, span: Span, text: String) -> TypNode {
    let node = TypNode::SpanInfo { span_infos_index: span_infos.len(), text };
    span_infos.push(span);
    node
}

// polarity = Some(true) for positive, Some(false) for negative, None for neither
fn check_positive_uses(
    datatype: &Datatype,
    global: &CheckPositiveGlobal,
    local: &CheckPositiveLocal,
    polarity: Option<bool>,
    typ: &Typ,
) -> Result<(), VirErr> {
    match &**typ {
        TypX::Bool => Ok(()),
        TypX::Int(..) => Ok(()),
        TypX::SpecFn(ts, tr) => {
            /* REVIEW: we could track both positive and negative polarity,
               but strict positivity is more conservative
            let flip_polarity = match polarity {
                None => None,
                Some(b) => Some(!b),
            };
            */
            let flip_polarity = None; // strict positivity
            for t in ts.iter() {
                check_positive_uses(datatype, global, local, flip_polarity, t)?;
            }
            check_positive_uses(datatype, global, local, polarity, tr)?;
            Ok(())
        }
        TypX::AnonymousClosure(..) => {
            unimplemented!();
        }
        TypX::Tuple(ts) => {
            for t in ts.iter() {
                check_positive_uses(datatype, global, local, polarity, t)?;
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
                check_positive_uses(datatype, global, local, t_polarity, t)?;
            }
            for impl_path in impl_paths.iter() {
                // REVIEW: this check isn't actually about polarity; should it be somewhere else?
                let impl_node = TypNode::TraitImpl(impl_path.clone());
                if global.type_graph.in_same_scc(&impl_node, &my_node) {
                    let scc_rep = global.type_graph.get_scc_rep(&my_node);
                    let scc_nodes = global.type_graph.shortest_cycle_back_to_self(&scc_rep);
                    return Err(type_scc_error(
                        &global.krate,
                        &global.span_infos,
                        &my_node,
                        &scc_nodes,
                    ));
                }
            }
            Ok(())
        }
        TypX::Decorate(_, _, t) => check_positive_uses(datatype, global, local, polarity, t),
        TypX::Primitive(_, ts) => {
            for t in ts.iter() {
                check_positive_uses(datatype, global, local, polarity, t)?;
            }
            Ok(())
        }
        TypX::FnDef(_fun, _type_args, _res_fun) => {
            panic!("FnDef type is not expected in struct definitions");
        }
        TypX::Boxed(t) => check_positive_uses(datatype, global, local, polarity, t),
        TypX::TypParam(x) => {
            let strictly_positive = local.tparams[x] != AcceptRecursiveType::Reject;
            match (strictly_positive, polarity) {
                (false, _) => Ok(()),
                (true, Some(true)) => Ok(()),
                (true, _) => Err(error(
                    &local.span,
                    format!(
                        "Type parameter {} of {} must be declared #[verifier::reject_recursive_types] to be used in a non-positive position",
                        x,
                        path_as_friendly_rust_name(&datatype.x.path),
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

pub(crate) fn build_datatype_graph(krate: &Krate, span_infos: &mut Vec<Span>) -> Graph<TypNode> {
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
        let trait_impl_src = TypNode::TraitImpl(ImplPath::TraitImplPath(a.x.impl_path.clone()));
        let src = new_span_info_typ_node(
            span_infos,
            a.span.clone(),
            ": associated type definition, which may depend on other trait implementations \
                to satisfy type bounds"
                .to_string(),
        );
        type_graph.add_edge(trait_impl_src, src.clone());
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

    type_graph
}

pub(crate) fn check_recursive_types(krate: &Krate) -> Result<(), VirErr> {
    let mut span_infos: Vec<Span> = Vec::new();
    let type_graph = build_datatype_graph(krate, &mut span_infos);
    let mut datatypes: HashMap<Path, Datatype> = HashMap::new();
    let mut datatypes_well_founded: HashSet<Path> = HashSet::new();

    for datatype in &krate.datatypes {
        datatypes.insert(datatype.x.path.clone(), datatype.clone());
    }

    let global = CheckPositiveGlobal { krate: krate.clone(), datatypes, type_graph, span_infos };

    for function in &krate.functions {
        if let FunctionKind::TraitMethodDecl { .. } = function.x.kind {
            assert!(&function.x.typ_params[0] == &crate::def::trait_self_type_param());
        }
    }

    for tr in &krate.traits {
        for bound in tr.x.typ_bounds.iter() {
            match &**bound {
                GenericBoundX::Trait(..) => {}
                GenericBoundX::TypEquality(..) => {}
                GenericBoundX::ConstTyp(..) => {}
            }
        }
    }

    for datatype in &krate.datatypes {
        let mut tparams: HashMap<Ident, AcceptRecursiveType> = HashMap::new();
        for (name, accept_rec) in datatype.x.typ_params.iter() {
            tparams.insert(name.clone(), *accept_rec);
        }
        let local = CheckPositiveLocal {
            span: datatype.span.clone(),
            my_datatype: datatype.x.path.clone(),
            tparams,
        };
        for bound in datatype.x.typ_bounds.iter() {
            match &**bound {
                GenericBoundX::Trait(..) => {}
                GenericBoundX::TypEquality(_, _, _, typ) => {
                    // This bound introduces a name (an abbreviation) for typ,
                    // so assume that we're going to use the typ in any position.
                    // (Actually, Rust's type system probably already stops a datatype
                    // from mentioning itself in its own type equality bound, but there's
                    // no harm in checking again.)
                    check_positive_uses(datatype, &global, &local, None, typ)?;
                }
                GenericBoundX::ConstTyp(..) => {}
            }
        }
        for variant in datatype.x.variants.iter() {
            for field in variant.fields.iter() {
                // Check that field type only uses SCC siblings in positive positions
                let (typ, _, _) = &field.a;
                check_positive_uses(datatype, &global, &local, Some(true), typ)?;
            }
        }
    }

    let type_sccs = global.type_graph.sort_sccs();
    for scc in &type_sccs {
        for node in &global.type_graph.get_scc_nodes(scc) {
            match node {
                TypNode::TraitImpl(_) if global.type_graph.node_is_in_cycle(node) => {
                    return Err(type_scc_error(
                        krate,
                        &global.span_infos,
                        node,
                        &global.type_graph.shortest_cycle_back_to_self(scc),
                    ));
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

fn type_scc_error(
    krate: &Krate,
    span_infos: &Vec<Span>,
    head: &TypNode,
    nodes: &Vec<TypNode>,
) -> VirErr {
    let msg = "found a cyclic self-reference in a definition, which may result in nontermination"
        .to_string();
    let mut err = crate::messages::error_bare(msg);
    for (i, node) in nodes.iter().enumerate() {
        let mut push = |node: &TypNode, span: Span, text: &str| {
            if node == head {
                err = err.primary_span(&span);
            }
            let msg = format!(
                "may be part of cycle (node {} of {} in cycle){}",
                i + 1,
                nodes.len(),
                text
            );
            err = err.secondary_label(&span, msg);
        };
        match node {
            TypNode::Datatype(path) => {
                if let Some(d) = krate.datatypes.iter().find(|t| t.x.path == *path) {
                    let span = d.span.clone();
                    push(node, span, ": type definition");
                }
            }
            TypNode::TraitImpl(impl_path) => {
                if let Some(t) = krate
                    .trait_impls
                    .iter()
                    .find(|t| ImplPath::TraitImplPath(t.x.impl_path.clone()) == *impl_path)
                {
                    let span = t.span.clone();
                    push(node, span, ": implementation of trait for a type");
                }
            }
            TypNode::SpanInfo { span_infos_index, text } => {
                push(node, span_infos[*span_infos_index].clone(), text);
            }
        }
    }
    err
}

fn scc_error(krate: &Krate, span_infos: &Vec<Span>, nodes: &Vec<Node>) -> VirErr {
    // Special case this error message because it doesn't look like
    // a 'trait' error to the user (even though we conceptualize it as a trait
    // error in VIR)
    let mut has_req_ens = false;
    let mut is_only_req_ens = true;
    for node in nodes.iter() {
        match node {
            Node::TraitImpl(ImplPath::FnDefImplPath(_)) => {
                has_req_ens = true;
            }
            Node::Fun(_) => {}
            Node::SpanInfo { .. } => {}
            _ => {
                is_only_req_ens = false;
            }
        }
    }
    let do_req_ens_error = has_req_ens && is_only_req_ens;

    let msg = if do_req_ens_error {
        "cyclic dependency in the requires/ensures of function"
    } else {
        "found a cyclic self-reference in a definition, which may result in nontermination"
    };
    let msg = msg.to_string();
    let mut err = crate::messages::error_bare(msg);

    // Try to put Node::Fun first, since this is likely to be the easiest to understand
    let mut nodes = nodes.clone();
    if let Some(i) = nodes.iter().position(|n| matches!(n, Node::Fun(..))) {
        let len = nodes.len();
        let second_part = nodes.split_off(i);
        nodes.splice(0..0, second_part);
        assert!(nodes.len() == len);
    }

    for (i, node) in nodes.iter().enumerate() {
        let mut push = |span: Span, text: &str| {
            if i == 0 {
                err = err.primary_span(&span);
            }
            let msg = format!(
                "may be part of cycle (node {} of {} in cycle){}",
                i + 1,
                nodes.len(),
                text
            );
            err = err.secondary_label(&span, msg);
        };
        match node {
            Node::Fun(fun)
            | Node::TraitImpl(ImplPath::FnDefImplPath(fun))
            | Node::TraitReqEns(ImplPath::FnDefImplPath(fun), _) => {
                if let Some(f) = krate.functions.iter().find(|f| f.x.name == *fun) {
                    let span = f.span.clone();
                    push(span, ": function definition, whose body may have dependencies");
                }
            }
            Node::Datatype(path) => {
                if let Some(d) = krate.datatypes.iter().find(|t| t.x.path == *path) {
                    let span = d.span.clone();
                    push(span, ": type definition");
                }
            }
            Node::Trait(trait_path) => {
                if let Some(t) = krate.traits.iter().find(|t| t.x.name == *trait_path) {
                    let span = t.span.clone();
                    push(span, ": declaration of trait");
                }
            }
            Node::TraitImpl(ImplPath::TraitImplPath(impl_path))
            | Node::TraitReqEns(ImplPath::TraitImplPath(impl_path), _) => {
                if let Some(t) =
                    krate.trait_impls.iter().find(|t| t.x.impl_path.clone() == *impl_path)
                {
                    let span = t.span.clone();
                    push(span, ": implementation of trait for a type");
                }
            }
            Node::ModuleReveal(path) => {
                if let Some(t) = krate.modules.iter().find(|m| &m.x.path == path) {
                    let span = t.span.clone();
                    push(span, ": module-level reveal");
                }
            }
            Node::SpanInfo { span_infos_index, text } => {
                push(span_infos[*span_infos_index].clone(), text);
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
    let (bound_path, args) = match &**bound {
        GenericBoundX::Trait(bound_path, args) => (bound_path, args),
        GenericBoundX::TypEquality(..) => {
            return false;
        }
        GenericBoundX::ConstTyp(..) => {
            return false;
        }
    };
    if trait_path == bound_path {
        assert!(args.len() <= typ_params.len());
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
        let u_path = match &**bound {
            GenericBoundX::Trait(u_path, _) => u_path,
            GenericBoundX::TypEquality(u_path, _, _, _) => u_path,
            GenericBoundX::ConstTyp(..) => {
                continue;
            }
        };
        let u_node = Node::Trait(u_path.clone());
        call_graph.add_edge(t_node.clone(), u_node);
    }
}

pub(crate) fn add_trait_impl_to_graph(
    span_infos: &mut Vec<Span>,
    call_graph: &mut Graph<Node>,
    t: &crate::ast::TraitImpl,
) {
    // For
    //   trait T<...> where ...: U1(...), ..., ...: Un(...)
    //   impl T<t1...tn> for ... { ... }
    // Add necessary impl_T_for_* --> impl_Ui_for_* edges
    // This corresponds to instantiating the a: Dictionary_U<A> field in the comments below
    let trait_impl_src_node = Node::TraitImpl(ImplPath::TraitImplPath(t.x.impl_path.clone()));
    let req_ens_src_node = Node::TraitReqEns(ImplPath::TraitImplPath(t.x.impl_path.clone()), false);
    let src_node = new_span_info_node(
        span_infos,
        t.x.trait_typ_arg_impls.span.clone(),
        ": an implementation of a trait, which depends on (1) any supertraits \
            of the trait or (2) any type arguments passed to the trait's type parameters. \
            Specifically, (1) the implementation of a subtrait builds on, and depends on, \
            the implementations of all supertraits of the subtrait, and \
            (2) the implementation of a trait must satisfy any bounds on any type arguments \
            used to instantiate the type parameters of the trait (including bounds on `Self`), \
            so this implementation may depend on other implementations to satisfy these bounds."
            .to_string(),
    );
    call_graph.add_edge(trait_impl_src_node, src_node.clone());
    for imp in t.x.trait_typ_arg_impls.x.iter() {
        if ImplPath::TraitImplPath(t.x.impl_path.clone()) != *imp {
            call_graph.add_edge(src_node.clone(), Node::TraitImpl(imp.clone()));
            call_graph.add_edge(req_ens_src_node.clone(), Node::TraitReqEns(imp.clone(), true));
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
    // (Note that since the members dictionary_T_for_D_f and dictionary_T_for_D_g precede the
    // construction of the Dictionary_T value, they do not depend on the implementation
    // of T for D, and they can be called as ordinary functions without needing
    // the implementation of T for D.  They can also call each other.)
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

    // To handle bounds on trait methods like this:
    //   trait T {
    //     fn f<A: U>(x: Self, y: Self) -> bool;
    //     fn g(x: Self, y: Self) -> Self { requires(f(x, y)); };
    //   }
    // We take a Dictionary_U as a parameter:
    //   struct Dictionary_T<Self, A> {
    //     f: Fn<A>(a: Dictionary_U<A>, x: Self, y: Self) -> bool,
    //     g: Fn(x: Self, y: Self) -> Self { requires(f(x, y)); },
    //   }
    // This adds an edge:
    //   - f --> U
    // which, together with T --> f, creates a path T --> U
    // This also ensures that whenever A is used in f,
    // the dictionary a: Dictionary_U<A> is available.

    // In Rust, declaring a subtrait "trait T: U" is equivalent to declaring
    // a trait with a Self bound: "trait T where Self: U".
    // We handle the bound "Self: U" the same as we handle a bound "A: U"
    // on any other type parameter A.
    // (Note that Rust also adds an implicit recursive "Self: T" bound for every "trait T";
    // as explained above, we remove this one particular "Self: T" bound,
    // even though we retain every other bounds on Self.)
    // For example:
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

    // To handle associated types, we pass each associated type in a trait as a separate parameter:
    //   trait T {
    //     type X;
    //     type Y;
    //     fn f(...);
    //   }
    //   fn g<A: T>(x: &A::X, y: &A::Y) { ... }
    // The bound g<A: T> is interpreted as g<A, A_X, A_Y>(x: &A_X, y: &A_Y).
    // (Note: passing each associated type separately is just for the hypothetical Coq/F* encoding;
    // in the SMT encoding, we use a single parameter rather than separate parameters.)
    // This separation makes it easier to encode type equality constraints such as:
    //   fn g<A: T<X = u8>>
    // which becomes g<A, A_Y>(x: &u8, y: &A_Y).

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
        for node in ctx.func_call_graph.get_scc_nodes(scc).iter() {
            match node {
                // handled by decreases checking:
                Node::Fun(_) | Node::TraitReqEns(..) => {}
                // disallowed cycles:
                _ if ctx.func_call_graph.node_is_in_cycle(node) => {
                    return Err(scc_error(
                        krate,
                        &ctx.datatype_graph_span_infos,
                        &ctx.func_call_graph.shortest_cycle_back_to_self(node),
                    ));
                }
                _ => {}
            }
        }
    }
    Ok(())
}
