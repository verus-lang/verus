use crate::ast::{Datatype, DatatypeTransparency, Dt, Path, Primitive, Typ, TypDecoration, TypX};
use crate::ast_visitor::VisitorControlFlow;
use std::collections::HashMap;

/// Used to determine whether `has_resolved` for a given type is trivial or nontrivial.
/// This allows us to avoid cluttering the AIR with useless `assume(has_resolved(...))`
/// statements.
///
/// There are no soundness consequences for this computation. Any type is safe to "resolve".
/// However, if too many types are considered nontrivial, then we end up cluttering the AIR code,
/// and if too few types are considered nontrivial, there may be completeness issues.
/// Therefore, we err on the side of considering a type nontrivial if we don't know.
pub(crate) struct ResolutionTypes {
    paths: HashMap<Path, bool>,
}

impl ResolutionTypes {
    pub(crate) fn new(datatypes: &HashMap<Path, Datatype>) -> Self {
        // We graph dependencies of all datatypes to see which datatypes can "reach"
        // a `&mut T` type
        let mut graph = crate::reachability::Graph::new();
        for (path, datatype) in datatypes.iter() {
            graph.add_node(path.clone());
            match &datatype.x.transparency {
                DatatypeTransparency::Never => {
                    // If a datatype is opaque, conservatively assume it might have mut refs
                    // (although this is rare)
                    graph.add_root(path.clone());
                }
                DatatypeTransparency::WhenVisible(_) => {
                    for variant in datatype.x.variants.iter() {
                        for field in variant.fields.iter() {
                            res_typ_visitor(
                                &field.a.0,
                                true,
                                &mut |resolvedness| match resolvedness {
                                    NodeResolve::Yes => {
                                        graph.add_root(path.clone());
                                    }
                                    NodeResolve::DatatypePath(p) => {
                                        graph.add_edge(p.clone(), path.clone());
                                    }
                                    NodeResolve::No | NodeResolve::TypArgDependent => {}
                                },
                            );
                        }
                    }
                }
            }
        }
        Self { paths: graph.into_reachable_set() }
    }

    pub(crate) fn has_nontrivial_resolve(&self, typ: &Typ) -> bool {
        let mut res = false;
        res_typ_visitor(typ, false, &mut |resolvedness| match resolvedness {
            NodeResolve::Yes => {
                res = true;
            }
            NodeResolve::DatatypePath(p) => {
                if self.paths[p] {
                    res = true;
                }
            }
            NodeResolve::No | NodeResolve::TypArgDependent => {}
        });
        res
    }
}

/// Indicates whether a gived node of a Typ tree indicates resolvedness
enum NodeResolve {
    /// Has resolvedness iff a type argument has resolvedness
    /// (i.e., we need to recurse into type arguments)
    TypArgDependent,
    /// Definitely has no resolvedness, no need to recurse (e.g., &T)
    No,
    /// Has resolvedness, e.g., &mut T
    /// Note: Type parameters and other opaque types are assumed to have resolvedness
    Yes,
    /// This is a datatype
    DatatypePath(Path),
}

/// Returns the NodeResolve for the root node of the Typ
fn typ_node_resolvability(t: &Typ) -> NodeResolve {
    match &**t {
        TypX::Bool
        | TypX::Int(_)
        | TypX::Real
        | TypX::Float(_)
        | TypX::SpecFn(..)
        | TypX::FnDef(..)
        | TypX::PointeeMetadata(..)
        | TypX::TypeId
        | TypX::ConstInt(..)
        | TypX::ConstBool(..)
        | TypX::Air(..) => NodeResolve::No,

        TypX::AnonymousClosure(..) | TypX::Datatype(Dt::Tuple(_), ..) | TypX::Boxed(..) => {
            NodeResolve::TypArgDependent
        }

        TypX::Primitive(primitive, _) => match primitive {
            Primitive::Array | Primitive::Slice => NodeResolve::TypArgDependent,
            Primitive::StrSlice | Primitive::Ptr | Primitive::Global => NodeResolve::No,
        },

        TypX::Decorate(dec, ..) => match dec {
            TypDecoration::Ref
            | TypDecoration::Rc
            | TypDecoration::Arc
            | TypDecoration::Ghost
            | TypDecoration::Never
            | TypDecoration::ConstPtr => NodeResolve::No,
            TypDecoration::Box | TypDecoration::Tracked => NodeResolve::TypArgDependent,
            TypDecoration::MutRef => NodeResolve::Yes,
        },

        TypX::Datatype(Dt::Path(p), ..) => NodeResolve::DatatypePath(p.clone()),

        TypX::Opaque { .. }
        | TypX::TypParam(..)
        | TypX::MutRef(..)
        | TypX::Dyn(..)
        | TypX::Projection { .. } => NodeResolve::Yes,
    }
}

fn res_typ_visitor(typ: &Typ, skip_typ_param: bool, mf: &mut impl FnMut(&NodeResolve)) {
    crate::ast_visitor::typ_visitor_dfs(typ, &mut |typ| {
        if skip_typ_param && matches!(&**typ, TypX::TypParam(_)) {
            return VisitorControlFlow::Return;
        }
        let res = typ_node_resolvability(typ);
        match res {
            NodeResolve::No => VisitorControlFlow::Return,
            NodeResolve::TypArgDependent => VisitorControlFlow::Recurse,
            NodeResolve::Yes => {
                mf(&res);
                VisitorControlFlow::Stop(())
            }
            NodeResolve::DatatypePath(_) => {
                mf(&res);
                VisitorControlFlow::Recurse
            }
        }
    });
}
