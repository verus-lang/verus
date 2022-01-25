use crate::ast::{Krate, Path, Typ, TypX, VirErr};
use crate::ast_util::{err_string, path_as_rust_name};
use crate::scc::Graph;
use air::ast::Span;

// polarity = Some(true) for positive, Some(false) for negative, None for neither
fn check_positive_uses(
    span: &Span,
    type_graph: &Graph<Path>,
    my_datatype: &Path,
    polarity: Option<bool>,
    typ: &Typ,
) -> Result<(), VirErr> {
    match &**typ {
        TypX::Bool => Ok(()),
        TypX::Int(..) => Ok(()),
        TypX::Lambda(ts, tr) => {
            let flip_polarity = match polarity {
                None => None,
                Some(b) => Some(!b),
            };
            for t in ts.iter() {
                check_positive_uses(span, type_graph, my_datatype, flip_polarity, t)?;
            }
            check_positive_uses(span, type_graph, my_datatype, polarity, tr)?;
            Ok(())
        }
        TypX::Tuple(ts) => {
            for t in ts.iter() {
                check_positive_uses(span, type_graph, my_datatype, polarity, t)?;
            }
            Ok(())
        }
        TypX::Datatype(path, ts) => {
            // Check path
            if path == my_datatype
                || type_graph.get_scc_rep(&path) == type_graph.get_scc_rep(&my_datatype)
            {
                match polarity {
                    Some(true) => {}
                    _ => {
                        return err_string(
                            span,
                            format!(
                                "Type {} recursively uses type {} in a non-positive polarity",
                                path_as_rust_name(my_datatype),
                                path_as_rust_name(path)
                            ),
                        );
                    }
                }
            }
            // Check ts, assuming that they must be invariant (neither positive nor negative):
            // TODO: this is overly conservative; we should track positive and negative more precisely:
            for t in ts.iter() {
                check_positive_uses(span, type_graph, my_datatype, None, t)?;
            }
            Ok(())
        }
        TypX::Boxed(t) => check_positive_uses(span, type_graph, my_datatype, polarity, t),
        TypX::TypParam(..) => Ok(()),
        TypX::TypeId => Ok(()),
        TypX::Air(_) => Ok(()),
    }
}

pub(crate) fn check_recursive_types(krate: &Krate) -> Result<(), VirErr> {
    let mut type_graph: Graph<Path> = Graph::new();

    // If datatype D1 has a field whose type mentions datatype D2, create a graph edge D1 --> D2
    for datatype in &krate.datatypes {
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

    for datatype in &krate.datatypes {
        for variant in datatype.x.variants.iter() {
            for field in variant.a.iter() {
                // Check that field type only uses SCC siblings in positive positions
                let (typ, _, _) = &field.a;
                check_positive_uses(
                    &datatype.span,
                    &type_graph,
                    &datatype.x.path,
                    Some(true),
                    typ,
                )?;
            }
        }
    }

    Ok(())
}
