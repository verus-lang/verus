use crate::ast::{Datatype, Krate, Path, Typ, TypX, VirErr};
use crate::ast_util::{err_str, err_string, path_as_rust_name};
use crate::scc::Graph;
use air::ast::Span;
use std::collections::HashMap;

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
        TypX::Bool | TypX::Int(_) | TypX::TypParam(_) | TypX::Lambda(..) => Ok(true),
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

    for datatype in &krate.datatypes {
        let _ = check_well_founded(&datatypes, &mut datatypes_well_founded, &datatype.x.path)?;
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
