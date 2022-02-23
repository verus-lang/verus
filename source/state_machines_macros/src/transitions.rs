use crate::ast::{Field, TransitionKind, TransitionStmt, SM, ShardableType};
use crate::util::combine_errors_or_ok;
use proc_macro2::Span;
use std::collections::HashMap;
use syn::spanned::Spanned;
use syn::{Error, Ident};

pub fn fields_contain(fields: &Vec<Field>, ident: &Ident) -> bool {
    for f in fields {
        if f.ident.to_string() == ident.to_string() {
            return true;
        }
    }
    return false;
}

/// Check that every update statement actually refers to a valid field.

fn check_updates_refer_to_valid_fields(
    fields: &Vec<Field>,
    ts: &TransitionStmt,
) -> syn::parse::Result<()> {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                check_updates_refer_to_valid_fields(fields, t)?;
            }
            Ok(())
        }
        TransitionStmt::Let(_, _, _) => Ok(()),
        TransitionStmt::If(_, _, thn, els) => {
            check_updates_refer_to_valid_fields(fields, thn)?;
            check_updates_refer_to_valid_fields(fields, els)?;
            Ok(())
        }
        TransitionStmt::Require(_, _) => Ok(()),
        TransitionStmt::Assert(_, _) => Ok(()),
        TransitionStmt::Update(sp, f, _) |
        TransitionStmt::AddSome(sp, f, _) |
        TransitionStmt::RemoveSome(sp, f, _) |
        TransitionStmt::HaveSome(sp, f, _) |
        TransitionStmt::AddElement(sp, f, _) |
        TransitionStmt::RemoveElement(sp, f, _) |
        TransitionStmt::HaveElement(sp, f, _) => {
            if !fields_contain(fields, f) {
                return Err(Error::new(sp.span(), format!("field '{}' not found", f.to_string())));
            }
            Ok(())
        }
        TransitionStmt::PostCondition(..) => Ok(()),
    }
}

fn disjoint_union(
    h1: &Vec<(Ident, Span)>,
    h2: &Vec<(Ident, Span)>,
) -> syn::parse::Result<Vec<(Ident, Span)>> {
    let mut h1_map: HashMap<Ident, Span> = HashMap::new();
    for (ident, span) in h1 {
        h1_map.insert(ident.clone(), span.clone());
    }
    for (ident, _span2) in h2 {
        match h1_map.get(ident) {
            None => {}
            Some(span1) => {
                return Err(Error::new(
                    *span1,
                    format!("field '{}' might be updated multiple times", ident.to_string()),
                ));
            }
        }
    }
    let mut con = h1.clone();
    con.extend(h2.clone());
    return Ok(con);
}

fn update_sets_eq(h1: &Vec<(Ident, Span)>, h2: &Vec<(Ident, Span)>) -> bool {
    if h1.len() != h2.len() {
        return false;
    }
    for (ident, _) in h1 {
        if !update_set_contains(h2, ident) {
            return false;
        }
    }
    return true;
}

fn update_set_contains(h: &Vec<(Ident, Span)>, ident: &Ident) -> bool {
    for (ident2, _) in h {
        if *ident == *ident2 {
            return true;
        }
    }
    return false;
}

fn check_has_all_fields(
    sp: Span,
    h: &Vec<(Ident, Span)>,
    fields: &Vec<Field>,
) -> syn::parse::Result<()> {
    for field in fields {
        if !update_set_contains(h, &field.ident) {
            return Err(Error::new(
                sp,
                format!(
                    "itialization procedure does not initialize field {}",
                    field.ident.to_string()
                ),
            ));
        }
    }
    Ok(())
}

/// Check well-formedness for a 'readonly' transition.
///
/// There should be no 'update' statements.

fn check_readonly(sm: &SM, ts: &TransitionStmt) -> syn::parse::Result<()> {
    for field in &sm.fields {
        match &field.stype {
            ShardableType::Variable(_ty) | ShardableType::NotTokenized(_ty) => {
                check_readonly_variable(field, ts)?;
            }
            ShardableType::Constant(_ty) => {
                check_constant_not_updated(field, ts)?;
            }
            ShardableType::Multiset(_ty) => {
                check_readonly_elemental(field, ts)?;
            }
            ShardableType::Optional(_ty) => {
                check_readonly_optional(field, ts)?;
            }
        }
    }
    Ok(())
}

fn check_readonly_variable(field: &Field, ts: &TransitionStmt) -> syn::parse::Result<()> {
    let mut errors = Vec::new();
    ts.visit_updatelike_stmts(&field.ident, &mut |ts: &TransitionStmt| {
        match ts {
            TransitionStmt::Block(_, _) |
            TransitionStmt::Let(_, _, _) |
            TransitionStmt::If(_, _, _, _) |
            TransitionStmt::Require(_, _) |
            TransitionStmt::Assert(_, _) => { panic!("visit_updatelike_stmts"); }
            TransitionStmt::Update(span, _, _) => {
                errors.push(Error::new(*span, "'update' statement not allowed in readonly transition"));
            }
            TransitionStmt::AddSome(span, _, _) |
            TransitionStmt::RemoveSome(span, _, _) |
            TransitionStmt::AddElement(span, _, _) |
            TransitionStmt::RemoveElement(span, _, _) => {
                errors.push(Error::new(*span, format!("'{:}' statement not allowed in readonly transition", ts.statement_name())));
                errors.push(Error::new(*span, format!("'{:}' statement not allowed for field with sharding strategy '{:}'", ts.statement_name(), field.stype.strategy_name())));
            }
            TransitionStmt::HaveSome(span, _, _) |
            TransitionStmt::HaveElement(span, _, _) => {
                errors.push(Error::new(*span, format!("'{:}' statement not allowed for field with sharding strategy '{:}'", ts.statement_name(), field.stype.strategy_name())));
            }
            TransitionStmt::PostCondition(..) => { }
        }
    });
    combine_errors_or_ok(errors)
}

fn check_readonly_elemental(field: &Field, ts: &TransitionStmt) -> syn::parse::Result<()> {
    let mut errors = Vec::new();
    ts.visit_updatelike_stmts(&field.ident, &mut |ts| {
        match ts {
            TransitionStmt::Block(_, _) |
            TransitionStmt::Let(_, _, _) |
            TransitionStmt::If(_, _, _, _) |
            TransitionStmt::Require(_, _) |
            TransitionStmt::Assert(_, _) => { panic!("visit_updatelike_stmts"); }
            TransitionStmt::Update(span, _, _) |
            TransitionStmt::AddSome(span, _, _) |
            TransitionStmt::RemoveSome(span, _, _) |
            TransitionStmt::AddElement(span, _, _) |
            TransitionStmt::RemoveElement(span, _, _) => {
                errors.push(Error::new(*span, format!("'{:}' statement not allowed in readonly transition", ts.statement_name())));
            }
            TransitionStmt::HaveElement(_, _, _) => { }
            TransitionStmt::HaveSome(span, _, _) => {
                errors.push(Error::new(*span, format!("'{:}' statement not allowed for field with sharding strategy '{:}'", ts.statement_name(), field.stype.strategy_name())));
            }
            TransitionStmt::PostCondition(..) => { }
        }
    });
    combine_errors_or_ok(errors)
}

fn check_readonly_optional(field: &Field, ts: &TransitionStmt) -> syn::parse::Result<()> {
    let mut errors = Vec::new();
    ts.visit_updatelike_stmts(&field.ident, &mut |ts| {
        match ts {
            TransitionStmt::Block(_, _) |
            TransitionStmt::Let(_, _, _) |
            TransitionStmt::If(_, _, _, _) |
            TransitionStmt::Require(_, _) |
            TransitionStmt::Assert(_, _) => { panic!("visit_updatelike_stmts"); }
            TransitionStmt::Update(span, _, _) |
            TransitionStmt::AddSome(span, _, _) |
            TransitionStmt::RemoveSome(span, _, _) |
            TransitionStmt::AddElement(span, _, _) |
            TransitionStmt::RemoveElement(span, _, _) => {
                errors.push(Error::new(*span, format!("'{:}' statement not allowed in readonly transition", ts.statement_name())));
            }
            TransitionStmt::HaveSome(_, _, _) => { }
            TransitionStmt::HaveElement(span, _, _) => {
                errors.push(Error::new(*span, format!("'{:}' statement not allowed for field with sharding strategy '{:}'", ts.statement_name(), field.stype.strategy_name())));
            }
            TransitionStmt::PostCondition(..) => { }
        }
    });
    combine_errors_or_ok(errors)
}

fn check_constant_not_updated(field: &Field, ts: &TransitionStmt) -> syn::parse::Result<()> {
    let mut errors = Vec::new();
    ts.visit_updatelike_stmts(&field.ident, &mut |ts: &TransitionStmt| {
        match ts {
            TransitionStmt::Block(_, _) |
            TransitionStmt::Let(_, _, _) |
            TransitionStmt::If(_, _, _, _) |
            TransitionStmt::Require(_, _) |
            TransitionStmt::Assert(_, _) => { panic!("visit_updatelike_stmts"); }
            TransitionStmt::Update(span, _, _) => {
                errors.push(Error::new(*span, "cannot update 'constant' field"))
            }
            TransitionStmt::AddSome(span, _, _) |
            TransitionStmt::RemoveSome(span, _, _) |
            TransitionStmt::HaveSome(span, _, _) |
            TransitionStmt::AddElement(span, _, _) |
            TransitionStmt::RemoveElement(span, _, _) |
            TransitionStmt::HaveElement(span, _, _) => {
                errors.push(Error::new(*span, format!("'{:}' statement not allowed for field with sharding strategy 'constant'", ts.statement_name())));
            }
            TransitionStmt::PostCondition(..) => { }
        }
    });
    combine_errors_or_ok(errors)
}

/// Check well-formedness for an 'initialization' transition.
///
/// We require every field to be updated exactly once. That means if a field
/// is updated in one branch of a conditional, it must also be updated in the other.

fn check_init(sm: &SM, ts: &TransitionStmt) -> syn::parse::Result<()> {
    let h = check_init_rec(&ts)?;
    let span = ts.get_span();

    // Check we actually got all the fields.
    check_has_all_fields(*span, &h, &sm.fields)?;

    Ok(())
}

fn check_init_rec(ts: &TransitionStmt) -> syn::parse::Result<Vec<(Ident, Span)>> {
    match ts {
        TransitionStmt::Block(_, v) => {
            let mut h = Vec::new();
            for t in v.iter() {
                let q = check_init_rec(t)?;
                h = disjoint_union(&h, &q)?;
            }
            Ok(h)
        }
        TransitionStmt::Let(_, _, _) => {
            Ok(Vec::new())
        }
        TransitionStmt::If(sp, _, thn, els) => {
            let h1 = check_init_rec(thn)?;
            let h2 = check_init_rec(els)?;
            if !update_sets_eq(&h1, &h2) {
                return Err(Error::new(
                    *sp,
                    "for initialization, both branches of if-statement must update the same fields",
                ));
            }
            Ok(h1)
        }
        TransitionStmt::Require(_, _) => {
            Ok(Vec::new())
        }
        TransitionStmt::Assert(span, _) => {
            Err(Error::new(*span, "'assert' statement not allowed in initialization"))
        }
        TransitionStmt::Update(span, ident, _) => {
            let mut v = Vec::new();
            v.push((ident.clone(), span.clone()));
            Ok(v)
        }
        TransitionStmt::AddSome(span, _, _) |
        TransitionStmt::RemoveSome(span, _, _) |
        TransitionStmt::HaveSome(span, _, _) |
        TransitionStmt::AddElement(span, _, _) |
        TransitionStmt::RemoveElement(span, _, _) |
        TransitionStmt::HaveElement(span, _, _) => {
            Err(Error::new(*span, format!("'{:}' statement not allowed in initialization", ts.statement_name())))
        }
        TransitionStmt::PostCondition(..) => Ok(Vec::new()),
    }
}

/// Check well-formedness for an 'ordinary' transition.
///
/// Don't allow any single field to be updated more than once.
/// (Note a field might be updated on both sides of a conditional, but it should not, e.g.,
/// be updated inside a conditional and also outside of it.)

pub fn check_normal(sm: &SM, ts: &TransitionStmt) -> syn::parse::Result<()> {
    for field in &sm.fields {
        match &field.stype {
            ShardableType::Variable(_ty) | ShardableType::NotTokenized(_ty) => {
                check_transition_variable(field, ts)?;
            }
            ShardableType::Constant(_ty) => {
                check_constant_not_updated(field, ts)?;
            }
            ShardableType::Multiset(_ty) => {
                check_transition_elemental(field, ts)?;
            }
            ShardableType::Optional(_ty) => {
                check_transition_optional(field, ts)?;
            }
        }
    }
    Ok(())
}

fn check_transition_variable(field: &Field, ts: &TransitionStmt) -> syn::parse::Result<Option<Span>> {
    match ts {
        TransitionStmt::Block(_, v) => {
            let mut o = None;
            for t in v.iter() {
                let o2 = check_transition_variable(field, t)?;
                o = match (o, o2) {
                    (None, None) => None,
                    (Some(s), None) => Some(s),
                    (None, Some(s)) => Some(s),
                    (Some(_s1), Some(s2)) => {
                        return Err(Error::new(s2,
                            format!("field '{}' might be updated multiple times", field.ident.to_string())));
                    }
                };
            }
            Ok(o)
        }
        TransitionStmt::If(_, _, thn, els) => {
            let o1 = check_transition_variable(field, thn)?;
            let o2 = check_transition_variable(field, els)?;
            Ok(if o1.is_some() { o1 } else { o2 })
        }
        TransitionStmt::Let(_, _, _) => Ok(None),
        TransitionStmt::Require(_, _) => Ok(None),
        TransitionStmt::Assert(_, _) => Ok(None),
        TransitionStmt::Update(span, id, _) => {
            if id.to_string() == field.ident.to_string() {
                Ok(Some(*span))
            } else {
                Ok(None)
            }
        }
        TransitionStmt::AddSome(span, id, _) |
        TransitionStmt::RemoveSome(span, id, _) |
        TransitionStmt::HaveSome(span, id, _) |
        TransitionStmt::AddElement(span, id, _) |
        TransitionStmt::RemoveElement(span, id, _) |
        TransitionStmt::HaveElement(span, id, _) => {
            if id.to_string() == field.ident.to_string() {
                Err(Error::new(*span, format!("'{:}' statement not allowed for field with sharding strategy '{:}'", ts.statement_name(), field.stype.strategy_name())))
            } else {
                Ok(None)
            }
        }
        TransitionStmt::PostCondition(..) => Ok(None),
    }
}

fn check_transition_elemental(field: &Field, ts: &TransitionStmt) -> syn::parse::Result<()> {
    let mut errors = Vec::new();
    ts.visit_updatelike_stmts(&field.ident, &mut |ts| {
        match ts {
            TransitionStmt::Block(_, _) |
            TransitionStmt::Let(_, _, _) |
            TransitionStmt::If(_, _, _, _) |
            TransitionStmt::Require(_, _) |
            TransitionStmt::Assert(_, _) => { panic!("visit_updatelike_stmts"); }

            TransitionStmt::RemoveSome(span, _, _) |
            TransitionStmt::HaveSome(span, _, _) |
            TransitionStmt::AddSome(span, _, _) |
            TransitionStmt::Update(span, _, _) => {
                errors.push(Error::new(*span, format!("'{:}' statement not allowed for field with sharding strategy '{:}'", ts.statement_name(), field.stype.strategy_name())));
            }

            // These 3 are expected:
            TransitionStmt::AddElement(_, _, _) => { }
            TransitionStmt::RemoveElement(_, _, _) => { }
            TransitionStmt::HaveElement(_, _, _) => { }
            TransitionStmt::PostCondition(..) => { }
        }
    });
    combine_errors_or_ok(errors)
}

fn check_transition_optional(field: &Field, ts: &TransitionStmt) -> syn::parse::Result<()> {
    let mut errors = Vec::new();
    ts.visit_updatelike_stmts(&field.ident, &mut |ts| {
        match ts {
            TransitionStmt::Block(_, _) |
            TransitionStmt::Let(_, _, _) |
            TransitionStmt::If(_, _, _, _) |
            TransitionStmt::Require(_, _) |
            TransitionStmt::Assert(_, _) => { panic!("visit_updatelike_stmts"); }

            TransitionStmt::AddElement(_, _, _) => { }
            TransitionStmt::RemoveElement(_, _, _) => { }
            TransitionStmt::HaveElement(_, _, _) => { }
            TransitionStmt::Update(span, _, _) => {
                errors.push(Error::new(*span, format!("'{:}' statement not allowed for field with sharding strategy '{:}'", ts.statement_name(), field.stype.strategy_name())));
            }

            // These 3 are expected:
            TransitionStmt::RemoveSome(_, _, _) |
            TransitionStmt::HaveSome(_, _, _) |
            TransitionStmt::AddSome(..) |

            TransitionStmt::PostCondition(..) => { }
        }
    });
    combine_errors_or_ok(errors)
}

/// Check simple well-formedness properties of the transitions.

pub fn check_transitions(sm: &SM) -> syn::parse::Result<()> {
    for tr in &sm.transitions {
        check_updates_refer_to_valid_fields(&sm.fields, &tr.body)?;

        match &tr.kind {
            TransitionKind::Readonly => {
                check_readonly(sm, &tr.body)?;
            }
            TransitionKind::Transition => {
                check_normal(sm, &tr.body)?;
            }
            TransitionKind::Init => {
                check_init(sm, &tr.body)?;
            }
        }
    }

    Ok(())
}
