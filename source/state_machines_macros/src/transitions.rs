use crate::ast::{Field, ShardableType, SpecialOp, TransitionKind, TransitionStmt, SM};
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

pub fn get_field<'a>(fields: &'a Vec<Field>, ident: &Ident) -> &'a Field {
    for f in fields {
        if f.ident.to_string() == ident.to_string() {
            return f;
        }
    }
    panic!("could not find field");
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
        TransitionStmt::Update(span, f, _)
        | TransitionStmt::Initialize(span, f, _)
        | TransitionStmt::Special(span, f, _) => {
            if !fields_contain(fields, f) {
                return Err(Error::new(
                    span.span(),
                    format!("field '{}' not found", f.to_string()),
                ));
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
    span: Span,
    h: &Vec<(Ident, Span)>,
    fields: &Vec<Field>,
) -> syn::parse::Result<()> {
    for field in fields {
        if !update_set_contains(h, &field.ident) {
            return Err(Error::new(
                span,
                format!(
                    "itialization procedure does not initialize field {}",
                    field.ident.to_string()
                ),
            ));
        }
    }
    Ok(())
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
        TransitionStmt::Let(_, _, _) => Ok(Vec::new()),
        TransitionStmt::If(span, _, thn, els) => {
            let h1 = check_init_rec(thn)?;
            let h2 = check_init_rec(els)?;
            if !update_sets_eq(&h1, &h2) {
                return Err(Error::new(
                    *span,
                    "for initialization, both branches of if-statement must update the same fields",
                ));
            }
            Ok(h1)
        }
        TransitionStmt::Require(_, _) => Ok(Vec::new()),
        TransitionStmt::Assert(span, _) => {
            Err(Error::new(*span, "'assert' statement not allowed in initialization"))
        }
        TransitionStmt::Initialize(span, ident, _) => {
            let mut v = Vec::new();
            v.push((ident.clone(), span.clone()));
            Ok(v)
        }
        TransitionStmt::Update(span, _, _) => Err(Error::new(
            *span,
            "'update' statement not allowed in initialization; use 'init' instead",
        )),
        TransitionStmt::Special(span, _, _) => Err(Error::new(
            *span,
            format!(
                "'{:}' statement not allowed in initialization; use 'init' instead",
                ts.statement_name()
            ),
        )),
        TransitionStmt::PostCondition(..) => {
            panic!("should have have PostCondition statement here");
        }
    }
}

fn check_at_most_one_update(sm: &SM, ts: &TransitionStmt) -> syn::parse::Result<()> {
    for f in &sm.fields {
        check_at_most_one_update_rec(f, ts)?;
    }
    Ok(())
}

fn check_at_most_one_update_rec(
    field: &Field,
    ts: &TransitionStmt,
) -> syn::parse::Result<Option<Span>> {
    match ts {
        TransitionStmt::Block(_, v) => {
            let mut o = None;
            for t in v.iter() {
                let o2 = check_at_most_one_update_rec(field, t)?;
                o = match (o, o2) {
                    (None, None) => None,
                    (Some(s), None) => Some(s),
                    (None, Some(s)) => Some(s),
                    (Some(_s1), Some(s2)) => {
                        return Err(Error::new(
                            s2,
                            format!(
                                "field '{}' might be updated multiple times",
                                field.ident.to_string()
                            ),
                        ));
                    }
                };
            }
            Ok(o)
        }
        TransitionStmt::If(_, _, thn, els) => {
            let o1 = check_at_most_one_update_rec(field, thn)?;
            let o2 = check_at_most_one_update_rec(field, els)?;
            Ok(if o1.is_some() { o1 } else { o2 })
        }
        TransitionStmt::Let(_, _, _) => Ok(None),
        TransitionStmt::Require(_, _) => Ok(None),
        TransitionStmt::Assert(_, _) => Ok(None),
        TransitionStmt::Initialize(_, _, _) => Ok(None),
        TransitionStmt::Update(span, id, _) => {
            if id.to_string() == field.ident.to_string() {
                Ok(Some(*span))
            } else {
                Ok(None)
            }
        }
        TransitionStmt::Special(..) => Ok(None),
        TransitionStmt::PostCondition(..) => Ok(None),
    }
}

fn is_allowed_in_update_in_normal_transition(stype: &ShardableType) -> bool {
    match stype {
        ShardableType::Variable(_) => true,
        ShardableType::Constant(_) => false,
        ShardableType::NotTokenized(_) => true,
        ShardableType::Multiset(_) => false,
        ShardableType::Optional(_) => false,
        ShardableType::StorageOptional(_) => false,
    }
}

fn is_allowed_in_special_op(stype: &ShardableType, sop: &SpecialOp) -> bool {
    match stype {
        ShardableType::Variable(_) => false,
        ShardableType::Constant(_) => false,
        ShardableType::NotTokenized(_) => false,

        ShardableType::Multiset(_) => match sop {
            SpecialOp::AddElement(_) => true,
            SpecialOp::RemoveElement(_) => true,
            SpecialOp::HaveElement(_) => true,
            _ => false,
        },

        ShardableType::Optional(_) => match sop {
            SpecialOp::AddSome(_) => true,
            SpecialOp::RemoveSome(_) => true,
            SpecialOp::HaveSome(_) => true,
            _ => false,
        },

        ShardableType::StorageOptional(_) => match sop {
            SpecialOp::DepositSome(_) => true,
            SpecialOp::WithdrawSome(_) => true,
            SpecialOp::GuardSome(_) => true,
            _ => false,
        },
    }
}

fn check_valid_ops(
    fields: &Vec<Field>,
    ts: &TransitionStmt,
    is_readonly: bool,
) -> syn::parse::Result<()> {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                check_valid_ops(fields, t, is_readonly)?;
            }
            Ok(())
        }
        TransitionStmt::Let(_, _, _) => Ok(()),
        TransitionStmt::If(_, _, thn, els) => {
            check_valid_ops(fields, thn, is_readonly)?;
            check_valid_ops(fields, els, is_readonly)?;
            Ok(())
        }
        TransitionStmt::Require(_, _) => Ok(()),
        TransitionStmt::Assert(_, _) => Ok(()),
        TransitionStmt::Initialize(span, _, _) => {
            return Err(Error::new(
                span.span(),
                format!("'init' statement not allowed outside 'init' routine"),
            ));
        }
        TransitionStmt::Update(span, f, _) => {
            let field = get_field(fields, f);
            if !is_allowed_in_update_in_normal_transition(&field.stype) {
                return Err(Error::new(
                    span.span(),
                    format!(
                        "'update' statement not allowed for field with sharding strategy '{:}'",
                        field.stype.strategy_name()
                    ),
                ));
            }
            if is_readonly {
                return Err(Error::new(
                    span.span(),
                    format!("'update' statement not allowed in readonly transition"),
                ));
            }
            Ok(())
        }
        TransitionStmt::Special(span, f, op) => {
            let field = get_field(fields, f);
            if !is_allowed_in_special_op(&field.stype, op) {
                return Err(Error::new(
                    span.span(),
                    format!(
                        "'{:}' statement not allowed for field with sharding strategy '{:}'",
                        op.statement_name(),
                        field.stype.strategy_name()
                    ),
                ));
            }
            if is_readonly && op.is_modifier() {
                return Err(Error::new(
                    span.span(),
                    format!(
                        "'{:}' statement not allowed in readonly transition",
                        op.statement_name()
                    ),
                ));
            }
            if !is_readonly && op.is_only_allowed_in_readonly() {
                return Err(Error::new(
                    span.span(),
                    format!(
                        "'{:}' statement only allowed in readonly transition",
                        op.statement_name()
                    ),
                ));
            }
            Ok(())
        }
        TransitionStmt::PostCondition(..) => Ok(()),
    }
}

/// Check simple well-formedness properties of the transitions.

pub fn check_transitions(sm: &SM) -> syn::parse::Result<()> {
    for tr in &sm.transitions {
        check_updates_refer_to_valid_fields(&sm.fields, &tr.body)?;

        match &tr.kind {
            TransitionKind::Readonly => {
                check_valid_ops(&sm.fields, &tr.body, true)?;
            }
            TransitionKind::Transition => {
                check_valid_ops(&sm.fields, &tr.body, false)?;
                check_at_most_one_update(sm, &tr.body)?;
            }
            TransitionKind::Init => {
                // check exactly one update
                check_init(sm, &tr.body)?;
            }
        }
    }

    Ok(())
}
