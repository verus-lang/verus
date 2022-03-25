use crate::ast::{
    Field, MonoidElt, ShardableType, SpecialOp, Transition, TransitionKind, TransitionStmt, SM,
};
use crate::check_birds_eye::check_birds_eye;
use crate::ident_visitor::validate_idents_transition;
use crate::inherent_safety_conditions::check_inherent_conditions;
use crate::util::{combine_errors_or_ok, combine_results};
use proc_macro2::Span;
use syn::spanned::Spanned;
use syn::{Error, Ident};

pub fn fields_contain(fields: &Vec<Field>, ident: &Ident) -> bool {
    for f in fields {
        if f.name.to_string() == ident.to_string() {
            return true;
        }
    }
    return false;
}

pub fn get_field<'a>(fields: &'a Vec<Field>, ident: &Ident) -> &'a Field {
    for f in fields {
        if f.name.to_string() == ident.to_string() {
            return f;
        }
    }
    panic!("could not find field");
}

/// Check that every update statement actually refers to a valid field.
/// We'll assume that all the fields are valid in the later checks.

fn check_updates_refer_to_valid_fields(
    fields: &Vec<Field>,
    ts: &TransitionStmt,
    errors: &mut Vec<Error>,
) {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                check_updates_refer_to_valid_fields(fields, t, errors);
            }
        }
        TransitionStmt::Let(_, _, _, _, child) => {
            check_updates_refer_to_valid_fields(fields, child, errors);
        }
        TransitionStmt::If(_, _, thn, els) => {
            check_updates_refer_to_valid_fields(fields, thn, errors);
            check_updates_refer_to_valid_fields(fields, els, errors);
        }
        TransitionStmt::Require(_, _) => {}
        TransitionStmt::Assert(..) => {}
        TransitionStmt::Update(span, f, _)
        | TransitionStmt::Initialize(span, f, _)
        | TransitionStmt::Special(span, f, _, _) => {
            if !fields_contain(fields, f) {
                errors
                    .push(Error::new(span.span(), format!("field '{}' not found", f.to_string())));
            }
        }
        TransitionStmt::PostCondition(..) => {}
    }
}

/// For each field, checks that this field is initialized *exactly* once.
/// This check applies for *all* fields.

fn check_exactly_one_init(sm: &SM, ts: &TransitionStmt, errors: &mut Vec<Error>) {
    for f in &sm.fields {
        match check_exactly_one_init_rec(f, ts) {
            Ok(Some(_)) => {}
            Ok(None) => {
                errors.push(Error::new(
                    *ts.get_span(),
                    format!(
                        "itialization procedure does not initialize field '{}'",
                        f.name.to_string()
                    ),
                ));
            }
            Err(e) => errors.push(e),
        }
    }
}

fn check_exactly_one_init_rec(
    field: &Field,
    ts: &TransitionStmt,
) -> syn::parse::Result<Option<Span>> {
    match ts {
        TransitionStmt::Block(_, v) => {
            let mut o = None;
            for t in v.iter() {
                let o2 = check_exactly_one_init_rec(field, t)?;
                o = match (o, o2) {
                    (None, None) => None,
                    (Some(s), None) => Some(s),
                    (None, Some(s)) => Some(s),
                    (Some(_s1), Some(s2)) => {
                        return Err(Error::new(
                            s2,
                            format!(
                                "field '{}' might be initialized multiple times",
                                field.name.to_string()
                            ),
                        ));
                    }
                };
            }
            Ok(o)
        }
        TransitionStmt::Let(_, _, _, _, child) => check_exactly_one_init_rec(field, child),
        TransitionStmt::If(if_span, _, thn, els) => {
            let o1 = check_exactly_one_init_rec(field, thn)?;
            let o2 = check_exactly_one_init_rec(field, els)?;
            // The user is required to initialize the field in both branches if they update
            // it in either. Therefore we need to produce an error if there was a mismatch
            // between the two branches.
            match (o1, o2) {
                (Some(span1), Some(_span2)) => Ok(Some(span1)),
                (None, None) => Ok(None),
                (Some(_span1), None) => {
                    return Err(Error::new(
                        *if_span,
                        format!(
                            "for initialization, both branches of if-statement must initialize the same fields; the else-branch does not initialize '{}'",
                            field.name
                        ),
                    ));
                }
                (None, Some(_span1)) => {
                    return Err(Error::new(
                        *if_span,
                        format!(
                            "for initialization, both branches of if-statement must initialize the same fields; the if-branch does not initialize '{}'",
                            field.name
                        ),
                    ));
                }
            }
        }
        TransitionStmt::Require(_, _) => Ok(None),
        TransitionStmt::Assert(..) => Ok(None),
        TransitionStmt::Initialize(span, id, _) => {
            if id.to_string() == field.name.to_string() {
                Ok(Some(*span))
            } else {
                Ok(None)
            }
        }
        TransitionStmt::Update(_, _, _) => Ok(None),
        TransitionStmt::Special(..) => Ok(None),
        TransitionStmt::PostCondition(..) => Ok(None),
    }
}

/// For each field, checks that this field is updated *at most* once.
/// Only checks 'update' statements, not special ops, and it
/// only does the check for fields for which 'update' statements are supported.

fn check_at_most_one_update(sm: &SM, ts: &TransitionStmt, errors: &mut Vec<Error>) {
    for f in &sm.fields {
        if is_allowed_in_update_in_normal_transition(&f.stype) {
            match check_at_most_one_update_rec(f, ts) {
                Ok(_) => {}
                Err(e) => errors.push(e),
            }
        }
    }
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
                                field.name.to_string()
                            ),
                        ));
                    }
                };
            }
            Ok(o)
        }
        TransitionStmt::Let(_, _, _, _, child) => check_at_most_one_update_rec(field, child),
        TransitionStmt::If(_, _, thn, els) => {
            let o1 = check_at_most_one_update_rec(field, thn)?;
            let o2 = check_at_most_one_update_rec(field, els)?;
            // In contrast to the initialization case,
            // it _is_ allowed to perform an 'update' in only one branch.
            // We return 'Some(_)' if either of the branches returned Some(_).
            Ok(if o1.is_some() { o1 } else { o2 })
        }
        TransitionStmt::Require(_, _) => Ok(None),
        TransitionStmt::Assert(..) => Ok(None),
        TransitionStmt::Initialize(_, _, _) => Ok(None),
        TransitionStmt::Update(span, id, _) => {
            if id.to_string() == field.name.to_string() {
                Ok(Some(*span))
            } else {
                Ok(None)
            }
        }
        TransitionStmt::Special(..) => Ok(None),
        TransitionStmt::PostCondition(..) => Ok(None),
    }
}

/// Returns `true` if you're allowed to have an 'update' statement for the given
/// sharding strategy. Naturally, this is false for constants, which cannot be updated
/// at all, and also false for option, multiset, etc. which have to be updated with
/// special ops.

fn is_allowed_in_update_in_normal_transition(stype: &ShardableType) -> bool {
    match stype {
        ShardableType::Variable(_) => true,
        ShardableType::Constant(_) => false,
        ShardableType::NotTokenized(_) => true,
        ShardableType::Multiset(_) => false,
        ShardableType::Option(_) => false,
        ShardableType::Map(_, _) => false,
        ShardableType::StorageOption(_) => false,
        ShardableType::StorageMap(_, _) => false,
    }
}

/// Big matrix for whether a given sharding type is allowed for a given SpecialOp type

fn is_allowed_in_special_op(
    span: Span,
    stype: &ShardableType,
    sop: &SpecialOp,
) -> syn::parse::Result<()> {
    match stype {
        ShardableType::Constant(_) => {
            Err(Error::new(span, "field marked 'constant' cannot be modified"))
        }

        ShardableType::Variable(_) | ShardableType::NotTokenized(_) => {
            let stmt_name = sop.stmt.name();
            let strat = stype.strategy_name();
            Err(Error::new(
                span,
                format!(
                    "'{stmt_name:}' statement not allowed for field with sharding strategy '{strat:}'; use 'update' instead"
                ),
            ))
        }

        ShardableType::Map(_, _)
        | ShardableType::Option(_)
        | ShardableType::Multiset(_)
        | ShardableType::StorageOption(_)
        | ShardableType::StorageMap(_, _) => {
            if !op_matches_type(stype, &sop.elt) {
                let syntax = sop.elt.syntax();
                let elt_name = sop.elt.type_name();
                let strat = stype.strategy_name();
                return Err(Error::new(
                    span,
                    format!(
                        "`{syntax:}` gives a `{elt_name:}` element but the given field has sharding strategy '{strat:}'",
                    ),
                ));
            }

            let strat_is_storage = stype.is_storage();
            let op_is_storage = sop.stmt.is_for_storage();

            if !strat_is_storage && op_is_storage {
                let stmt_name = sop.stmt.name();
                let strat = stype.strategy_name();
                return Err(Error::new(
                    span,
                    format!(
                        "'{stmt_name:}' statement not allowed for field with sharding strategy '{strat:}'; '{stmt_name:}' is only for storage types; use add/remove/have statements instead"
                    ),
                ));
            }
            if strat_is_storage && !op_is_storage {
                let stmt_name = sop.stmt.name();
                let strat = stype.strategy_name();
                return Err(Error::new(
                    span,
                    format!(
                        "'{stmt_name:}' statement not allowed for field with sharding strategy '{strat:}'; use deposit/withdraw/guard statements for storage strategies"
                    ),
                ));
            }

            Ok(())
        }
    }
}

fn op_matches_type(stype: &ShardableType, elt: &MonoidElt) -> bool {
    match stype {
        ShardableType::Constant(_)
        | ShardableType::Variable(_)
        | ShardableType::NotTokenized(_) => false,

        ShardableType::Map(_, _) | ShardableType::StorageMap(_, _) => match elt {
            MonoidElt::General(_) => true,
            MonoidElt::SingletonKV(_, _) => true,
            _ => false,
        },

        ShardableType::Option(_) | ShardableType::StorageOption(_) => match elt {
            MonoidElt::General(_) => true,
            MonoidElt::OptionSome(_) => true,
            _ => false,
        },

        ShardableType::Multiset(_) => match elt {
            MonoidElt::General(_) => true,
            MonoidElt::SingletonMultiset(_) => true,
            _ => false,
        },
    }
}

/// Check that every Update and SpecialOp statement is allowed for the given
/// sharding strategy of its field.
///
/// This check is meant for 'transition' and 'readonly' transitions, so it also checks
/// that there are no 'init' statements, which are only meaningful in 'init' transitions.
///
/// It also checks that no fields are modified if it's a 'readonly' transition,
/// and conversely for a 'transition' transition, it checks that there are no
/// guard operations (these operations are allowed ONLY in 'readonly' transitions).

fn check_valid_ops(
    fields: &Vec<Field>,
    ts: &TransitionStmt,
    is_readonly: bool,
    errors: &mut Vec<Error>,
) {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                check_valid_ops(fields, t, is_readonly, errors);
            }
        }
        TransitionStmt::Let(_, _, _, _, child) => {
            check_valid_ops(fields, child, is_readonly, errors);
        }
        TransitionStmt::If(_, _, thn, els) => {
            check_valid_ops(fields, thn, is_readonly, errors);
            check_valid_ops(fields, els, is_readonly, errors);
        }
        TransitionStmt::Require(_, _) => {}
        TransitionStmt::Assert(..) => {}
        TransitionStmt::Initialize(span, _, _) => {
            errors.push(Error::new(
                span.span(),
                format!("'init' statement not allowed outside 'init' routine"),
            ));
        }
        TransitionStmt::Update(span, f, _) => {
            let field = get_field(fields, f);
            if !is_allowed_in_update_in_normal_transition(&field.stype) {
                errors.push(Error::new(
                    span.span(),
                    format!(
                        "'update' statement not allowed for field with sharding strategy '{:}'",
                        field.stype.strategy_name()
                    ),
                ));
            }
            if is_readonly {
                errors.push(Error::new(
                    span.span(),
                    format!("'update' statement not allowed in readonly transition"),
                ));
            }
        }
        TransitionStmt::Special(span, f, op, _) => {
            let field = get_field(fields, f);
            match is_allowed_in_special_op(*span, &field.stype, op) {
                Ok(()) => {}
                Err(err) => {
                    errors.push(err);
                }
            }
            if is_readonly && op.is_modifier() {
                errors.push(Error::new(
                    span.span(),
                    format!("'{:}' statement not allowed in readonly transition", op.stmt.name()),
                ));
            }
            if !is_readonly && op.is_only_allowed_in_readonly() {
                errors.push(Error::new(
                    span.span(),
                    format!("'{:}' statement only allowed in readonly transition", op.stmt.name()),
                ));
            }
        }
        TransitionStmt::PostCondition(..) => {
            panic!("should not have created any PostCondition statement yet");
        }
    }
}

/// Version of `check_valid_ops` but for 'init' routines.
/// The only valid ops in an 'init' routine are the 'init' statements.
/// Updates and special ops are all disallowed.

fn check_valid_ops_init(fields: &Vec<Field>, ts: &TransitionStmt, errors: &mut Vec<Error>) {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                check_valid_ops_init(fields, t, errors);
            }
        }
        TransitionStmt::Let(_, _, _, _, child) => {
            check_valid_ops_init(fields, child, errors);
        }
        TransitionStmt::If(_, _, thn, els) => {
            check_valid_ops_init(fields, thn, errors);
            check_valid_ops_init(fields, els, errors);
        }
        TransitionStmt::Require(_, _) => {}
        TransitionStmt::Assert(span, _, _) => {
            errors.push(Error::new(*span, "'assert' statement not allowed in initialization"));
        }
        TransitionStmt::Initialize(_, _, _) => {}
        TransitionStmt::Update(span, _, _) => {
            errors.push(Error::new(
                *span,
                "'update' statement not allowed in initialization; use 'init' instead",
            ));
        }
        TransitionStmt::Special(span, _, _, _) => {
            errors.push(Error::new(
                *span,
                format!(
                    "'{:}' statement not allowed in initialization; use 'init' instead",
                    ts.statement_name()
                ),
            ));
        }
        TransitionStmt::PostCondition(..) => {
            panic!("should have have PostCondition statement here");
        }
    }
}

/// Check that the identifiers bound in 'let' statements are all distinct,
/// and that they don't overlap with the parameters of a transition.

fn check_let_shadowing(trans: &Transition, errors: &mut Vec<Error>) {
    let mut ids = trans.params.iter().map(|p| p.name.to_string()).collect();
    check_let_shadowing_rec(&trans.body, &mut ids, errors)
}

fn check_let_shadowing_rec(ts: &TransitionStmt, ids: &mut Vec<String>, errors: &mut Vec<Error>) {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v {
                check_let_shadowing_rec(t, ids, errors);
            }
        }
        TransitionStmt::Let(span, id, _, _, child) => {
            let s = id.to_string();
            if ids.contains(&s) {
                errors.push(Error::new(
                    *span,
                    format!("state machine transitions forbid let-shadowing"),
                ));
            } else {
                ids.push(s);
            }

            check_let_shadowing_rec(child, ids, errors);
        }
        TransitionStmt::If(_, _, e1, e2) => {
            check_let_shadowing_rec(e1, ids, errors);
            check_let_shadowing_rec(e2, ids, errors);
        }
        TransitionStmt::Require(..) => {}
        TransitionStmt::Assert(..) => {}
        TransitionStmt::Update(..) => {}
        TransitionStmt::Initialize(..) => {}
        TransitionStmt::PostCondition(..) => {}
        TransitionStmt::Special(..) => {}
    }
}

/// Check simple well-formedness properties of the transitions.

pub fn check_transitions(sm: &mut SM) -> syn::parse::Result<()> {
    let mut results: Vec<syn::parse::Result<()>> = Vec::new();

    let mut transitions = Vec::new();
    std::mem::swap(&mut transitions, &mut sm.transitions);

    for tr in transitions.iter_mut() {
        results.push(check_transition(sm, tr));
    }

    std::mem::swap(&mut transitions, &mut sm.transitions);

    combine_results(results)
}

pub fn check_transition(sm: &SM, tr: &mut Transition) -> syn::parse::Result<()> {
    validate_idents_transition(tr)?;

    let mut errors = Vec::new();
    check_updates_refer_to_valid_fields(&sm.fields, &tr.body, &mut errors);

    if errors.len() > 0 {
        return combine_errors_or_ok(errors);
    }

    match &tr.kind {
        TransitionKind::Readonly => {
            check_valid_ops(&sm.fields, &tr.body, true, &mut errors);
        }
        TransitionKind::Transition => {
            check_valid_ops(&sm.fields, &tr.body, false, &mut errors);
            check_at_most_one_update(sm, &tr.body, &mut errors);
        }
        TransitionKind::Init => {
            check_valid_ops_init(&sm.fields, &tr.body, &mut errors);
            if errors.len() == 0 {
                check_exactly_one_init(sm, &tr.body, &mut errors);
            }
        }
    }

    check_let_shadowing(tr, &mut errors);
    check_birds_eye(tr, sm.concurrent, &mut errors);
    check_inherent_conditions(sm, &mut tr.body, &mut errors);

    combine_errors_or_ok(errors)
}
