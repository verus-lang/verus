use crate::ast::Field;
use crate::ast::{
    AssertProof, MonoidElt, MonoidStmtType, PostConditionReason, PostConditionReasonField, SM,
    ShardableType, SimplStmt, SpecialOp, SplitKind, SubIdx, TransitionKind, TransitionStmt,
};
use crate::check_bind_stmts::uses_bind;
use crate::concurrency_tokens::assign_pat_or_arbitrary;
use crate::transitions::get_field;
use crate::util::is_definitely_irrefutable;
use proc_macro2::Span;
use quote::{quote, quote_spanned};
use verus_syn::spanned::Spanned;
use verus_syn::{Expr, Ident, Pat, Type};

/// Simplify out `update` statements, including `add_element` etc.
///
/// Note: for 'readonly' stuff, there's less to do because we don't need to handle
/// updates. However, we still need to handle 'guard' and 'have' statements, which will
/// be translated into 'asserts'.
// Implementation:
//
// The simplification process has 3 primary passes here:
//
//  1. Turn the TransitionStmt into a SimplStmt by translating all the update, init,
//     and special ops into require, assert, and assign statements.
//     For example, `update x = 5` becomes `assign tmp_update_x = 5;`
//     or `add x += z` becomes
//        `assert (tmp_update_x + z is valid); assign tmp_update_x = tmp_update_x + z`
//
//  2. Add PostCondition statements that relate the final values of the tmp variables
//     to the post.{field} values.
//
//  3. A transformation pass to handle 'assert' statements (simplify_asserts.rs)
//
// So for example if we have fields {a, b, c} and a transition declared as
//
//    `update a = 5;`
//
// Then after steps 1 and 2 we would have:
//
//    assign tmp_update_a = pre.a;      // Prologue initializing each tmp
//    assign tmp_update_b = pre.b;      // variable to the initial state
//    assign tmp_update_c = pre.c;      // (This part is skipped for init transitions)
//
//    assign tmp_update_a = 5;          // Translated from the 'update' statement
//
//    postcondition post.a == tmp_update_a    // Added in phase 2
//    postcondition post.b == tmp_update_a
//    postcondition post.c == tmp_update_a
//
// Thus for the second phase, placing the PostCondition statements,
// the key is that the PostCondition statement has to go some
// place where temp_foo has taken on its final value (i.e., the PostCondition can't come
// before any statement which might update the value). Granted, one option would be to
// always put them at the end (in which case one might ask why we bother).
//
// The reason is because of conditionals. Consider,
//
//      if cond {
//          update(foo, x);
//      } else {
//          update(foo, y);
//      }
//
// One option would be to generate a relation that looks like,
//      `post.foo == (if cond { x } else { y })`
// But for better user experience, we'd ideally want one predicate per 'update' statement,
// since more fine-grained predicates make it easier to diagnose errors and each predicate
// could then be associated with the source line of a single 'update' statement.
// So we would place the PostCondition statements like this:
//
//      if cond {
//          assign tmp_update_foo = x;                 // from update(foo, x)
//          PostCondition(post.foo == tmp_update_foo); // inserted
//      } else {
//          assign tmp_update_foo = y;                 // from update(foo, y)
//          PostCondition(post.foo == tmp_update_foo); // inserted
//      }
//
// Which then generates relations like:
//
//      `cond ==> post.foo == x`
//      `!cond ==> post.foo == y`
//
// Thus the purpose of this phase is to find these ideal positions for the
// PostCondition statements.
pub fn simplify_ops(sm: &SM, ts: &TransitionStmt, kind: TransitionKind) -> Vec<SimplStmt> {
    // Phase 1: translate the update, init, and special ops into SimplStmts
    let sops = simplify_ops_with_pre(&ts, &sm, kind);

    // Phase 2: Add PostCondition statements
    let sops = add_postconditions(sm, sops);

    sops
}

// Phase 2. Adding the PostCondition operations.
//
// The key correctness criteria are:
//
//    1. A postcondition for a field `foo` cannot come before a statement that updates `foo`
//    2. Every control-flow path must encounter exactly one PostCondition statement
//
// Other than that, we want the PostCondition to come as soon as possible.
// So we basically just walk the tree backwards, keeping track of which fields we have
// made placements for. When we encounter the first update statement (the first from the end,
// that is) we add the PostCondition.
//
// For each conditional, we have to check if we added a statement on one branch but not
// the other, and if so, resolve.

fn add_postconditions(sm: &SM, sops: Vec<SimplStmt>) -> Vec<SimplStmt> {
    let mut found = Vec::new();
    let mut sops = sops;
    add_postconditions_vec(&mut sops, &mut found);

    for field in &sm.fields {
        if !contains_ident(&found, &field.name) {
            panic!("add_postconditions_vec failed to properly add all postconditions");
        }
    }

    sops
}

fn add_postconditions_vec(sops: &mut Vec<SimplStmt>, found: &mut Vec<Ident>) {
    // To be appended at the end
    let mut new_sops = Vec::new();

    for sop in sops.iter_mut().rev() {
        // Add a postcondition statement if necessary.

        match &sop {
            SimplStmt::Assign(span, tmp_ident, _, _, is_prequel) => {
                let f_ident_opt = field_name_from_tmp(tmp_ident);
                if let Some(f_ident) = f_ident_opt {
                    if !contains_ident(found, &f_ident) {
                        // If it's an assign statement, AND we haven't added
                        // a postcondition for this field yet, then add a postcondition
                        // at the end of this block of statements.
                        // (And leave the current statement unchanged).

                        let reason = if *is_prequel {
                            PostConditionReasonField::NoUpdateTopLevel
                        } else {
                            PostConditionReasonField::Update
                        };

                        found.push(f_ident.clone());
                        new_sops.push(postcondition_stmt(*span, f_ident, reason));
                    }
                }
            }
            _ => {}
        }

        // Recurse.

        match sop {
            SimplStmt::Let(_, _, _, _, v, _) => {
                add_postconditions_vec(v, found);
            }
            SimplStmt::Split(_span, _, es, _) => {
                let idx = found.len();
                let mut found_inner = vec![found.clone(); es.len()];

                for i in 0..es.len() {
                    add_postconditions_vec(&mut es[i].1, &mut found_inner[i]);
                }

                // For each side of the conditional (or arm of the match),
                // look at any newly-found
                // fields from that conditional (those after `idx`, the original
                // length of the array). For such a field, if it wasn't ALSO found
                // in some other branch, then we go ahead and add it to the other
                // branch now. Thus we maintain that, for each field and for each
                // conditional, we will either get a postcondition on both branches,
                // or on neither.

                // Step 1: Collect any field which is newly updated in any branch.

                let mut all_new = Vec::new();

                for j in 0..es.len() {
                    for i in idx..found_inner[j].len() {
                        if !contains_ident(&all_new, &found_inner[j][i]) {
                            all_new.push(found_inner[j][i].clone());
                        }
                    }
                }

                // Step 2: For each field and each branch, check if it needs to be
                // added, and if so, do so.

                for f in &all_new {
                    for j in 0..es.len() {
                        if !contains_ident(&found_inner[j], f) {
                            found_inner[j].push(f.clone());
                            let span = es[j].0;
                            es[j].1.push(postcondition_stmt(
                                span,
                                f.clone(),
                                PostConditionReasonField::NoUpdateConditional,
                            ));
                        }
                    }
                }

                // Make sure we end with `found` (the &mut argument) containing the
                // union of all the fields that were found on either branch.

                *found = found_inner[0].clone();
            }

            SimplStmt::Require(..)
            | SimplStmt::PostCondition(..)
            | SimplStmt::Assert(..)
            | SimplStmt::Assign(..) => {}
        }
    }

    sops.append(&mut new_sops);
}

fn postcondition_stmt(span: Span, f: Ident, pcrf: PostConditionReasonField) -> SimplStmt {
    let cur = get_cur(&f);
    SimplStmt::PostCondition(
        span,
        Expr::Verbatim(quote_spanned_vstd! { vstd, span =>
            #vstd::prelude::equal(post.#f, #cur)
        }),
        PostConditionReason::FieldValue(pcrf, f.to_string()),
    )
}

fn contains_ident(v: &Vec<Ident>, id: &Ident) -> bool {
    v.iter().any(|id0| id0 == id)
}

fn get_cur(field_name: &Ident) -> Expr {
    let id = get_cur_ident(field_name);
    Expr::Verbatim(quote! { #id })
}

pub const UPDATE_TMP_PREFIX: &str = "update_tmp_";

fn get_cur_ident(field_name: &Ident) -> Ident {
    let name = UPDATE_TMP_PREFIX.to_string() + &field_name.to_string();
    Ident::new(&name, field_name.span())
}

fn field_name_from_tmp(tmp_name: &Ident) -> Option<Ident> {
    let s = tmp_name.to_string();
    let ident_str = s.strip_prefix(UPDATE_TMP_PREFIX)?;
    Some(Ident::new(ident_str, tmp_name.span()))
}

// Phase 1. Give meaning to all the update, init, and special op statements.
// User-provided require and assert statements are just translated as they are.

fn simplify_ops_with_pre(ts: &TransitionStmt, sm: &SM, kind: TransitionKind) -> Vec<SimplStmt> {
    let mut ops = simplify_ops_rec(ts, sm);
    if kind == TransitionKind::Init {
        ops
    } else {
        // For each field, add `assign tmp_update_a = pre.a`
        // to the beginning for each field. (We don't do this step
        // for 'init' transitions because there is no 'pre' object.)
        //
        // Note that in either case, we are guaranteed to have at least
        // one 'assign' statement for each field. In the Init case, it's because
        // the user must initialize each field.
        // In the Transition case, it's because we do this step here.

        let mut ops1: Vec<SimplStmt> = sm
            .fields
            .iter()
            .map(|f| {
                let f_ident = &f.name;
                SimplStmt::Assign(
                    *ts.get_span(),
                    get_cur_ident(f_ident),
                    Box::new(f.get_type()),
                    Expr::Verbatim(quote! {pre.#f_ident}),
                    true,
                )
            })
            .collect();
        ops1.append(&mut ops);
        ops1
    }
}

fn simplify_ops_rec(ts: &TransitionStmt, sm: &SM) -> Vec<SimplStmt> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            let mut res = Vec::new();
            for t in v {
                let mut t = simplify_ops_rec(t, sm);
                res.append(&mut t);
            }
            res
        }
        TransitionStmt::Split(span, split_kind, es) => match &**split_kind {
            SplitKind::If(..) | SplitKind::Match(..) => {
                let mut new_es: Vec<(Span, Vec<SimplStmt>)> = Vec::new();
                for e in es {
                    let new_e1 = simplify_ops_rec(&e, sm);
                    new_es.push((*e.get_span(), new_e1));
                }

                vec![SimplStmt::Split(*span, split_kind.clone(), new_es, vec![])]
            }
            SplitKind::Let(pat, ty, _lk, e) => {
                assert!(es.len() == 1);
                let child = es.into_iter().next().expect("child");
                let new_child = simplify_ops_rec(child, sm);
                vec![SimplStmt::Let(*span, pat.clone(), ty.clone(), e.clone(), new_child, vec![])]
            }
            SplitKind::Special(f, op, proof, pat_opt) => {
                let field = get_field(&sm.fields, f);
                let (cond_ops, mut update_ops) =
                    simplify_special_op(*span, &field, op, pat_opt, proof);

                match pat_opt {
                    None => {
                        assert!(es.len() == 1 && es[0].is_trivial());
                        assert!(!uses_bind(&op.elt));
                        let mut res = cond_ops;
                        res.append(&mut update_ops);
                        res
                    }
                    Some(pat) => {
                        assert!(es.len() == 1);
                        assert!(uses_bind(&op.elt));
                        let child = es.into_iter().next().expect("child");
                        let mut new_child = simplify_ops_rec(child, sm);

                        let mut all_children = update_ops;
                        all_children.append(&mut new_child);

                        let initializer = get_initializer_expr(f, op);

                        let opt = assign_pat_or_arbitrary(pat, &initializer);

                        let mut res = cond_ops;
                        if let Some((pat1, init1)) = opt {
                            res.push(SimplStmt::Let(
                                *span,
                                Box::new(pat1),
                                None,
                                init1,
                                all_children,
                                vec![],
                            ));
                        } else {
                            res.append(&mut all_children);
                        }
                        res
                    }
                }
            }
        },

        TransitionStmt::PostCondition(_span, _e) => {
            panic!("unexpected TransitionStmt::PostCondition");
        }
        TransitionStmt::Require(span, e) => {
            vec![SimplStmt::Require(*span, e.clone())]
        }
        TransitionStmt::Assert(span, e, pf) => {
            vec![SimplStmt::Assert(*span, e.clone(), pf.clone())]
        }

        TransitionStmt::Initialize(span, f, e) | TransitionStmt::Update(span, f, e) => {
            let field = get_field(&sm.fields, f);
            vec![SimplStmt::Assign(
                *span,
                get_cur_ident(f),
                Box::new(field.get_type()),
                e.clone(),
                false,
            )]
        }
        TransitionStmt::SubUpdate(span, f, subs, e) => {
            let field = get_field(&sm.fields, f);
            let ty = field.get_type();
            // Errors are reported earlier by `transitions::desugar_sub_updates`;
            // this keeps them errors rather than panics.
            let value = sub_update_expr(&get_cur(f), Some(&ty), f, subs, e)
                .unwrap_or_else(|err| Expr::Verbatim(err.to_compile_error()));
            vec![SimplStmt::Assign(*span, get_cur_ident(f), Box::new(ty), value, false)]
        }
    }
}

fn simplify_special_op(
    span: Span,
    field: &Field,
    op: &SpecialOp,
    pat_opt: &Option<Box<Pat>>,
    proof: &AssertProof,
) -> (Vec<SimplStmt>, Vec<SimplStmt>) {
    match op {
        SpecialOp { stmt: MonoidStmtType::Have, elt } => {
            let cur = get_cur(&field.name);
            let prec = expr_ge(&field.stype, &cur, elt, pat_opt);
            (vec![SimplStmt::Require(span, prec)], vec![])
        }

        SpecialOp { stmt: MonoidStmtType::Add(_), elt } => {
            let cur = get_cur(&field.name);
            let new_val = expr_add(&field.stype, &cur, elt);

            (
                match expr_can_add(&field.stype, &cur, elt) {
                    Some(safety) => vec![SimplStmt::Assert(span, safety, proof.clone())],
                    None => vec![],
                },
                vec![SimplStmt::Assign(
                    span,
                    get_cur_ident(&field.name),
                    Box::new(field.get_type()),
                    new_val,
                    false,
                )],
            )
        }

        SpecialOp { stmt: MonoidStmtType::Remove, elt } => {
            let cur = get_cur(&field.name);
            let new_val = expr_remove(&field.stype, &cur, elt);
            let prec = expr_ge(&field.stype, &cur, elt, pat_opt);
            (
                vec![SimplStmt::Require(span, prec)],
                vec![SimplStmt::Assign(
                    span,
                    get_cur_ident(&field.name),
                    Box::new(field.get_type()),
                    new_val,
                    false,
                )],
            )
        }

        SpecialOp { stmt: MonoidStmtType::Guard, elt } => {
            let cur = get_cur(&field.name);
            assert!(pat_opt.is_none());
            let prec = expr_ge(&field.stype, &cur, elt, pat_opt);
            (vec![SimplStmt::Assert(span, prec, proof.clone())], vec![])
        }

        SpecialOp { stmt: MonoidStmtType::Deposit, elt } => {
            let cur = get_cur(&field.name);
            let new_val = expr_add(&field.stype, &cur, elt);
            (
                match expr_can_add(&field.stype, &cur, elt) {
                    Some(safety) => vec![SimplStmt::Assert(span, safety, proof.clone())],
                    None => vec![],
                },
                vec![SimplStmt::Assign(
                    span,
                    get_cur_ident(&field.name),
                    Box::new(field.get_type()),
                    new_val,
                    false,
                )],
            )
        }

        SpecialOp { stmt: MonoidStmtType::Withdraw, elt } => {
            let cur = get_cur(&field.name);
            let new_val = expr_remove(&field.stype, &cur, elt);
            let prec = expr_ge(&field.stype, &cur, elt, pat_opt);
            (
                vec![SimplStmt::Assert(span, prec, proof.clone())],
                vec![SimplStmt::Assign(
                    span,
                    get_cur_ident(&field.name),
                    Box::new(field.get_type()),
                    new_val,
                    false,
                )],
            )
        }
    }
}

fn get_initializer_expr(f: &Ident, op: &SpecialOp) -> Expr {
    let cur = get_cur(f);
    match &op.elt {
        MonoidElt::OptionSome(None) => Expr::Verbatim(quote! {
            #cur.arrow_0()
        }),
        MonoidElt::SingletonKV(key, None) => Expr::Verbatim(quote! {
            #cur.index(#key)
        }),
        _ => {
            panic!("simplify_let_value got unexpected elt");
        }
    }
}

/// The whole-field value of the sub-update `update f<subs> = val`, where `root`
/// is the value of `f` before the update and `root_ty` its declared type.
///
/// An index step `[i]` becomes `root.update_at_index(i, ..)`. A field step
/// `.m` becomes a struct update `Path { m: .., ..root }` when the type of
/// `root` is a path (a struct, or a tuple struct with `.0`), and rebuilds the
/// tuple when it is a tuple type. The macro does not see struct definitions,
/// so the type at each step is only known syntactically: from the field's
/// declared type, through tuple elements and the values of `Map`/`IMap`/`Seq`.
/// A field step at a point of unknown type (e.g. `.a.b` with `a` a struct
/// field) is an error.
pub fn sub_update_expr(
    root: &Expr,
    root_ty: Option<&Type>,
    field: &Ident,
    subs: &[SubIdx],
    val: &Expr,
) -> verus_syn::parse::Result<Expr> {
    sub_update_rec(root, root_ty, field.to_string(), subs, val)
}

fn sub_update_rec(
    root: &Expr,
    root_ty: Option<&Type>,
    desc: String,
    subs: &[SubIdx],
    val: &Expr,
) -> verus_syn::parse::Result<Expr> {
    let Some((sub, rest)) = subs.split_first() else {
        return Ok(val.clone());
    };
    let ty = root_ty.map(strip_type_parens);
    match sub {
        SubIdx::Idx(idx_e) => {
            let child = Expr::Verbatim(quote_spanned! { idx_e.span() => #root.index(#idx_e) });
            let child_ty = ty.and_then(collection_value_type);
            let desc = format!("{desc}[..]");
            let r = sub_update_rec(&child, child_ty.as_ref(), desc, rest, val)?;
            Ok(Expr::Verbatim(quote_spanned! { idx_e.span() =>
                #root.update_at_index(#idx_e, #r)
            }))
        }
        SubIdx::Field(member) => {
            let span = member.span();
            let child = Expr::Verbatim(quote_spanned! { span => #root.#member });
            let child_desc = format!("{desc}.{}", member_string(member));
            match ty {
                None => Err(verus_syn::Error::new(
                    span,
                    format!(
                        "cannot update a field of `{desc}`: its type is not known to the state machine macro \
                        (field updates are supported on the field's declared type, tuple elements, and \
                        `Map`/`IMap`/`Seq` values); update `{desc}` as a whole instead"
                    ),
                )),
                Some(Type::Tuple(tuple)) => {
                    let verus_syn::Member::Unnamed(index) = member else {
                        return Err(verus_syn::Error::new(
                            span,
                            format!("`{desc}` has a tuple type; expected a tuple index"),
                        ));
                    };
                    let i = index.index as usize;
                    if i >= tuple.elems.len() {
                        return Err(verus_syn::Error::new(
                            span,
                            format!("`{desc}` has no element {i}"),
                        ));
                    }
                    let elem_ty = tuple.elems.iter().nth(i);
                    let r = sub_update_rec(&child, elem_ty, child_desc, rest, val)?;
                    let elems = (0..tuple.elems.len()).map(|j| {
                        if j == i {
                            quote_spanned! { span => #r }
                        } else {
                            let j = verus_syn::Index { index: j as u32, span };
                            quote_spanned! { span => #root.#j }
                        }
                    });
                    Ok(Expr::Verbatim(quote_spanned! { span => ( #(#elems,)* ) }))
                }
                Some(Type::Path(type_path)) if type_path.qself.is_none() => {
                    // Spanned at the field, so that e.g. "expected struct, found
                    // enum" points at the update.
                    let path = respan(
                        quote::ToTokens::to_token_stream(&expr_path_of_type(
                            &type_path.path,
                            span,
                        )?),
                        span,
                    );
                    let r = sub_update_rec(&child, None, child_desc, rest, val)?;
                    Ok(Expr::Verbatim(quote_spanned! { span =>
                        #path { #member: #r, .. #root }
                    }))
                }
                Some(_) => Err(verus_syn::Error::new(
                    span,
                    format!(
                        "cannot update a field of `{desc}`: field updates are supported on struct and tuple types"
                    ),
                )),
            }
        }
    }
}

fn respan(tokens: proc_macro2::TokenStream, span: Span) -> proc_macro2::TokenStream {
    tokens
        .into_iter()
        .map(|mut tt| {
            if let proc_macro2::TokenTree::Group(g) = &tt {
                let mut group = proc_macro2::Group::new(g.delimiter(), respan(g.stream(), span));
                group.set_span(span);
                tt = proc_macro2::TokenTree::Group(group);
            } else {
                tt.set_span(span);
            }
            tt
        })
        .collect()
}

fn strip_type_parens(ty: &Type) -> &Type {
    match ty {
        Type::Paren(p) => strip_type_parens(&p.elem),
        Type::Group(g) => strip_type_parens(&g.elem),
        _ => ty,
    }
}

fn member_string(member: &verus_syn::Member) -> String {
    match member {
        verus_syn::Member::Named(ident) => ident.to_string(),
        verus_syn::Member::Unnamed(index) => index.index.to_string(),
    }
}

/// The value type `V` of `Map<K, V>`, `IMap<K, V>` or `Seq<V>` (by name).
fn collection_value_type(ty: &Type) -> Option<Type> {
    let Type::Path(type_path) = ty else { return None };
    if type_path.qself.is_some() {
        return None;
    }
    let segment = type_path.path.segments.last()?;
    let verus_syn::PathArguments::AngleBracketed(args) = &segment.arguments else { return None };
    let types: Vec<&Type> = args
        .args
        .iter()
        .filter_map(|a| match a {
            verus_syn::GenericArgument::Type(t) => Some(t),
            _ => None,
        })
        .collect();
    match (segment.ident.to_string().as_str(), types.len()) {
        ("Map" | "IMap", 2) => Some(types[1].clone()),
        ("Seq", 1) => Some(types[0].clone()),
        _ => None,
    }
}

/// The type path `a::B<T>` as an expression path `a::B::<T>` for a struct
/// expression.
fn expr_path_of_type(
    path: &verus_syn::Path,
    span: Span,
) -> verus_syn::parse::Result<verus_syn::Path> {
    let mut path = path.clone();
    for segment in path.segments.iter_mut() {
        match &mut segment.arguments {
            verus_syn::PathArguments::None => {}
            verus_syn::PathArguments::AngleBracketed(args) => {
                args.colon2_token = Some(Default::default());
            }
            verus_syn::PathArguments::Parenthesized(_) => {
                return Err(verus_syn::Error::new(
                    span,
                    "field updates are supported on struct and tuple types",
                ));
            }
        }
    }
    Ok(path)
}

fn get_opt_type(stype: &ShardableType) -> Type {
    match stype {
        ShardableType::Option(ty) => ty.clone(),
        ShardableType::StorageOption(ty) => ty.clone(),
        ShardableType::PersistentOption(ty) => ty.clone(),
        _ => {
            panic!("get_opt_type expected option");
        }
    }
}

pub(crate) fn expr_can_add(stype: &ShardableType, cur: &Expr, elt: &MonoidElt) -> Option<Expr> {
    if stype.is_persistent() {
        match elt {
            MonoidElt::SingletonKV(key, val) => Some(Expr::Verbatim(quote_vstd! { vstd =>
                #vstd::prelude::imply(
                    (#cur).dom().contains(#key),
                    #vstd::prelude::equal((#cur).index(#key), #val),
                )
            })),
            MonoidElt::OptionSome(e) => Some(Expr::Verbatim(quote_vstd! { vstd =>
                #vstd::prelude::imply(
                    (#cur) is Some,
                    #vstd::prelude::equal((#cur).arrow_0(), #e),
                )
            })),
            MonoidElt::SingletonMultiset(_) => None,
            MonoidElt::SingletonSet(_e) => None,
            MonoidElt::True => None,
            MonoidElt::General(e) => match stype {
                ShardableType::PersistentSet(_) => None,
                ShardableType::PersistentISet(_) => None,
                ShardableType::PersistentCount => None,
                ShardableType::PersistentBool => None,
                ShardableType::PersistentMap(_, _) => Some(Expr::Verbatim(quote! {
                    (#cur).agrees(#e)
                })),
                ShardableType::PersistentIMap(_, _) => Some(Expr::Verbatim(quote! {
                    (#cur).agrees(#e)
                })),
                ShardableType::PersistentOption(_) => {
                    let ty = get_opt_type(stype);
                    Some(Expr::Verbatim(quote_vstd! { vstd =>
                        #vstd::state_machine_internal::opt_agree::<#ty>(#cur, #e)
                    }))
                }
                _ => {
                    panic!("expr_can_add invalid case {:?}", stype);
                }
            },
        }
    } else {
        match elt {
            MonoidElt::OptionSome(_e) => Some(Expr::Verbatim(quote! { (#cur) is None })),
            MonoidElt::SingletonKV(key, _val) => {
                Some(Expr::Verbatim(quote! { !(#cur).dom().contains(#key) }))
            }
            MonoidElt::SingletonSet(e) => Some(Expr::Verbatim(quote! { !(#cur).contains(#e) })),
            MonoidElt::True => Some(Expr::Verbatim(quote! { !(#cur) })),
            MonoidElt::SingletonMultiset(_e) => None,
            MonoidElt::General(e) => match stype {
                ShardableType::Option(_) | ShardableType::StorageOption(_) => {
                    let ty = get_opt_type(stype);
                    Some(Expr::Verbatim(quote_vstd! { vstd =>
                        #vstd::state_machine_internal::opt_is_none::<#ty>(#e)
                          || (#cur) is None
                    }))
                }

                ShardableType::Map(_, _)
                | ShardableType::StorageMap(_, _)
                | ShardableType::IMap(_, _)
                | ShardableType::StorageIMap(_, _) => Some(Expr::Verbatim(quote! {
                    (#cur).dom().disjoint((#e).dom())
                })),

                ShardableType::Multiset(_) => None,
                ShardableType::Count => None,
                ShardableType::Bool => Some(Expr::Verbatim(quote! {
                    (!(#cur) || !(#e))
                })),
                ShardableType::Set(_) | ShardableType::ISet(_) => Some(Expr::Verbatim(quote! {
                    (#cur).disjoint(#e)
                })),

                _ => {
                    panic!("expected option/map/multiset/count");
                }
            },
        }
    }
}

/// Add the elements, assuming they are addable. Build the expression assuming
/// to "prefer" the content from the right-hand side, even though it shouldn't really matter.
/// That's often easier, anyway.
pub(crate) fn expr_add(stype: &ShardableType, cur: &Expr, elt: &MonoidElt) -> Expr {
    if stype.is_persistent() {
        match elt {
            MonoidElt::SingletonKV(key, val) => {
                Expr::Verbatim(quote! { (#cur).insert(#key, #val) })
            }
            MonoidElt::OptionSome(e) => {
                let ty = get_opt_type(stype);
                Expr::Verbatim(quote! {
                    ::core::option::Option::<#ty>::Some(#e)
                })
            }
            MonoidElt::SingletonMultiset(_) => {
                panic!("singleton multiset not supported");
            }
            MonoidElt::SingletonSet(e) => Expr::Verbatim(quote! {
                (#cur).insert(#e)
            }),
            MonoidElt::True => Expr::Verbatim(quote! { true }),
            MonoidElt::General(e) => match stype {
                ShardableType::PersistentMap(_, _) | ShardableType::PersistentIMap(_, _) => {
                    Expr::Verbatim(quote! { (#cur).union_prefer_right(#e) })
                }
                ShardableType::PersistentOption(_) => {
                    let ty = get_opt_type(stype);
                    Expr::Verbatim(quote_vstd! { vstd =>
                        #vstd::state_machine_internal::opt_add::<#ty>(#cur, #e)
                    })
                }
                ShardableType::PersistentSet(_) | ShardableType::PersistentISet(_) => {
                    Expr::Verbatim(quote! {
                        ((#cur).union(#e))
                    })
                }
                ShardableType::PersistentCount => Expr::Verbatim(quote_vstd! { vstd =>
                    #vstd::state_machine_internal::nat_max(#cur, #e)
                }),
                ShardableType::PersistentBool => Expr::Verbatim(quote! {
                    ((#cur) || (#e))
                }),
                _ => {
                    panic!("expr_can_add invalid case {:?}", stype);
                }
            },
        }
    } else {
        match elt {
            MonoidElt::OptionSome(Some(e)) => {
                let ty = get_opt_type(stype);
                Expr::Verbatim(quote! {
                    ::core::option::Option::<#ty>::Some(#e)
                })
            }
            MonoidElt::OptionSome(None) => {
                panic!("expr_add: no value found");
            }
            MonoidElt::SingletonKV(key, Some(val)) => Expr::Verbatim(quote! {
                (#cur).insert(#key, #val)
            }),
            MonoidElt::SingletonKV(_key, None) => {
                panic!("expr_add: no value found");
            }
            MonoidElt::SingletonMultiset(e) => Expr::Verbatim(quote! {
                (#cur).insert(#e)
            }),
            MonoidElt::SingletonSet(e) => Expr::Verbatim(quote! {
                (#cur).insert(#e)
            }),
            MonoidElt::True => Expr::Verbatim(quote! {
                true
            }),
            MonoidElt::General(e) => match stype {
                ShardableType::Option(_) | ShardableType::StorageOption(_) => {
                    let ty = get_opt_type(stype);
                    Expr::Verbatim(quote_vstd! { vstd =>
                        #vstd::state_machine_internal::opt_add::<#ty>(#cur, #e)
                    })
                }

                ShardableType::Map(_, _)
                | ShardableType::StorageMap(_, _)
                | ShardableType::IMap(_, _)
                | ShardableType::StorageIMap(_, _) => Expr::Verbatim(quote! {
                    (#cur).union_prefer_right(#e)
                }),

                ShardableType::Multiset(_) => Expr::Verbatim(quote! {
                    (#cur).add(#e)
                }),

                ShardableType::Set(_) | ShardableType::ISet(_) => Expr::Verbatim(quote! {
                    ((#cur).union(#e))
                }),

                ShardableType::Count => Expr::Verbatim(quote! {
                    (#cur) + (#e)
                }),

                ShardableType::Bool => Expr::Verbatim(quote! {
                    (#cur) || (#e)
                }),

                _ => {
                    panic!("expected option/map/multiset (case 1)");
                }
            },
        }
    }
}

fn expr_matches(e: &Expr, pat: &Pat) -> Expr {
    Expr::Verbatim(quote_spanned! { pat.span() =>
        match (#e) {
            #pat => true,
            #[allow(unreachable_patterns)] _ => false
        }
    })
}

fn expr_ge(stype: &ShardableType, cur: &Expr, elt: &MonoidElt, pat_opt: &Option<Box<Pat>>) -> Expr {
    // note: persistent case should always be the same as the normal case

    match elt {
        MonoidElt::OptionSome(None) => {
            let pat = pat_opt.as_ref().unwrap();
            if !is_definitely_irrefutable(pat) {
                let e = expr_matches(&Expr::Verbatim(quote! { (#cur).arrow_0() }), pat);
                Expr::Verbatim(quote! { (#cur) is Some && (#e) })
            } else {
                Expr::Verbatim(quote! { (#cur) is Some })
            }
        }
        MonoidElt::OptionSome(Some(e)) => {
            let ty = get_opt_type(stype);
            Expr::Verbatim(quote_vstd! { vstd =>
                #vstd::prelude::equal(
                    #cur,
                    ::core::option::Option::<#ty>::Some(#e)
                )
            })
        }
        MonoidElt::SingletonKV(key, None) => {
            let pat = pat_opt.as_ref().unwrap();
            if !is_definitely_irrefutable(pat) {
                let e = expr_matches(&Expr::Verbatim(quote! { (#cur).index(#key) }), pat);
                Expr::Verbatim(quote! {
                    (#cur).dom().contains(#key) && (#e)
                })
            } else {
                Expr::Verbatim(quote! {
                    (#cur).dom().contains(#key)
                })
            }
        }
        MonoidElt::SingletonKV(key, Some(val)) => Expr::Verbatim(quote! {
            (#cur).contains_pair(#key, #val)
        }),
        MonoidElt::SingletonMultiset(e) => Expr::Verbatim(quote! {
            (#cur).count(#e) >= spec_literal_nat("1")
        }),
        MonoidElt::SingletonSet(e) => Expr::Verbatim(quote! {
            (#cur).contains(#e)
        }),
        MonoidElt::True => Expr::Verbatim(quote! {
            (#cur)
        }),
        MonoidElt::General(e) => match stype {
            ShardableType::Option(_)
            | ShardableType::PersistentOption(_)
            | ShardableType::StorageOption(_) => {
                let ty = get_opt_type(stype);
                Expr::Verbatim(quote_vstd! { vstd =>
                    #vstd::state_machine_internal::opt_ge::<#ty>(#cur, #e)
                })
            }

            ShardableType::Map(_, _)
            | ShardableType::PersistentMap(_, _)
            | ShardableType::IMap(_, _)
            | ShardableType::PersistentIMap(_, _)
            | ShardableType::StorageMap(_, _)
            | ShardableType::StorageIMap(_, _) => Expr::Verbatim(quote! {
                (#e).submap_of(#cur)
            }),

            ShardableType::Multiset(_) => Expr::Verbatim(quote! {
                (#e).subset_of(#cur)
            }),

            ShardableType::Set(_)
            | ShardableType::PersistentSet(_)
            | ShardableType::ISet(_)
            | ShardableType::PersistentISet(_) => Expr::Verbatim(quote! {
                (#e).subset_of(#cur)
            }),

            ShardableType::Count | ShardableType::PersistentCount => Expr::Verbatim(quote! {
                (#cur) >= (#e)
            }),

            ShardableType::Bool | ShardableType::PersistentBool => {
                Expr::Verbatim(quote_vstd! { vstd =>
                    #vstd::prelude::imply(#e, #cur)
                })
            }

            _ => {
                panic!("expected option/map/multiset (case 2)");
            }
        },
    }
}

pub(crate) fn expr_remove(stype: &ShardableType, cur: &Expr, elt: &MonoidElt) -> Expr {
    assert!(!stype.is_persistent());
    match elt {
        MonoidElt::OptionSome(_e) => {
            let ty = get_opt_type(stype);
            Expr::Verbatim(quote! {
                ::core::option::Option::<#ty>::None
            })
        }
        MonoidElt::SingletonKV(key, _val) => Expr::Verbatim(quote! {
            (#cur).remove(#key)
        }),
        MonoidElt::SingletonMultiset(e) => Expr::Verbatim(quote! {
            (#cur).remove(#e)
        }),
        MonoidElt::SingletonSet(e) => Expr::Verbatim(quote! {
            (#cur).remove(#e)
        }),
        MonoidElt::True => Expr::Verbatim(quote! {
            false
        }),
        MonoidElt::General(e) => match stype {
            ShardableType::Option(_) | ShardableType::StorageOption(_) => {
                let ty = get_opt_type(stype);
                Expr::Verbatim(quote_vstd! { vstd =>
                    #vstd::state_machine_internal::opt_sub::<#ty>(#cur, #e)
                })
            }

            ShardableType::Map(_, _)
            | ShardableType::StorageMap(_, _)
            | ShardableType::IMap(_, _)
            | ShardableType::StorageIMap(_, _) => Expr::Verbatim(quote! {
                (#cur).remove_keys(#e.dom())
            }),

            ShardableType::Multiset(_) => Expr::Verbatim(quote! {
                (#cur).sub(#e)
            }),

            ShardableType::Set(_) | ShardableType::ISet(_) => Expr::Verbatim(quote! {
                (#cur).difference(#e)
            }),

            ShardableType::Count => Expr::Verbatim(quote! {
                (((#cur) - (#e)) as nat)
            }),

            ShardableType::Bool => Expr::Verbatim(quote! {
                (#cur) && !(#e)
            }),

            _ => {
                panic!("expected option/map/multiset (case 3)");
            }
        },
    }
}

/// For the verified backend: the fields a transition assigns (beyond the
/// prologue `assign update_tmp_f = pre.f`), and the statements with the
/// prologue of every other field dropped and its `update_tmp_f` read as
/// `pre.f`. A field the transition does not update then costs no temporary in
/// the generated relations and executors.
pub fn inline_unassigned(
    sm: &SM,
    sops: Vec<SimplStmt>,
) -> (Vec<SimplStmt>, std::collections::HashSet<String>) {
    fn assigned(sops: &[SimplStmt], out: &mut std::collections::HashSet<String>) {
        for s in sops {
            match s {
                SimplStmt::Assign(_, n, _, _, false) => {
                    if let Some(f) = field_name_from_tmp(n) {
                        out.insert(f.to_string());
                    }
                }
                SimplStmt::Let(_, _, _, _, v, _) => assigned(v, out),
                SimplStmt::Split(_, _, es, _) => {
                    for (_, v) in es {
                        assigned(v, out)
                    }
                }
                _ => {}
            }
        }
    }
    let mut set = std::collections::HashSet::new();
    assigned(&sops, &mut set);
    let inline: std::collections::HashMap<String, Ident> = sm
        .fields
        .iter()
        .filter(|f| !set.contains(&f.name.to_string()))
        .map(|f| (get_cur_ident(&f.name).to_string(), f.name.clone()))
        .collect();
    fn rw(
        ts: proc_macro2::TokenStream,
        m: &std::collections::HashMap<String, Ident>,
    ) -> proc_macro2::TokenStream {
        use proc_macro2::{Group, TokenTree};
        let mut out = proc_macro2::TokenStream::new();
        for t in ts {
            match t {
                TokenTree::Ident(id) if m.contains_key(&id.to_string()) => {
                    let f = &m[&id.to_string()];
                    out.extend(quote! {(pre.#f)});
                }
                TokenTree::Group(g) => {
                    let mut ng = Group::new(g.delimiter(), rw(g.stream(), m));
                    ng.set_span(g.span());
                    out.extend([TokenTree::Group(ng)]);
                }
                t => out.extend([t]),
            }
        }
        out
    }
    fn ex(e: &Expr, m: &std::collections::HashMap<String, Ident>) -> Expr {
        Expr::Verbatim(rw(quote! {#e}, m))
    }
    fn pf(p: &AssertProof, m: &std::collections::HashMap<String, Ident>) -> AssertProof {
        AssertProof {
            proof: p.proof.as_ref().map(|b| {
                let b = &**b;
                std::rc::Rc::new(
                    verus_syn::parse2(rw(quote! {#b}, m)).expect("rewritten proof block"),
                )
            }),
            error_msg: p.error_msg.clone(),
        }
    }
    fn go(sops: Vec<SimplStmt>, m: &std::collections::HashMap<String, Ident>) -> Vec<SimplStmt> {
        let mut out = vec![];
        for s in sops {
            out.push(match s {
                SimplStmt::Assign(_, ref n, _, _, true) if m.contains_key(&n.to_string()) => {
                    continue;
                }
                SimplStmt::Assign(sp, n, t, e, p) => SimplStmt::Assign(sp, n, t, ex(&e, m), p),
                SimplStmt::Require(sp, e) => SimplStmt::Require(sp, ex(&e, m)),
                SimplStmt::PostCondition(sp, e, r) => SimplStmt::PostCondition(sp, ex(&e, m), r),
                SimplStmt::Assert(sp, e, p) => SimplStmt::Assert(sp, ex(&e, m), pf(&p, m)),
                SimplStmt::Let(sp, pat, ty, e, v, ids) => {
                    SimplStmt::Let(sp, pat, ty, ex(&e, m), go(v, m), ids)
                }
                SimplStmt::Split(sp, k, es, ids) => {
                    let k = match *k {
                        SplitKind::If(e) => SplitKind::If(ex(&e, m)),
                        SplitKind::Match(e, arms) => SplitKind::Match(
                            ex(&e, m),
                            arms.into_iter()
                                .map(|mut a| {
                                    a.guard = a.guard.map(|(t, g)| (t, Box::new(ex(&g, m))));
                                    a
                                })
                                .collect(),
                        ),
                        k => k,
                    };
                    let es = es.into_iter().map(|(sp, v)| (sp, go(v, m))).collect();
                    SimplStmt::Split(sp, Box::new(k), es, ids)
                }
            });
        }
        out
    }
    (go(sops, &inline), set)
}

/// For the verified backend's strong relation: the top-level postconditions of
/// the fields in `preserved` (each `equal(post.f, pre.f)` with its own error
/// message) as one conjunction, reported for all of them.
pub fn merge_preserved(
    sops: Vec<SimplStmt>,
    preserved: &std::collections::HashSet<String>,
) -> Vec<SimplStmt> {
    let mut out = vec![];
    let mut merged: Vec<(Span, Expr, String)> = vec![];
    for s in sops {
        match s {
            SimplStmt::PostCondition(
                sp,
                e,
                PostConditionReason::FieldValue(PostConditionReasonField::NoUpdateTopLevel, f),
            ) if preserved.contains(&f) => merged.push((sp, e, f)),
            s => out.push(s),
        }
    }
    if let Some((sp, _, _)) = merged.first() {
        let sp = *sp;
        let es: Vec<_> = merged.iter().map(|(_, e, _)| e).collect();
        let names: Vec<_> = merged.iter().map(|(_, _, f)| f.clone()).collect();
        out.push(SimplStmt::PostCondition(
            sp,
            Expr::Verbatim(quote! {(true #(&& #es)*)}),
            PostConditionReason::FieldValue(
                PostConditionReasonField::NoUpdateTopLevel,
                names.join("`, `"),
            ),
        ));
    }
    out
}
