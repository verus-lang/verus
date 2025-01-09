use crate::ast::{
    Arm, AssertProof, LetKind, MonoidElt, MonoidStmtType, SpecialOp, SplitKind, SubIdx, Transition,
    TransitionKind, TransitionParam, TransitionStmt,
};
use crate::parse_token_stream::{keyword, peek_keyword};
use crate::util::combine_errors_or_ok;
use crate::util::{expr_from_tokens, pat_from_tokens};
use proc_macro2::Span;
use quote::{quote, quote_spanned};
use std::rc::Rc;
use syn_verus::parse;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::parse2;
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::token;
use syn_verus::visit::Visit;
use syn_verus::{
    braced, bracketed, parenthesized, Block, Error, Expr, ExprBlock, ExprLet, Ident, Macro, Pat,
    PatIdent, PatOr, Token, Type,
};

/// Translate Rust AST into a transition AST by parsing our transition DSL.
/// Every statement should be one of:
///   let, if, match (similar to the same statements in Rust)
///   init, update, add, remove, have, deposit, withdraw, guard (statements specific to our DSL)

pub fn parse_transition(mac: Macro) -> parse::Result<Transition> {
    // A transition definition looks like
    //    init!{ name(args) { ... } }
    // First, we determine the TransitionKind from the name of the macro,
    // then parse the token stream inside the macro.

    let kind = if mac.path.is_ident("init") {
        TransitionKind::Init
    } else if mac.path.is_ident("transition") {
        TransitionKind::Transition
    } else if mac.path.is_ident("readonly") {
        TransitionKind::ReadonlyTransition
    } else if mac.path.is_ident("property") {
        TransitionKind::Property
    } else {
        return Err(Error::new(
            mac.span(),
            "unrecognized macro for definiting a transition: expected `init!`, `transition!`, `readonly!`, or `property!`",
        ));
    };

    let ti: TransitionInner = parse2(mac.tokens)?;

    let TransitionInner { name, params, body } = ti;
    Ok(Transition { kind, name, params, body })
}

// Part of the transition that can be parsed via the macro's token stream,
// i.e., everything except the TransitionKind, which comes from the macro name.

struct TransitionInner {
    pub name: Ident,
    pub params: Vec<TransitionParam>,
    pub body: TransitionStmt,
}

impl Parse for TransitionInner {
    fn parse(input: ParseStream) -> parse::Result<TransitionInner> {
        let params_stream;
        let mut ctxt = Ctxt { counter: 0 };

        // parse `name(args...)`
        let name: Ident = input.parse()?;
        let _ = parenthesized!(params_stream in input);
        let params = parse_params(&params_stream)?;

        // parse `{ block ... }`
        let body = parse_transition_block(&mut ctxt, input)?;

        Ok(TransitionInner { name, params, body })
    }
}

struct Ctxt {
    counter: u64,
}

fn parse_params(input: ParseStream) -> parse::Result<Vec<TransitionParam>> {
    let args: Punctuated<(Ident, Type), token::Comma> = input.parse_terminated(parse_arg_typed)?;
    let mut v = Vec::new();
    for (ident, ty) in args.into_iter() {
        v.push(TransitionParam { name: ident, ty });
    }
    Ok(v)
}

fn parse_arg_typed(input: ParseStream) -> parse::Result<(Ident, Type)> {
    let ident: Ident = input.parse()?;
    let _: Token![:] = input.parse()?;
    let ty: Type = input.parse()?;
    Ok((ident, ty))
}

struct TLet(Span, Pat, Option<Type>, LetKind, Expr);
struct TSpecial(Span, Ident, SpecialOp, AssertProof, Pat);

enum StmtOrLet {
    Stmt(TransitionStmt),
    Let(TLet),
    Special(TSpecial),
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum Refute {
    Exhaustive, // normal let
    Require,    // require let
    Assert,     // asssert let
}

/// Parse any kind of transition statement. Note that 'let' statements aren't turned
/// into full TransitionStmts yet; instead we return the TLet stub.
fn parse_transition_stmt(ctxt: &mut Ctxt, input: ParseStream) -> parse::Result<Vec<StmtOrLet>> {
    // If the next token is a brace, parse as a block.
    if input.peek(token::Brace) {
        return Ok(vec![StmtOrLet::Stmt(parse_transition_block(ctxt, input)?)]);
    }

    // Try to parse as a 'let' statement (not 'let' won't parse as an identifier)
    if input.peek(Token![let]) {
        let let_token: Token![let] = input.parse()?;
        return Ok(parse_let(ctxt, let_token.span, Refute::Exhaustive, LetKind::Normal, input)?);
    }

    // Try to parse as an 'if' statement
    if input.peek(Token![if]) {
        return Ok(vec![StmtOrLet::Stmt(parse_conditional(ctxt, input)?)]);
    }

    // Try to parse as a 'match' statement
    if input.peek(Token![match]) {
        return Ok(vec![StmtOrLet::Stmt(parse_match(ctxt, input)?)]);
    }

    // Parse anything else by reading the next identifier and treating it as a "keyword"
    // in our DSL.

    let ident: Ident = match input.parse() {
        Ok(ident) => ident,
        Err(_) => {
            return Err(input.error("expected transition statement (e.g., `update ...`)"));
        }
    };

    // first we have to handle all these:
    //    birds_eye let
    //    require
    //    assert
    //    require let
    //    assert let
    //    require birds_eye let   (not allowed - see explanation in check_birds_eye.rs)
    //    assert birds_eye let

    if ident.to_string() == "birds_eye" {
        let _let_token: Token![let] = input.parse()?;
        return Ok(parse_let(ctxt, ident.span(), Refute::Exhaustive, LetKind::BirdsEye, input)?);
    } else if ident.to_string() == "require" || ident.to_string() == "assert" {
        let refute = if ident.to_string() == "require" { Refute::Require } else { Refute::Assert };
        if input.peek(Token![let]) {
            let _let_token: Token![let] = input.parse()?;
            Ok(parse_let(ctxt, ident.span(), refute, LetKind::Normal, input)?)
        } else if peek_keyword(input.cursor(), "birds_eye") {
            let _ = keyword(input, "birds_eye");
            let _let_token: Token![let] = input.parse()?;
            Ok(parse_let(ctxt, ident.span(), refute, LetKind::BirdsEye, input)?)
        } else {
            // Normal require/assert
            if ident.to_string() == "require" {
                Ok(vec![StmtOrLet::Stmt(parse_require(ident, input)?)])
            } else {
                Ok(vec![StmtOrLet::Stmt(parse_assert(ident, input)?)])
            }
        }
    } else if ident.to_string() == "update" {
        Ok(vec![StmtOrLet::Stmt(parse_update(ident, input)?)])
    } else if ident.to_string() == "init" {
        Ok(vec![StmtOrLet::Stmt(parse_init(ident, input)?)])
    } else if ident.to_string() == "have" {
        Ok(vec![parse_monoid_stmt(ident, input, MonoidStmtType::Have)?])
    } else if ident.to_string() == "add" {
        Ok(vec![parse_monoid_stmt(ident, input, MonoidStmtType::Add(false))?])
    } else if ident.to_string() == "remove" {
        Ok(vec![parse_monoid_stmt(ident, input, MonoidStmtType::Remove)?])
    } else if ident.to_string() == "guard" {
        Ok(vec![parse_monoid_stmt(ident, input, MonoidStmtType::Guard)?])
    } else if ident.to_string() == "deposit" {
        Ok(vec![parse_monoid_stmt(ident, input, MonoidStmtType::Deposit)?])
    } else if ident.to_string() == "withdraw" {
        Ok(vec![parse_monoid_stmt(ident, input, MonoidStmtType::Withdraw)?])
    } else {
        Err(Error::new(ident.span(), "expected transition stmt"))
    }
}

/// Parse a block `{ transition stmts }`

fn parse_transition_block(ctxt: &mut Ctxt, input: ParseStream) -> parse::Result<TransitionStmt> {
    let content;
    let brace_token = braced!(content in input);
    let mut stmts: Vec<StmtOrLet> = Vec::new();
    while !content.is_empty() {
        let mut new_stmts = parse_transition_stmt(ctxt, &content)?;
        stmts.append(&mut new_stmts);
    }
    Ok(stmts_or_lets_to_block(brace_token.span, stmts))
}

fn stmts_or_lets_to_block(span: Span, tstmts: Vec<StmtOrLet>) -> TransitionStmt {
    // A block is a list of statements, but we want to re-organize the AST
    // into the style of a 'let ... in ...' expression, so that
    // for each 'let' statement, the scope of the bound variable is given by
    // the child of the 'let' node in our tree representation.
    //
    // So for example, if the Rust AST has a block like this:
    //
    //    a;
    //    let x = foo;
    //    b;
    //    c;
    //
    // We'd turn it into:
    //
    //    {a; let x = foo in { b; c; } }

    // Note that we traverse in reverse-order; thus, cur_block is
    // constructed in reverse order, and therefore we need to reverse it back
    // when we use it.

    let mut cur_block = Vec::new();
    for stmt_or_let in tstmts.into_iter().rev() {
        match stmt_or_let {
            StmtOrLet::Stmt(s) => cur_block.push(s),
            StmtOrLet::Let(TLet(span, pat, ty, lk, lv)) => {
                cur_block = vec![TransitionStmt::Split(
                    span,
                    SplitKind::Let(pat, ty, lk, lv),
                    vec![TransitionStmt::Block(span, cur_block.into_iter().rev().collect())],
                )];
            }
            StmtOrLet::Special(TSpecial(span, ident, op, proof, pat)) => {
                cur_block = vec![TransitionStmt::Split(
                    span,
                    SplitKind::Special(ident, op, proof, Some(pat)),
                    vec![TransitionStmt::Block(span, cur_block.into_iter().rev().collect())],
                )];
            }
        }
    }

    TransitionStmt::Block(span, cur_block.into_iter().rev().collect())
}

/// Parse a statement that looks like `add field += ...;`
/// Assumes the parsing cursor starts after the initial keyword.
/// This handles add, remove, have, deposit, withdraw, guard.

fn parse_monoid_stmt(
    kw: Ident,
    input: ParseStream,
    monoid_stmt_type: MonoidStmtType,
) -> parse::Result<StmtOrLet> {
    // Parse the field name we are operating on.
    let field: Ident = input.parse()?;

    // Parse the operator depending on the type of statement this is.
    let monoid_stmt_type = match monoid_stmt_type {
        MonoidStmtType::Have | MonoidStmtType::Guard => {
            let _t: Token![>=] = input.parse()?;
            monoid_stmt_type
        }
        MonoidStmtType::Deposit => {
            let _t: Token![+=] = input.parse()?;
            monoid_stmt_type
        }
        MonoidStmtType::Add(_) => {
            if input.peek(Token![+=]) {
                let _t: Token![+=] = input.parse()?;
                MonoidStmtType::Add(false)
            } else if input.peek(token::Paren) {
                let paren_content;
                let _ = parenthesized!(paren_content in input);
                let _ = keyword(&paren_content, "union");
                let _: Token![=] = input.parse()?;
                MonoidStmtType::Add(true)
            } else {
                return Err(input.error("expected += or union="));
            }
        }
        MonoidStmtType::Remove | MonoidStmtType::Withdraw => {
            let _t: Token![-=] = input.parse()?;
            monoid_stmt_type
        }
    };

    // Parse the part after the operator. The syntax used here determines what "type"
    // the data is (e.g., multiset, option, or map).
    let (elem, pat_opt) = parse_monoid_elt(input, monoid_stmt_type)?;

    if pat_opt.is_some() {
        match monoid_stmt_type {
            MonoidStmtType::Have | MonoidStmtType::Remove | MonoidStmtType::Withdraw => {
                // okay
            }
            MonoidStmtType::Guard | MonoidStmtType::Add(_) | MonoidStmtType::Deposit => {}
        }
    }

    // Parse a proof block after the 'by' keyword, if it's there.
    let proof_block = if peek_keyword(input.cursor(), "by") {
        let _ = keyword(input, "by");
        let block: Block = input.parse()?;
        Some(Rc::new(block))
    } else {
        None
    };

    let semi: Token![;] = input.parse()?;

    let stmt_span = kw.span().join(semi.span()).unwrap_or(kw.span());

    match (&monoid_stmt_type, &elem) {
        (MonoidStmtType::Guard, MonoidElt::SingletonMultiset(_e))
        | (MonoidStmtType::Deposit, MonoidElt::SingletonMultiset(_e))
        | (MonoidStmtType::Withdraw, MonoidElt::SingletonMultiset(_e)) => {
            return Err(Error::new(stmt_span, "storage_multiset strategy not implemented"));
        }
        _ => {}
    };

    // We fill this in later.
    let error_msg = "".to_string();

    let op = SpecialOp { stmt: monoid_stmt_type, elt: elem };

    let proof = AssertProof { proof: proof_block, error_msg };

    match pat_opt {
        None => {
            // No bindings: return special op as a standalone statement with no child statement
            let kind = SplitKind::Special(field, op, proof, None);
            Ok(StmtOrLet::Stmt(TransitionStmt::Split(
                stmt_span,
                kind,
                vec![TransitionStmt::Block(stmt_span, vec![])],
            )))
        }
        Some(pat) => {
            // Bindings: Return TSpecial, so that all statements after the special op
            // end up in the scope of the pattern bindings
            Ok(StmtOrLet::Special(TSpecial(stmt_span, field, op, proof, pat)))
        }
    }
}

/// Parse the element to be added, removed, etc. Looks like one of:
///
/// * `{x}` multiset singleton (TODO change to `multiset {...}`?
/// * `set {x}` set singleton
/// * `true`
/// * `[key => value]` map singleton
/// * `Some(x)` optional value
/// * `(x)` general value
fn parse_monoid_elt(
    input: ParseStream,
    monoid_stmt_type: MonoidStmtType,
) -> parse::Result<(MonoidElt, Option<Pat>)> {
    if input.peek(token::Brace) {
        let content;
        let _ = braced!(content in input);
        let e: Expr = parse_expr_for_monoid_elt(&content)?;
        Ok((MonoidElt::SingletonMultiset(e), None))
    } else if input.peek(token::Bracket) {
        let content;
        let _ = bracketed!(content in input);
        let key: Expr = parse_expr_for_monoid_elt(&content)?;
        let _: Token![=>] = content.parse()?;
        if content.peek(Token![let]) {
            let _: Token![let] = content.parse()?;
            let pat: Pat = content.parse()?;
            Ok((MonoidElt::SingletonKV(key, None), Some(pat)))
        } else {
            let val: Expr = content.parse()?;
            Ok((MonoidElt::SingletonKV(key, Some(val)), None))
        }
    } else if peek_keyword(input.cursor(), "Some") {
        let _ = keyword(input, "Some");
        let content;
        let _ = parenthesized!(content in input);
        if content.peek(Token![let]) {
            let _: Token![let] = content.parse()?;
            let pat: Pat = content.parse()?;
            Ok((MonoidElt::OptionSome(None), Some(pat)))
        } else {
            let e: Expr = content.parse()?;
            Ok((MonoidElt::OptionSome(Some(e)), None))
        }
    } else if peek_keyword(input.cursor(), "set") {
        let _ = keyword(input, "set");
        let content;
        let _ = braced!(content in input);
        let e: Expr = parse_expr_for_monoid_elt(&content)?;
        Ok((MonoidElt::SingletonSet(e), None))
    } else if peek_keyword(input.cursor(), "true") {
        let _ = keyword(input, "true");
        Ok((MonoidElt::True, None))
    } else if input.peek(token::Paren) {
        let content;
        let _ = parenthesized!(content in input);
        let e: Expr = parse_expr_for_monoid_elt(&content)?;
        Ok((MonoidElt::General(e), None))
    } else {
        let name = monoid_stmt_type.name();
        Err(input.error(format!("malformed {name:} statement")))
    }
}

fn parse_expr_for_monoid_elt(input: ParseStream) -> parse::Result<Expr> {
    if input.peek(Token![let]) {
        Err(input.error("A let-pattern binding is not supported here; only supported in the positions `[... => let PAT]` or `Some(let PAT)`."))
    } else {
        input.parse()
    }
}

/// Parse conditional `if { stmts } else { stmts }`
fn parse_conditional(ctxt: &mut Ctxt, input: ParseStream) -> parse::Result<TransitionStmt> {
    let if_token: Token![if] = input.parse()?;
    // Based on implementation of syn::ExprIf::parse
    let cond: Expr = input.call(Expr::parse_without_eager_brace)?;
    let thn = parse_transition_block(ctxt, input)?;
    if input.peek(Token![else]) {
        let els = parse_else_block(ctxt, input)?;
        let span = if_token.span.join(*els.get_span()).unwrap_or(if_token.span);
        error_on_if_let(&cond)?;
        Ok(TransitionStmt::Split(span, SplitKind::If(cond), vec![thn, els]))
    } else {
        let span = if_token.span.join(*thn.get_span()).unwrap_or(if_token.span);
        let els = TransitionStmt::Block(if_token.span, vec![]);
        error_on_if_let(&cond)?;
        Ok(TransitionStmt::Split(span, SplitKind::If(cond), vec![thn, els]))
    }
}

fn parse_else_block(ctxt: &mut Ctxt, input: ParseStream) -> parse::Result<TransitionStmt> {
    let _else_token: Token![else] = input.parse()?;

    // handle the `else if` case

    let lookahead = input.lookahead1();
    if input.peek(Token![if]) {
        parse_conditional(ctxt, input)
    } else if input.peek(token::Brace) {
        parse_transition_block(ctxt, input)
    } else {
        Err(lookahead.error())
    }
}

/// Parse `let x = ...;` or `birds_eye let x = ...;`
fn parse_let(
    ctxt: &mut Ctxt,
    span: Span,
    refute: Refute,
    lk: LetKind,
    input: ParseStream,
) -> parse::Result<Vec<StmtOrLet>> {
    if refute == Refute::Require && lk == LetKind::BirdsEye {
        return Err(input.error("'require birds_eye let' is not allowed because 'require' statements should not be in the scope of a `birds_eye` let-binding; preconditions of an exchange cannot depend on such bindings"));
    }

    let pat: Pat = input.parse()?;

    match &pat {
        Pat::Ident(PatIdent { ident, .. }) => {
            if ident.to_string() == "birds_eye" {
                return Err(Error::new(
                    pat.span(),
                    "keywords in the wrong order: use `birds_eye let` instead",
                ));
            }
        }
        _ => {}
    }

    let ty = if input.peek(Token![:]) {
        let _t: Token![:] = input.parse()?;
        let ty: Type = input.parse()?;
        Some(ty)
    } else {
        None
    };

    let _t: Token![=] = input.parse()?;
    let e: Expr = input.parse()?;
    let semi: Token![;] = input.parse()?;

    let stmt_span = span.join(semi.span()).unwrap_or(span);

    match refute {
        Refute::Exhaustive => Ok(vec![StmtOrLet::Let(TLet(stmt_span, pat, ty, lk, e))]),
        Refute::Require | Refute::Assert => {
            // We immediately de-sugar a 'require let' or 'require assert' into something like
            //    let tmp (: type)? = expr;
            //    require(match tmp { pat => true, _ => false })
            //    let (ids) = match tmp { pat => (ids), _ => arbitrary() }

            let uniq_id = ctxt.counter;
            ctxt.counter += 1;

            let tmp_ident =
                Ident::new(&("tmp_for_match_".to_string() + &uniq_id.to_string()), stmt_span);

            let pat_tmp = Pat::Ident(PatIdent {
                attrs: vec![],
                by_ref: None,
                mutability: None,
                ident: tmp_ident.clone(),
                subpat: None,
            });
            let match_cond = expr_from_tokens(quote! {
                match #tmp_ident { #pat => true, _ => false }
            });
            let proof = AssertProof { proof: None, error_msg: "assert_let_pattern".to_string() };

            let mut v = vec![
                StmtOrLet::Let(TLet(stmt_span, pat_tmp, ty, lk, e)),
                if refute == Refute::Require {
                    StmtOrLet::Stmt(TransitionStmt::Require(stmt_span, match_cond))
                } else {
                    StmtOrLet::Stmt(TransitionStmt::Assert(stmt_span, match_cond, proof))
                },
            ];

            let ids = crate::ident_visitor::pattern_get_bound_idents(&pat);
            if ids.len() > 0 {
                let match_select;
                let pat_tup;

                if ids.len() > 1 {
                    match_select = expr_from_tokens(quote_spanned_vstd! { vstd, stmt_span =>
                        match #tmp_ident { #pat => (#(#ids),*) , _ => #vstd::pervasive::arbitrary() }
                    });
                    pat_tup = pat_from_tokens(quote_spanned! { stmt_span =>
                        (#(#ids),*)
                    });
                } else {
                    let id = &ids[0];
                    match_select = expr_from_tokens(quote_spanned_vstd! { vstd, stmt_span =>
                        match #tmp_ident { #pat => #id , _ => #vstd::pervasive::arbitrary() }
                    });
                    pat_tup = pat_from_tokens(quote_spanned! { stmt_span =>
                        #id
                    });
                }

                v.push(StmtOrLet::Let(TLet(
                    stmt_span,
                    pat_tup,
                    None,
                    LetKind::Normal,
                    match_select,
                )));
            }

            Ok(v)
        }
    }
}

/// Parse `update field = ...;`
fn parse_update(kw: Ident, input: ParseStream) -> parse::Result<TransitionStmt> {
    let field: Ident = input.parse()?;

    let mut subs = Vec::new();
    loop {
        if input.peek(Token![.]) {
            let _: Token![.] = input.parse()?;
            let sub_field: Ident = input.parse()?;
            subs.push(SubIdx::Field(sub_field));
        } else if input.peek(token::Bracket) {
            let content;
            let _ = bracketed!(content in input);
            let idx_expr: Expr = content.parse()?;
            subs.push(SubIdx::Idx(idx_expr));
        } else {
            break;
        }
    }

    let _t: Token![=] = input.parse()?;
    let e: Expr = input.parse()?;
    let semi: Token![;] = input.parse()?;

    let stmt_span = kw.span().join(semi.span()).unwrap_or(kw.span());

    if subs.len() > 0 {
        Ok(TransitionStmt::SubUpdate(stmt_span, field, subs, e))
    } else {
        Ok(TransitionStmt::Update(stmt_span, field, e))
    }
}

/// Parse `init field = ...;`
fn parse_init(kw: Ident, input: ParseStream) -> parse::Result<TransitionStmt> {
    let field: Ident = input.parse()?;
    let _t: Token![=] = input.parse()?;
    let e: Expr = input.parse()?;
    let semi: Token![;] = input.parse()?;

    let stmt_span = kw.span().join(semi.span()).unwrap_or(kw.span());

    Ok(TransitionStmt::Initialize(stmt_span, field, e))
}

/// Parse `assert ...;` or `assert ... by { ... }`
fn parse_assert(kw: Ident, input: ParseStream) -> parse::Result<TransitionStmt> {
    let e: Expr = input.parse()?;

    let proof_block = if peek_keyword(input.cursor(), "by") {
        let _ = keyword(input, "by");
        let block: Block = input.parse()?;
        Some(Rc::new(block))
    } else {
        None
    };

    let semi: Token![;] = input.parse()?;

    let stmt_span = kw.span().join(semi.span()).unwrap_or(kw.span());

    let proof = AssertProof { proof: proof_block, error_msg: "assert_safety".to_string() };
    Ok(TransitionStmt::Assert(stmt_span, e, proof))
}

/// Parse `require ...;`
fn parse_require(kw: Ident, input: ParseStream) -> parse::Result<TransitionStmt> {
    let e: Expr = input.parse()?;
    let semi: Token![;] = input.parse()?;
    let stmt_span = kw.span().join(semi.span()).unwrap_or(kw.span());
    Ok(TransitionStmt::Require(stmt_span, e))
}

/// Parse `match ... { ... }`
/// This is based on syn's `impl Parse for ExprMatch`,
/// but we have to modify it so that it parses a TransitionStmt instead of an Expr
/// in each arm. However, we can re-use some of the code for parsing the patterns

fn parse_match(ctxt: &mut Ctxt, input: ParseStream) -> parse::Result<TransitionStmt> {
    let match_token: Token![match] = input.parse()?;
    let expr = Expr::parse_without_eager_brace(input)?;

    let content;
    let brace_token = braced!(content in input);

    let mut arms = Vec::new();
    let mut stmts = Vec::new();
    while !content.is_empty() {
        let (arm, stmt) = parse_arm(ctxt, &content)?;
        arms.push(arm);
        stmts.push(stmt);
    }

    let span = match_token.span.join(brace_token.span).unwrap_or(match_token.span);

    Ok(TransitionStmt::Split(span, SplitKind::Match(expr, arms), stmts))
}

/// Parse an arm of a match statement. Based on `impl Parse for syn::Arm`
/// (but note that we return our own ast::Arm, not the syn::Arm)

fn parse_arm(ctxt: &mut Ctxt, input: ParseStream) -> parse::Result<(Arm, TransitionStmt)> {
    let pat = multi_pat_with_leading_vert(input)?;
    let guard = {
        if input.peek(Token![if]) {
            let if_token: Token![if] = input.parse()?;
            let guard: Expr = input.parse()?;
            Some((if_token, Box::new(guard)))
        } else {
            None
        }
    };
    let fat_arrow_token = input.parse()?;
    let body = parse_transition_block(ctxt, input)?;

    let requires_comma = false;
    let comma = {
        if requires_comma && !input.is_empty() { Some(input.parse()?) } else { input.parse()? }
    };

    let arm = Arm { pat, guard, fat_arrow_token, comma };
    Ok((arm, body))
}

// these are (private) functions from syn, used for parsing patterns in a `match` statement

fn multi_pat_with_leading_vert(input: ParseStream) -> parse::Result<Pat> {
    let leading_vert: Option<Token![|]> = input.parse()?;
    multi_pat_impl(input, leading_vert)
}

fn multi_pat_impl(input: ParseStream, leading_vert: Option<Token![|]>) -> parse::Result<Pat> {
    let mut pat: Pat = input.parse()?;
    if leading_vert.is_some()
        || input.peek(Token![|]) && !input.peek(Token![||]) && !input.peek(Token![|=])
    {
        let mut cases = Punctuated::new();
        cases.push_value(pat);
        while input.peek(Token![|]) && !input.peek(Token![||]) && !input.peek(Token![|=]) {
            let punct = input.parse()?;
            cases.push_punct(punct);
            let pat: Pat = input.parse()?;
            cases.push_value(pat);
        }
        pat = Pat::Or(PatOr { attrs: Vec::new(), leading_vert, cases });
    }
    Ok(pat)
}

/// Error if the user writes `if let ... = ... { ... }` which is unsupported.
/// Descend into the expression to check for chained if-let as well.
fn error_on_if_let(cond: &Expr) -> parse::Result<()> {
    let mut ilv = IfLetVisitor { errors: Vec::new() };
    ilv.visit_expr(cond);
    combine_errors_or_ok(ilv.errors)
}

struct IfLetVisitor {
    pub errors: Vec<Error>,
}

impl<'ast> Visit<'ast> for IfLetVisitor {
    fn visit_expr_block(&mut self, _node: &'ast ExprBlock) {
        // do nothing here; don't recurse into block expressions
    }

    fn visit_expr_let(&mut self, node: &'ast ExprLet) {
        self.errors.push(Error::new(
            node.span(),
            "transition definitions do not support if-let conditionals (try using a 'match' statement instead)",
        ));
    }
}
