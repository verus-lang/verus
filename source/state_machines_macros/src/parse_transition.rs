use crate::ast::{
    AssertProof, LetKind, SpecialOp, Transition, TransitionKind, TransitionParam, TransitionStmt,
};
use crate::parse_token_stream::{keyword, peek_keyword};
use proc_macro2::Span;
use std::rc::Rc;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::Comma;
use syn::{braced, bracketed, parenthesized, Block, Error, Expr, Ident, Macro, Token, Type};

/// Translate Rust AST into a transition AST by parsing our transition DSL.
/// Every statement should be one of:

pub fn parse_transition(mac: Macro) -> syn::parse::Result<Transition> {
    // A transition definition looks like
    //    init!{ name(args) { ... } }
    // First, we determine the TransitionKind from the name of the macro,
    // then parse the token stream inside the macro.

    let kind = if mac.path.is_ident("init") {
        TransitionKind::Init
    } else if mac.path.is_ident("transition") {
        TransitionKind::Transition
    } else if mac.path.is_ident("readonly") {
        TransitionKind::Readonly
    } else {
        return Err(Error::new(
            mac.span(),
            "unrecognized macro for definiting a transition: expected `init!`, `transition!`, or `readonly!`",
        ));
    };

    let ti: TransitionInner = syn::parse2(mac.tokens)?;

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
    fn parse(input: ParseStream) -> syn::parse::Result<TransitionInner> {
        let params_stream;

        // parse `name(args...)`
        let name: Ident = input.parse()?;
        let _ = parenthesized!(params_stream in input);
        let params = parse_params(&params_stream)?;

        // parse `{ block ... }`
        let body = parse_transition_block(input)?;

        Ok(TransitionInner { name, params, body })
    }
}

fn parse_params(input: ParseStream) -> syn::parse::Result<Vec<TransitionParam>> {
    let args: Punctuated<(Ident, Type), Comma> = input.parse_terminated(parse_arg_typed)?;
    let mut v = Vec::new();
    for (ident, ty) in args.into_iter() {
        v.push(TransitionParam { name: ident, ty });
    }
    Ok(v)
}

fn parse_arg_typed(input: ParseStream) -> syn::parse::Result<(Ident, Type)> {
    let ident: Ident = input.parse()?;
    let _: Token![:] = input.parse()?;
    let ty: Type = input.parse()?;
    Ok((ident, ty))
}

struct TLet(Span, Ident, LetKind, Expr);

enum StmtOrLet {
    Stmt(TransitionStmt),
    Let(TLet),
}

/// Parse any kind of transition statement. Note that 'let' statements aren't turned
/// into full TransitionStmts yet; instead we return the TLet stub.
fn parse_transition_stmt(input: ParseStream) -> syn::parse::Result<StmtOrLet> {
    // If the next token is a brace, parse as a block.
    if input.peek(syn::token::Brace) {
        return Ok(StmtOrLet::Stmt(parse_transition_block(input)?));
    }

    // Try to parse as a 'let' statement (not 'let' won't parse as an identifier)
    if input.peek(Token![let]) {
        let let_token: Token![let] = input.parse()?;
        return Ok(StmtOrLet::Let(parse_let(let_token.span, LetKind::Normal, input)?));
    }

    // Try to parse as an 'if' statement
    if input.peek(Token![if]) {
        return Ok(StmtOrLet::Stmt(parse_conditional(input)?));
    }

    // Parse anything else by reading the next identifier and treating it as a "keyword"
    // in our DSL.

    let ident: Ident = match input.parse() {
        Ok(ident) => ident,
        Err(_) => {
            return Err(input.error("expected transition statement (e.g., `update ...`)"));
        }
    };

    if ident.to_string() == "update" {
        Ok(StmtOrLet::Stmt(parse_update(ident, input)?))
    } else if ident.to_string() == "init" {
        Ok(StmtOrLet::Stmt(parse_init(ident, input)?))
    } else if ident.to_string() == "require" {
        Ok(StmtOrLet::Stmt(parse_require(ident, input)?))
    } else if ident.to_string() == "assert" {
        Ok(StmtOrLet::Stmt(parse_assert(ident, input)?))
    } else if ident.to_string() == "have" {
        Ok(StmtOrLet::Stmt(parse_monoid_stmt(ident, input, MonoidStmtType::Have)?))
    } else if ident.to_string() == "add" {
        Ok(StmtOrLet::Stmt(parse_monoid_stmt(ident, input, MonoidStmtType::Add)?))
    } else if ident.to_string() == "remove" {
        Ok(StmtOrLet::Stmt(parse_monoid_stmt(ident, input, MonoidStmtType::Remove)?))
    } else if ident.to_string() == "guard" {
        Ok(StmtOrLet::Stmt(parse_monoid_stmt(ident, input, MonoidStmtType::Guard)?))
    } else if ident.to_string() == "deposit" {
        Ok(StmtOrLet::Stmt(parse_monoid_stmt(ident, input, MonoidStmtType::Deposit)?))
    } else if ident.to_string() == "withdraw" {
        Ok(StmtOrLet::Stmt(parse_monoid_stmt(ident, input, MonoidStmtType::Withdraw)?))
    } else if ident.to_string() == "birds_eye" {
        let let_token: Token![let] = input.parse()?;
        return Ok(StmtOrLet::Let(parse_let(let_token.span, LetKind::BirdsEye, input)?));
    } else {
        Err(Error::new(ident.span(), "expected transition stmt"))
    }
}

/// Parse a block `{ transition stmts }`

fn parse_transition_block(input: ParseStream) -> syn::parse::Result<TransitionStmt> {
    let content;
    let brace_token = braced!(content in input);
    let mut stmts = Vec::new();
    while !content.is_empty() {
        let stmt = parse_transition_stmt(&content)?;
        stmts.push(stmt);
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
            StmtOrLet::Let(TLet(span, id, lk, e)) => {
                cur_block = vec![TransitionStmt::Let(
                    span,
                    id,
                    lk,
                    e,
                    Box::new(TransitionStmt::Block(span, cur_block.into_iter().rev().collect())),
                )];
            }
        }
    }

    TransitionStmt::Block(span, cur_block.into_iter().rev().collect())
}

#[derive(Clone, Copy)]
enum MonoidStmtType {
    Have,
    Add,
    Remove,
    Guard,
    Deposit,
    Withdraw,
}

impl MonoidStmtType {
    fn name(self) -> &'static str {
        match self {
            MonoidStmtType::Have => "have",
            MonoidStmtType::Add => "add",
            MonoidStmtType::Remove => "remove",
            MonoidStmtType::Guard => "guard",
            MonoidStmtType::Deposit => "deposit",
            MonoidStmtType::Withdraw => "withdraw",
        }
    }
}

enum MonoidElt {
    OptionSome(Expr),
    SingletonKV(Expr, Expr),
    SingletonMultiset(Expr),
}

/// Parse a statement that looks like `add field += ...;`
/// Assumes the parsing cursor starts after the initial keyword.
/// This handles add, remove, have, deposit, withdraw, guard.

fn parse_monoid_stmt(
    kw: Ident,
    input: ParseStream,
    monoid_stmt_type: MonoidStmtType,
) -> syn::parse::Result<TransitionStmt> {
    // Parse the field name we are operating on.
    let field: Ident = input.parse()?;

    // Parse the operator depending on the type of statement this is.
    match monoid_stmt_type {
        MonoidStmtType::Have | MonoidStmtType::Guard => {
            let _t: Token![>=] = input.parse()?;
        }
        MonoidStmtType::Add | MonoidStmtType::Deposit => {
            let _t: Token![+=] = input.parse()?;
        }
        MonoidStmtType::Remove | MonoidStmtType::Withdraw => {
            let _t: Token![-=] = input.parse()?;
        }
    }

    // Parse the part after the operator. The syntax used here determines what "type"
    // the data is (e.g., multiset, option, or map).
    let elem = parse_monoid_elt(input, monoid_stmt_type)?;

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

    // The user is allowed to attach a proof block to any statement which has an inherent
    // safety condition.
    // Here, we check if the given statement actually has such a safety condition,
    // and if not, gives an appropriate error.
    //
    // withdraw, guard: yes, has a safety condition
    // remove, have: no safety condition; thus no proof needed
    // add, desposit: yes iff the underlying monoid's composition operator is not total.
    //   (e.g., composition is total for multiset, so AddElement returns false)
    //
    // See `docs/command-reference.md` for more explanation, or `simplification.rs`
    // for the expansions.

    if proof_block.is_some() {
        match monoid_stmt_type {
            MonoidStmtType::Withdraw | MonoidStmtType::Guard => {}
            MonoidStmtType::Have | MonoidStmtType::Remove => {
                let name = monoid_stmt_type.name();
                return Err(Error::new(
                    stmt_span,
                    format!(
                        "'{name:}' statement has no inherent safety condition, adding a proof body is meaningless"
                    ),
                ));
            }
            MonoidStmtType::Add | MonoidStmtType::Deposit => match elem {
                MonoidElt::OptionSome(..) | MonoidElt::SingletonKV(..) => {}
                MonoidElt::SingletonMultiset(..) => {
                    let name = monoid_stmt_type.name();
                    return Err(Error::new(
                        stmt_span,
                        format!(
                            "'{name:}' statement for multisets has no nontrivial inherent safety condition (as composition is total and thus this statement never fails); adding a proof body is meaningless"
                        ),
                    ));
                }
            },
        }
    }

    // Return a SpecialOp depending on the inferred sharding type and command type.
    // The `error_msg` should refer to the name of a lemma in
    // `pervasive::state_machine_internal`.

    let (op, error_msg) = match (monoid_stmt_type, elem) {
        (MonoidStmtType::Have, MonoidElt::OptionSome(e)) => (SpecialOp::HaveSome(e), ""),
        (MonoidStmtType::Have, MonoidElt::SingletonKV(k, v)) => (SpecialOp::HaveKV(k, v), ""),
        (MonoidStmtType::Have, MonoidElt::SingletonMultiset(e)) => (SpecialOp::HaveElement(e), ""),

        (MonoidStmtType::Add, MonoidElt::OptionSome(e)) => {
            (SpecialOp::AddSome(e), "assert_add_some")
        }
        (MonoidStmtType::Add, MonoidElt::SingletonKV(k, v)) => {
            (SpecialOp::AddKV(k, v), "assert_add_kv")
        }
        (MonoidStmtType::Add, MonoidElt::SingletonMultiset(e)) => (SpecialOp::AddElement(e), ""),

        (MonoidStmtType::Remove, MonoidElt::OptionSome(e)) => (SpecialOp::RemoveSome(e), ""),
        (MonoidStmtType::Remove, MonoidElt::SingletonKV(k, v)) => (SpecialOp::RemoveKV(k, v), ""),
        (MonoidStmtType::Remove, MonoidElt::SingletonMultiset(e)) => {
            (SpecialOp::RemoveElement(e), "")
        }

        (MonoidStmtType::Guard, MonoidElt::OptionSome(e)) => {
            (SpecialOp::GuardSome(e), "assert_guard_some")
        }
        (MonoidStmtType::Guard, MonoidElt::SingletonKV(k, v)) => {
            (SpecialOp::GuardKV(k, v), "assert_guard_kv")
        }

        (MonoidStmtType::Deposit, MonoidElt::OptionSome(e)) => {
            (SpecialOp::DepositSome(e), "assert_deposit_some")
        }
        (MonoidStmtType::Deposit, MonoidElt::SingletonKV(k, v)) => {
            (SpecialOp::DepositKV(k, v), "assert_deposit_kv")
        }

        (MonoidStmtType::Withdraw, MonoidElt::OptionSome(e)) => {
            (SpecialOp::WithdrawSome(e), "assert_withdraw_some")
        }
        (MonoidStmtType::Withdraw, MonoidElt::SingletonKV(k, v)) => {
            (SpecialOp::WithdrawKV(k, v), "assert_withdraw_kv")
        }

        (_, MonoidElt::SingletonMultiset(_e)) => {
            return Err(Error::new(stmt_span, "storage_multiset strategy not implemented"));
        }
    };

    let proof = AssertProof { proof: proof_block, error_msg };
    Ok(TransitionStmt::Special(stmt_span, field, op, proof))
}

/// Parse the element to be added, removed, etc. Looks like one of:
///
/// * `{x}` multiset singleton
/// * `[key => value]` map singleton
/// * `Some(x)` optional value
fn parse_monoid_elt(
    input: ParseStream,
    monoid_stmt_type: MonoidStmtType,
) -> syn::parse::Result<MonoidElt> {
    if input.peek(syn::token::Brace) {
        let content;
        let _ = braced!(content in input);
        let e: Expr = content.parse()?;
        Ok(MonoidElt::SingletonMultiset(e))
    } else if input.peek(syn::token::Bracket) {
        let content;
        let _ = bracketed!(content in input);
        let key: Expr = content.parse()?;
        let _: Token![=>] = content.parse()?;
        let val: Expr = content.parse()?;
        Ok(MonoidElt::SingletonKV(key, val))
    } else if peek_keyword(input.cursor(), "Some") {
        let _ = keyword(input, "Some");
        let content;
        let _ = parenthesized!(content in input);
        let e: Expr = content.parse()?;
        Ok(MonoidElt::OptionSome(e))
    } else {
        let name = monoid_stmt_type.name();
        Err(input.error(format!("malformed {name:} statement")))
    }
}

/// Parse conditional `if { stmts } else { stmts }`
fn parse_conditional(input: ParseStream) -> syn::parse::Result<TransitionStmt> {
    let if_token: Token![if] = input.parse()?;
    // Based on implementation of syn::ExprIf::parse
    let cond: Expr = input.call(Expr::parse_without_eager_brace)?;
    let thn = parse_transition_block(input)?;
    if input.peek(Token![else]) {
        let els = parse_else_block(input)?;
        let span = if_token.span.join(*els.get_span()).unwrap_or(if_token.span);
        Ok(TransitionStmt::If(span, cond, Box::new(thn), Box::new(els)))
    } else {
        let span = if_token.span.join(*thn.get_span()).unwrap_or(if_token.span);
        Ok(TransitionStmt::If(
            span,
            cond,
            Box::new(thn),
            Box::new(TransitionStmt::Block(if_token.span, vec![])),
        ))
    }
}

fn parse_else_block(input: ParseStream) -> syn::parse::Result<TransitionStmt> {
    let _else_token: Token![else] = input.parse()?;

    // handle the `else if` case

    let lookahead = input.lookahead1();
    if input.peek(Token![if]) {
        parse_conditional(input)
    } else if input.peek(syn::token::Brace) {
        parse_transition_block(input)
    } else {
        Err(lookahead.error())
    }
}

/// Parse `let x = ...;` or `birds_eye let x = ...;`
fn parse_let(span: Span, lk: LetKind, input: ParseStream) -> syn::parse::Result<TLet> {
    let varname: Ident = input.parse()?;
    let _t: Token![=] = input.parse()?;
    let e: Expr = input.parse()?;
    let semi: Token![;] = input.parse()?;

    let stmt_span = span.join(semi.span()).unwrap_or(span);

    Ok(TLet(stmt_span, varname, lk, e))
}

/// Parse `update field = ...;`
fn parse_update(kw: Ident, input: ParseStream) -> syn::parse::Result<TransitionStmt> {
    let field: Ident = input.parse()?;
    let _t: Token![=] = input.parse()?;
    let e: Expr = input.parse()?;
    let semi: Token![;] = input.parse()?;

    let stmt_span = kw.span().join(semi.span()).unwrap_or(kw.span());

    Ok(TransitionStmt::Update(stmt_span, field, e))
}

/// Parse `init field = ...;`
fn parse_init(kw: Ident, input: ParseStream) -> syn::parse::Result<TransitionStmt> {
    let field: Ident = input.parse()?;
    let _t: Token![=] = input.parse()?;
    let e: Expr = input.parse()?;
    let semi: Token![;] = input.parse()?;

    let stmt_span = kw.span().join(semi.span()).unwrap_or(kw.span());

    Ok(TransitionStmt::Initialize(stmt_span, field, e))
}

/// Parse `assert ...;` or `assert ... by { ... }`
fn parse_assert(kw: Ident, input: ParseStream) -> syn::parse::Result<TransitionStmt> {
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

    let proof = AssertProof { proof: proof_block, error_msg: "assert_safety" };
    Ok(TransitionStmt::Assert(stmt_span, e, proof))
}

/// Parse `require ...;`
fn parse_require(kw: Ident, input: ParseStream) -> syn::parse::Result<TransitionStmt> {
    let e: Expr = input.parse()?;
    let semi: Token![;] = input.parse()?;
    let stmt_span = kw.span().join(semi.span()).unwrap_or(kw.span());
    Ok(TransitionStmt::Require(stmt_span, e))
}
