use crate::ast::{
    Arm, AssertProof, LetKind, MonoidElt, MonoidStmtType, SpecialOp, SplitKind, SubIdx, Transition,
    TransitionKind, TransitionParam, TransitionStmt,
};
use crate::parse_token_stream::{keyword, peek_keyword};
use crate::util::combine_errors_or_ok;
use proc_macro2::Span;
use std::rc::Rc;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::Comma;
use syn::visit::Visit;
use syn::{braced, bracketed, parenthesized, Block, Error, Expr, Ident, Macro, Pat, Token, Type};

/// Translate Rust AST into a transition AST by parsing our transition DSL.
/// Every statement should be one of:
///   let, if, match (similar to the same statements in Rust)
///   init, update, add, remove, have, deposit, withdraw, guard (statements specific to our DSL)

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

struct TLet(Span, Pat, Option<Type>, LetKind, Expr);
struct TSpecial(Span, Ident, SpecialOp, AssertProof, Pat);

enum StmtOrLet {
    Stmt(TransitionStmt),
    Let(TLet),
    Special(TSpecial),
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

    // Try to parse as a 'match' statement
    if input.peek(Token![match]) {
        return Ok(StmtOrLet::Stmt(parse_match(input)?));
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
        Ok(parse_monoid_stmt(ident, input, MonoidStmtType::Have)?)
    } else if ident.to_string() == "add" {
        Ok(parse_monoid_stmt(ident, input, MonoidStmtType::Add)?)
    } else if ident.to_string() == "remove" {
        Ok(parse_monoid_stmt(ident, input, MonoidStmtType::Remove)?)
    } else if ident.to_string() == "guard" {
        Ok(parse_monoid_stmt(ident, input, MonoidStmtType::Guard)?)
    } else if ident.to_string() == "deposit" {
        Ok(parse_monoid_stmt(ident, input, MonoidStmtType::Deposit)?)
    } else if ident.to_string() == "withdraw" {
        Ok(parse_monoid_stmt(ident, input, MonoidStmtType::Withdraw)?)
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
        let new_stmt = parse_transition_stmt(&content)?;
        stmts.push(new_stmt);
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
) -> syn::parse::Result<StmtOrLet> {
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
    let (elem, pat_opt) = parse_monoid_elt(input, monoid_stmt_type)?;

    if pat_opt.is_some() {
        match monoid_stmt_type {
            MonoidStmtType::Have | MonoidStmtType::Remove | MonoidStmtType::Withdraw => {
                // okay
            }
            MonoidStmtType::Guard | MonoidStmtType::Add | MonoidStmtType::Deposit => {}
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
/// * `{x}` multiset singleton
/// * `[key => value]` map singleton
/// * `Some(x)` optional value
/// * `(x)` general value
fn parse_monoid_elt(
    input: ParseStream,
    monoid_stmt_type: MonoidStmtType,
) -> syn::parse::Result<(MonoidElt, Option<Pat>)> {
    if input.peek(syn::token::Brace) {
        let content;
        let _ = braced!(content in input);
        let e: Expr = content.parse()?;
        Ok((MonoidElt::SingletonMultiset(e), None))
    } else if input.peek(syn::token::Bracket) {
        let content;
        let _ = bracketed!(content in input);
        let key: Expr = content.parse()?;
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
    } else if input.peek(syn::token::Paren) {
        let content;
        let _ = parenthesized!(content in input);
        let e: Expr = content.parse()?;
        Ok((MonoidElt::General(e), None))
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
        error_on_if_let(&cond)?;
        Ok(TransitionStmt::Split(span, SplitKind::If(cond), vec![thn, els]))
    } else {
        let span = if_token.span.join(*thn.get_span()).unwrap_or(if_token.span);
        let els = TransitionStmt::Block(if_token.span, vec![]);
        error_on_if_let(&cond)?;
        Ok(TransitionStmt::Split(span, SplitKind::If(cond), vec![thn, els]))
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
    let pat: Pat = input.parse()?;

    match &pat {
        Pat::Ident(syn::PatIdent { ident, .. }) => {
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

    Ok(TLet(stmt_span, pat, ty, lk, e))
}

/// Parse `update field = ...;`
fn parse_update(kw: Ident, input: ParseStream) -> syn::parse::Result<TransitionStmt> {
    let field: Ident = input.parse()?;

    let mut subs = Vec::new();
    loop {
        if input.peek(Token![.]) {
            let _: Token![.] = input.parse()?;
            let sub_field: Ident = input.parse()?;
            subs.push(SubIdx::Field(sub_field));
        } else if input.peek(syn::token::Bracket) {
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

    let proof = AssertProof { proof: proof_block, error_msg: "assert_safety".to_string() };
    Ok(TransitionStmt::Assert(stmt_span, e, proof))
}

/// Parse `require ...;`
fn parse_require(kw: Ident, input: ParseStream) -> syn::parse::Result<TransitionStmt> {
    let e: Expr = input.parse()?;
    let semi: Token![;] = input.parse()?;
    let stmt_span = kw.span().join(semi.span()).unwrap_or(kw.span());
    Ok(TransitionStmt::Require(stmt_span, e))
}

/// Parse `match ... { ... }`
/// This is based on syn's `impl Parse for ExprMatch`,
/// but we have to modify it so that it parses a TransitionStmt instead of an Expr
/// in each arm. However, we can re-use some of the code for parsing the patterns

fn parse_match(input: ParseStream) -> syn::parse::Result<TransitionStmt> {
    let match_token: Token![match] = input.parse()?;
    let expr = Expr::parse_without_eager_brace(input)?;

    let content;
    let brace_token = braced!(content in input);

    let mut arms = Vec::new();
    let mut stmts = Vec::new();
    while !content.is_empty() {
        let (arm, stmt) = parse_arm(&content)?;
        arms.push(arm);
        stmts.push(stmt);
    }

    let span = match_token.span.join(brace_token.span).unwrap_or(match_token.span);

    Ok(TransitionStmt::Split(span, SplitKind::Match(expr, arms), stmts))
}

/// Parse an arm of a match statement. Based on `impl Parse for syn::Arm`
/// (but note that we return our own ast::Arm, not the syn::Arm)

fn parse_arm(input: ParseStream) -> syn::parse::Result<(Arm, TransitionStmt)> {
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
    let body = parse_transition_block(input)?;

    let requires_comma = false;
    let comma = {
        if requires_comma && !input.is_empty() { Some(input.parse()?) } else { input.parse()? }
    };

    let arm = Arm { pat, guard, fat_arrow_token, comma };
    Ok((arm, body))
}

// these are (private) functions from syn, used for parsing patterns in a `match` statement

fn multi_pat_with_leading_vert(input: ParseStream) -> syn::parse::Result<Pat> {
    let leading_vert: Option<Token![|]> = input.parse()?;
    multi_pat_impl(input, leading_vert)
}

fn multi_pat_impl(input: ParseStream, leading_vert: Option<Token![|]>) -> syn::parse::Result<Pat> {
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
        pat = Pat::Or(syn::PatOr { attrs: Vec::new(), leading_vert, cases });
    }
    Ok(pat)
}

/// Error if the user writes `if let ... = ... { ... }` which is unsupported.
/// Descend into the expression to check for chained if-let as well.
fn error_on_if_let(cond: &Expr) -> syn::parse::Result<()> {
    let mut ilv = IfLetVisitor { errors: Vec::new() };
    ilv.visit_expr(cond);
    combine_errors_or_ok(ilv.errors)
}

struct IfLetVisitor {
    pub errors: Vec<Error>,
}

impl<'ast> Visit<'ast> for IfLetVisitor {
    fn visit_expr_block(&mut self, _node: &'ast syn::ExprBlock) {
        // do nothing here; don't recurse into block expressions
    }

    fn visit_expr_let(&mut self, node: &'ast syn::ExprLet) {
        self.errors.push(Error::new(
            node.span(),
            "transition definitions do not support if-let conditionals",
        ));
    }
}
