use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use proc_macro2::TokenTree as TokenTree2;
use quote::ToTokens;
use verus_syn::parse::{Parse, ParseStream};
use verus_syn::{Error, Expr, ExprPath, Ident, Member, Pat, Token, Type};
use verus_syn::{parse_quote_spanned, parse2};

#[derive(Debug)]
struct Element {
    expr: Expr,
    typ: Option<Type>,
}

#[derive(Debug)]
enum Source {
    FiniteType,
    Set(Expr),
    Range { start: Expr, end: Expr, inclusive_end: bool },
}

#[derive(Debug)]
struct Decl {
    x: Ident,
    typ: Type,
    source: Source,
    is_exists: bool,
}

#[derive(Debug)]
enum DeclOrCond {
    Decl(Decl),
    Cond(Expr),
}

#[derive(Debug)]
struct SetBuild {
    element: Element,
    decls: Vec<Decl>,
    conds: Vec<Expr>,
}

impl Parse for Element {
    fn parse(input: ParseStream) -> Result<Self, Error> {
        let expr = Expr::parse(input)?;
        let typ = if input.peek(Token![:]) {
            let _ = input.parse::<Token![:]>()?;
            let typ = Type::parse(input)?;
            Some(typ)
        } else {
            None
        };
        Ok(Element { expr, typ })
    }
}

impl Parse for DeclOrCond {
    fn parse(input: ParseStream) -> Result<Self, Error> {
        let is_exists = if input.peek(Token![exists]) && input.peek3(Token![:]) {
            let _ = input.parse::<Token![exists]>();
            true
        } else {
            false
        };
        if input.peek2(Token![:]) {
            // x: typ in expr
            let x = Ident::parse(input)?;
            let _ = input.parse::<Token![:]>()?;
            let typ = Type::parse(input)?;
            let source = if input.peek(Token![in]) {
                let _ = input.parse::<Token![in]>()?;
                let expr = Expr::parse(input)?;
                match expr {
                    Expr::Range(range) => {
                        use verus_syn::RangeLimits;
                        use verus_syn::spanned::Spanned;
                        let inclusive_end = match &range.limits {
                            RangeLimits::HalfOpen(_) => false,
                            RangeLimits::Closed(_) => true,
                        };
                        let span = range.span();
                        let start = match range.start {
                            Some(start) => *start,
                            None => {
                                return Err(Error::new(span, "unexpected `..`"));
                            }
                        };
                        let end = match range.end {
                            Some(end) => *end,
                            None => {
                                return Err(Error::new(span, "missing expression after `..`"));
                            }
                        };
                        Source::Range { start, end, inclusive_end }
                    }
                    _ => Source::Set(expr),
                }
            } else {
                Source::FiniteType
            };
            let decl = Decl { x, typ, source, is_exists };
            Ok(DeclOrCond::Decl(decl))
        } else {
            let expr = Expr::parse(input)?;
            Ok(DeclOrCond::Cond(expr))
        }
    }
}

fn rewrite_expr_to_token_stream(expr: &Expr) -> TokenStream2 {
    use crate::cfg_erase;
    use crate::syntax::rewrite_expr;
    TokenStream2::from(rewrite_expr(cfg_erase(), true, expr.to_token_stream().into()))
}

fn parse_set_build(input: TokenStream2) -> Result<SetBuild, Error> {
    let mut trees: Vec<TokenTree2> = Vec::new();
    let mut element_trees: Option<Vec<TokenTree2>> = None;
    let mut decl_conds: Vec<Vec<TokenTree2>> = Vec::new();
    let mut found_bar = false;
    let mut found_comma = false;
    for tree in input.into_iter() {
        let span = tree.span().into();
        if let TokenTree2::Punct(punct) = &tree {
            if punct.as_char() == '|' {
                if trees.len() == 0 {
                    return Err(Error::new(span, "unexpected `|`"));
                }
                if found_bar {
                    return Err(Error::new(span, "only one `|` allowed"));
                }
                if found_comma {
                    return Err(Error::new(span, "`|` not allowed after `,`"));
                }
                found_bar = true;
                assert!(element_trees.is_none());
                element_trees = Some(trees);
                trees = Vec::new();
                continue;
            }
            if punct.as_char() == ',' {
                if trees.len() == 0 {
                    return Err(Error::new(span, "unexpected `,`"));
                }
                found_comma = true;
                decl_conds.push(trees);
                trees = Vec::new();
                continue;
            }
        }
        trees.push(tree);
    }
    if trees.len() > 0 {
        decl_conds.push(trees);
    }

    use std::iter::FromIterator;
    let mut decls: Vec<Decl> = Vec::new();
    let mut conds: Vec<Expr> = Vec::new();
    for decl_cond in decl_conds {
        let stream = TokenStream2::from_iter(decl_cond.into_iter());
        match parse2::<DeclOrCond>(stream)? {
            DeclOrCond::Decl(decl) => decls.push(decl),
            DeclOrCond::Cond(cond) => conds.push(cond),
        }
    }
    if decls.len() == 0 {
        let span = proc_macro2::Span::call_site();
        return Err(Error::new(span, "set must declare at least one variable using `x: type`"));
    }
    let element = if let Some(element_trees) = element_trees {
        let stream = TokenStream2::from_iter(element_trees.into_iter());
        parse2::<Element>(stream)?
    } else {
        // Omitted element means use "x" from the one and only decl as the element
        let (x, typ) = match &decls[..] {
            [decl] => (decl.x.clone(), Some(decl.typ.clone())),
            _ => {
                let span = proc_macro2::Span::call_site();
                return Err(Error::new(
                    span,
                    "when `|` is omitted, set must declare exactly one `x: type`",
                ));
            }
        };
        let expr = Expr::Path(ExprPath { attrs: vec![], qself: None, path: x.into() });
        Element { expr, typ }
    };
    Ok(SetBuild { element, decls, conds })
}

fn decl_to_expr(d: &Decl) -> Expr {
    let span = d.x.span();
    let typ = &d.typ;
    match &d.source {
        Source::FiniteType => {
            // TODO: add version of from_finite_type that takes no filter
            parse_quote_spanned_vstd!(vstd, span =>
                #vstd::set::Set::<#typ>::from_finite_type(|x: #typ| true)
            )
        }
        Source::Set(expr) => expr.clone(),
        Source::Range { start, end, inclusive_end } => {
            if *inclusive_end {
                parse_quote_spanned_vstd!(vstd, span => #vstd::set::Set::<#typ>::range_inclusive(#start, #end))
            } else {
                parse_quote_spanned_vstd!(vstd, span => #vstd::set::Set::<#typ>::range(#start, #end))
            }
        }
    }
}

fn conds_to_expr(conds: &Vec<Expr>) -> Expr {
    assert!(conds.len() != 0);
    let mut expr = conds[0].clone();
    for cond in conds.iter().skip(1) {
        use verus_syn::spanned::Spanned;
        let span = cond.span();
        expr = parse_quote_spanned!(span => (#expr) && (#cond));
    }
    expr
}

fn is_exactly_x(x: &Ident, e: &Expr) -> bool {
    match e {
        Expr::Paren(expr) => is_exactly_x(x, &*expr.expr),
        Expr::Path(path) if path.qself.is_none() && path.path.get_ident() == Some(x) => true,
        _ => false,
    }
}

// When we see f(args), we don't know whether this is a function call
// or a datatype construction.
// HACK: treat it as a datatype if it is capitalized.
fn is_probably_datatype_name(e: &Expr) -> bool {
    match e {
        Expr::Path(path) if path.qself.is_none() => {
            if let Some(x) = path.path.segments.last() {
                if let Some(c) = x.ident.to_string().chars().next() {
                    c.is_uppercase()
                } else {
                    false
                }
            } else {
                false
            }
        }
        _ => false,
    }
}

// Reverse computation from element back to x1, ..., xn
fn reverse_rec(build: &SetBuild, x: &Ident, e: &Expr) -> Option<Box<dyn Fn(Expr) -> Expr>> {
    use verus_syn::spanned::Spanned;
    let span = e.span();
    match e {
        Expr::Paren(expr) => reverse_rec(build, x, &*expr.expr),
        Expr::Path(path) if path.qself.is_none() && path.path.get_ident() == Some(x) => {
            Some(Box::new(|e| e))
        }
        Expr::Tuple(tuple) => {
            // Example: e = (D { d: x }, y)
            // for x, generate e.0.d
            for (n, e) in tuple.elems.iter().enumerate() {
                if let Some(f) = reverse_rec(build, x, e) {
                    // f = |e| e.d
                    // generate f(e.0) = e.0.d
                    let m: Member = n.into();
                    return Some(Box::new(move |e| f(parse_quote_spanned!(span => #e.#m))));
                }
            }
            None
        }
        Expr::Call(call) if is_probably_datatype_name(&call.func) => {
            for (n, e) in call.args.iter().enumerate() {
                if let Some(f) = reverse_rec(build, x, e) {
                    let m: Member = n.into();
                    return Some(Box::new(move |e| f(parse_quote_spanned!(span => #e.#m))));
                }
            }
            None
        }
        Expr::Struct(s) => {
            for field in &s.fields {
                if let Some(f) = reverse_rec(build, x, &field.expr) {
                    let m = field.member.clone();
                    return Some(Box::new(move |e| f(parse_quote_spanned!(span => #e.#m))));
                }
            }
            None
        }
        _ => None,
    }
}

fn reverse(build: &SetBuild, x: &Ident) -> Result<Expr, Error> {
    use verus_syn::spanned::Spanned;

    let span = build.element.expr.span();
    if let Some(f) = reverse_rec(build, x, &build.element.expr) {
        let elem_x = parse_quote_spanned!(span => __VERUS_x);
        let rev = f(elem_x);
        Ok(rev)
    } else {
        let msg = format!(
            "Could not find variable {x} in a field of the set element (the set element must construct a datatype containing each declared variable, or use `exists {x}:` instead of `{x}:`)"
        );
        Err(Error::new(span, msg))
    }
}

pub fn set_build_inner(input: TokenStream2, debug: bool) -> Result<TokenStream2, Error> {
    use verus_syn::spanned::Spanned;

    let set_build = parse_set_build(input)?;
    let element = &set_build.element.expr;
    let element_type = &set_build.element.typ;
    let decls = &set_build.decls;
    let conds = &set_build.conds;

    let expr = if decls.len() == 1 {
        // decls.len() == 1 is a special case for several reasons:
        // - we apply conditions before mapping
        // - we use map_by rather than map_flatten_by
        // - we omit mapping in the further special case that the element is exactly x
        // Example:
        // { (x, true) | x: int in s, x < 10 }
        // ==>
        // s.filter(|x: int| x < 10).map_by(|x: int| (x, true), |__VERUS_x| __VERUS_x.0)
        let decl = &decls[0];
        let x = &decl.x;
        let typ = &decl.typ;
        let mut expr = decl_to_expr(&decl);
        if conds.len() != 0 {
            let conds = conds_to_expr(&conds);
            let span = conds.span();
            expr = parse_quote_spanned!(span => #expr.filter(|#x: #typ| (#conds)));
        }
        if !is_exactly_x(x, element) {
            let span = element.span();
            if decl.is_exists {
                expr = parse_quote_spanned!(span =>
                    #expr.map(|#x: #typ| (#element))
                );
            } else {
                let rev = reverse(&set_build, x)?;
                if let Some(elem_typ) = element_type {
                    expr = parse_quote_spanned!(span =>
                        #expr.map_by(|#x: #typ| (#element), |__VERUS_x: #elem_typ| (#rev))
                    );
                } else {
                    expr = parse_quote_spanned!(span =>
                        #expr.map_by(|#x: #typ| (#element), |__VERUS_x| (#rev))
                    );
                }
            }
        }
        expr
    } else {
        assert!(decls.len() > 1);
        // Example: five declarations x0: ..., ..., x4: ...
        // Compute the set for x0
        // Use map_flatten_by to generate tuples (x0, x1)
        // Use map_flatten_by to generate tuples ((x0, x1), x2)
        // Use map_flatten_by to generate tuples (((x0, x1), x2), x3)
        // Use map_flatten_by to generate the final elements as a function of x0...x4
        // If there are any conditions, add a single filter with all conditions
        let elem_span = element.span();
        let span = decls[0].x.span();
        let x = &decls[0].x;
        let mut expr = decl_to_expr(&decls[0]);
        let mut typs = decls[0].typ.clone();
        let mut xtuple: Pat = parse_quote_spanned!(span => #x);
        let mut revs = if decls[0].is_exists { None } else { Some(reverse(&set_build, x)?) };
        for (n, decl) in decls.iter().enumerate().skip(1) {
            assert!(0 < n && n < decls.len());
            let span = decl.x.span();
            // typs == (...(typ0 ...), typ_n-1)
            // xtuple == (...(x0 ...), x_n-1)
            // revs == (...(rev_x0(VERUS_x) ...), rev_x_n-1(VERUS_x))
            // next_typs = ((...(typ0 ...), typ_n-1), typ_n)
            // next_xtuple = ((...(x0 ...), x_n-1), x_n)
            // revs == ((...(rev_x0(VERUS_x) ...), rev_x_n-1(VERUS_x)), rev_x_n(VERUS_x))
            let x = &decl.x;
            let typ = &decl.typ;
            let rev = if decl.is_exists { None } else { Some(reverse(&set_build, x)?) };
            let next_typs = parse_quote_spanned!(span => (#typs, #typ));
            let next_xtuple = parse_quote_spanned!(span => (#xtuple, #x));
            let next_revs = if let (Some(revs), Some(rev)) = (&revs, &rev) {
                Some(parse_quote_spanned!(span => (#revs, (#rev))))
            } else {
                None
            };

            let mut source = decl_to_expr(&decl);
            if n < decls.len() - 1 {
                // Example: n = 2
                // use map_flatten_by to generate tuples ((x0, x1), x2)
                // expr.map_flatten_by(
                //     |VERUS_x: (typ0, typ1)| {
                //         let (x0, x1) = VERUS_x;
                //         source2.map_by(
                //             |x2: typ2| (VERUS_x, x2),
                //             |xs: ((typ0, typ1), typ2)| xs.1,
                //         )
                //     }
                //     |xs: ((typ0, typ1), typ2)| xs.0,
                // )
                let f_fwd: Expr = parse_quote_spanned!(span => |#x: #typ| (__VERUS_x, #x));
                let f_rev: Expr = parse_quote_spanned!(span => |xs: #next_typs| xs.1);
                let body: Expr = parse_quote_spanned!(span => {
                    let #xtuple = __VERUS_x;
                    #source.map_by(#f_fwd, #f_rev)
                });
                let g_fwd: Expr = parse_quote_spanned!(span => |__VERUS_x: #typs| #body);
                let g_rev: Expr = parse_quote_spanned!(span => |xs: #next_typs| xs.0);
                expr = parse_quote_spanned!(span => #expr.map_flatten_by(#g_fwd, #g_rev));
            } else {
                // Example: n = 4
                // expr.map_flatten_by(
                //     |VERUS_x: (((typ0, typ1), typ2), typ3)| {
                //         let (((x0, x1), x2), x3) = VERUS_x;
                //         source4
                //             .filter(
                //                 |x4: typ4| conds,
                //             )
                //             .map_by(
                //                 |x4: typ4| element,
                //                 |VERUS_x: elem_typ| rev_x4(VERUS_x),
                //             )
                //     }
                //     |VERUS_x: elem_typ| (((rev_x0(VERUS_x), ...), rev_x3(VERUS_x)),
                // )
                if conds.len() != 0 {
                    let conds = conds_to_expr(&conds);
                    source = parse_quote_spanned!(span => #source.filter(|#x: #typ| (#conds)));
                }
                // Note:
                // the last x (x4) can be "exists" independently
                // the others (x0..x3) are all "exists" if any of them are "exists"
                let f_fwd: Expr = parse_quote_spanned!(span => |#x: #typ| (#element));
                let body: Expr = if let Some(rev) = rev {
                    let f_rev: Expr = if let Some(elem_typ) = element_type {
                        parse_quote_spanned!(elem_span => |__VERUS_x: #elem_typ| (#rev))
                    } else {
                        parse_quote_spanned!(elem_span => |__VERUS_x| (#rev))
                    };
                    parse_quote_spanned!(span => {
                        let #xtuple = __VERUS_x;
                        #source.map_by(#f_fwd, #f_rev)
                    })
                } else {
                    parse_quote_spanned!(span => {
                        let #xtuple = __VERUS_x;
                        #source.map(#f_fwd)
                    })
                };
                let g_fwd: Expr = parse_quote_spanned!(span => |__VERUS_x: #typs| #body);
                if let Some(revs) = revs {
                    let g_rev: Expr = if let Some(elem_typ) = element_type {
                        parse_quote_spanned!(elem_span => |__VERUS_x: #elem_typ| #revs)
                    } else {
                        parse_quote_spanned!(elem_span => |__VERUS_x| #revs)
                    };
                    expr = parse_quote_spanned!(span => #expr.map_flatten_by(#g_fwd, #g_rev));
                } else {
                    // TODO: add map_flatten to set_lib
                    //expr = parse_quote_spanned!(span => #expr.map_flatten(#g_fwd));
                    expr = parse_quote_spanned!(span => #expr.map(#g_fwd).flatten());
                }
            }
            typs = next_typs;
            xtuple = next_xtuple;
            revs = next_revs;
        }
        expr
    };

    if debug {
        let set = verus_prettyplease::unparse_expr(&expr);
        let set = set.replace("::vstd::set::Set", "Set");
        let span = proc_macro2::Span::call_site();
        eprintln!();
        eprintln!("printing set_build result for {} {:?}", span.file(), span.start());
        if let Some(source) = span.source_text() {
            eprintln!("{}", source);
        }
        eprintln!("-->");
        eprintln!("{}", set);
        eprintln!();
    }

    Ok(rewrite_expr_to_token_stream(&expr))
}

pub fn set_build(input: TokenStream, debug: bool) -> TokenStream {
    match set_build_inner(TokenStream2::from(input), debug) {
        Ok(tokens) => tokens.to_token_stream().into(),
        Err(err) => err.into_compile_error().into(),
    }
}
