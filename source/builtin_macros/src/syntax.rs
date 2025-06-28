use crate::EraseGhost;
use crate::rustdoc::env_rustdoc;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use proc_macro2::TokenTree;
use quote::ToTokens;
use quote::format_ident;
use quote::{quote, quote_spanned};
use syn_verus::BroadcastUse;
use syn_verus::ExprBlock;
use syn_verus::ExprForLoop;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::parse_quote_spanned;
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::token;
use syn_verus::token::{Brace, Bracket, Paren, Semi};
use syn_verus::visit_mut::{
    VisitMut, visit_block_mut, visit_expr_loop_mut, visit_expr_mut, visit_expr_while_mut,
    visit_field_mut, visit_impl_item_const_mut, visit_impl_item_fn_mut, visit_item_const_mut,
    visit_item_enum_mut, visit_item_fn_mut, visit_item_static_mut, visit_item_struct_mut,
    visit_item_union_mut, visit_local_mut, visit_specification_mut, visit_trait_item_fn_mut,
};
use syn_verus::{
    AssumeSpecification, Attribute, BareFnArg, BinOp, Block, DataMode, Decreases, Ensures, Expr,
    ExprBinary, ExprCall, ExprLit, ExprLoop, ExprMatches, ExprTuple, ExprUnary, ExprWhile, Field,
    FnArg, FnArgKind, FnMode, Global, Ident, ImplItem, ImplItemFn, Invariant, InvariantEnsures,
    InvariantExceptBreak, InvariantNameSet, InvariantNameSetList, InvariantNameSetSet, Item,
    ItemBroadcastGroup, ItemConst, ItemEnum, ItemFn, ItemImpl, ItemMod, ItemStatic, ItemStruct,
    ItemTrait, ItemUnion, Lit, Local, MatchesOpExpr, MatchesOpToken, ModeSpec, ModeSpecChecked,
    Pat, PatIdent, PatType, Path, Publish, Recommends, Requires, ReturnType, Returns, Signature,
    SignatureDecreases, SignatureInvariants, SignatureSpec, SignatureSpecAttr, SignatureUnwind,
    Stmt, Token, TraitItem, TraitItemFn, Type, TypeFnProof, TypeFnSpec, TypePath, UnOp, Visibility,
    braced, bracketed, parenthesized, parse_macro_input,
};

const VERUS_SPEC: &str = "VERUS_SPEC__";

fn take_expr(expr: &mut Expr) -> Expr {
    let dummy: Expr = Expr::Verbatim(TokenStream::new());
    std::mem::replace(expr, dummy)
}

fn take_type(expr: &mut Type) -> Type {
    let dummy: Type = Type::Verbatim(TokenStream::new());
    std::mem::replace(expr, dummy)
}

fn take_pat(pat: &mut Pat) -> Pat {
    let dummy: Pat = Pat::Verbatim(TokenStream::new());
    std::mem::replace(pat, dummy)
}

fn take_ghost<T: Default>(erase_ghost: EraseGhost, dest: &mut T) -> T {
    if erase_ghost.erase() {
        *dest = T::default();
        T::default()
    } else {
        std::mem::take(dest)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InsideArith {
    None,
    Widen,
    Fixed,
}

struct Visitor {
    erase_ghost: EraseGhost,
    // TODO: this should always be true
    use_spec_traits: bool,
    // inside_ghost > 0 means we're currently visiting ghost code
    inside_ghost: u32,
    // inside_type > 0 means we're currently visiting a type
    inside_type: u32,
    // inside_external_code > 0 means we're currently visiting an external or external_body body
    inside_external_code: u32,
    // visiting a constant, for which we have to translate ghost code even when erasing
    inside_const: bool,
    // Widen means we're a direct subexpression in an arithmetic expression that will widen the result.
    // (e.g. "x" or "3" in x + 3 or in x < (3), but not in f(x) + g(3)).
    // When we see a constant in inside_arith, we preemptively give it type "int" rather than
    // asking Rust to infer an integer type, since the inference would usually fail.
    // We also use Widen inside "... as typ".
    // It is inherited through parentheses, if/else, match, and blocks.
    // Fixed is used for bitwise operations, where we use Rust's native integer literals
    // rather than an int literal.
    inside_arith: InsideArith,
    // assign_to == true means we're an expression being assigned to by Assign
    assign_to: bool,

    // Add extra verus signature information to the docstring
    rustdoc: bool,
}

// For exec "let pat = init" declarations, recursively find Tracked(x), Ghost(x), x in pat
struct ExecGhostPatVisitor {
    inside_ghost: u32,
    tracked: Option<Token![tracked]>,
    ghost: Option<Token![ghost]>,
    x_decls: Vec<Stmt>,
    x_assigns: Vec<Stmt>,
}

fn data_mode_attrs(mode: &DataMode) -> Vec<Attribute> {
    match mode {
        DataMode::Default => vec![],
        DataMode::Ghost(token) => {
            vec![mk_verus_attr(token.ghost_token.span, quote! { spec })]
        }
        DataMode::Tracked(token) => {
            vec![mk_verus_attr(token.tracked_token.span, quote! { proof })]
        }
        DataMode::Exec(token) => {
            vec![mk_verus_attr(token.exec_token.span, quote! { exec })]
        }
    }
}

fn path_is_ident(path: &Path, s: &str) -> bool {
    let segments = &path.segments;
    segments.len() == 1 && segments.first().unwrap().ident.to_string() == s
}

pub(crate) fn into_spans(span: Span) -> proc_macro2::extra::DelimSpan {
    let mut group = proc_macro2::Group::new(proc_macro2::Delimiter::None, TokenStream::new());
    group.set_span(span);
    group.delim_span()
}

macro_rules! stmt_with_semi {
    ($b:ident, $span:expr => $($tok:tt)*) => {
        {
            let sp = $span;
            let $b = crate::syntax::Builtin(sp);
            stmt_with_semi!{ sp => $($tok)* }
        }
    };
    ($span:expr => $($tok:tt)*) => {
        Stmt::Expr(
            Expr::Verbatim(quote_spanned!{ $span => $($tok)* }),
            Some(Semi { spans: [ $span ] }),
        )
    };
}

macro_rules! quote_verbatim {
    ($b: ident, $span:expr, $attrs:tt => $($tok:tt)*) => {
        {
            let sp = $span;
            let $b = crate::syntax::Builtin(sp);
            quote_verbatim!{ $span, $attrs => $($tok)* }
        }
    };
    ($span:expr, $attrs:tt => $($tok:tt)*) => {
        Expr::Verbatim(quote_spanned!{ $span => #(#$attrs)* $($tok)* })
    }
}

macro_rules! quote_spanned_builtin {
    ($b:ident, $span:expr => $($tt:tt)*) => {
        {
            let sp = $span;
            let $b = crate::syntax::Builtin(sp);
            ::quote::quote_spanned!{ sp => $($tt)* }
        }
    }
}

macro_rules! quote_spanned_builtin_vstd {
    ($b:ident, $v:ident, $span:expr => $($tt:tt)*) => {
        {
            let sp = $span;
            let $b = crate::syntax::Builtin(sp);
            let $v = crate::syntax::Vstd(sp);
            ::quote::quote_spanned!{ sp => $($tt)* }
        }
    }
}

macro_rules! quote_vstd {
    ($b:ident => $($tt:tt)*) => {
        {
            let sp = ::proc_macro2::Span::call_site();
            let $b = crate::syntax::Vstd(sp);
            ::quote::quote!{ $($tt)* }
        }
    }
}

macro_rules! quote_builtin {
    ($b:ident => $($tt:tt)*) => {
        {
            let sp = ::proc_macro2::Span::call_site();
            let $b = crate::syntax::Builtin(sp);
            ::quote::quote!{ $($tt)* }
        }
    }
}

macro_rules! quote_spanned_vstd {
    ($b:ident, $span:expr => $($tt:tt)*) => {
        {
            let sp = $span;
            let $b = crate::syntax::Vstd(sp);
            ::quote::quote_spanned!{ sp => $($tt)* }
        }
    }
}

macro_rules! parse_quote_spanned_vstd {
    ($b:ident, $span:expr => $($tt:tt)*) => {
        {
            let sp = $span;
            let $b = crate::syntax::Vstd(sp);
            ::syn_verus::parse_quote_spanned!{ sp => $($tt)* }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ProofFnUsage {
    FnOnce,
    FnMut,
    Fn,
}

impl Default for ProofFnUsage {
    fn default() -> Self {
        ProofFnUsage::Fn
    }
}

#[derive(Default)]
struct ProofFnOptions {
    usage: ProofFnUsage,
    req_ens: Option<Type>,
    copy: bool,
    send: bool,
    sync: bool,
}

enum ProofFnTypeArg {
    Usage(ProofFnUsage),
    ReqEns(Option<Type>),
    Copy,
    Send,
    Sync,
    Tracked,
    Ghost,
    Zero,
}

const PROOF_FN_ONCE: u8 = 1;
const PROOF_FN_MUT: u8 = 2;
const PROOF_FN: u8 = 3;
const PROOF_FN_COPY: u8 = 4;
const PROOF_FN_SEND: u8 = 5;
const PROOF_FN_SYNC: u8 = 6;

impl ProofFnTypeArg {
    fn to_type(&self, span: Span) -> Type {
        let (s, n) = match self {
            ProofFnTypeArg::Usage(ProofFnUsage::FnOnce) => (None, Some(PROOF_FN_ONCE)),
            ProofFnTypeArg::Usage(ProofFnUsage::FnMut) => (None, Some(PROOF_FN_MUT)),
            ProofFnTypeArg::Usage(ProofFnUsage::Fn) => (None, Some(PROOF_FN)),
            ProofFnTypeArg::ReqEns(Some(_)) => (Some("RqEn".to_string()), None),
            ProofFnTypeArg::ReqEns(None) => (None, None),
            ProofFnTypeArg::Copy => (None, Some(PROOF_FN_COPY)),
            ProofFnTypeArg::Send => (None, Some(PROOF_FN_SEND)),
            ProofFnTypeArg::Sync => (None, Some(PROOF_FN_SYNC)),
            ProofFnTypeArg::Tracked => (Some("Trk".to_string()), None),
            ProofFnTypeArg::Ghost => (None, None),
            ProofFnTypeArg::Zero => (None, Some(0)),
        };
        let s = s.map(|s| format_ident!("{}", s));
        let stream = match (self, s, n) {
            (ProofFnTypeArg::ReqEns(t), Some(s), None) => {
                quote_spanned_builtin!(builtin, span => #builtin::#s<#t>)
            }
            (_, Some(s), _) => {
                quote_spanned_builtin!(builtin, span => #builtin::#s)
            }
            (_, _, Some(n)) => {
                quote_spanned!(span => #n)
            }
            (_, None, None) => {
                quote_spanned!(span => ())
            }
        };
        Type::Verbatim(stream)
    }
}

impl ProofFnOptions {
    fn parse<'a>(iter: impl Iterator<Item = &'a syn_verus::PathSegment>) -> Result<Self, String> {
        let mut options = ProofFnOptions::default();
        for path in iter {
            use syn_verus::{GenericArgument, PathArguments};
            match (path.ident.to_string().as_str(), &path.arguments) {
                ("Once", PathArguments::None) if options.usage == ProofFnUsage::Fn => {
                    options.usage = ProofFnUsage::FnOnce;
                }
                ("Mut", PathArguments::None) if options.usage == ProofFnUsage::Fn => {
                    options.usage = ProofFnUsage::FnMut;
                }
                ("ReqEns", PathArguments::AngleBracketed(args))
                    if options.req_ens.is_none()
                        && args.colon2_token.is_none()
                        && args.args.len() == 1
                        && matches!(args.args[0], GenericArgument::Type(_)) =>
                {
                    match &args.args[0] {
                        GenericArgument::Type(t) => options.req_ens = Some(t.clone()),
                        _ => unreachable!(),
                    }
                }
                ("Copy", PathArguments::None) if !options.copy => options.copy = true,
                ("Send", PathArguments::None) if !options.send => options.send = true,
                ("Sync", PathArguments::None) if !options.sync => options.sync = true,
                _ => {
                    return Err(format!("unexpected option {}", path.ident.to_string()));
                }
            }
        }
        Ok(options)
    }

    fn parse_opt(opt: &Option<syn_verus::FnProofOptions>) -> Result<Self, String> {
        if let Some(opt) = opt {
            Self::parse(opt.options.iter())
        } else {
            Ok(ProofFnOptions::default())
        }
    }

    fn to_types(&self, span: Span) -> (Type, Type, Type, Type, Type) {
        let usage = ProofFnTypeArg::Usage(self.usage).to_type(span);
        let req_ens = match &self.req_ens {
            None => ProofFnTypeArg::ReqEns(None).to_type(span),
            Some(t) => ProofFnTypeArg::ReqEns(Some(t.clone())).to_type(span),
        };
        let f = |b: bool, arg: ProofFnTypeArg| {
            (if b { arg } else { ProofFnTypeArg::Zero }).to_type(span)
        };
        let copy = f(self.copy, ProofFnTypeArg::Copy);
        let send = f(self.send, ProofFnTypeArg::Send);
        let sync = f(self.sync, ProofFnTypeArg::Sync);
        (usage, req_ens, copy, send, sync)
    }
}

fn proof_fn_track_to_type(span: Span, is_tracked: bool) -> Type {
    let arg = if is_tracked { ProofFnTypeArg::Tracked } else { ProofFnTypeArg::Ghost };
    arg.to_type(span)
}

fn proof_fn_tracks_to_type(span: Span, tracks: impl Iterator<Item = bool>) -> Type {
    // build a tuple type (t1, ..., tn)
    // where each tk is Trk or ()
    let mut elems = Punctuated::new();
    for tracked in tracks {
        elems.push(proof_fn_track_to_type(span, tracked));
    }
    let paren_token = Paren { span: into_spans(span) };
    Type::Tuple(syn_verus::TypeTuple { paren_token, elems })
}

pub(crate) fn rewrite_exe_pat(pat: &mut Pat) -> (Vec<Stmt>, Vec<Stmt>) {
    let mut visit_pat = ExecGhostPatVisitor {
        inside_ghost: 0,
        tracked: None,
        ghost: None,
        x_decls: Vec::new(),
        x_assigns: Vec::new(),
    };

    visit_pat.visit_pat_mut(pat);
    let ExecGhostPatVisitor { x_decls, x_assigns, .. } = visit_pat;
    return (x_decls, x_assigns);
}

fn rewrite_args_unwrap_ghost_tracked(erase_ghost: &EraseGhost, arg: &mut FnArg) -> Vec<Stmt> {
    // Check for Ghost(x) or Tracked(x) argument
    let mut unwrap_ghost_tracked = Vec::new();
    if let FnArgKind::Typed(PatType { pat, .. }) = &mut arg.kind {
        let pat = &mut **pat;
        let mut tracked_wrapper = false;
        let mut wrapped_pat_id = None;
        if let Pat::TupleStruct(tup) = &*pat {
            let ghost_wrapper = path_is_ident(&tup.path, "Ghost");
            tracked_wrapper = path_is_ident(&tup.path, "Tracked");
            if ghost_wrapper || tracked_wrapper || tup.elems.len() == 1 {
                if let Pat::Ident(id) = &tup.elems[0] {
                    wrapped_pat_id = Some(id.clone());
                }
            }
        }
        if let Some(mut wrapped_pat_id) = wrapped_pat_id {
            // Change
            //   fn f(x: Tracked<T>) {
            // to
            //   fn f(verus_tmp_x: Tracked<T>) {
            //       #[verus::internal(header_unwrap_parameter)] let t;
            //       #[verifier::proof_block] { t = verus_tmp_x.get() };
            let span = pat.span();
            let x = wrapped_pat_id.ident;
            let tmp_id =
                Ident::new(&format!("verus_tmp_{x}"), Span::mixed_site().located_at(pat.span()));
            wrapped_pat_id.ident = tmp_id.clone();
            *pat = Pat::Ident(wrapped_pat_id);
            if erase_ghost.keep() {
                unwrap_ghost_tracked.push(stmt_with_semi!(
                    span => #[verus::internal(header_unwrap_parameter)] let #x));
                if tracked_wrapper {
                    unwrap_ghost_tracked.push(stmt_with_semi!(
                        span => #[verifier::proof_block] { #x = #tmp_id.get() }));
                } else {
                    unwrap_ghost_tracked.push(stmt_with_semi!(
                        span => #[verifier::proof_block] { #x = #tmp_id.view() }));
                }
            }
        }
    }
    unwrap_ghost_tracked
}

impl Visitor {
    fn take_ghost<T: Default>(&self, dest: &mut T) -> T {
        take_ghost(self.erase_ghost, dest)
    }

    fn maybe_erase_expr(&self, span: Span, e: Expr) -> Expr {
        if self.erase_ghost.erase() { Expr::Verbatim(quote_spanned!(span => {})) } else { e }
    }

    fn filter_attrs(&mut self, attrs: &mut Vec<Attribute>) {
        if self.erase_ghost.erase_all() {
            // Remove verus:: and verifier:: attributes to make it easier for
            // standard rustc to compile the code
            attrs.retain(|attr| {
                let prefix = attr.path().segments[0].ident.to_string();
                prefix != "verus" && prefix != "verifier"
            });
        }
    }

    fn visit_loop_spec(&mut self, spec: &mut syn_verus::LoopSpec) {
        let mut visit_spec = |exprs: &mut syn_verus::Specification| {
            for expr in exprs.exprs.iter_mut() {
                self.visit_expr_mut(expr);
            }
        };
        if let Some(exprs) = spec.invariants.as_mut() {
            visit_spec(&mut exprs.exprs);
        }
        if let Some(exprs) = spec.invariant_except_breaks.as_mut() {
            visit_spec(&mut exprs.exprs);
        }
        if let Some(exprs) = spec.ensures.as_mut() {
            visit_spec(&mut exprs.exprs);
        }
        if let Some(exprs) = spec.decreases.as_mut() {
            visit_spec(&mut exprs.exprs);
        }
    }

    fn take_sig_specs<TType: ToTokens>(
        &mut self,
        spec: &mut SignatureSpec,
        ret_pat: Option<(Pat, TType)>,
        final_ret_pat: Option<Pat>, // Some(pat) if different from ret_pat,
        is_const: bool,
        span: Span,
    ) -> Vec<Stmt> {
        let requires = self.take_ghost(&mut spec.requires);
        let recommends = self.take_ghost(&mut spec.recommends);
        let ensures = self.take_ghost(&mut spec.ensures);
        let returns = self.take_ghost(&mut spec.returns);
        let decreases = self.take_ghost(&mut spec.decreases);
        let opens_invariants = self.take_ghost(&mut spec.invariants);
        let unwind = self.take_ghost(&mut spec.unwind);

        let mut spec_stmts = Vec::new();
        // TODO: wrap specs inside ghost blocks
        if let Some(Requires { token, mut exprs }) = requires {
            if exprs.exprs.len() > 0 {
                for expr in exprs.exprs.iter_mut() {
                    self.visit_expr_mut(expr);
                }
                spec_stmts.push(Stmt::Expr(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, token.span => #builtin::requires([#exprs])),
                    ),
                    Some(Semi { spans: [token.span] }),
                ));
            }
        }
        if let Some(Recommends { token, mut exprs, via }) = recommends {
            if exprs.exprs.len() > 0 {
                for expr in exprs.exprs.iter_mut() {
                    self.visit_expr_mut(expr);
                }
                spec_stmts.push(Stmt::Expr(
                    Expr::Verbatim(quote_spanned_builtin!(builtin, token.span => #builtin::recommends([#exprs]))),
                    Some(Semi { spans: [token.span] }),
                ));
            }
            if let Some((via_token, via_expr)) = via {
                spec_stmts.push(Stmt::Expr(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, via_expr.span() => #builtin::recommends_by(#via_expr)),
                    ),
                    Some(Semi { spans: [via_token.span] }),
                ));
            }
        }
        if let Some(Ensures { attrs, token, mut exprs }) = ensures {
            if exprs.exprs.len() > 0 {
                for expr in exprs.exprs.iter_mut() {
                    self.visit_expr_mut(expr);
                }
                let cont = match self.extract_quant_triggers(attrs, token.span) {
                    Ok(
                        found @ (ExtractQuantTriggersFound::Auto
                        | ExtractQuantTriggersFound::AllTriggers
                        | ExtractQuantTriggersFound::Triggers(..)),
                    ) => {
                        if exprs.exprs.len() == 0 {
                            let err =
                                "when using #![trigger f(x)], at least one ensures is required";
                            let expr =
                                Expr::Verbatim(quote_spanned!(token.span => compile_error!(#err)));
                            spec_stmts.push(Stmt::Expr(expr, Some(Semi { spans: [token.span] })));
                            false
                        } else {
                            let span = exprs.exprs[0].span();
                            let e = take_expr(&mut exprs.exprs[0]);
                            match found {
                                ExtractQuantTriggersFound::Auto => {
                                    exprs.exprs[0] = Expr::Verbatim(
                                        quote_spanned!(span => #[verus::internal(auto_trigger)] (#e)),
                                    );
                                }
                                ExtractQuantTriggersFound::AllTriggers => {
                                    exprs.exprs[0] = Expr::Verbatim(
                                        quote_spanned!(span => #[verus::internal(all_triggers)] (#e)),
                                    );
                                }
                                ExtractQuantTriggersFound::Triggers(tuple) => {
                                    exprs.exprs[0] = Expr::Verbatim(
                                        quote_spanned_builtin!(builtin, span => #builtin::with_triggers(#tuple, #e)),
                                    );
                                }
                                ExtractQuantTriggersFound::None => unreachable!(),
                            }
                            true
                        }
                    }
                    Ok(ExtractQuantTriggersFound::None) => true,
                    Err(err_expr) => {
                        exprs.exprs[0] = err_expr;
                        false
                    }
                };
                if cont {
                    if let Some((p, ty)) = ret_pat {
                        if let Some(final_ret_pat) = final_ret_pat {
                            for expr in exprs.exprs.iter_mut() {
                                *expr = Expr::Verbatim(
                                    quote_spanned! {token.span => {let #final_ret_pat = #p; #expr}},
                                )
                            }
                        }
                        spec_stmts.push(Stmt::Expr(
                            Expr::Verbatim(
                                quote_spanned_builtin!(builtin, token.span => #builtin::ensures(|#p: #ty| [#exprs])),
                            ),
                            Some(Semi { spans: [token.span] }),
                        ));
                    } else {
                        spec_stmts.push(Stmt::Expr(
                            Expr::Verbatim(
                                quote_spanned_builtin!(builtin, token.span => #builtin::ensures([#exprs])),
                            ),
                            Some(Semi { spans: [token.span] }),
                        ));
                    }
                }
            }
        }
        if let Some(Returns { token, mut exprs }) = returns {
            if exprs.exprs.len() > 0 {
                for expr in exprs.exprs.iter_mut() {
                    self.visit_expr_mut(expr);
                }
                spec_stmts.push(Stmt::Expr(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, token.span => #builtin::returns([#exprs])),
                    ),
                    Some(Semi { spans: [token.span] }),
                ));
            }
        }
        if let Some(SignatureDecreases { decreases: Decreases { token, mut exprs }, when, via }) =
            decreases
        {
            for expr in exprs.exprs.iter_mut() {
                self.visit_expr_mut(expr);
                if matches!(expr, Expr::Tuple(..)) {
                    let err = "decreases cannot be a tuple; use `decreases x, y` rather than `decreases (x, y)`";
                    let expr = Expr::Verbatim(quote_spanned!(token.span => compile_error!(#err)));
                    spec_stmts.push(Stmt::Expr(expr, Some(Semi { spans: [token.span] })));
                }
            }
            spec_stmts.push(Stmt::Expr(
                Expr::Verbatim(
                    quote_spanned_builtin!(builtin, token.span => #builtin::decreases((#exprs))),
                ),
                Some(Semi { spans: [token.span] }),
            ));
            if let Some((when_token, mut when_expr)) = when {
                self.visit_expr_mut(&mut when_expr);
                spec_stmts.push(Stmt::Expr(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, when_expr.span() => #builtin::decreases_when(#when_expr)),
                    ),
                    Some(Semi { spans: [when_token.span] }),
                ));
            }
            if let Some((via_token, via_expr)) = via {
                spec_stmts.push(Stmt::Expr(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, via_expr.span() => #builtin::decreases_by(#via_expr)),
                    ),
                    Some(Semi { spans: [via_token.span] }),
                ));
            }
        }
        if let Some(SignatureInvariants { token: _, set }) = opens_invariants {
            match set {
                InvariantNameSet::Any(any) => {
                    spec_stmts.push(Stmt::Expr(
                        Expr::Verbatim(
                            quote_spanned_builtin!(builtin, any.span() => #builtin::opens_invariants_any()),
                        ),
                        Some(Semi { spans: [any.span()] }),
                    ));
                }
                InvariantNameSet::None(none) => {
                    spec_stmts.push(Stmt::Expr(
                        Expr::Verbatim(
                            quote_spanned_builtin!(builtin, none.span() => #builtin::opens_invariants_none()),
                        ),
                        Some(Semi { spans: [none.span()] }),
                    ));
                }
                InvariantNameSet::List(InvariantNameSetList { bracket_token, mut exprs }) => {
                    for expr in exprs.iter_mut() {
                        self.visit_expr_mut(expr);
                    }
                    spec_stmts.push(Stmt::Expr(
                        Expr::Verbatim(
                            quote_spanned_builtin!(builtin, bracket_token.span.join() => #builtin::opens_invariants([#exprs])),
                        ),
                        Some(Semi { spans: [bracket_token.span.close()] }),
                    ));
                }
                InvariantNameSet::Set(InvariantNameSetSet { mut expr }) => {
                    self.visit_expr_mut(&mut expr);
                    spec_stmts.push(Stmt::Expr(
                        Expr::Verbatim(
                            quote_spanned_builtin!(builtin, expr.span() => #builtin::opens_invariants_set(#expr)),
                        ),
                        Some(Semi { spans: [expr.span()] }),
                    ));
                }
            }
        }

        if let Some(SignatureUnwind { token, when }) = unwind {
            if let Some((when_token, mut when_expr)) = when {
                self.visit_expr_mut(&mut when_expr);
                spec_stmts.push(Stmt::Expr(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, when_expr.span() => #builtin::no_unwind_when(#when_expr)),
                    ),
                    Some(Semi { spans: [when_token.span] }),
                ));
            } else {
                spec_stmts.push(Stmt::Expr(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, token.span() => #builtin::no_unwind()),
                    ),
                    Some(Semi { spans: [token.span] }),
                ));
            }
        }

        if is_const {
            vec![Stmt::Expr(
                Expr::Verbatim(
                    quote_spanned!(span => #[verus::internal(const_header_wrapper)] || { #(#spec_stmts)* };),
                ),
                None,
            )]
        } else {
            spec_stmts
        }
    }

    fn visit_fn(
        &mut self,
        attrs: &mut Vec<Attribute>,
        vis: Option<&Visibility>,
        sig: &mut Signature,
        semi_token: Option<Token![;]>,
        is_trait: bool,
    ) -> Vec<Stmt> {
        let mut stmts: Vec<Stmt> = Vec::new();
        let mut unwrap_ghost_tracked: Vec<Stmt> = Vec::new();

        let has_body = semi_token.is_none();

        // attrs.push(mk_verus_attr(sig.fn_token.span, quote! { verus_macro }));
        if self.erase_ghost.keep() {
            attrs.push(mk_verus_attr(sig.fn_token.span, quote! { verus_macro }));
        }

        for arg in &mut sig.inputs {
            match (arg.tracked, &mut arg.kind) {
                _ if self.erase_ghost.erase_all() => {}
                (None, _) => {}
                (Some(token), FnArgKind::Receiver(receiver)) => {
                    receiver.attrs.push(mk_verus_attr(token.span, quote! { proof }));
                }
                (Some(token), FnArgKind::Typed(typed)) => {
                    typed.attrs.push(mk_verus_attr(token.span, quote! { proof }));
                }
            }

            // Check for Ghost(x) or Tracked(x) argument
            unwrap_ghost_tracked.extend(rewrite_args_unwrap_ghost_tracked(&self.erase_ghost, arg));

            arg.tracked = None;
        }
        let ret_pat = match &mut sig.output {
            ReturnType::Default => None,
            ReturnType::Type(_, ref mut tracked, ref mut ret_opt, ty) => {
                self.visit_type_mut(ty);
                if let Some(token) = tracked {
                    if !self.erase_ghost.erase_all() {
                        attrs.push(mk_verus_attr(token.span, quote! { returns(proof) }));
                    }
                    *tracked = None;
                }
                match std::mem::take(ret_opt) {
                    None => None,
                    Some(ret) => Some((ret.1.clone(), ty.clone())),
                }
            }
        };

        match (vis, &sig.publish, &sig.mode, &semi_token, self.erase_ghost.erase()) {
            (Some(Visibility::Inherited), _, _, _, _) => {}
            (
                Some(_),
                Publish::Default,
                FnMode::Spec(ModeSpec { spec_token })
                | FnMode::SpecChecked(ModeSpecChecked { spec_token, .. }),
                None,
                false,
            ) => {
                stmts.push(stmt_with_semi!(
                    spec_token.span =>
                    compile_error!("non-private spec function must be marked open or closed to indicate whether the function body is public (pub open) or private (pub closed)")
                ));
            }
            _ => {}
        }

        if matches!(
            sig.mode,
            FnMode::Default | FnMode::Exec(_) | FnMode::Proof(_) | FnMode::ProofAxiom(_)
        ) && !matches!(sig.publish, Publish::Default)
        {
            let publish_span = sig.publish.span();
            stmts.push(stmt_with_semi!(
                publish_span =>
                compile_error!("only `spec` functions can be marked `open`, `closed`, or `uninterp`")
            ));
        }

        if sig.broadcast.is_some() && !matches!(sig.mode, FnMode::Proof(_) | FnMode::ProofAxiom(_))
        {
            let broadcast_span = sig.broadcast.span();
            stmts.push(stmt_with_semi!(
                broadcast_span =>
                compile_error!("only `proof` functions can be marked `broadcast`")
            ));
        }

        if !is_trait && matches!(sig.mode, FnMode::Proof(_)) && !has_body {
            stmts.push(stmt_with_semi!(
                sig.mode.span() =>
                compile_error!("a `proof` function must have a body (if you intentionally want to omit the body, use the `axiom` keyword)")
            ));
        }

        if matches!(sig.mode, FnMode::ProofAxiom(_)) && has_body && !self.erase_ghost.erase() {
            stmts.push(stmt_with_semi!(
                sig.mode.span() =>
                compile_error!("an `axiom` should not have a body")
            ));
        }

        if is_trait && matches!(sig.mode, FnMode::ProofAxiom(_)) {
            stmts.push(stmt_with_semi!(
                sig.mode.span() =>
                compile_error!("`axiom` keyword unexpected in trait declarations")
            ));
        }

        let broadcast_attrs = if let Some(b) = sig.broadcast {
            vec![mk_verus_attr(b.span, quote! { broadcast_forall })]
        } else {
            vec![]
        };

        let publish_attrs = match &sig.publish {
            Publish::Default => vec![],
            Publish::Closed(o) => vec![mk_verus_attr(o.token.span, quote! { closed })],
            Publish::Open(o) => vec![mk_verus_attr(o.token.span, quote! { open })],
            Publish::Uninterp(o) => vec![mk_verus_attr(o.token.span, quote! { uninterp })],
            Publish::OpenRestricted(o) => {
                let in_token = &o.in_token;
                let p = &o.path;
                stmts.push(stmt_with_semi!(
                    o.path.span() =>
                    #[verus::internal(open_visibility_qualifier)]
                    pub(#in_token#p) use crate as _
                ));
                vec![mk_verus_attr(o.open_token.span, quote! { open })]
            }
        };

        let (unimpl, ext_attrs) = match (&sig.mode, semi_token, is_trait) {
            (FnMode::ProofAxiom(_), Some(semi), false) => {
                let unimpl = vec![Stmt::Expr(
                    Expr::Verbatim(quote_spanned!(semi.span => unimplemented!())),
                    None,
                )];
                (unimpl, vec![mk_verus_attr(semi.span, quote! { external_body })])
            }
            (FnMode::Spec(_) | FnMode::SpecChecked(_), Some(semi), false) => {
                // uninterpreted function
                let unimpl = vec![Stmt::Expr(
                    Expr::Verbatim(quote_spanned!(semi.span => unimplemented!())),
                    None,
                )];
                #[cfg(verus_keep_ghost)]
                if !matches!(&sig.publish, Publish::Uninterp(_)) {
                    proc_macro::Diagnostic::spanned(
                        sig.span().unwrap(),
                        proc_macro::Level::Warning,
                        "uninterpreted functions (`spec` functions defined without a body) need to be marked as `uninterp`\nthis will become a hard error in the future",
                    )
                    .emit();
                }
                (unimpl, vec![mk_verus_attr(semi.span, quote! { external_body })])
            }
            _ => (vec![], vec![]),
        };

        let (inside_ghost, mode_attrs): (u32, Vec<Attribute>) = match &sig.mode {
            FnMode::Default => (0, vec![]),
            FnMode::Spec(token) => (1, vec![mk_verus_attr(token.spec_token.span, quote! { spec })]),
            FnMode::SpecChecked(token) => (
                1,
                vec![mk_verus_attr(
                    token.spec_token.span,
                    quote_spanned! { token.spec_token.span => spec(checked) },
                )],
            ),
            FnMode::Proof(token) => {
                (1, vec![mk_verus_attr(token.proof_token.span, quote! { proof })])
            }
            FnMode::ProofAxiom(token) => {
                (1, vec![mk_verus_attr(token.axiom_token.span, quote! { proof })])
            }
            FnMode::Exec(token) => (0, vec![mk_verus_attr(token.exec_token.span, quote! { exec })]),
        };
        self.inside_ghost = inside_ghost;

        let prover = self.take_ghost(&mut sig.spec.prover);
        let prover_attr = prover.as_ref().map(|syn_verus::Prover { id: prover_ident, .. }| {
            mk_verus_attr(prover_ident.span(), quote! { prover(#prover_ident) })
        });

        self.inside_ghost += 1; // for requires, ensures, etc.

        let sig_span = sig.span().clone();
        let spec_stmts =
            self.take_sig_specs(&mut sig.spec, ret_pat, None, sig.constness.is_some(), sig_span);
        if !self.erase_ghost.erase() {
            stmts.extend(spec_stmts);
        }

        self.inside_ghost -= 1;

        sig.publish = Publish::Default;
        sig.mode = FnMode::Default;
        attrs.extend(broadcast_attrs);
        attrs.extend(publish_attrs);
        attrs.extend(mode_attrs);
        attrs.extend(prover_attr.into_iter());
        attrs.extend(ext_attrs);
        self.filter_attrs(attrs);
        // unwrap_ghost_tracked must go first so that unwrapped vars are in scope in other headers
        stmts.splice(0..0, unwrap_ghost_tracked);
        stmts.extend(unimpl);
        stmts
    }

    pub fn desugar_const_or_static(
        &mut self,
        con_mode: &FnMode,
        con_ensures: &mut Option<Ensures>,
        con_block: &mut Option<Box<Block>>,
        con_expr: &mut Option<Box<Expr>>,
        con_eq_token: &mut Option<Token![=]>,
        con_semi_token: &mut Option<Token![;]>,
        con_ty: &Type,
        con_span: Span,
    ) {
        if matches!(con_mode, FnMode::Spec(_) | FnMode::SpecChecked(_)) {
            if let Some(mut expr) = con_expr.take() {
                let mut stmts = Vec::new();
                self.inside_ghost += 1;
                self.visit_expr_mut(&mut expr);
                self.inside_ghost -= 1;
                stmts.push(Stmt::Expr(Expr::Verbatim(quote_spanned!(con_span => #[allow(non_snake_case)]#[verus::internal(verus_macro)] #[verus::internal(const_body)] fn __VERUS_CONST_BODY__() -> #con_ty { #expr } )), None));
                stmts.push(Stmt::Expr(
                    Expr::Verbatim(quote_spanned!(con_span => unsafe { core::mem::zeroed() })),
                    None,
                ));
                *con_expr = Some(Box::new(Expr::Block(syn_verus::ExprBlock {
                    attrs: vec![],
                    label: None,
                    block: Block { brace_token: token::Brace(expr.span()), stmts },
                })));
            }
        } else {
            let ensures = self.take_ghost(con_ensures);
            if let Some(Ensures { token, mut exprs, attrs }) = ensures {
                self.inside_ghost += 1;
                let mut stmts: Vec<Stmt> = Vec::new();
                if attrs.len() > 0 {
                    let err = "outer attributes only allowed on function's ensures";
                    let expr = Expr::Verbatim(quote_spanned!(token.span => compile_error!(#err)));
                    stmts.push(Stmt::Expr(expr, Some(Semi { spans: [token.span] })));
                } else if exprs.exprs.len() > 0 {
                    for expr in exprs.exprs.iter_mut() {
                        self.visit_expr_mut(expr);
                    }
                    // Use a closure in the ensures to avoid circular const definition.
                    // Note: we can't use con.ident as the closure pattern,
                    // because Rust would treat this as a const path pattern.
                    // So we use a 0-parameter closure.
                    stmts.push(stmt_with_semi!(builtin, token.span => #[verus::internal(const_header_wrapper)] || { #builtin::ensures(|| [#exprs]); }));
                }
                let mut block = std::mem::take(con_block).expect("const-with-ensures block");
                block.stmts.splice(0..0, stmts);
                *con_block = Some(block);
                self.inside_ghost -= 1;
            }
            if let Some(block) = std::mem::take(con_block) {
                let expr_block = syn_verus::ExprBlock { attrs: vec![], label: None, block: *block };
                *con_expr = Some(Box::new(Expr::Block(expr_block)));
                *con_eq_token = Some(syn_verus::token::Eq { spans: [con_span] });
                *con_semi_token = Some(Semi { spans: [con_span] });
            }
        }
    }

    fn visit_const_or_static(
        &mut self,
        span: proc_macro2::Span,
        attrs: &mut Vec<Attribute>,
        vis: Option<&Visibility>,
        publish: &mut Publish,
        mode: &mut FnMode,
    ) -> FnMode {
        if self.erase_ghost.keep() {
            attrs.push(mk_verus_attr(span, quote! { verus_macro }));
        }

        let publish_attrs = match (&mode, vis, &publish) {
            (FnMode::Exec(_) | FnMode::Proof(_) | FnMode::ProofAxiom(_), _, _) => vec![],
            (_, Some(Visibility::Inherited), _) => vec![],
            (_, _, Publish::Default) => vec![mk_verus_attr(span, quote! { open })],
            (_, _, Publish::Closed(o)) => vec![mk_verus_attr(o.token.span, quote! { closed })],
            (_, _, Publish::Open(o)) => vec![mk_verus_attr(o.token.span, quote! { open })],
            (_, _, Publish::Uninterp(o)) => vec![mk_verus_attr(o.token.span, quote! { uninterp })],
            (_, _, Publish::OpenRestricted(_)) => {
                unimplemented!("TODO: support open(...)")
            }
        };

        let (inside_ghost, mode_attrs): (u32, Vec<Attribute>) = match &mode {
            FnMode::Default => (0, vec![]),
            FnMode::Spec(token) => (1, vec![mk_verus_attr(token.spec_token.span, quote! { spec })]),
            FnMode::SpecChecked(token) => (
                1,
                vec![mk_verus_attr(
                    token.spec_token.span,
                    quote_spanned! { token.spec_token.span => spec(checked) },
                )],
            ),
            FnMode::Proof(token) => {
                (1, vec![mk_verus_attr(token.proof_token.span, quote! { proof })])
            }
            FnMode::ProofAxiom(_) => {
                unimplemented!("axiom should only be used with functions")
            }
            FnMode::Exec(token) => (0, vec![mk_verus_attr(token.exec_token.span, quote! { exec })]),
        };
        self.inside_ghost = inside_ghost;
        self.inside_const = true;
        *publish = Publish::Default;
        let orig_mode = mode.clone();
        *mode = FnMode::Default;
        attrs.extend(publish_attrs);
        attrs.extend(mode_attrs);
        self.filter_attrs(attrs);
        orig_mode
    }
}

impl VisitMut for ExecGhostPatVisitor {
    // Recursive traverse pat, finding all Tracked(x), Ghost(x), and, for ghost/tracked, x.
    fn visit_pat_mut(&mut self, pat: &mut Pat) {
        // Replace
        //   pat[Tracked(x), Ghost(y), z]
        // with (for mode != exec and inside_ghost != 0):
        //   pat[tmp_x, tmp_y, z]
        //   x_decls: let tracked x = tmp_x.get(); let ghost y = tmp_y.view();
        //   x_assigns: []
        // with (for mode = exec):
        //   pat[tmp_x, tmp_y, z]
        //   x_decls: let tracked x; let ghost mut y;
        //   x_assigns: x = tmp_x.get(); y = tmp_y.view();
        // with (for mode != exec and inside_ghost == 0):
        //   pat[tmp_x, tmp_y, tmp_z]
        //   x_decls: let tracked x; let ghost mut y; let [mode] mut z;
        //   x_assigns: x = tmp_x.get(); y = tmp_y.view(); z = tmp_z;
        let pat_span = pat.span();
        let mk_ident_tmp = |x: &Ident| {
            Ident::new(
                &("verus_tmp_".to_string() + &x.to_string()),
                Span::mixed_site().located_at(pat_span),
            )
        };
        match pat {
            Pat::TupleStruct(pts)
                if pts.elems.len() == 1
                    && (path_is_ident(&pts.path, "Tracked")
                        || path_is_ident(&pts.path, "Ghost")) =>
            {
                if let Pat::Ident(id) = &mut pts.elems[0] {
                    if id.by_ref.is_some() || id.subpat.is_some() {
                        return;
                    }
                    let tmp_x = mk_ident_tmp(&id.ident);
                    let mut x = id.clone();
                    x.mutability = None;
                    let span = id.span();
                    let decl = if path_is_ident(&pts.path, "Tracked") {
                        if self.inside_ghost == 0 {
                            parse_quote_spanned!(span => #[verus::internal(proof)] let mut #x;)
                        } else if id.mutability.is_some() {
                            parse_quote_spanned!(span => #[verus::internal(proof)] let mut #x = #tmp_x.get();)
                        } else {
                            parse_quote_spanned!(span => #[verus::internal(proof)] let #x = #tmp_x.get();)
                        }
                    } else {
                        if self.inside_ghost == 0 {
                            parse_quote_spanned!(span => #[verus::internal(spec)] let mut #x;)
                        } else if id.mutability.is_some() {
                            parse_quote_spanned!(span => #[verus::internal(spec)] let mut #x = #tmp_x.view();)
                        } else {
                            parse_quote_spanned!(span => #[verus::internal(spec)] let #x = #tmp_x.view();)
                        }
                    };
                    self.x_decls.push(decl);
                    if self.inside_ghost == 0 {
                        let assign = if path_is_ident(&pts.path, "Tracked") {
                            quote_spanned!(span => #x = #tmp_x.get())
                        } else {
                            quote_spanned!(span => #x = #tmp_x.view())
                        };
                        let assign =
                            Stmt::Expr(Expr::Verbatim(assign), Some(Semi { spans: [span] }));
                        self.x_assigns.push(assign);
                    }
                    *pat = parse_quote_spanned!(span => #tmp_x);
                    return;
                }
            }
            Pat::Struct(pat_struct) => {
                // When syn parses a struct pattern like `Foo { x }`,
                // it results in an AST similar to `Foo { x: x }`,
                // that is, with a separate node for the field and the expression.
                // The only difference is that one of the nodes has a 'colon' token
                // and one doesn't.
                // Since the transformation we're doing here might change
                // `x: x` to `x: verus_tmp_x`, we can't output it using the shorthand.
                // So we need to add the colon token in.
                for field_pat in pat_struct.fields.iter_mut() {
                    if field_pat.colon_token.is_none() {
                        let span = field_pat.member.span();
                        field_pat.colon_token = Some(token::Colon { spans: [span] });
                    }
                }
            }
            Pat::Ident(id)
                if (self.tracked.is_some() || self.ghost.is_some()) && self.inside_ghost == 0 =>
            {
                if id.by_ref.is_some() || id.subpat.is_some() {
                    return;
                }
                let tmp_x = mk_ident_tmp(&id.ident);
                let mut x = id.clone();
                x.mutability = None;
                let span = id.span();
                let decl = if self.ghost.is_some() {
                    parse_quote_spanned!(span => #[verus::internal(spec)] let mut #x;)
                } else {
                    parse_quote_spanned!(span => #[verus::internal(infer_mode)] let mut #x;)
                };
                let assign = quote_spanned!(span => #x = #tmp_x);
                id.ident = tmp_x;
                self.x_decls.push(decl);
                self.x_assigns
                    .push(Stmt::Expr(Expr::Verbatim(assign), Some(Semi { spans: [span] })));
                return;
            }
            _ => {}
        }
        syn_verus::visit_mut::visit_pat_mut(self, pat);
    }
}

macro_rules! do_split_trait_method {
    ($s:ident, $fun:ident, $spec_fun:ident, $mk_rust_attr:ident) => {
        let mut $spec_fun = $fun.clone();
        let x = &$fun.sig.ident;
        let span = x.span();
        $spec_fun.sig.ident = $s::Ident::new(&format!("{VERUS_SPEC}{x}"), span);
        $spec_fun.attrs.push($mk_rust_attr(span, "doc", quote! { hidden }));
    };
}

// In addition to prefiltering ghost code, we also split methods declarations
// into separate spec and implementation declarations.  For example:
//   fn f() requires x;
// becomes
//   fn VERUS_SPEC__f() requires x;
//   fn f();
// In a later pass, this becomes:
//   fn VERUS_SPEC__f() { requires(x); ... }
//   fn f();
// Note: we don't do this if there's a default body,
// because it turns out that the parameter names
// don't exactly match between fun and fun.clone() (they have different macro contexts),
// which would cause the body and specs to mismatch.
// (See also split_trait_method_syn below.)
fn split_trait_method(spec_items: &mut Vec<TraitItem>, fun: &mut TraitItemFn, erase_ghost: bool) {
    if !erase_ghost && fun.default.is_none() {
        // Copy into separate spec method, then remove spec from original method
        do_split_trait_method!(syn_verus, fun, spec_fun, mk_rust_attr);
        spec_items.push(TraitItem::Fn(spec_fun));
        fun.sig.erase_spec_fields();
    } else if erase_ghost {
        match (&mut fun.default, &fun.sig.mode) {
            (
                Some(default),
                FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) | FnMode::ProofAxiom(_),
            ) => {
                // replace body with panic!()
                let span = default.span();
                let expr: Expr = Expr::Verbatim(quote_spanned! {
                    span => { panic!() }
                });
                let stmt = Stmt::Expr(expr, None);
                default.stmts = vec![stmt];
            }
            _ => {}
        }
    }
}

// syn version of split_trait_method (see above)
// (Note: there are no spec fields to erase in syn; the spec attribute must be erased separately.)
pub(crate) fn split_trait_method_syn(
    fun: &syn::TraitItemFn,
    erase_ghost: bool,
) -> Option<syn::TraitItemFn> {
    use syn::{Block, Expr, Stmt, token::Brace};
    if !erase_ghost && fun.default.is_none() {
        do_split_trait_method!(syn, fun, spec_fun, mk_rust_attr_syn);
        // We won't run visit_trait_item_fn_mut, so we need to add no_method_body here:
        let span = fun.sig.fn_token.span;
        let stmts = vec![Stmt::Expr(
            Expr::Verbatim(quote_spanned_builtin!(builtin, span => #builtin::no_method_body())),
            None,
        )];
        spec_fun.default = Some(Block { brace_token: Brace(span), stmts });
        Some(spec_fun)
    } else {
        // Note: we only support exec functions via syn; there is no fun.sig.mode here
        // So there's no case for spec, proof as in split_trait_method above
        None
    }
}

impl Visitor {
    fn visit_local_extend(&mut self, local: &mut Local) -> (bool, Vec<Stmt>) {
        if self.erase_ghost.erase() && (local.tracked.is_some() || local.ghost.is_some()) {
            return (true, vec![]);
        }
        if local.init.is_none() {
            return (false, vec![]);
        }

        // Replace
        //   let [mode] pat[Tracked(x), Ghost(y), z] = init;
        // with (for mode != exec and inside_ghost != 0):
        //   let pat[tmp_x, tmp_y, z] = init;
        //   let x = tmp_x.get();
        //   let y = tmp_y.view();
        // with (for mode = exec):
        //   let pat[tmp_x, tmp_y, z] = init;
        //   let tracked x;
        //   let ghost mut y;
        //   proof {
        //       x = tmp_x.get();
        //       y = tmp_y.view();
        //   }
        // with (for mode != exec and inside_ghost == 0):
        //   let [mode] mut tmp;
        //   proof { tmp = init; } // save init in tmp to guard against name conflicts with x, y, z
        //   let tracked x;
        //   let ghost mut y;
        //   let [mode] mut z;
        //   proof {
        //       let pat[tmp_x, tmp_y, tmp_z] = tmp;
        //       x = tmp_x.get();
        //       y = tmp_y.view();
        //       z = tmp_z;
        //   }

        let mut stmts: Vec<Stmt> = Vec::new();
        let mut visit_pat = ExecGhostPatVisitor {
            inside_ghost: self.inside_ghost,
            tracked: local.tracked.clone(),
            ghost: local.ghost.clone(),
            x_decls: Vec::new(),
            x_assigns: Vec::new(),
        };
        visit_pat.visit_pat_mut(&mut local.pat);
        if visit_pat.x_decls.len() == 0 && local.tracked.is_none() && local.ghost.is_none() {
            assert!(visit_pat.x_assigns.len() == 0);
            return (false, vec![]);
        }
        if self.erase_ghost.erase() {
            return (false, vec![]);
        }

        let span = local.span();
        // Make proof block that will be subsequently visited with inside_ghost > 0
        let mk_proof_block = |block: Block| {
            let expr_block = syn_verus::ExprBlock { attrs: vec![], label: None, block };
            let op = UnOp::Proof(token::Proof { span });
            Expr::Unary(ExprUnary { attrs: vec![], expr: Box::new(Expr::Block(expr_block)), op })
        };

        if self.inside_ghost != 0 {
            assert!(visit_pat.x_assigns.len() == 0);
            stmts.extend(visit_pat.x_decls);
            (false, stmts)
        } else if local.tracked.is_none() && local.ghost.is_none() {
            stmts.extend(visit_pat.x_decls);
            let block = Block { brace_token: Brace(span), stmts: visit_pat.x_assigns };
            stmts.push(Stmt::Expr(mk_proof_block(block), Some(Semi { spans: [span] })));
            (false, stmts)
        } else {
            let tmp = Ident::new("verus_tmp", Span::mixed_site().located_at(local.span()));
            let tmp_decl = if local.tracked.is_some() {
                parse_quote_spanned!(span => #[verus::internal(proof)] #[verus::internal(unwrapped_binding)] let #tmp;)
            } else {
                parse_quote_spanned!(span => #[verus::internal(spec)] #[verus::internal(unwrapped_binding)] let mut #tmp;)
            };
            stmts.push(tmp_decl);
            let pat = take_pat(&mut local.pat);
            let init = take_expr(&mut local.init.as_mut().expect("init").expr);
            let block1 = parse_quote_spanned!(span => { #tmp = #init });
            stmts.push(Stmt::Expr(mk_proof_block(block1), Some(Semi { spans: [span] })));
            stmts.extend(visit_pat.x_decls);
            let let_pat = if local.tracked.is_some() {
                parse_quote_spanned!(span => #[verus::internal(proof)] let #pat = #tmp;)
            } else {
                parse_quote_spanned!(span => #[verus::internal(spec)] let #pat = #tmp;)
            };
            let mut block_stmts = vec![let_pat];
            block_stmts.extend(visit_pat.x_assigns);
            let block2 = Block { brace_token: Brace(span), stmts: block_stmts };
            stmts.push(Stmt::Expr(mk_proof_block(block2), Some(Semi { spans: [span] })));
            (true, stmts)
        }
    }

    fn visit_stmt_extend(&mut self, stmt: &mut Stmt) -> (bool, Vec<Stmt>) {
        let span = stmt.span();
        match stmt {
            Stmt::Local(local) => self.visit_local_extend(local),
            Stmt::Item(Item::BroadcastUse(broadcast_use)) => {
                let BroadcastUse { attrs, paths, .. } = broadcast_use;
                if self.erase_ghost.erase() {
                    (true, vec![])
                } else {
                    let stmts: Vec<Stmt> = paths.iter().map(|path| Stmt::Expr(Expr::Verbatim(
                        quote_spanned_builtin!(builtin, span => #builtin::reveal_hide_({#[verus::internal(reveal_fn)] fn __VERUS_REVEAL_INTERNAL__() { #builtin::reveal_hide_internal_path_(#path) } #[verus::internal(broadcast_use_reveal)] __VERUS_REVEAL_INTERNAL__}, 1); )
                    ), None)).collect();
                    let mut attrs = attrs.clone();
                    if self.inside_ghost == 0 {
                        attrs.push(mk_verus_attr(span, quote! { proof_block }));
                    }
                    let block = Stmt::Expr(
                        Expr::Block(ExprBlock {
                            attrs: attrs,
                            label: None,
                            block: Block { brace_token: token::Brace(span), stmts },
                        }),
                        None,
                    );
                    (true, vec![block])
                }
            }
            _ => (false, vec![]),
        }
    }

    fn visit_stream_expr(&mut self, stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
        let mut expr: Expr = parse_macro_input!(stream as Expr);
        let mut new_stream = TokenStream::new();
        self.visit_expr_mut(&mut expr);
        expr.to_tokens(&mut new_stream);
        proc_macro::TokenStream::from(new_stream)
    }

    fn visit_items_prefilter(&mut self, items: &mut Vec<Item>) {
        if self.erase_ghost.erase_all() {
            // Erase ghost functions and constants
            items.retain(|item| match item {
                Item::Fn(fun) => match fun.sig.mode {
                    FnMode::Spec(_)
                    | FnMode::SpecChecked(_)
                    | FnMode::Proof(_)
                    | FnMode::ProofAxiom(_) => false,
                    FnMode::Exec(_) | FnMode::Default => true,
                },
                Item::Const(c) => match c.mode {
                    FnMode::Spec(_)
                    | FnMode::SpecChecked(_)
                    | FnMode::Proof(_)
                    | FnMode::ProofAxiom(_) => false,
                    FnMode::Exec(_) | FnMode::Default => true,
                },
                _ => true,
            });
            // We can't erase ghost datatypes D, because they can be used
            // as Ghost<D> or Tracked<D>.
        }
        let erase_ghost = self.erase_ghost.erase();
        let mut assume_spec_extra_impl_items = vec![];
        // We'd like to erase ghost items, but there may be dangling references to the ghost items:
        // - "use" declarations may refer to the items ("use m::f;" makes it hard to erase f)
        // - "impl" may refer to struct and enum items ("impl<A> S<A> { ... }" impedes erasing S)
        // Therefore, we leave arbitrary named stubs in the place of the erased ghost items:
        // - For erased pub spec or proof Fn item x, keep decl, replace body with panic!()
        // - For erased pub Const item x, keep as-is (REVIEW: it's not clear what expressions we can support)
        // - For erased non-pub Fn and Const item x, leave "use bool as x;"
        // - Leave Struct and Enum as-is (REVIEW: we could leave stubs with PhantomData fields)
        for item in items.iter_mut() {
            let span = item.span();
            match item {
                Item::Fn(fun) => match (&fun.vis, &fun.sig.mode) {
                    (
                        Visibility::Public(_),
                        FnMode::Spec(_)
                        | FnMode::SpecChecked(_)
                        | FnMode::Proof(_)
                        | FnMode::ProofAxiom(_),
                    ) if erase_ghost => {
                        // replace body with panic!()
                        let expr: Expr = Expr::Verbatim(quote_spanned! {
                            span => { panic!() }
                        });
                        let stmt = Stmt::Expr(expr, None);
                        fun.block.stmts = vec![stmt];
                        fun.semi_token = None;
                        continue;
                    }
                    _ => {}
                },
                _ => {}
            }
            let erase_fn = match item {
                Item::Fn(fun) => match fun.sig.mode {
                    FnMode::Spec(_)
                    | FnMode::SpecChecked(_)
                    | FnMode::Proof(_)
                    | FnMode::ProofAxiom(_)
                        if erase_ghost =>
                    {
                        Some((fun.sig.ident.clone(), fun.vis.clone()))
                    }
                    _ => None,
                },
                Item::Const(c) => match (&c.vis, &c.mode) {
                    (Visibility::Public(_), _) => None,
                    (
                        _,
                        FnMode::Spec(_)
                        | FnMode::SpecChecked(_)
                        | FnMode::Proof(_)
                        | FnMode::ProofAxiom(_),
                    ) if erase_ghost => Some((c.ident.clone(), c.vis.clone())),
                    _ => None,
                },
                /*
                Item::Struct(s) => match s.mode {
                    DataMode::Ghost(_) | DataMode::Tracked(_) if erase_ghost => {
                        ...
                    }
                    _ => None,
                },
                Item::Enum(e) => match e.mode {
                    DataMode::Ghost(_) | DataMode::Tracked(_) if erase_ghost => {
                        ...
                    }
                    _ => None,
                },
                */
                _ => None,
            };
            if let Some((name, vis)) = erase_fn {
                *item = Item::Verbatim(quote_spanned! {
                    span => #[allow(unused_imports)] #vis fn #name() { unimplemented!() }
                });
            }
        }
        for item in items.iter_mut() {
            match &item {
                Item::Global(global) => {
                    let Global { attrs: _, global_token: _, inner, semi: _ } = global;
                    let (type_, size_lit, align_lit) = match inner {
                        syn_verus::GlobalInner::SizeOf(size_of) => {
                            (&size_of.type_, &size_of.expr_lit, None)
                        }
                        syn_verus::GlobalInner::Layout(layout) => {
                            (&layout.type_, &layout.size.2, layout.align.as_ref().map(|a| &a.3))
                        }
                    };
                    let span = item.span();
                    let static_assert_size = if self.erase_ghost.erase() {
                        quote! {
                            if ::core::mem::size_of::<#type_>() != #size_lit {
                                panic!("does not have the expected size");
                            }
                        }
                    } else {
                        quote! {}
                    };
                    let static_assert_align = if let Some(align_lit) = align_lit {
                        if self.erase_ghost.erase() {
                            quote! {
                                if ::core::mem::align_of::<#type_>() != #align_lit {
                                    panic!("does not have the expected alignment");
                                }
                            }
                        } else {
                            quote! {}
                        }
                    } else {
                        quote! {}
                    };
                    if self.erase_ghost.erase() {
                        *item = Item::Verbatim(quote_spanned! { span => const _: () = {
                            #static_assert_size
                            #static_assert_align
                        }; });
                    } else {
                        let type_name_escaped = format!("{}", type_.into_token_stream())
                            .replace(" ", "")
                            .replace("<", "_LL_")
                            .replace(">", "_RR_");
                        if !type_name_escaped.chars().all(|c| c.is_alphanumeric() || c == '_') {
                            let err = "this type name is not supported (it must only include A-Za-z0-9<>)";
                            *item = Item::Verbatim(
                                quote_spanned!(span => const _: () = { compile_error!(#err) };),
                            );
                        } else {
                            let lemma_ident =
                                format_ident!("VERUS_layout_of_{}", type_name_escaped);

                            let ensures_align = if let Some(align_lit) = align_lit {
                                quote_vstd! { vstd => #vstd::layout::align_of::<#type_>() == #align_lit, }
                            } else {
                                quote! {}
                            };

                            *item = Item::Verbatim(
                                quote_spanned_builtin_vstd! { builtin, vstd, span =>
                                #[verus::internal(size_of)] const _: () = {
                                    #builtin::global_size_of::<#type_>(#size_lit);

                                    #static_assert_size
                                    #static_assert_align
                                };

                                ::builtin_macros::verus! {
                                    #[verus::internal(size_of_broadcast_proof)]
                                    #[verifier::external_body]
                                    #[allow(non_snake_case)]
                                    broadcast proof fn #lemma_ident()
                                        ensures
                                            #[trigger] #vstd::layout::size_of::<#type_>() == #size_lit,
                                            #ensures_align
                                    {
                                    }
                                }
                                },
                            );
                        }
                    }
                }
                Item::BroadcastUse(item_broadcast_use) => {
                    let span = item.span();
                    let paths = &item_broadcast_use.paths;
                    if self.erase_ghost.erase() {
                        if item_broadcast_use.warning {
                            #[cfg(verus_keep_ghost)]
                            proc_macro::Diagnostic::spanned(
                                span.unwrap(),
                                proc_macro::Level::Warning,
                                "Outdated syntax for broadcast use.\n\
                                         Use curly braces for multiple uses.",
                            )
                            .emit();
                        }
                        *item = Item::Verbatim(quote! { const _: () = (); });
                    } else {
                        let stmts: Vec<Stmt> = paths.iter().map(|path| Stmt::Expr(Expr::Verbatim(
                            quote_spanned_builtin!(builtin, span => #builtin::reveal_hide_({#[verus::internal(reveal_fn)] fn __VERUS_REVEAL_INTERNAL__() { #builtin::reveal_hide_internal_path_(#path) } #[verus::internal(broadcast_use_reveal)] __VERUS_REVEAL_INTERNAL__}, 1); )
                        ), None)).collect();
                        let block =
                            Block { brace_token: token::Brace { span: into_spans(span) }, stmts };
                        *item = Item::Verbatim(quote_spanned! { span =>
                            #[verus::internal(verus_macro)]
                            #[verus::internal(item_broadcast_use)]
                            const _: () = #block;
                        });
                    }
                }
                Item::BroadcastGroup(item_broadcast_group) => {
                    *item = Item::Verbatim(
                        self.handle_broadcast_group(item_broadcast_group, item.span()),
                    );
                }
                Item::AssumeSpecification(assume_specification) => {
                    *item = self.handle_assume_specification(
                        assume_specification,
                        item.span(),
                        &mut assume_spec_extra_impl_items,
                    );
                }
                _ => (),
            }
        }
        if assume_spec_extra_impl_items.len() > 0 {
            items.push(Item::Verbatim(quote_vstd! {vstd =>
                impl #vstd::std_specs::VstdSpecsForRustStdLib {
                    #(#assume_spec_extra_impl_items)*
                }
            }))
        }
    }

    fn handle_assume_specification(
        &mut self,
        assume_specification: &AssumeSpecification,
        span: Span,
        assume_spec_extra_impl_items: &mut Vec<ImplItem>,
    ) -> Item {
        let AssumeSpecification {
            mut attrs,
            vis,
            assume_specification: assume_specification_token,
            generics,
            bracket_token: _,
            qself,
            path,
            paren_token,
            inputs,
            output,
            requires,
            ensures,
            returns,
            invariants,
            unwind,
            semi,
        } = assume_specification.clone();
        let ex_ident = get_ex_ident_mangle_path(&qself, &path);

        let sig = Signature {
            publish: Publish::Default,
            constness: None,
            asyncness: None,
            unsafety: Some(token::Unsafe { span }),
            abi: None,
            broadcast: None,
            mode: FnMode::Default,
            fn_token: token::Fn { span },
            ident: ex_ident,
            generics: generics,
            paren_token: paren_token,
            inputs: inputs,
            variadic: None,
            output: output,
            spec: SignatureSpec {
                prover: None,
                requires: requires,
                recommends: None,
                ensures: ensures,
                returns: returns,
                decreases: None,
                invariants: invariants,
                unwind: unwind,
                with: None,
            },
        };

        match sig.inputs.first() {
            Some(FnArg { tracked: _, kind: FnArgKind::Receiver(_) }) => {
                return Item::Verbatim(
                    quote_spanned!(span => compile_error!("use a named param instead of 'self' argument");),
                );
            }
            _ => false,
        };

        attrs.push(mk_verus_attr(
            assume_specification_token.span,
            quote_spanned! { assume_specification_token.span => external_fn_specification },
        ));
        attrs.push(mk_rust_attr(
            assume_specification_token.span,
            "allow",
            quote! { non_snake_case },
        ));

        let block =
            Box::new(Block { brace_token: token::Brace { span: into_spans(span) }, stmts: vec![] });
        let mut item_fn = ItemFn { attrs, vis, sig, block, semi_token: None };

        if self.rustdoc {
            crate::rustdoc::process_item_fn_assume_specification(
                &mut item_fn,
                assume_specification,
            );
        }

        let mut stmts = self.visit_fn(
            &mut item_fn.attrs,
            Some(&item_fn.vis),
            &mut item_fn.sig,
            Some(semi),
            false,
        );

        if self.rustdoc && crate::cfg_verify_vstd() {
            let mut block = (*item_fn.block).clone();
            block.stmts.push(Stmt::Expr(Expr::Verbatim(quote! { ::core::unimplemented!() }), None));
            let impl_item_fn = syn_verus::ImplItem::Fn(syn_verus::ImplItemFn {
                attrs: item_fn.attrs.clone(),
                vis: item_fn.vis.clone(),
                defaultness: None,
                sig: item_fn.sig.clone(),
                block,
                semi_token: None,
            });
            assume_spec_extra_impl_items.push(impl_item_fn);
        }

        let mut args = vec![];
        for input in item_fn.sig.inputs.iter() {
            let ident = match &input.kind {
                FnArgKind::Receiver(recvr) => {
                    return Item::Verbatim(
                        quote_spanned!(recvr.self_token.span() => compile_error!("bad argument");),
                    );
                }
                FnArgKind::Typed(pat_type) => match &*pat_type.pat {
                    Pat::Ident(PatIdent { ident, .. }) => ident,
                    _ => {
                        return Item::Verbatim(
                            quote_spanned!(pat_type.pat.span() => compile_error!("'assume_specification' expects ident, not complex pattern");),
                        );
                    }
                },
            };
            args.push(Expr::Verbatim(quote! { #ident }));
        }

        let callee =
            syn_verus::ExprPath { attrs: vec![], qself: qself.clone(), path: path.clone() };
        // We wrap the function call in an 'unsafe' block, since the user might be applying
        // a specification to an unsafe function.
        let e = Expr::Verbatim(quote! {
            unsafe { #callee(#(#args),*) }
        });
        stmts.push(Stmt::Expr(e, None));

        item_fn.block.stmts = stmts;

        Item::Fn(item_fn)
    }

    fn handle_broadcast_group(
        &mut self,
        item_broadcast_group: &ItemBroadcastGroup,
        span: Span,
    ) -> TokenStream {
        let ItemBroadcastGroup {
            attrs,
            vis,
            broadcast_group_tokens: _,
            ident,
            brace_token: _,
            paths,
        } = item_broadcast_group;
        if self.erase_ghost.erase() {
            if matches!(vis, Visibility::Public(_)) {
                let mut item_fn: ItemFn = parse_quote_spanned! { span =>
                    #vis fn #ident() { panic!() }
                };
                item_fn.attrs.extend(attrs.into_iter().cloned());
                item_fn.to_token_stream()
            } else {
                TokenStream::new()
            }
        } else {
            let stmts: Vec<Stmt> = paths.iter().map(|path| Stmt::Expr(Expr::Verbatim(quote_spanned_builtin!{ builtin, span =>
                #builtin::reveal_hide_({#[verus::internal(reveal_fn)] fn __VERUS_REVEAL_INTERNAL__() { #builtin::reveal_hide_internal_path_(#path) } __VERUS_REVEAL_INTERNAL__}, 1); }), None))
                .collect();
            let block = Block { brace_token: token::Brace { span: into_spans(span) }, stmts };
            let mut item_fn: ItemFn = parse_quote_spanned! { span =>
                #[verus::internal(reveal_group)]
                #[verus::internal(verus_macro)]
                #[verus::internal(proof)]
                #vis fn #ident() #block
            };
            item_fn.attrs.extend(attrs.into_iter().cloned());
            if self.rustdoc {
                crate::rustdoc::process_item_fn_broadcast_group(&mut item_fn);
            }
            item_fn.to_token_stream()
        }
    }

    fn visit_items_post(&mut self, items: &mut Vec<Item>) {
        let mut i = 0;
        while i < items.len() {
            if let Item::Enum(enum_) = &mut items[i] {
                if let Some(new_item) =
                    crate::enum_synthesize::visit_item_enum_synthesize(&self.erase_ghost, enum_)
                {
                    items.insert(i + 1, new_item);
                    i += 1;
                }
            }
            i += 1;
        }
    }

    fn visit_impl_items_prefilter(&mut self, items: &mut Vec<ImplItem>, for_trait: bool) {
        if self.erase_ghost.erase_all() {
            items.retain(|item| match item {
                ImplItem::Fn(fun) => match fun.sig.mode {
                    FnMode::Spec(_)
                    | FnMode::SpecChecked(_)
                    | FnMode::Proof(_)
                    | FnMode::ProofAxiom(_) => false,
                    FnMode::Exec(_) | FnMode::Default => true,
                },
                ImplItem::Const(c) => match c.mode {
                    FnMode::Spec(_)
                    | FnMode::SpecChecked(_)
                    | FnMode::Proof(_)
                    | FnMode::ProofAxiom(_) => false,
                    FnMode::Exec(_) | FnMode::Default => true,
                },
                _ => true,
            });
        }
        let erase_ghost = self.erase_ghost.erase();
        // Unfortunately, we just have to assume that if for_trait == true,
        // the methods might be public
        items.retain(|item| match item {
            ImplItem::Fn(fun) => match ((&fun.vis, for_trait), &fun.sig.mode) {
                (
                    (Visibility::Public(_), _) | (_, true),
                    FnMode::Spec(_)
                    | FnMode::SpecChecked(_)
                    | FnMode::Proof(_)
                    | FnMode::ProofAxiom(_),
                ) => true,
                (
                    _,
                    FnMode::Spec(_)
                    | FnMode::SpecChecked(_)
                    | FnMode::Proof(_)
                    | FnMode::ProofAxiom(_),
                ) => !erase_ghost,
                (_, FnMode::Exec(_) | FnMode::Default) => true,
            },
            ImplItem::Const(c) => match (&c.vis, &c.mode) {
                (Visibility::Public(_), _) => true,
                (
                    _,
                    FnMode::Spec(_)
                    | FnMode::SpecChecked(_)
                    | FnMode::Proof(_)
                    | FnMode::ProofAxiom(_),
                ) => !erase_ghost,
                (_, FnMode::Exec(_) | FnMode::Default) => true,
            },
            _ => true,
        });
        for item in items.iter_mut() {
            let span = item.span();
            match item {
                ImplItem::Fn(fun) => match ((&fun.vis, for_trait), &fun.sig.mode) {
                    (
                        (Visibility::Public(_), _) | (_, true),
                        FnMode::Spec(_)
                        | FnMode::SpecChecked(_)
                        | FnMode::Proof(_)
                        | FnMode::ProofAxiom(_),
                    ) if erase_ghost => {
                        // replace body with panic!()
                        let expr: Expr = Expr::Verbatim(quote_spanned! {
                            span => { panic!() }
                        });
                        let stmt = Stmt::Expr(expr, None);
                        fun.block.stmts = vec![stmt];
                        fun.semi_token = None;
                        continue;
                    }
                    _ => {}
                },
                ImplItem::BroadcastGroup(item_broadcast_group) => {
                    *item =
                        ImplItem::Verbatim(self.handle_broadcast_group(item_broadcast_group, span));
                }
                _ => {}
            }
        }
    }

    fn visit_trait_items_prefilter(&mut self, items: &mut Vec<TraitItem>) {
        if self.rustdoc {
            for trait_item in items.iter_mut() {
                match trait_item {
                    TraitItem::Fn(trait_item_method) => {
                        crate::rustdoc::process_trait_item_method(trait_item_method);
                    }
                    _ => {}
                }
            }
        }

        if self.erase_ghost.erase_all() {
            items.retain(|item| match item {
                TraitItem::Fn(fun) => match fun.sig.mode {
                    FnMode::Spec(_)
                    | FnMode::SpecChecked(_)
                    | FnMode::Proof(_)
                    | FnMode::ProofAxiom(_) => false,
                    FnMode::Exec(_) | FnMode::Default => true,
                },
                _ => true,
            });
        }
        let erase_ghost = self.erase_ghost.erase();
        let mut spec_items: Vec<TraitItem> = Vec::new();
        for item in items.iter_mut() {
            match item {
                TraitItem::Fn(ref mut fun) => {
                    split_trait_method(&mut spec_items, fun, erase_ghost);
                }
                _ => {}
            }
        }
        items.append(&mut spec_items);
    }
}

fn chain_count(expr: &Expr) -> u32 {
    if let Expr::Binary(binary) = expr {
        match binary.op {
            BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_) | BinOp::Eq(_) => {
                1 + chain_count(&binary.left)
            }
            _ => 0,
        }
    } else {
        0
    }
}

const ILLEGAL_CALLEES: &[&str] = &["forall", "exists", "choose"];

impl Visitor {
    fn chain_operators(&mut self, expr: &mut Expr) -> bool {
        let count = chain_count(expr);
        if count < 2 {
            return false;
        }
        let mut rights: Vec<(Expr, &'static str, proc_macro2::Span)> = Vec::new();

        let mut cur_expr = take_expr(expr);

        let inside_arith = self.inside_arith;
        self.inside_arith = InsideArith::Widen;

        for _ in 0..count {
            if let Expr::Binary(binary) = cur_expr {
                let span = binary.span();
                let op = match binary.op {
                    BinOp::Le(_) => "spec_chained_le",
                    BinOp::Lt(_) => "spec_chained_lt",
                    BinOp::Ge(_) => "spec_chained_ge",
                    BinOp::Gt(_) => "spec_chained_gt",
                    BinOp::Eq(_) => "spec_chained_eq",
                    _ => panic!("chain_operators"),
                };
                let left = *binary.left;
                let mut right = *binary.right;
                self.visit_expr_mut(&mut right);
                rights.push((right, op, span));

                cur_expr = left;
            } else {
                panic!("chain_operators");
            }
        }
        self.visit_expr_mut(&mut cur_expr);

        self.inside_arith = inside_arith;

        // example:
        //   ((e0 <= e1) <= e2) <= e3
        //   count == 3
        //   cur_expr = e0
        //   rights = [e3, e2, e1]
        // goal:
        //   spec_chained_cmp(spec_chained_le(spec_chained_le(spec_chained_le(spec_chained_value(e0), e1), e2), e3))

        let span = cur_expr.span();
        let mut toks =
            quote_spanned_builtin!(builtin, span => #builtin::spec_chained_value(#cur_expr));
        for (right, op, span) in rights.iter().rev() {
            let ident = Ident::new(op, *span);
            toks = quote_spanned_builtin!(builtin, *span => #builtin::#ident(#toks, #right));
        }
        toks = quote_spanned_builtin!(builtin, span => #builtin::spec_chained_cmp(#toks));

        *expr = Expr::Verbatim(toks);

        true
    }

    /// Turn `forall|x| ...`
    /// into `#builtin::forall(|x| ...)`
    /// and similarly for `exists` and `choose`
    ///
    /// Also handle trigger attributes.
    ///
    /// Returns true if the transform is attempted, false if the transform is inapplicable.

    fn closure_quant_operators(&mut self, expr: &mut Expr) -> bool {
        let unary = match expr {
            Expr::Unary(u @ ExprUnary { op: UnOp::Forall(..), .. }) => u,
            Expr::Unary(u @ ExprUnary { op: UnOp::Exists(..), .. }) => u,
            Expr::Unary(u @ ExprUnary { op: UnOp::Choose(..), .. }) => u,
            Expr::Call(ExprCall { attrs: _, func, paren_token: _, args: _ }) => {
                if let Expr::Path(syn_verus::ExprPath { path, qself: None, attrs: _ }) = &**func {
                    if path.segments.len() == 1
                        && ILLEGAL_CALLEES.contains(&path.segments[0].ident.to_string().as_str())
                    {
                        let err = format!(
                            "forall, choose, and exists do not allow parentheses, use `{}|<vars>| expr` instead",
                            path.segments[0].ident.to_string()
                        );
                        *expr = Expr::Verbatim(quote_spanned!(expr.span() => compile_error!(#err)));
                        return true;
                    }
                }
                return false;
            }
            _ => {
                return false;
            }
        };

        // Recursively visit the closure expression, but *don't* call our
        // custom visitor fn on the closure node itself.
        visit_expr_mut(self, &mut unary.expr);

        let span = unary.span();

        let attrs = std::mem::take(&mut unary.attrs);

        let arg = &mut *unary.expr;
        let (inner_attrs, closure_input_types) = match &mut *arg {
            Expr::Closure(closure) => {
                if closure.requires.is_some() || closure.ensures.is_some() {
                    let err = "quantifiers cannot have requires/ensures";
                    *expr = Expr::Verbatim(quote_spanned!(span => compile_error!(#err)));
                    return true;
                }
                let closure_input_types = closure
                    .inputs
                    .iter()
                    .map(|arg| match &arg.pat {
                        Pat::Type(pat_ty) => Some(pat_ty.clone()),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                (std::mem::take(&mut closure.inner_attrs), closure_input_types)
            }
            _ => panic!("expected closure for quantifier"),
        };

        match self.extract_quant_triggers(inner_attrs, span) {
            Ok(ExtractQuantTriggersFound::Auto) => match &mut *arg {
                Expr::Closure(closure) => {
                    let body = take_expr(&mut closure.body);
                    closure.body = Box::new(Expr::Verbatim(
                        quote_spanned!(span => #[verus::internal(auto_trigger)] (#body)),
                    ));
                }
                _ => panic!("expected closure for quantifier"),
            },
            Ok(ExtractQuantTriggersFound::AllTriggers) => match &mut *arg {
                Expr::Closure(closure) => {
                    let body = take_expr(&mut closure.body);
                    closure.body = Box::new(Expr::Verbatim(
                        quote_spanned!(span => #[verus::internal(all_triggers)] (#body)),
                    ));
                }
                _ => panic!("expected closure for quantifier"),
            },
            Ok(ExtractQuantTriggersFound::Triggers(tuple)) => match &mut *arg {
                Expr::Closure(closure) => {
                    let body = take_expr(&mut closure.body);
                    closure.body = Box::new(Expr::Verbatim(
                        quote_spanned_builtin!(builtin, span => #builtin::with_triggers(#tuple, #body)),
                    ));
                }
                _ => panic!("expected closure for quantifier"),
            },
            Ok(ExtractQuantTriggersFound::None) => {}
            Err(err_expr) => {
                *expr = err_expr;
                return true;
            }
        }

        match unary.op {
            UnOp::Forall(..) => {
                *expr = quote_verbatim!(builtin, span, attrs => #builtin::forall(#arg));
            }
            UnOp::Exists(..) => {
                *expr = quote_verbatim!(builtin, span, attrs => #builtin::exists(#arg));
            }
            UnOp::Choose(..) => {
                fn in_ty_to_ty_arg(arg: &Option<syn_verus::PatType>) -> TokenStream {
                    match arg {
                        Some(arg) => arg.ty.to_token_stream(),
                        None => quote! { _ },
                    }
                }
                match &closure_input_types[..] {
                    [in_ty] => {
                        let targ = in_ty_to_ty_arg(in_ty);
                        *expr = quote_verbatim!(builtin, span, attrs => #builtin::choose::<#targ, _>(#arg));
                    }
                    _ => {
                        let targs: Punctuated<TokenStream, syn_verus::token::Comma> =
                            closure_input_types.iter().map(in_ty_to_ty_arg).collect();
                        *expr = quote_verbatim!(builtin, span, attrs => #builtin::choose_tuple::<(#targs,), _>(#arg));
                    }
                }
            }
            _ => panic!("unary"),
        }

        true
    }

    /// Handle &&& and |||
    fn handle_big_and_big_or(&mut self, expr: &mut Expr) -> bool {
        if !matches!(expr, Expr::BigAnd(_) | Expr::BigOr(_)) {
            return false;
        }

        self.visit_expr_with_arith(expr, InsideArith::None);

        if let Expr::BigAnd(exprs) = expr {
            let mut new_expr = take_expr(&mut exprs.exprs[0].expr);
            for i in 1..exprs.exprs.len() {
                let span = exprs.exprs[i].tok.span();
                let spans = [span, span];
                let right = take_expr(&mut exprs.exprs[i].expr);
                let left = Box::new(Expr::Verbatim(quote_spanned!(new_expr.span() => (#new_expr))));
                let right = Box::new(Expr::Verbatim(quote_spanned!(right.span() => (#right))));
                let attrs = Vec::new();
                let op = BinOp::And(syn_verus::token::AndAnd { spans });
                let bin = ExprBinary { attrs, op, left, right };
                new_expr = Expr::Binary(bin);
            }
            *expr = new_expr;
        } else if let Expr::BigOr(exprs) = expr {
            let mut new_expr = take_expr(&mut exprs.exprs[0].expr);
            for i in 1..exprs.exprs.len() {
                let span = exprs.exprs[i].tok.span();
                let spans = [span, span];
                let right = take_expr(&mut exprs.exprs[i].expr);
                let left = Box::new(Expr::Verbatim(quote_spanned!(new_expr.span() => (#new_expr))));
                let right = Box::new(Expr::Verbatim(quote_spanned!(right.span() => (#right))));
                let attrs = Vec::new();
                let op = BinOp::Or(syn_verus::token::OrOr { spans });
                let bin = ExprBinary { attrs, op, left, right };
                new_expr = Expr::Binary(bin);
            }
            *expr = new_expr;
        } else {
            unreachable!();
        }

        true
    }

    fn handle_spec_operators(&mut self, expr: &mut Expr) -> bool {
        if !matches!(
            expr,
            Expr::Index(_)
                | Expr::View(_)
                | Expr::Is(_)
                | Expr::IsNot(_)
                | Expr::Has(_)
                | Expr::HasNot(_)
                | Expr::Matches(_)
                | Expr::GetField(_)
        ) {
            return false;
        }

        self.visit_expr_with_arith(expr, InsideArith::None);

        match take_expr(expr) {
            Expr::Index(idx) => {
                if self.use_spec_traits && self.inside_ghost > 0 {
                    let span = idx.span();
                    let src = idx.expr;
                    let attrs = idx.attrs;
                    let index = idx.index;
                    *expr = quote_verbatim!(span, attrs => #src.spec_index(#index));
                } else {
                    *expr = Expr::Index(idx);
                }
            }
            Expr::View(view) if !self.assign_to => {
                let at_token = view.at_token;
                let view_call = quote_spanned!(at_token.span => .view());
                let span = view.span();
                let attrs = view.attrs;
                let base = view.expr;
                *expr = quote_verbatim!(span, attrs => (#base#view_call));
            }
            Expr::View(view) => {
                assert!(self.assign_to);
                let at_token = view.at_token;
                let span1 = at_token.span;
                let span2 = view.span();
                let attrs = view.attrs;
                let base = view.expr;
                let borrowed: Expr = Expr::Verbatim(quote_spanned!(span1 => #base.borrow_mut()));
                *expr = quote_verbatim!(span2, attrs => (*(#borrowed)));
            }
            Expr::Is(is_) => {
                let _is_token = is_.is_token;
                let span = is_.span();
                let base = is_.base;
                let variant_str = is_.variant_ident.to_string();
                *expr = Expr::Verbatim(
                    quote_spanned_builtin!(builtin, span => #builtin::is_variant(#base, #variant_str)),
                );
            }
            Expr::IsNot(isnot_) => {
                let _is_not_token = isnot_.is_not_token;
                let span = isnot_.span();
                let base = isnot_.base;
                let variant_str = isnot_.variant_ident.to_string();
                *expr = Expr::Verbatim(
                    quote_spanned_builtin!(builtin, span => !(#builtin::is_variant(#base, #variant_str))),
                );
            }
            Expr::Has(has) => {
                let has_token = has.has_token;
                let span = has.span();
                let rhs = has.rhs;
                let has_call = quote_spanned!(has_token.span => .spec_has(#rhs));
                let lhs = has.lhs;
                *expr = Expr::Verbatim(quote_spanned!(span => (#lhs#has_call)));
            }
            Expr::HasNot(hasnot) => {
                let has_not_token = hasnot.has_not_token;
                let span = hasnot.span();
                let rhs = hasnot.rhs;
                let has_call = quote_spanned!(has_not_token.span => .spec_has(#rhs));
                let lhs = hasnot.lhs;
                *expr = Expr::Verbatim(quote_spanned!(span => !(#lhs#has_call)));
            }
            Expr::Matches(matches) => {
                let span = matches.span();
                let syn_verus::ExprMatches { attrs: _, lhs, matches_token: _, pat, op_expr } =
                    matches;
                if let Some(op_expr) = op_expr {
                    let MatchesOpExpr { op_token, rhs } = op_expr;
                    match op_token {
                        MatchesOpToken::Implies(_) => {
                            *expr = Expr::Verbatim(quote_spanned!(span => (
                                (if let #pat = (#lhs) { #rhs } else { true })
                            )));
                        }
                        MatchesOpToken::AndAnd(_) => {
                            *expr = Expr::Verbatim(quote_spanned!(span => (
                                (if let #pat = (#lhs) { #rhs } else { false })
                            )));
                        }
                        MatchesOpToken::BigAnd => {
                            *expr = Expr::Verbatim(quote_spanned!(span => (
                                (if let #pat = (#lhs) { #rhs } else { false })
                            )));
                        }
                    }
                } else {
                    *expr = Expr::Verbatim(quote_spanned!(span => (
                        (if let #pat = (#lhs) { true } else { false })
                    )));
                }
            }
            Expr::GetField(gf) => {
                let span = gf.span();
                let base = gf.base;
                let member_ident = quote::format_ident!("arrow_{}", gf.member);
                let get_call = quote_spanned!(gf.arrow_token.span() => .#member_ident());
                *expr = Expr::Verbatim(quote_spanned!(span => (#base#get_call)));
            }
            _ => unreachable!(),
        }

        true
    }

    /// Handle UnaryOp expressions Neg and Sub
    fn handle_unary_ops(&mut self, expr: &mut Expr) -> bool {
        let Expr::Unary(unary) = expr else {
            return false;
        };

        let sub_inside_arith = match unary.op {
            UnOp::Neg(..) => InsideArith::Widen,
            UnOp::Not(..) => InsideArith::Fixed,
            _ => InsideArith::None,
        };

        self.visit_expr_with_arith(expr, sub_inside_arith);

        let Expr::Unary(unary) = expr else {
            unreachable!();
        };

        if self.use_spec_traits && self.inside_ghost > 0 {
            let span = unary.span();
            let attrs = &unary.attrs;
            match &unary.op {
                UnOp::Neg(_neg) => {
                    let arg = &unary.expr;
                    if let Expr::Lit(..) = &**arg {
                        // leave native Rust literal with native Rust negation
                    } else {
                        *expr = quote_verbatim!(span, attrs => (#arg).spec_neg());
                    }
                }
                _ => {}
            }
        }

        true
    }

    /// Handle all BinaryOp expressions, transforming them if necessary
    /// (e.g., `a + b` -> `a.spec_add(b)`
    fn handle_binary_ops(&mut self, expr: &mut Expr) -> bool {
        let Expr::Binary(binary) = expr else {
            return false;
        };

        if let Expr::Matches(ExprMatches {
            op_expr: Some(MatchesOpExpr { op_token, .. }), ..
        }) = &*binary.right
        {
            match op_token {
                MatchesOpToken::BigAnd => {}
                MatchesOpToken::Implies(_) => {
                    *expr = Expr::Verbatim(
                        quote_spanned! { expr.span() => compile_error!("matches with ==> is currently not allowed on the right-hand-side of most binary operators (use parentheses)") },
                    );
                    return true;
                }
                MatchesOpToken::AndAnd(_) => {
                    *expr = Expr::Verbatim(
                        quote_spanned! { expr.span() => compile_error!("matches with && is currently not allowed on the right-hand-side of most binary operators (use parentheses)") },
                    );
                    return true;
                }
            }
        }

        let sub_inside_arith = match binary.op {
            BinOp::Add(..)
            | BinOp::Sub(..)
            | BinOp::Mul(..)
            | BinOp::Eq(..)
            | BinOp::Ne(..)
            | BinOp::Lt(..)
            | BinOp::Le(..)
            | BinOp::Gt(..)
            | BinOp::Ge(..) => InsideArith::Widen,
            BinOp::Div(..) | BinOp::Rem(..) => InsideArith::None,
            BinOp::BitXor(..)
            | BinOp::BitAnd(..)
            | BinOp::BitOr(..)
            | BinOp::Shl(..)
            | BinOp::Shr(..) => InsideArith::Fixed,
            _ => InsideArith::None,
        };

        self.visit_expr_with_arith(expr, sub_inside_arith);

        let Expr::Binary(binary) = expr else {
            unreachable!();
        };

        let span = binary.span();
        let low_prec_op = match binary.op {
            BinOp::Equiv(syn_verus::token::Equiv { spans }) => {
                let spans = [spans[1], spans[2]];
                Some(BinOp::Eq(syn_verus::token::EqEq { spans }))
            }
            _ => None,
        };
        let ply = match binary.op {
            BinOp::Imply(_) => Some(true),
            BinOp::Exply(_) => Some(false),
            _ => None,
        };
        let verus_eq = match binary.op {
            BinOp::BigEq(_) => true,
            BinOp::BigNe(_) => true,
            BinOp::ExtEq(_) => true,
            BinOp::ExtNe(_) => true,
            BinOp::ExtDeepEq(_) => true,
            BinOp::ExtDeepNe(_) => true,
            _ => false,
        };
        if let Some(op) = low_prec_op {
            let attrs = std::mem::take(&mut binary.attrs);
            let left = take_expr(&mut *binary.left);
            let right = take_expr(&mut *binary.right);
            let left = Box::new(Expr::Verbatim(quote_spanned!(left.span() => (#left))));
            let right = Box::new(Expr::Verbatim(quote_spanned!(right.span() => (#right))));
            let bin = ExprBinary { attrs, op, left, right };
            *expr = Expr::Binary(bin);
        } else if let Some(imply) = ply {
            let attrs = std::mem::take(&mut binary.attrs);
            let func =
                Box::new(Expr::Verbatim(quote_spanned_builtin!(builtin, span => #builtin::imply)));
            let paren_token = Paren { span: into_spans(span) };
            let mut args = Punctuated::new();
            if imply {
                // imply `left ==> right`
                args.push(take_expr(&mut *binary.left));
                args.push(take_expr(&mut *binary.right));
            } else {
                // exply `left <== right` (flip the arguments)
                args.push(take_expr(&mut *binary.right));
                args.push(take_expr(&mut *binary.left));
            }
            *expr = Expr::Call(ExprCall { attrs, func, paren_token, args });
        } else if verus_eq {
            let attrs = std::mem::take(&mut binary.attrs);
            let func = match binary.op {
                BinOp::BigEq(_) | BinOp::BigNe(_) => Box::new(Expr::Verbatim(
                    quote_spanned_builtin!(builtin, span => #builtin::equal),
                )),
                BinOp::ExtEq(_) | BinOp::ExtNe(_) => Box::new(Expr::Verbatim(
                    quote_spanned_builtin!(builtin, span => #builtin::ext_equal),
                )),
                BinOp::ExtDeepEq(_) | BinOp::ExtDeepNe(_) => Box::new(Expr::Verbatim(
                    quote_spanned_builtin!(builtin, span => #builtin::ext_equal_deep),
                )),
                _ => unreachable!(),
            };
            let eq = match binary.op {
                BinOp::BigEq(_) | BinOp::ExtEq(_) | BinOp::ExtDeepEq(_) => true,
                BinOp::BigNe(_) | BinOp::ExtNe(_) | BinOp::ExtDeepNe(_) => false,
                _ => unreachable!(),
            };
            let paren_token = Paren { span: into_spans(span) };
            let mut args = Punctuated::new();
            args.push(take_expr(&mut *binary.left));
            args.push(take_expr(&mut *binary.right));
            let call = Expr::Call(ExprCall { attrs, func, paren_token, args });
            if eq {
                *expr = call;
            } else {
                *expr = Expr::Verbatim(quote_spanned!(span => ! #call));
            }
        } else if self.use_spec_traits && self.inside_ghost > 0 {
            let attrs = &binary.attrs;
            let left = &binary.left;
            let right = &binary.right;
            match binary.op {
                BinOp::Eq(..) => {
                    *expr =
                        quote_verbatim!(builtin, span, attrs => #builtin::spec_eq(#left, #right));
                }
                BinOp::Ne(..) => {
                    *expr =
                        quote_verbatim!(builtin, span, attrs => ! #builtin::spec_eq(#left, #right));
                }
                BinOp::Le(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_le(#right));
                }
                BinOp::Lt(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_lt(#right));
                }
                BinOp::Ge(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_ge(#right));
                }
                BinOp::Gt(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_gt(#right));
                }
                BinOp::Add(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_add(#right));
                }
                BinOp::Sub(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_sub(#right));
                }
                BinOp::Mul(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_mul(#right));
                }
                BinOp::Div(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_euclidean_div(#right));
                }
                BinOp::Rem(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_euclidean_mod(#right));
                }
                BinOp::BitAnd(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_bitand(#right));
                }
                BinOp::BitOr(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_bitor(#right));
                }
                BinOp::BitXor(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_bitxor(#right));
                }
                BinOp::Shl(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_shl(#right));
                }
                BinOp::Shr(..) => {
                    let left = quote_spanned! { left.span() => (#left) };
                    *expr = quote_verbatim!(span, attrs => #left.spec_shr(#right));
                }
                _ => {
                    // nothing to do
                }
            }
        }

        true
    }

    /// Handle `as` casts. These need to turn into `spec_cast_integer` calls in spec contexts.
    fn handle_cast(&mut self, expr: &mut Expr) -> bool {
        let Expr::Cast(_) = expr else {
            return false;
        };

        self.visit_expr_with_arith(expr, InsideArith::Widen);

        let Expr::Cast(cast) = &*expr else {
            unreachable!();
        };
        let do_replace = self.use_spec_traits && self.inside_ghost > 0 && !is_ptr_type(&cast.ty);

        if do_replace {
            let Expr::Cast(cast) = take_expr(expr) else {
                unreachable!();
            };
            let span = cast.span();
            let src = cast.expr;
            let attrs = cast.attrs;
            let ty = cast.ty;
            *expr = quote_verbatim!(builtin, span, attrs => #builtin::spec_cast_integer::<_, #ty>(#src));
        } else {
            if is_probably_nat_or_int_type(&cast.ty) {
                *expr = Expr::Verbatim(
                    quote_spanned!(expr.span() => compile_error!("The Verus types 'nat' and 'int' can only be used in ghost code (e.g., in a 'spec' or 'proof' function, inside a 'proof' block, or when assigning to a 'ghost' or 'tracked' variable)")),
                );
            }
        }

        true
    }

    /// Handle integer literals.
    fn handle_lit(&mut self, expr: &mut Expr) -> bool {
        let Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs }) = expr else {
            return false;
        };

        if self.use_spec_traits && self.inside_ghost > 0 && self.inside_type == 0 {
            let span = lit.span();
            let n = lit.base10_digits().to_string();
            if lit.suffix() == "" {
                match self.inside_arith {
                    InsideArith::None => {
                        // We don't know which integer type to use,
                        // so defer the decision to type inference.
                        *expr = quote_verbatim!(builtin, span, attrs => #builtin::spec_literal_integer(#n));
                    }
                    InsideArith::Widen if n.starts_with("-") => {
                        // Use int inside +, -, etc., since these promote to int anyway
                        *expr =
                            quote_verbatim!(builtin, span, attrs => #builtin::spec_literal_int(#n));
                    }
                    InsideArith::Widen => {
                        // Use int inside +, -, etc., since these promote to int anyway
                        *expr =
                            quote_verbatim!(builtin, span, attrs => #builtin::spec_literal_nat(#n));
                    }
                    InsideArith::Fixed => {
                        // We generally won't want int/nat literals for bitwise ops,
                        // so use Rust's native integer literals
                    }
                }
            } else if lit.suffix() == "int" {
                *expr = quote_verbatim!(builtin, span, attrs => #builtin::spec_literal_int(#n));
            } else if lit.suffix() == "nat" {
                *expr = quote_verbatim!(builtin, span, attrs => #builtin::spec_literal_nat(#n));
            } else {
                // Has a native Rust integer suffix, so leave it as a native Rust literal
            }
        }

        true
    }

    /// Handle `assume` statements. Automatically wrap them in a proof block.
    fn handle_assume(&mut self, expr: &mut Expr) -> bool {
        let Expr::Assume(_) = expr else {
            return false;
        };

        self.inside_ghost += 1;
        self.visit_expr_with_arith(expr, InsideArith::None);
        self.inside_ghost -= 1;

        let Expr::Assume(assume) = take_expr(expr) else { unreachable!() };

        let span = assume.assume_token.span;
        let arg = assume.expr;
        let attrs = assume.attrs;
        *expr = quote_verbatim!(builtin, span, attrs => #builtin::assume_(#arg));

        self.auto_proof_block(expr, span);

        true
    }

    /// Handle `assert` statements. Automatically wrap them in a proof block.
    fn handle_assert(&mut self, expr: &mut Expr) -> bool {
        let Expr::Assert(_) = expr else {
            return false;
        };

        self.inside_ghost += 1;
        self.visit_expr_with_arith(expr, InsideArith::None);
        self.inside_ghost -= 1;

        let Expr::Assert(assert) = take_expr(expr) else { unreachable!() };

        let span = assert.assert_token.span;
        let arg = assert.expr;
        let attrs = assert.attrs;

        if let Some(prover) = &assert.prover {
            let prover_id = prover.1.to_string();
            match prover_id.as_str() {
                "compute" => {
                    if assert.body.is_some() {
                        *expr = quote_verbatim!(span, attrs => compile_error!("the 'compute' prover does not support a body"));
                    } else if assert.requires.is_some() {
                        *expr = quote_verbatim!(span, attrs => compile_error!("the 'compute' prover does not support a 'requires' clause"));
                    } else {
                        *expr = Expr::Verbatim(
                            quote_spanned_builtin!(builtin, span => #builtin::assert_by_compute(#arg)),
                        );
                    }
                }
                "compute_only" => {
                    if assert.body.is_some() {
                        *expr = quote_verbatim!(span, attrs => compile_error!("the 'compute_only' prover does not support a body"));
                    } else if assert.requires.is_some() {
                        *expr = quote_verbatim!(span, attrs => compile_error!("the 'compute_only' prover does not support a 'requires' clause"));
                    } else {
                        *expr = Expr::Verbatim(
                            quote_spanned_builtin!(builtin, span => #builtin::assert_by_compute_only(#arg)),
                        );
                    }
                }
                "bit_vector" | "nonlinear_arith" => {
                    let mut block = if let Some(block) = assert.body {
                        *block
                    } else {
                        Block {
                            brace_token: token::Brace { span: into_spans(span) },
                            stmts: vec![],
                        }
                    };
                    let mut stmts: Vec<Stmt> = Vec::new();
                    if let Some(Requires { token, exprs }) = &assert.requires {
                        stmts.push(Stmt::Expr(
                            Expr::Verbatim(
                                quote_spanned_builtin!(builtin, token.span => #builtin::requires([#exprs])),
                            ),
                            Some(Semi { spans: [token.span] }),
                        ));
                    }
                    stmts.push(Stmt::Expr(
                        Expr::Verbatim(
                            quote_spanned_builtin!(builtin, span => #builtin::ensures(#arg)),
                        ),
                        Some(Semi { spans: [span] }),
                    ));
                    block.stmts.splice(0..0, stmts);
                    let assert_x_by: Expr = if prover_id == "bit_vector" {
                        quote_verbatim!(builtin, span, attrs => #builtin::assert_bitvector_by(#block))
                    } else {
                        quote_verbatim!(builtin, span, attrs => #builtin::assert_nonlinear_by(#block))
                    };
                    *expr = Expr::Verbatim(quote_spanned!(span => {#assert_x_by}));
                }
                _ => {
                    *expr = quote_verbatim!(span, attrs => compile_error!("unknown prover name for assert-by (supported provers: 'compute_only', 'compute', 'bit_vector', and 'nonlinear_arith')"));
                }
            }
        } else if let Some(block) = &assert.body {
            // assert-by
            if assert.requires.is_some() {
                *expr = quote_verbatim!(span, attrs => compile_error!("the 'requires' clause is only used with the 'bit_vector' and 'nonlinear_arith' solvers (use `by(bit_vector)` or `by(nonlinear_arith)"));
            } else {
                *expr =
                    quote_verbatim!(builtin, span, attrs => {#builtin::assert_by(#arg, #block);});
            }
        } else {
            // Normal 'assert'
            *expr = quote_verbatim!(builtin, span, attrs => #builtin::assert_(#arg));
        }

        self.auto_proof_block(expr, span);

        true
    }

    /// Handle `assert forall` statements. Automatically wrap them in a proof block.
    fn handle_assert_forall(&mut self, expr: &mut Expr) -> bool {
        let Expr::AssertForall(_) = expr else {
            return false;
        };

        self.inside_ghost += 1;
        self.visit_expr_with_arith(expr, InsideArith::None);
        self.inside_ghost -= 1;

        let Expr::AssertForall(assert) = take_expr(expr) else { unreachable!() };
        let span = assert.assert_token.span;
        let mut arg = assert.expr;
        match self.extract_quant_triggers(assert.attrs, span) {
            Ok(ExtractQuantTriggersFound::Auto) => {
                arg = Box::new(Expr::Verbatim(
                    quote_spanned!(arg.span() => #[verus::internal(auto_trigger)] #arg),
                ));
            }
            Ok(ExtractQuantTriggersFound::AllTriggers) => {
                arg = Box::new(Expr::Verbatim(
                    quote_spanned!(arg.span() => #[verus::internal(all_triggers)] #arg),
                ));
            }
            Ok(ExtractQuantTriggersFound::Triggers(tuple)) => {
                arg = Box::new(Expr::Verbatim(
                    quote_spanned_builtin!(builtin, span => #builtin::with_triggers(#tuple, #arg)),
                ));
            }
            Ok(ExtractQuantTriggersFound::None) => {}
            Err(err_expr) => {
                *expr = err_expr;
                return true;
            }
        }
        let inputs = assert.inputs;
        let mut block = assert.body;
        let mut stmts: Vec<Stmt> = Vec::new();
        if let Some((_, rhs)) = assert.implies {
            stmts.push(stmt_with_semi!(builtin, span => #builtin::requires(#arg)));
            stmts.push(stmt_with_semi!(builtin, span => #builtin::ensures(#rhs)));
        } else {
            stmts.push(stmt_with_semi!(builtin, span => #builtin::ensures(#arg)));
        }
        block.stmts.splice(0..0, stmts);
        *expr = Expr::Verbatim(
            quote_spanned_builtin!(builtin, span => {#builtin::assert_forall_by(|#inputs| #block);}),
        );

        self.auto_proof_block(expr, span);

        true
    }

    /// Handle `reveal` and `hide` statements.
    /// Automatically `reveal` statements in a proof block.
    fn handle_reveal_hide(&mut self, expr: &mut Expr) -> bool {
        let Expr::RevealHide(_) = expr else {
            return false;
        };

        self.inside_ghost += 1;
        self.visit_expr_with_arith(expr, InsideArith::None);
        self.inside_ghost -= 1;

        let Expr::RevealHide(reveal) = take_expr(expr) else { unreachable!() };

        let span = reveal
            .reveal_token
            .map(|x| x.span)
            .or(reveal.reveal_with_fuel_token.map(|x| x.span))
            .or(reveal.hide_token.map(|x| x.span))
            .expect("span for Reveal");
        let reveal_fuel = if let Some((_, fuel)) = reveal.fuel {
            quote_spanned!(span => #fuel)
        } else if reveal.hide_token.is_some() {
            quote_spanned!(span => 0)
        } else {
            quote_spanned!(span => 1)
        };
        let is_hide = reveal.hide_token.is_some();
        let path = reveal.path;
        let expr_replacement = if path.path.segments.first().map(|x| x.ident.to_string())
            == Some("Self".to_owned())
            || path.qself.as_ref().and_then(|qself| match &*qself.ty {
                Type::Path(qself_ty_path) => {
                    qself_ty_path.path.segments.first().map(|x| x.ident.to_string())
                }
                _ => None,
            }) == Some("Self".to_owned())
        {
            Expr::Verbatim(
                quote_spanned!(span => { compile_error!("Self is not supported in reveal/hide, use the type name instead, or <T as X> for functions in trait impls") }),
            )
        } else {
            Expr::Verbatim(
                quote_spanned_builtin!(builtin, span => #builtin::reveal_hide_({#[verus::internal(reveal_fn)] fn __VERUS_REVEAL_INTERNAL__() { #builtin::reveal_hide_internal_path_(#path) } __VERUS_REVEAL_INTERNAL__}, #reveal_fuel) ),
            )
        };
        if is_hide {
            *expr = self.maybe_erase_expr(span, expr_replacement);
        } else {
            *expr = expr_replacement;
        }

        if !is_hide {
            self.auto_proof_block(expr, span);
        }

        true
    }

    fn auto_proof_block(&mut self, expr: &mut Expr, span: Span) {
        if self.inside_ghost == 0 {
            let inner = take_expr(expr);
            *expr = self.maybe_erase_expr(
                span,
                Expr::Verbatim(
                    quote_spanned!(span => #[verifier::proof_block] /* vattr */ { #[verus::internal(const_header_wrapper)]||{#inner}; } ),
                ),
            );
        }
    }

    /// Handle:
    ///   - proof { ... } blocks
    ///   - Ghost(...)
    ///   - Tracked(...)
    fn handle_mode_blocks(&mut self, expr: &mut Expr) -> bool {
        let mode_block = match expr {
            Expr::Unary(ExprUnary { op: UnOp::Proof(..), .. }) => (false, false),
            Expr::Call(ExprCall { func, args, .. }) => match &**func {
                Expr::Path(path) if path.qself.is_none() && args.len() == 1 => {
                    if path_is_ident(&path.path, "Ghost") {
                        (true, false)
                    } else if path_is_ident(&path.path, "Tracked") {
                        (true, true)
                    } else {
                        return false;
                    }
                }
                _ => {
                    return false;
                }
            },
            _ => {
                return false;
            }
        };

        self.inside_ghost += 1;
        self.visit_expr_with_arith(expr, InsideArith::None);
        self.inside_ghost -= 1;

        let is_inside_ghost = self.inside_ghost > 0;

        if let Expr::Call(call) = expr {
            let (_, is_tracked) = mode_block;
            let span = call.span();
            if is_tracked {
                // Tracked(...)
                let inner = take_expr(&mut call.args[0]);
                *expr = Expr::Verbatim(if self.erase_ghost.erase() {
                    quote_spanned!(span => Tracked::assume_new_fallback(|| unreachable!()))
                } else if is_inside_ghost {
                    quote_spanned_builtin!(builtin, span => #builtin::Tracked::new(#inner))
                } else {
                    quote_spanned_builtin!(builtin, span => #[verifier::ghost_wrapper] /* vattr */ #builtin::tracked_exec(#[verifier::tracked_block_wrapped] /* vattr */ #inner))
                });
            } else {
                // Ghost(...)
                let inner = take_expr(&mut call.args[0]);
                *expr = Expr::Verbatim(if self.erase_ghost.erase() {
                    quote_spanned!(span => Ghost::assume_new_fallback(|| unreachable!()))
                } else if is_inside_ghost {
                    quote_spanned_builtin!(builtin, span => #builtin::Ghost::new(#inner))
                } else {
                    quote_spanned_builtin!(builtin, span => #[verifier::ghost_wrapper] /* vattr */ #builtin::ghost_exec(#[verifier::ghost_block_wrapped] /* vattr */ #inner))
                });
            }
        } else if let Expr::Unary(unary) = expr {
            let span = unary.span();
            match (mode_block, &*unary.expr) {
                ((false, _), Expr::Block(..)) => {
                    // proof { ... }
                    let mut inner = take_expr(&mut *unary.expr);
                    if self.inside_const {
                        inner = Expr::Verbatim(
                            quote_spanned!(span => {#[verus::internal(const_header_wrapper)] ||/* vattr */{#inner};}),
                        );
                    }
                    let e = if is_inside_ghost {
                        quote_spanned!(span => #[verifier::proof_in_spec] /* vattr */ #inner)
                    } else {
                        quote_spanned!(span => #[verifier::proof_block] /* vattr */ #inner)
                    };
                    *expr = self.maybe_erase_expr(span, Expr::Verbatim(e));
                }
                _ => {
                    *expr = Expr::Verbatim(
                        quote_spanned!(span => compile_error!("unexpected proof block")),
                    );
                }
            }
        }

        true
    }

    /// Handle closures
    fn handle_closures(&mut self, expr: &mut Expr) -> bool {
        if !matches!(expr, Expr::Closure(..)) {
            return false;
        };

        self.visit_expr_with_arith(expr, InsideArith::None);

        let Expr::Closure(mut clos) = take_expr(expr) else {
            unreachable!();
        };

        let is_proof_fn = clos.proof_fn.is_some();
        let is_spec_fn = self.inside_ghost > 0 && !is_proof_fn;
        assert!(is_proof_fn || clos.options.is_none());
        if is_spec_fn {
            let span = clos.span();
            if clos.requires.is_some() || clos.ensures.is_some() {
                let err = "ghost closures cannot have requires/ensures";
                *expr = Expr::Verbatim(quote_spanned!(span => compile_error!(#err)));
            } else {
                *expr = Expr::Verbatim(quote_spanned_builtin!(builtin, span =>
                    #builtin::closure_to_fn_spec(#clos)
                ));
            }
        } else if is_proof_fn && self.inside_ghost == 0 {
            let span = clos.span();
            let err = "proof_fn closures are only allowed in proof mode";
            *expr = Expr::Verbatim(quote_spanned!(span => compile_error!(#err)));
        } else {
            assert!(is_proof_fn == (self.inside_ghost > 0));
            let (ret_pat, ret_tracked) = match &mut clos.output {
                ReturnType::Default => (None, false),
                ReturnType::Type(_, ref mut tracked, ref mut ret_opt, ty) => {
                    self.visit_type_mut(ty);
                    if !is_proof_fn && tracked.is_some() {
                        *expr = Expr::Verbatim(quote_spanned!(tracked.unwrap().span() =>
                            compile_error!("'tracked' not supported here")
                        ));
                        return true;
                    }
                    let is_tracked = tracked.is_some();
                    *tracked = None;
                    match std::mem::take(ret_opt) {
                        None => (None, is_tracked),
                        Some(ret) => (Some((ret.1.clone(), ty.clone())), is_tracked),
                    }
                }
            };
            let requires = self.take_ghost(&mut clos.requires);
            let ensures = self.take_ghost(&mut clos.ensures);
            let opts = match ProofFnOptions::parse_opt(&clos.options) {
                Ok(opts) => opts,
                Err(err) => {
                    *expr = Expr::Verbatim(quote_spanned!(clos.span() =>
                        compile_error!(#err)
                    ));
                    return true;
                }
            };
            if opts.req_ens.is_some() && (requires.is_some() || ensures.is_some()) {
                *expr = Expr::Verbatim(quote_spanned!(clos.span() =>
                    compile_error!("ReqEns and requires/ensures cannot be used together")
                ));
                return true;
            }
            let mut stmts: Vec<Stmt> = Vec::new();
            // TODO: wrap specs inside ghost blocks
            self.inside_ghost += 1;
            if let Some(t) = &opts.req_ens {
                let mut elems = Punctuated::new();
                for input in &clos.inputs {
                    let arg = match &input.pat {
                        Pat::Type(p) => &p.pat,
                        p => p,
                    };
                    elems.push(Expr::Verbatim(quote_spanned!(clos.span() => #arg)));
                }
                let paren_token = Paren { span: into_spans(clos.span()) };
                let args = Expr::Tuple(ExprTuple { attrs: vec![], paren_token, elems });
                stmts.push(stmt_with_semi!(builtin, clos.span() =>
                    #builtin::requires([<#t as #builtin::ProofFnReqEnsDef<_, _>>::req(#args)])
                ));
                stmts.push(stmt_with_semi!(builtin, clos.span() =>
                    #builtin::ensures(|ret| [<#t as #builtin::ProofFnReqEnsDef<_, _>>::ens(#args, ret)])
                ));
            }
            if let Some(Requires { token, mut exprs }) = requires {
                for expr in exprs.exprs.iter_mut() {
                    self.visit_expr_mut(expr);
                }
                stmts.push(stmt_with_semi!(
                    builtin, token.span => #builtin::requires([#exprs])));
            }
            if let Some(Ensures { token, mut exprs, attrs }) = ensures {
                if attrs.len() > 0 {
                    let err = "outer attributes only allowed on function's ensures";
                    let expr = Expr::Verbatim(quote_spanned!(token.span => compile_error!(#err)));
                    stmts.push(Stmt::Expr(expr, Some(Semi { spans: [token.span] })));
                } else {
                    for expr in exprs.exprs.iter_mut() {
                        self.visit_expr_mut(expr);
                    }
                    if let Some((p, ty)) = ret_pat {
                        stmts.push(stmt_with_semi!(
                            builtin, token.span => #builtin::ensures(|#p: #ty| [#exprs])));
                    } else {
                        stmts.push(stmt_with_semi!(
                            builtin, token.span => #builtin::ensures([#exprs])));
                    }
                }
            }
            self.inside_ghost -= 1;
            if stmts.len() > 0 {
                if let Expr::Block(block) = &mut *clos.body {
                    block.block.stmts.splice(0..0, stmts);
                } else {
                    panic!("parser requires Expr::Block for requires/ensures")
                }
            }
            let span = clos.span();
            let inputs = clos.inputs.clone();
            clos.proof_fn = None;
            clos.options = None;
            for input in clos.inputs.iter_mut() {
                input.tracked_token = None;
            }
            let mut new_expr = Expr::Closure(clos);
            if is_proof_fn {
                let (usage, _req_ens, copy, send, sync) = opts.to_types(span);
                let arg_modes =
                    proof_fn_tracks_to_type(span, inputs.iter().map(|x| x.tracked_token.is_some()));
                let ret_mode = proof_fn_track_to_type(span, ret_tracked);
                new_expr = Expr::Verbatim(quote_spanned_builtin!(builtin, span =>
                    #builtin::closure_to_fn_proof::<#usage, #copy, #send, #sync, #arg_modes, #ret_mode, _, _, _>(#new_expr)
                ));
                if let Some(t) = &opts.req_ens {
                    new_expr = Expr::Verbatim(quote_spanned_vstd!(vstd, span =>
                        #vstd::function::proof_fn_as_req_ens::<#t, #usage, _, #copy, #send, #sync, _, _, _, _>(#new_expr)
                    ));
                }
            }
            *expr = new_expr;
        }

        true
    }

    fn add_loop_specs(
        &mut self,
        stmts: &mut Vec<Stmt>,
        invariant_except_breaks: Option<InvariantExceptBreak>,
        invariants: Option<Invariant>,
        invariant_ensures: Option<InvariantEnsures>,
        ensures: Option<Ensures>,
        decreases: Option<Decreases>,
    ) {
        // TODO: wrap specs inside ghost blocks
        self.inside_ghost += 1;
        let old_style = if invariant_ensures.is_some() {
            #[cfg(verus_keep_ghost)]
            proc_macro::Diagnostic::spanned(
                invariant_ensures.span().unwrap(),
                proc_macro::Level::Warning,
                "invariant_ensures is deprecated - \
                    instead of 'invariant/invariant_ensures/ensures', \
                    use 'invariant_except_break/invariant/ensures'",
            )
            .emit();
            true
        } else {
            false
        };
        if let Some(InvariantExceptBreak { token, exprs }) = invariant_except_breaks {
            if exprs.exprs.len() > 0 {
                stmts.push(stmt_with_semi!(builtin, token.span =>
                    #builtin::invariant_except_break([#exprs])
                ));
            }
        }
        if let Some(Invariant { token, exprs }) = invariants {
            if exprs.exprs.len() > 0 && old_style {
                stmts.push(stmt_with_semi!(builtin, token.span =>
                    #builtin::invariant_except_break([#exprs])
                ));
            } else if exprs.exprs.len() > 0 {
                stmts.push(stmt_with_semi!(builtin, token.span => #builtin::invariant([#exprs])));
            }
        }
        if let Some(InvariantEnsures { token, exprs }) = invariant_ensures {
            if exprs.exprs.len() > 0 {
                stmts.push(stmt_with_semi!(builtin, token.span => #builtin::invariant([#exprs])));
            }
        }
        if let Some(Ensures { token, exprs, attrs }) = ensures {
            if attrs.len() > 0 {
                let err = "outer attributes only allowed on function's ensures";
                let expr = Expr::Verbatim(quote_spanned!(token.span => compile_error!(#err)));
                stmts.push(Stmt::Expr(expr, Some(Semi { spans: [token.span] })));
            } else if exprs.exprs.len() > 0 {
                stmts.push(stmt_with_semi!(builtin, token.span => #builtin::ensures([#exprs])));
            }
        }
        if let Some(Decreases { token, exprs }) = decreases {
            for expr in exprs.exprs.iter() {
                if matches!(expr, Expr::Tuple(..)) {
                    let err = "decreases cannot be a tuple; use `decreases x, y` rather than `decreases (x, y)`";
                    let expr = Expr::Verbatim(quote_spanned!(token.span => compile_error!(#err)));
                    stmts.push(Stmt::Expr(expr, Some(Semi { spans: [token.span] })));
                }
            }
            stmts.push(stmt_with_semi!(builtin, token.span => #builtin::decreases((#exprs))));
        }
        self.inside_ghost -= 1;
    }

    fn desugar_for_loop(&mut self, for_loop: syn_verus::ExprForLoop) -> Expr {
        // The regular Rust for-loop doesn't give us direct access to the iterator,
        // which we need for writing invariants.
        // Therefore, rather than letting Rust desugar a for-loop into a loop with a break,
        // we desugar the for-loop into a loop with a break here.
        // (See https://doc.rust-lang.org/reference/expressions/loop-expr.html for the
        // official definition of the desugaring that we follow.)
        // Specifically, we desugar:
        //  'label: for x in y: e invariant inv { body }
        // into:
        //  {
        //      #[allow(non_snake_case)]
        //      let VERUS_iter = e;
        //      #[allow(non_snake_case)]
        //      let VERUS_loop_result = match ::core::iter::IntoIterator::into_iter(VERUS_iter) {
        //          #[allow(non_snake_case)]
        //          mut VERUS_exec_iter => {
        //              #[allow(non_snake_case)]
        //              let ghost mut y = ::vstd::pervasive::ForLoopGhostIteratorNew::ghost_iter(
        //                  &VERUS_exec_iter);
        //              'label: loop
        //                  invariant
        //                      ::vstd::pervasive::ForLoopGhostIterator::exec_invariant(&y,
        //                          &VERUS_exec_iter),
        //                      ::vstd::pervasive::ForLoopGhostIterator::ghost_invariant(&y,
        //                          builtin::infer_spec_for_loop_iter(
        //                              &::vstd::pervasive::ForLoopGhostIteratorNew::ghost_iter(
        //                                  &::core::iter::IntoIterator::into_iter(VERUS_iter)),
        //                              &::vstd::pervasive::ForLoopGhostIteratorNew::ghost_iter(
        //                                  &::core::iter::IntoIterator::into_iter(e)),
        //                          )),
        //                      { let x =
        //                          ::vstd::pervasive::ForLoopGhostIterator::ghost_peek_next(&y)
        //                          .unwrap_or(vstd::pervasive::arbitrary());
        //                        inv },
        //                  ensures
        //                      ::vstd::pervasive::ForLoopGhostIterator::ghost_ensures(&y),
        //                  decreases
        //                      ::vstd::pervasive::ForLoopGhostIterator::ghost_decrease(&y)
        //                      .unwrap_or(vstd::pervasive::arbitrary()),
        //
        //              {
        //                  #[allow(non_snake_case)]
        //                  let mut VERUS_loop_next;
        //                  match ::core::iter::Iterator::next(&mut VERUS_exec_iter) {
        //                      ::core::option::Option::Some(VERUS_loop_val) => {
        //                          VERUS_loop_next = VERUS_loop_val;
        //                      }
        //                      ::core::option::Option::None => break,
        //                  };
        //                  let x = VERUS_loop_next;
        //                  let () = { body };
        //                  proof { y = ::vstd::pervasive::ForLoopGhostIterator::ghost_advance(
        //                      &y, &VERUS_exec_iter); }
        //              }
        //          }
        //      };
        //      VERUS_loop_result
        //  }
        // Note that "continue" and labels are not yet supported;
        // continue would also need to call ghost_advance.
        let span = for_loop.span();

        let syn_verus::ExprForLoop {
            mut attrs,
            label,
            for_token,
            pat,
            in_token,
            expr_name,
            expr,
            invariant,
            mut decreases,
            body,
        } = for_loop;

        let no_loop_invariant = attrs.iter().position(|attr| {
            attr.path().segments.len() == 2
                && attr.path().segments[0].ident.to_string() == "verifier"
                && attr.path().segments[1].ident.to_string() == "no_loop_invariant"
        });
        if let Some(i) = no_loop_invariant {
            attrs.remove(i);
        }
        // Note: in principle, the automatically generated loop invariant
        // should always succeed.  In case something goes unexpectedly wrong, though,
        // give people a reasonable way to disable it:
        let no_auto_loop_invariant = attrs.iter().position(|attr| {
            attr.path().segments.len() == 2
                && attr.path().segments[0].ident.to_string() == "verifier"
                && attr.path().segments[1].ident.to_string() == "no_auto_loop_invariant"
        });
        if let Some(i) = no_auto_loop_invariant {
            attrs.remove(i);
        }

        if !self.erase_ghost.keep() || self.inside_external_code > 0 {
            return Expr::ForLoop(syn_verus::ExprForLoop {
                attrs,
                label,
                for_token,
                pat,
                in_token,
                expr_name: None,
                expr,
                invariant: None,
                decreases: None,
                body,
            });
        }

        attrs.push(mk_verus_attr(span, quote! { for_loop }));
        let exec_inv_msg = "For-loop iterator invariant failed. \
            This may indicate a bug in the definition of the ForLoopGhostIterator. \
            You might try using a `loop` instead of a `for`.";
        let ghost_inv_msg = "Automatically generated loop invariant failed. \
            You can disable the automatic generation by adding \
            #[verifier::no_auto_loop_invariant] \
            to the loop. \
            You might also try storing the loop expression in a variable outside the loop \
            (e.g. `let e = 0..10; for x in e { ... }`).";
        let print_hint: Expr = if expr_name.is_some() {
            Expr::Verbatim(quote_spanned!(expr.span() => false))
        } else {
            Expr::Verbatim(quote_spanned!(expr.span() => true))
        };

        let x_exec_iter = Ident::new("VERUS_exec_iter", span);
        let x_ghost_iter = if let Some(x_ghost_iter_box) = expr_name {
            let (x_ghost_iter, _) = *x_ghost_iter_box;
            x_ghost_iter
        } else {
            Ident::new("VERUS_ghost_iter", span)
        };
        let mut stmts: Vec<Stmt> = Vec::new();
        let expr_inv = expr.clone();
        //              ::vstd::pervasive::ForLoopGhostIterator::exec_invariant(&y, &VERUS_exec_iter),
        //              ::vstd::pervasive::ForLoopGhostIterator::ghost_invariant(&y,
        //                  builtin::infer_spec_for_loop_iter(
        //                      &::vstd::pervasive::ForLoopGhostIteratorNew::ghost_iter(
        //                          &::core::iter::IntoIterator::into_iter(VERUS_iter)),
        //                      &::vstd::pervasive::ForLoopGhostIteratorNew::ghost_iter(
        //                          &::core::iter::IntoIterator::into_iter(e)),
        //                  )),
        let exec_inv: Expr = Expr::Verbatim(quote_spanned_vstd!(vstd, expr.span() =>
            #[verifier::custom_err(#exec_inv_msg)]
            #vstd::pervasive::ForLoopGhostIterator::exec_invariant(&#x_ghost_iter, &#x_exec_iter)
        ));
        let ghost_inv: Expr = Expr::Verbatim(quote_spanned_vstd!(vstd, expr.span() =>
            #[verifier::custom_err(#ghost_inv_msg)]
            #vstd::pervasive::ForLoopGhostIterator::ghost_invariant(&#x_ghost_iter,
                builtin::infer_spec_for_loop_iter(
                    &#vstd::pervasive::ForLoopGhostIteratorNew::ghost_iter(
                        &::core::iter::IntoIterator::into_iter(VERUS_iter)),
                    &#vstd::pervasive::ForLoopGhostIteratorNew::ghost_iter(
                        &::core::iter::IntoIterator::into_iter(#expr_inv)),
                    #print_hint,
                ))
        ));
        let invariant_for = if let Some(mut invariant) = invariant {
            for inv in &mut invariant.exprs.exprs {
                *inv = Expr::Verbatim(quote_spanned_vstd!(vstd, inv.span() => {
                    let #pat =
                        #vstd::pervasive::ForLoopGhostIterator::ghost_peek_next(&#x_ghost_iter)
                        .unwrap_or(#vstd::pervasive::arbitrary());
                    #inv
                }));
            }
            if no_loop_invariant.is_none() {
                invariant.exprs.exprs.insert(0, exec_inv);
                if no_auto_loop_invariant.is_none() {
                    invariant.exprs.exprs.insert(1, ghost_inv);
                }
            }
            Some(Invariant { token: Token![invariant](span), exprs: invariant.exprs })
        } else if no_loop_invariant.is_none() && no_auto_loop_invariant.is_none() {
            Some(parse_quote_spanned!(span => invariant #exec_inv, #ghost_inv,))
        } else if no_loop_invariant.is_none() && no_auto_loop_invariant.is_some() {
            Some(parse_quote_spanned!(span => invariant #exec_inv,))
        } else {
            None
        };
        if let Some(decreases) = &mut decreases {
            for expr in &mut decreases.exprs.exprs {
                *expr = Expr::Verbatim(quote_spanned_vstd!(vstd, expr.span() => {
                    let #pat =
                        #vstd::pervasive::ForLoopGhostIterator::ghost_peek_next(&#x_ghost_iter)
                        .unwrap_or(#vstd::pervasive::arbitrary());
                    #expr
                }));
            }
        } else {
            attrs.push(mk_verus_attr(span, quote! { auto_decreases }));
            decreases = Some(parse_quote_spanned_vstd!(vstd, span =>
                decreases
                    #vstd::pervasive::ForLoopGhostIterator::ghost_decrease(&#x_ghost_iter)
                    .unwrap_or(#vstd::pervasive::arbitrary()),
            ))
        }
        // REVIEW: we might also want no_auto_loop_invariant to suppress the ensures,
        // but at the moment, user-supplied ensures aren't supported, so this would be hard to use.
        let ensure = if no_loop_invariant.is_none() {
            Some(parse_quote_spanned_vstd!(vstd, span =>
                ensures #vstd::pervasive::ForLoopGhostIterator::ghost_ensures(&#x_ghost_iter),
            ))
        } else {
            None
        };
        self.add_loop_specs(&mut stmts, None, invariant_for, None, ensure, decreases);
        let body_exec = Expr::Verbatim(quote_spanned!(span => {
            #[allow(non_snake_case)]
            let mut VERUS_loop_next;
            match ::core::iter::Iterator::next(&mut #x_exec_iter) {
                ::core::option::Option::Some(VERUS_loop_val) => {
                    VERUS_loop_next = VERUS_loop_val;
                }
                ::core::option::Option::None => break,
            };
            let #pat = VERUS_loop_next;
            let () = #body;
        }));
        let mut body: Block = if no_loop_invariant.is_none() {
            let body_ghost = Expr::Verbatim(quote_spanned_vstd!(vstd, span =>
                #[verifier::proof_block] {
                    #x_ghost_iter = #vstd::pervasive::ForLoopGhostIterator::ghost_advance(
                        &#x_ghost_iter, &#x_exec_iter);
                }
            ));
            parse_quote_spanned!(span => {
                #body_exec
                #body_ghost
            })
        } else {
            parse_quote_spanned!(span => {
                #body_exec
            })
        };
        body.stmts.splice(0..0, stmts);
        let mut loop_expr: ExprLoop = parse_quote_spanned!(span => loop #body);
        loop_expr.label = label;
        loop_expr.attrs = attrs;
        let full_loop: Expr = if no_loop_invariant.is_none() {
            Expr::Verbatim(quote_spanned_vstd!(vstd, span => {
                #[allow(non_snake_case)]
                #[verus::internal(spec)]
                let mut #x_ghost_iter;
                #[verifier::proof_block] {
                    #x_ghost_iter =
                        #vstd::pervasive::ForLoopGhostIteratorNew::ghost_iter(&#x_exec_iter);
                }
                #loop_expr
            }))
        } else {
            Expr::Verbatim(quote_spanned!(span => { #loop_expr }))
        };
        Expr::Verbatim(quote_spanned!(span => {
            #[allow(non_snake_case)]
            let VERUS_iter = #expr;
            #[allow(non_snake_case)]
            let VERUS_loop_result = match ::core::iter::IntoIterator::into_iter(VERUS_iter) {
                #[allow(non_snake_case)]
                mut #x_exec_iter => #full_loop
            };
            VERUS_loop_result
        }))
    }

    fn extract_quant_triggers(
        &mut self,
        inner_attrs: Vec<Attribute>,
        span: Span,
    ) -> Result<ExtractQuantTriggersFound, Expr> {
        let mut triggers: Vec<Expr> = Vec::new();
        for attr in inner_attrs {
            use syn_verus::Meta;
            let trigger: syn_verus::Result<Punctuated<Expr, Token![,]>> = match &attr.meta {
                Meta::Path(_) => Ok(Punctuated::new()),
                Meta::List(list) => {
                    let spec: syn_verus::Result<syn_verus::Specification> =
                        syn_verus::parse2(list.tokens.clone());
                    spec.map(|e| e.exprs)
                }
                Meta::NameValue(_) => Err(syn_verus::Error::new(span, "expected trigger")),
            };
            let path_segments_str =
                attr.path().segments.iter().map(|x| x.ident.to_string()).collect::<Vec<_>>();
            let ident_str = match &path_segments_str[..] {
                [attr_name] => Some(attr_name),
                _ => None,
            };
            match (trigger, ident_str) {
                (Ok(trigger), Some(id)) if id == &"auto" && trigger.len() == 0 => {
                    return Ok(ExtractQuantTriggersFound::Auto);
                }
                (Ok(trigger), Some(id)) if id == &"all_triggers" && trigger.len() == 0 => {
                    return Ok(ExtractQuantTriggersFound::AllTriggers);
                }
                (Ok(trigger), Some(id)) if id == &"trigger" => {
                    let mut exprs = trigger;
                    for expr in exprs.iter_mut() {
                        self.visit_expr_mut(expr);
                    }
                    let tuple = ExprTuple { attrs: vec![], paren_token: Paren(span), elems: exprs };
                    triggers.push(Expr::Tuple(tuple));
                }
                (Err(err), _) => {
                    let span = attr.span();
                    let err = err.to_string();

                    return Err(Expr::Verbatim(quote_spanned!(span => compile_error!(#err))));
                }
                _ => {
                    let span = attr.span();
                    return Err(Expr::Verbatim(
                        quote_spanned!(span => compile_error!("expected trigger")),
                    ));
                }
            }
        }

        Ok(if triggers.len() > 0 {
            let mut elems = Punctuated::new();
            for elem in triggers {
                elems.push(elem);
                elems.push_punct(Token![,](span));
            }
            ExtractQuantTriggersFound::Triggers(ExprTuple {
                attrs: vec![],
                paren_token: Paren(span),
                elems,
            })
        } else {
            ExtractQuantTriggersFound::None
        })
    }

    fn visit_expr_with_arith(&mut self, expr: &mut Expr, arith_mode: InsideArith) {
        if !(self.inside_ghost > 0 && self.erase_ghost.erase()) || self.inside_const {
            let is_inside_arith = self.inside_arith;
            self.inside_arith = arith_mode;
            visit_expr_mut(self, expr);
            self.inside_arith = is_inside_arith;
        }
    }
}

enum ExtractQuantTriggersFound {
    Auto,
    AllTriggers,
    Triggers(ExprTuple),
    None,
}

// For
// assert(false && E::A matches E::A ==> true);
// to preserve && precedence it would turn into
//     if let E::A = E::A { false && true ==> true } else { false && false ==> true }
//
//     assert(v == 4 && x matches E::A { v } ==> v == 4);
//
//     if let E::A { v } = x { v == 4 && true ==> true } else { v == 4 && false ==> true }
//
// For
//     assert(true || E::A matches E::A ==> true);
// to preserve || precedence it would turn into
//     if let E::A = E::A { true } else { false || false ==> true }

impl VisitMut for Visitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        if self.chain_operators(expr)
            || self.closure_quant_operators(expr)
            || self.handle_binary_ops(expr)
            || self.handle_assume(expr)
            || self.handle_assert(expr)
            || self.handle_assert_forall(expr)
            || self.handle_reveal_hide(expr)
            || self.handle_mode_blocks(expr)
            || self.handle_cast(expr)
            || self.handle_lit(expr)
            || self.handle_closures(expr)
            || self.handle_unary_ops(expr)
            || self.handle_big_and_big_or(expr)
            || self.handle_spec_operators(expr)
        {
            return;
        }

        let sub_inside_arith = match expr {
            Expr::Paren(..) | Expr::Block(..) | Expr::Group(..) => self.inside_arith,
            _ => InsideArith::None,
        };
        let sub_assign_to = match expr {
            Expr::Field(..) => self.assign_to,
            _ => false,
        };

        // Recursively call visit_expr_mut
        let is_inside_ghost = self.inside_ghost > 0;
        let is_inside_arith = self.inside_arith;
        let is_assign_to = self.assign_to;
        self.inside_arith = sub_inside_arith;
        self.assign_to = sub_assign_to;
        let assign_left = if let Expr::Assign(assign) = expr {
            let mut left = take_expr(&mut assign.left);
            self.assign_to = true;
            self.visit_expr_mut(&mut left);
            self.assign_to = false;
            Some(left)
        } else {
            None
        };
        if !(is_inside_ghost && self.erase_ghost.erase()) || self.inside_const {
            visit_expr_mut(self, expr);
        }
        if let Expr::Assign(assign) = expr {
            assign.left = Box::new(assign_left.expect("assign_left"));
        }
        self.inside_arith = is_inside_arith;
        self.assign_to = is_assign_to;

        if let Expr::Macro(macro_expr) = expr {
            macro_expr.mac.path.segments.first_mut().map(|x| {
                let ident = x.ident.to_string();
                // NOTE: this is currently hardcoded for
                // open_*_invariant macros, but this could be extended
                // to rewrite other macro names depending on proof vs exec mode.
                if is_inside_ghost
                    && (ident == "open_atomic_invariant" || ident == "open_local_invariant")
                {
                    x.ident = Ident::new((ident + "_in_proof").as_str(), x.span());
                }
            });
        }

        let do_replace = match &expr {
            Expr::ForLoop(..) => true,
            _ => false,
        };
        if do_replace && self.inside_type == 0 {
            match take_expr(expr) {
                Expr::ForLoop(for_loop) => {
                    *expr = self.desugar_for_loop(for_loop);
                }
                _ => panic!("expected to replace expression"),
            }
        }
    }

    fn visit_attribute_mut(&mut self, attr: &mut Attribute) {
        fn path_verifier(
            span: Span,
        ) -> Punctuated<syn_verus::PathSegment, syn_verus::token::PathSep> {
            let mut path_segments = Punctuated::new();
            path_segments.push(syn_verus::PathSegment {
                ident: Ident::new("verifier", span),
                arguments: syn_verus::PathArguments::None,
            });
            path_segments
        }
        fn invalid_attribute(span: Span, trigger: bool) -> Attribute {
            let mut path_segments = path_verifier(span);
            path_segments.push(syn_verus::PathSegment {
                ident: if trigger {
                    Ident::new("invalid_trigger_attribute", span)
                } else {
                    Ident::new("invalid_attribute", span)
                },
                arguments: syn_verus::PathArguments::None,
            });
            let path = Path { leading_colon: None, segments: path_segments };
            Attribute {
                pound_token: token::Pound { spans: [span] },
                style: syn_verus::AttrStyle::Outer,
                bracket_token: token::Bracket { span: into_spans(span) },
                meta: syn_verus::Meta::Path(path),
            }
        }
        if let syn_verus::AttrStyle::Outer = attr.style {
            match &attr.path().segments.iter().map(|x| &x.ident).collect::<Vec<_>>()[..] {
                [attr_name] if attr_name.to_string() == "trigger" => {
                    let mut valid = true;
                    if let syn_verus::Meta::List(list) = &attr.meta {
                        if !list.tokens.is_empty() {
                            *attr = invalid_attribute(attr.span(), true);
                            valid = false;
                        }
                    }
                    if valid {
                        *attr = mk_verus_attr(attr.span(), quote! { trigger });
                    }
                }
                [attr_name] if attr_name.to_string() == "via_fn" => {
                    *attr = mk_verus_attr(attr.span(), quote! { via });
                }
                [attr_name] if attr_name.to_string() == "verifier" => {
                    let span = attr.span();
                    let Ok(parsed) = attr.parse_args_with(
                        Punctuated::<syn_verus::Meta, Token![,]>::parse_terminated,
                    ) else {
                        *attr = invalid_attribute(span, false);
                        return;
                    };
                    match parsed {
                        meta_list if meta_list.len() == 1 => {
                            let (second_segment, nested) = match &meta_list[0] {
                                syn_verus::Meta::List(meta_list) => {
                                    let rest = &meta_list.tokens;
                                    (&meta_list.path.segments[0], Some(quote! { #rest }))
                                }
                                syn_verus::Meta::Path(meta_path) => (&meta_path.segments[0], None),
                                _ => {
                                    *attr = invalid_attribute(span, false);
                                    return;
                                }
                            };
                            let mut path_segments = path_verifier(span);
                            path_segments.push(second_segment.clone());
                            let path = Path { leading_colon: None, segments: path_segments };
                            let meta = if let Some(nested) = nested {
                                syn_verus::Meta::List(syn_verus::MetaList {
                                    path,
                                    delimiter: syn_verus::MacroDelimiter::Paren(token::Paren {
                                        span: into_spans(span),
                                    }),
                                    tokens: quote! { #nested },
                                })
                            } else {
                                syn_verus::Meta::Path(path)
                            };
                            *attr = Attribute {
                                pound_token: token::Pound { spans: [span] },
                                style: syn_verus::AttrStyle::Outer,
                                bracket_token: token::Bracket { span: into_spans(span) },
                                meta,
                            };
                        }
                        _ => {
                            *attr = invalid_attribute(span, false);
                            return;
                        }
                    }
                }
                _ => (),
            }
        }

        if let syn_verus::AttrStyle::Inner(_) = attr.style {
            match &attr.path().segments.iter().map(|x| &x.ident).collect::<Vec<_>>()[..] {
                [attr_name] if attr_name.to_string() == "trigger" => {
                    // process something like: #![trigger f(a, b), g(c, d)]
                    use syn_verus::Meta;
                    match &mut attr.meta {
                        Meta::Path(_) => {}
                        Meta::List(list) => {
                            // list.tokens is f(a, b), g(c, d)
                            // turn this into a tuple (f(a, b), g(c, d)),
                            // parse it into an Expr, visit the Expr, turn the Expr back into tokens,
                            // remove the ( and ).
                            let old_stream = proc_macro::TokenStream::from(list.tokens.clone());
                            let mut tuple_stream = proc_macro::TokenStream::new();
                            let group = proc_macro::Group::new(
                                proc_macro::Delimiter::Parenthesis,
                                old_stream,
                            );
                            tuple_stream.extend(vec![proc_macro::TokenTree::Group(group)]);
                            let mut new_tuples = self.visit_stream_expr(tuple_stream).into_iter();
                            let new_tuple = new_tuples.next().expect("visited tuple");
                            assert!(new_tuples.next().is_none());
                            if let proc_macro::TokenTree::Group(group) = new_tuple {
                                assert!(group.delimiter() == proc_macro::Delimiter::Parenthesis);
                                list.tokens = proc_macro2::TokenStream::from(group.stream());
                            } else {
                                panic!("expected tuple");
                            }
                        }
                        Meta::NameValue(_) => {}
                    }
                }
                _ => (),
            }
        }
    }

    fn visit_expr_while_mut(&mut self, expr_while: &mut ExprWhile) {
        visit_expr_while_mut(self, expr_while);
        let invariant_except_breaks = self.take_ghost(&mut expr_while.invariant_except_break);
        let invariants = self.take_ghost(&mut expr_while.invariant);
        let invariant_ensures = self.take_ghost(&mut expr_while.invariant_ensures);
        let ensures = self.take_ghost(&mut expr_while.ensures);
        let decreases = self.take_ghost(&mut expr_while.decreases);
        let mut stmts: Vec<Stmt> = Vec::new();
        self.add_loop_specs(
            &mut stmts,
            invariant_except_breaks,
            invariants,
            invariant_ensures,
            ensures,
            decreases,
        );
        expr_while.body.stmts.splice(0..0, stmts);
    }

    fn visit_expr_loop_mut(&mut self, expr_loop: &mut ExprLoop) {
        visit_expr_loop_mut(self, expr_loop);
        let invariant_except_breaks = self.take_ghost(&mut expr_loop.invariant_except_break);
        let invariants = self.take_ghost(&mut expr_loop.invariant);
        let invariant_ensures = self.take_ghost(&mut expr_loop.invariant_ensures);
        let ensures = self.take_ghost(&mut expr_loop.ensures);
        let decreases = self.take_ghost(&mut expr_loop.decreases);
        let mut stmts: Vec<Stmt> = Vec::new();
        self.add_loop_specs(
            &mut stmts,
            invariant_except_breaks,
            invariants,
            invariant_ensures,
            ensures,
            decreases,
        );
        expr_loop.body.stmts.splice(0..0, stmts);
    }

    fn visit_specification_mut(&mut self, spec: &mut syn_verus::Specification) {
        self.inside_ghost += 1;
        visit_specification_mut(self, spec);
        self.inside_ghost -= 1;
    }

    fn visit_local_mut(&mut self, local: &mut Local) {
        // Note: exec-mode "let ghost" and "let tracked" have already been transformed
        // into proof blocks by point, so we don't need to change inside_ghost here.
        if let Some(tracked) = std::mem::take(&mut local.tracked) {
            local.attrs.push(mk_verus_attr(tracked.span, quote! { proof }));
        } else if let Some(ghost) = std::mem::take(&mut local.ghost) {
            local.attrs.push(mk_verus_attr(ghost.span, quote! { spec }));
        }
        visit_local_mut(self, local);
    }

    fn visit_block_mut(&mut self, block: &mut Block) {
        let mut stmts: Vec<Stmt> = Vec::new();
        let block_stmts = std::mem::replace(&mut block.stmts, vec![]);
        for mut stmt in block_stmts {
            let (skip, extra_stmts) = self.visit_stmt_extend(&mut stmt);
            if !skip {
                stmts.push(stmt);
            }
            stmts.extend(extra_stmts);
        }
        block.stmts = stmts;
        visit_block_mut(self, block);
    }

    fn visit_type_param_mut(&mut self, p: &mut syn_verus::TypeParam) {
        self.filter_attrs(&mut p.attrs);
        syn_verus::visit_mut::visit_type_param_mut(self, p);
    }

    fn visit_item_fn_mut(&mut self, fun: &mut ItemFn) {
        // Process rustdoc before processing the ItemFn itself.
        // That way, the generated rustdoc gets the prettier syntax instead of the
        // de-sugared syntax.
        if self.rustdoc {
            crate::rustdoc::process_item_fn(fun);
        }
        let stmts =
            self.visit_fn(&mut fun.attrs, Some(&fun.vis), &mut fun.sig, fun.semi_token, false);
        fun.block.stmts.splice(0..0, stmts);
        fun.semi_token = None;
        let is_external_code = has_external_code(&fun.attrs);
        if is_external_code {
            self.inside_external_code += 1;
        }
        visit_item_fn_mut(self, fun);
        if is_external_code {
            self.inside_external_code -= 1;
        }
    }

    fn visit_impl_item_fn_mut(&mut self, method: &mut ImplItemFn) {
        if self.rustdoc {
            crate::rustdoc::process_impl_item_method(method);
        }

        let stmts = self.visit_fn(
            &mut method.attrs,
            Some(&method.vis),
            &mut method.sig,
            method.semi_token,
            false,
        );
        method.block.stmts.splice(0..0, stmts);
        method.semi_token = None;
        let is_external_code = has_external_code(&method.attrs);
        if is_external_code {
            self.inside_external_code += 1;
        }
        visit_impl_item_fn_mut(self, method);
        if is_external_code {
            self.inside_external_code -= 1;
        }
    }

    fn visit_trait_item_fn_mut(&mut self, method: &mut TraitItemFn) {
        let is_spec_method = method.sig.ident.to_string().starts_with(VERUS_SPEC);
        let mut stmts =
            self.visit_fn(&mut method.attrs, None, &mut method.sig, method.semi_token, true);
        if let Some(block) = &mut method.default {
            block.stmts.splice(0..0, stmts);
        } else if self.erase_ghost.keep() && is_spec_method {
            let span = method.sig.fn_token.span;
            stmts.push(Stmt::Expr(
                Expr::Verbatim(quote_spanned_builtin!(builtin, span => #builtin::no_method_body())),
                None,
            ));
            let block = Block { brace_token: Brace(span), stmts };
            method.default = Some(block);
        }
        if self.erase_ghost.keep() && is_spec_method {
            method.semi_token = None;
        }
        let is_external_code = has_external_code(&method.attrs);
        if is_external_code {
            self.inside_external_code += 1;
        }
        visit_trait_item_fn_mut(self, method);
        if is_external_code {
            self.inside_external_code -= 1;
        }
    }

    fn visit_item_const_mut(&mut self, con: &mut ItemConst) {
        let mode = self.visit_const_or_static(
            con.const_token.span,
            &mut con.attrs,
            Some(&con.vis),
            &mut con.publish,
            &mut con.mode,
        );
        self.desugar_const_or_static(
            &mode,
            &mut con.ensures,
            &mut con.block,
            &mut con.expr,
            &mut con.eq_token,
            &mut con.semi_token,
            &con.ty,
            con.const_token.span,
        );
        visit_item_const_mut(self, con);
    }

    fn visit_item_static_mut(&mut self, sta: &mut ItemStatic) {
        let mode = self.visit_const_or_static(
            sta.static_token.span,
            &mut sta.attrs,
            Some(&sta.vis),
            &mut sta.publish,
            &mut sta.mode,
        );
        self.desugar_const_or_static(
            &mode,
            &mut sta.ensures,
            &mut sta.block,
            &mut sta.expr,
            &mut sta.eq_token,
            &mut sta.semi_token,
            &sta.ty,
            sta.static_token.span,
        );
        visit_item_static_mut(self, sta);
    }

    fn visit_impl_item_const_mut(&mut self, con: &mut syn_verus::ImplItemConst) {
        let mode = self.visit_const_or_static(
            con.const_token.span,
            &mut con.attrs,
            Some(&con.vis),
            &mut con.publish,
            &mut con.mode,
        );
        self.desugar_const_or_static(
            &mode,
            &mut con.ensures,
            &mut con.block,
            &mut con.expr,
            &mut con.eq_token,
            &mut con.semi_token,
            &con.ty,
            con.const_token.span,
        );
        visit_impl_item_const_mut(self, con);
    }

    fn visit_field_mut(&mut self, field: &mut Field) {
        visit_field_mut(self, field);
        field.attrs.extend(data_mode_attrs(&field.mode));
        field.mode = DataMode::Default;
        self.filter_attrs(&mut field.attrs);
    }

    fn visit_item_enum_mut(&mut self, item: &mut ItemEnum) {
        item.attrs.push(mk_verus_attr(item.span(), quote! { verus_macro }));
        visit_item_enum_mut(self, item);
        item.attrs.extend(data_mode_attrs(&item.mode));
        item.mode = DataMode::Default;
        self.filter_attrs(&mut item.attrs);
    }

    fn visit_item_union_mut(&mut self, item: &mut ItemUnion) {
        item.attrs.push(mk_verus_attr(item.span(), quote! { verus_macro }));
        visit_item_union_mut(self, item);
        self.filter_attrs(&mut item.attrs);
    }

    fn visit_item_struct_mut(&mut self, item: &mut ItemStruct) {
        item.attrs.push(mk_verus_attr(item.span(), quote! { verus_macro }));
        visit_item_struct_mut(self, item);
        item.attrs.extend(data_mode_attrs(&item.mode));
        item.mode = DataMode::Default;
        self.filter_attrs(&mut item.attrs);
    }

    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))]
    fn visit_type_mut(&mut self, ty: &mut Type) {
        self.inside_type += 1;
        syn_verus::visit_mut::visit_type_mut(self, ty);
        self.inside_type -= 1;

        let span = ty.span();
        let tmp_ty = take_type(ty);

        match tmp_ty {
            Type::FnSpec(TypeFnSpec {
                spec_fn_token: _,
                fn_spec_token,
                paren_token: _,
                inputs,
                output,
            }) => {
                #[cfg(verus_keep_ghost)]
                if fn_spec_token.is_some() {
                    proc_macro::Diagnostic::spanned(
                        span.unwrap(),
                        proc_macro::Level::Warning,
                        "FnSpec is deprecated - use spec_fn instead",
                    )
                    .emit();
                }

                // Turn `FnSpec(Args...) -> Output`
                // into `FnSpec<Args, Output>`
                // Note that we have to turn `Args` into a tuple type, e.g.
                //
                // `FnSpec() -> Output`      -->  `FnSpec<(), Output>`
                // `FnSpec(X) -> Output`     -->  `FnSpec<(X, ), Output>`
                // `FnSpec(X, Y) -> Output`  -->  `FnSpec<(X, Y, ), Output>`

                let mut param_types: Vec<&Type> = Vec::new();
                for bare_fn_arg in inputs.iter() {
                    let BareFnArg { attrs, name: _, ty: param_ty } = bare_fn_arg;
                    if attrs.len() > 0 {
                        *ty = Type::Verbatim(quote_spanned!(attrs[0].span() =>
                            compile_error!("'tracked' not supported here")
                        ));
                        return;
                    }
                    param_types.push(param_ty);
                }

                let out_type: Type = match output {
                    ReturnType::Default => Type::Verbatim(quote_spanned! { span => () }),
                    ReturnType::Type(_, opt_tracked, opt_name, out_type) => {
                        if let Some(tracked) = opt_tracked {
                            *ty = Type::Verbatim(quote_spanned!(tracked.span() =>
                                compile_error!("'tracked' not supported here")
                            ));
                            return;
                        }
                        if let Some(name) = opt_name {
                            *ty = Type::Verbatim(quote_spanned!(name.1.span() =>
                                compile_error!("return-value name not expected here")
                            ));
                            return;
                        }
                        *out_type
                    }
                };

                *ty = Type::Verbatim(quote_spanned_builtin! { builtin, span =>
                    #builtin::FnSpec<(#(#param_types ,)*), #out_type>
                });
            }
            Type::FnProof(TypeFnProof {
                proof_fn_token: _,
                generics,
                options,
                paren_token: _,
                inputs,
                output,
            }) => {
                let mut param_types: Vec<&Type> = Vec::new();
                for input in inputs.iter() {
                    param_types.push(&input.arg.ty);
                }
                let (out_type, out_tracked) = match output {
                    ReturnType::Default => (Type::Verbatim(quote_spanned! { span => () }), false),
                    ReturnType::Type(_, tracked, opt_name, out_type) => {
                        if let Some(name) = opt_name {
                            *ty = Type::Verbatim(quote_spanned!(name.1.span() =>
                                compile_error!("return-value name not expected here")
                            ));
                            return;
                        }
                        (*out_type, tracked.is_some())
                    }
                };
                let (life, options_arg) = if let Some(generics) = &generics {
                    use syn_verus::GenericArgument;
                    let args: Vec<&GenericArgument> = generics.args.iter().collect();
                    match &args[..] {
                        [] => (None, None),
                        [l @ GenericArgument::Lifetime(_)] => (Some((*l).clone()), None),
                        [GenericArgument::Type(t)] if options.is_none() => {
                            (None, Some((*t).clone()))
                        }
                        [l @ GenericArgument::Lifetime(_), GenericArgument::Type(t)]
                            if options.is_none() =>
                        {
                            (Some((*l).clone()), Some((*t).clone()))
                        }
                        _ => {
                            *ty = Type::Verbatim(quote_spanned!(generics.span() =>
                                compile_error!("unexpected generic arguments to proof_fn")
                            ));
                            return;
                        }
                    }
                } else {
                    (None, None)
                };
                let options_arg = if let Some(options_arg) = options_arg {
                    options_arg
                } else {
                    let opts = match ProofFnOptions::parse_opt(&options) {
                        Ok(opts) => opts,
                        Err(err) => {
                            *ty = Type::Verbatim(quote_spanned!(options.span() =>
                                compile_error!(#err)
                            ));
                            return;
                        }
                    };
                    let (usage, req_ens, copy, send, sync) = opts.to_types(options.span());
                    Type::Verbatim(quote_spanned_builtin!(builtin, span =>
                        #builtin::FOpts<#usage, #req_ens, #copy, #send, #sync>
                    ))
                };

                let arg_modes =
                    proof_fn_tracks_to_type(span, inputs.iter().map(|x| x.tracked_token.is_some()));
                let out_mode = proof_fn_track_to_type(span, out_tracked);
                if let Some(life) = life {
                    *ty = Type::Verbatim(quote_spanned_builtin!(builtin, span =>
                        #builtin::FnProof<#life, #options_arg, #arg_modes, #out_mode, (#(#param_types ,)*), #out_type>
                    ));
                } else {
                    *ty = Type::Verbatim(quote_spanned_builtin!(builtin, span =>
                        #builtin::FnProof<#options_arg, #arg_modes, #out_mode, (#(#param_types ,)*), #out_type>
                    ));
                }
            }
            _ => {
                *ty = tmp_ty;
            }
        }
    }

    fn visit_path_mut(&mut self, path: &mut Path) {
        // generic type arguments can appear inside paths
        self.inside_type += 1;
        syn_verus::visit_mut::visit_path_mut(self, path);
        self.inside_type -= 1;
    }

    fn visit_generic_argument_mut(&mut self, arg: &mut syn_verus::GenericArgument) {
        self.inside_type += 1;
        syn_verus::visit_mut::visit_generic_argument_mut(self, arg);
        self.inside_type -= 1;
    }

    fn visit_item_mod_mut(&mut self, item: &mut ItemMod) {
        item.attrs.push(mk_verus_attr(item.span(), quote! { verus_macro }));
        if let Some((_, items)) = &mut item.content {
            self.visit_items_prefilter(items);
        }
        self.filter_attrs(&mut item.attrs);
        syn_verus::visit_mut::visit_item_mod_mut(self, item);
        if let Some((_, items)) = &mut item.content {
            self.visit_items_post(items);
        }
    }

    fn visit_item_impl_mut(&mut self, imp: &mut ItemImpl) {
        imp.attrs.push(mk_verus_attr(imp.span(), quote! { verus_macro }));
        self.visit_impl_items_prefilter(&mut imp.items, imp.trait_.is_some());
        self.filter_attrs(&mut imp.attrs);
        syn_verus::visit_mut::visit_item_impl_mut(self, imp);
    }

    fn visit_item_trait_mut(&mut self, tr: &mut ItemTrait) {
        tr.attrs.push(mk_verus_attr(tr.span(), quote! { verus_macro }));
        self.visit_trait_items_prefilter(&mut tr.items);
        self.filter_attrs(&mut tr.attrs);
        syn_verus::visit_mut::visit_item_trait_mut(self, tr);
    }

    fn visit_reveal_hide_mut(&mut self, _i: &mut syn_verus::RevealHide) {
        // we have already transformed this, do not recurse into it
    }

    fn visit_item_broadcast_group_mut(&mut self, _i: &mut ItemBroadcastGroup) {
        // we have already transformed this, do not recurse into it
    }
}

struct Items {
    items: Vec<Item>,
}

impl Parse for Items {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<Items> {
        let mut items = Vec::new();
        while !input.is_empty() {
            items.push(input.parse()?);
        }
        Ok(Items { items })
    }
}

#[derive(Debug)]
enum MacroElement {
    Comma(Token![,]),
    Semi(Token![;]),
    FatArrow(Token![=>]),
    Colon(Token![:]),
    Expr(Expr),
}

#[derive(Debug)]
enum MacroElementExplicitExpr {
    Comma(Token![,]),
    Semi(Token![;]),
    FatArrow(Token![=>]),
    Colon(Token![:]),
    ExplicitExpr(Token![@], Token![@], Expr),
    TT(TokenTree),
}

#[derive(Debug)]
struct MacroElements {
    elements: Vec<MacroElement>,
}

#[derive(Debug)]
struct MacroElementsExplicitExpr {
    elements: Vec<MacroElementExplicitExpr>,
}

#[derive(Debug)]
enum Delimiter {
    Paren(Paren),
    Bracket(Bracket),
    Brace(Brace),
}

#[derive(Debug)]
struct MacroInvoke {
    path: Path,
    bang: Token![!],
    delimiter: Delimiter,
    elements: MacroElements,
}

#[derive(Debug)]
struct MacroInvokeExplicitExpr {
    path: Path,
    bang: Token![!],
    delimiter: Delimiter,
    elements: MacroElementsExplicitExpr,
}

impl Parse for MacroElement {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroElement> {
        if input.peek(Token![,]) {
            Ok(MacroElement::Comma(input.parse()?))
        } else if input.peek(Token![;]) {
            Ok(MacroElement::Semi(input.parse()?))
        } else if input.peek(Token![=>]) {
            Ok(MacroElement::FatArrow(input.parse()?))
        } else if input.peek(Token![:]) {
            Ok(MacroElement::Colon(input.parse()?))
        } else {
            Ok(MacroElement::Expr(input.parse()?))
        }
    }
}

impl Parse for MacroElementExplicitExpr {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroElementExplicitExpr> {
        if input.peek(Token![,]) {
            Ok(MacroElementExplicitExpr::Comma(input.parse()?))
        } else if input.peek(Token![;]) {
            Ok(MacroElementExplicitExpr::Semi(input.parse()?))
        } else if input.peek(Token![=>]) {
            Ok(MacroElementExplicitExpr::FatArrow(input.parse()?))
        } else if input.peek(Token![:]) {
            Ok(MacroElementExplicitExpr::Colon(input.parse()?))
        } else if input.peek(Token![@]) && input.peek2(Token![@]) {
            let at1 = input.parse()?;
            let at2 = input.parse()?;
            let e = input.parse()?;
            Ok(MacroElementExplicitExpr::ExplicitExpr(at1, at2, e))
        } else {
            Ok(MacroElementExplicitExpr::TT(input.parse()?))
        }
    }
}

impl Parse for MacroElements {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroElements> {
        let mut elements = Vec::new();
        while !input.is_empty() {
            elements.push(input.parse()?);
        }
        Ok(MacroElements { elements })
    }
}

impl Parse for MacroElementsExplicitExpr {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroElementsExplicitExpr> {
        let mut elements = Vec::new();
        while !input.is_empty() {
            elements.push(input.parse()?);
        }
        Ok(MacroElementsExplicitExpr { elements })
    }
}

impl Parse for MacroInvoke {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroInvoke> {
        let path = input.parse()?;
        let bang = input.parse()?;
        let content;
        if input.peek(syn_verus::token::Paren) {
            let paren = parenthesized!(content in input);
            let elements = content.parse()?;
            Ok(MacroInvoke { path, bang, delimiter: Delimiter::Paren(paren), elements })
        } else if input.peek(syn_verus::token::Bracket) {
            let bracket = bracketed!(content in input);
            let elements = content.parse()?;
            Ok(MacroInvoke { path, bang, delimiter: Delimiter::Bracket(bracket), elements })
        } else {
            let brace = braced!(content in input);
            let elements = content.parse()?;
            Ok(MacroInvoke { path, bang, delimiter: Delimiter::Brace(brace), elements })
        }
    }
}

impl Parse for MacroInvokeExplicitExpr {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroInvokeExplicitExpr> {
        let path = input.parse()?;
        let bang = input.parse()?;
        let content;
        if input.peek(syn_verus::token::Paren) {
            let paren = parenthesized!(content in input);
            let elements = content.parse()?;
            Ok(MacroInvokeExplicitExpr { path, bang, delimiter: Delimiter::Paren(paren), elements })
        } else if input.peek(syn_verus::token::Bracket) {
            let bracket = bracketed!(content in input);
            let elements = content.parse()?;
            Ok(MacroInvokeExplicitExpr {
                path,
                bang,
                delimiter: Delimiter::Bracket(bracket),
                elements,
            })
        } else {
            let brace = braced!(content in input);
            let elements = content.parse()?;
            Ok(MacroInvokeExplicitExpr { path, bang, delimiter: Delimiter::Brace(brace), elements })
        }
    }
}

impl ToTokens for MacroElement {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            MacroElement::Comma(e) => e.to_tokens(tokens),
            MacroElement::Semi(e) => e.to_tokens(tokens),
            MacroElement::FatArrow(e) => e.to_tokens(tokens),
            MacroElement::Colon(e) => e.to_tokens(tokens),
            MacroElement::Expr(e) => e.to_tokens(tokens),
        }
    }
}

impl ToTokens for MacroElementExplicitExpr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            MacroElementExplicitExpr::Comma(e) => e.to_tokens(tokens),
            MacroElementExplicitExpr::Semi(e) => e.to_tokens(tokens),
            MacroElementExplicitExpr::FatArrow(e) => e.to_tokens(tokens),
            MacroElementExplicitExpr::Colon(e) => e.to_tokens(tokens),
            MacroElementExplicitExpr::ExplicitExpr(_at1, _at2, e) => e.to_tokens(tokens),
            MacroElementExplicitExpr::TT(e) => e.to_tokens(tokens),
        }
    }
}

impl quote::ToTokens for MacroElements {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for element in &self.elements {
            element.to_tokens(tokens);
        }
    }
}

impl quote::ToTokens for MacroElementsExplicitExpr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for element in &self.elements {
            element.to_tokens(tokens);
        }
    }
}

impl quote::ToTokens for MacroInvoke {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.path.to_tokens(tokens);
        self.bang.to_tokens(tokens);
        match self.delimiter {
            Delimiter::Paren(d) => {
                d.surround(tokens, |tokens| {
                    self.elements.to_tokens(tokens);
                });
            }
            Delimiter::Bracket(d) => {
                d.surround(tokens, |tokens| {
                    self.elements.to_tokens(tokens);
                });
            }
            Delimiter::Brace(d) => {
                d.surround(tokens, |tokens| {
                    self.elements.to_tokens(tokens);
                });
            }
        }
    }
}

impl quote::ToTokens for MacroInvokeExplicitExpr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.path.to_tokens(tokens);
        self.bang.to_tokens(tokens);
        match self.delimiter {
            Delimiter::Paren(d) => {
                d.surround(tokens, |tokens| {
                    self.elements.to_tokens(tokens);
                });
            }
            Delimiter::Bracket(d) => {
                d.surround(tokens, |tokens| {
                    self.elements.to_tokens(tokens);
                });
            }
            Delimiter::Brace(d) => {
                d.surround(tokens, |tokens| {
                    self.elements.to_tokens(tokens);
                });
            }
        }
    }
}

pub(crate) fn rewrite_items(
    stream: proc_macro::TokenStream,
    erase_ghost: EraseGhost,
    use_spec_traits: bool,
) -> proc_macro::TokenStream {
    let stream = rejoin_tokens(stream);
    let mut items: Items = parse_macro_input!(stream as Items);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits,
        inside_ghost: 0,
        inside_type: 0,
        inside_external_code: 0,
        inside_const: false,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    visitor.visit_items_prefilter(&mut items.items);
    for mut item in &mut items.items {
        visitor.visit_item_mut(&mut item);
        visitor.inside_ghost = 0;
        visitor.inside_const = false;
        visitor.inside_arith = InsideArith::None;
    }
    visitor.visit_items_post(&mut items.items);
    for item in items.items {
        item.to_tokens(&mut new_stream);
    }
    proc_macro::TokenStream::from(new_stream)
}

pub(crate) fn rewrite_expr(
    erase_ghost: EraseGhost,
    inside_ghost: bool,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let stream = rejoin_tokens(stream);
    let mut expr: Expr = parse_macro_input!(stream as Expr);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: if inside_ghost { 1 } else { 0 },
        inside_type: 0,
        inside_external_code: 0,
        inside_const: false,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    visitor.visit_expr_mut(&mut expr);
    expr.to_tokens(&mut new_stream);
    proc_macro::TokenStream::from(new_stream)
}

struct Stmts(Vec<Stmt>);

impl Parse for Stmts {
    fn parse(input: ParseStream) -> syn_verus::Result<Self> {
        Block::parse_within(input).map(|stmts| Stmts(stmts))
    }
}

pub(crate) fn rewrite_proof_decl(
    erase_ghost: EraseGhost,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let stream = rejoin_tokens(stream);
    let Stmts(stmts) = parse_macro_input!(stream as Stmts);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: 0,
        inside_type: 0,
        inside_external_code: 0,
        inside_const: false,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    for mut ss in stmts {
        match ss {
            Stmt::Local(Local { tracked: None, ghost: None, .. }) => {
                return quote_spanned!(ss.span() => compile_error!("Exec local is not allowed in proof_decl")).into();
            }
            Stmt::Local(_) => {
                let (skip, mut new_stmts) = visitor.visit_stmt_extend(&mut ss);
                if !skip {
                    new_stmts.insert(0, ss)
                }
                for mut ss in new_stmts {
                    visitor.visit_stmt_mut(&mut ss);
                    ss.to_tokens(&mut new_stream);
                }
            }
            Stmt::Macro(mut mac) => {
                // Due to the difference between function-like macro vs proceudure macro,
                // Macros used inside proof block need to explicitly call proof or proof_decl.
                // We should avoid entering proof mode if calling a macro.
                visitor.visit_macro_mut(&mut mac.mac);
                mac.to_tokens(&mut new_stream);
            }
            _ => {
                let span = ss.span();
                let mut proof_expr = Expr::Unary(ExprUnary {
                    attrs: vec![],
                    expr: Box::new(Expr::Block(ExprBlock {
                        attrs: vec![],
                        label: None,
                        block: Block { brace_token: Brace(span), stmts: vec![ss] },
                    })),
                    op: UnOp::Proof(Token![proof](span)),
                });
                visitor.visit_expr_mut(&mut proof_expr);
                proof_expr.to_tokens(&mut new_stream);
            }
        };
    }
    proc_macro::TokenStream::from(new_stream)
}

pub(crate) fn rewrite_expr_node(erase_ghost: EraseGhost, inside_ghost: bool, expr: &mut Expr) {
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: if inside_ghost { 1 } else { 0 },
        inside_type: 0,
        inside_external_code: 0,
        inside_const: false,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    visitor.visit_expr_mut(expr);
}

fn take_sig_with_spec(
    erase_ghost: EraseGhost,
    with: syn_verus::WithSpecOnFn,
    sig: &mut syn::Signature,
    ret_pat: &mut Option<Pat>,
) -> Vec<Stmt> {
    let syn_verus::WithSpecOnFn { mut inputs, outputs, .. } = with;
    let mut spec_stmts = vec![];
    if inputs.len() > 0 {
        for arg in inputs.iter_mut() {
            spec_stmts.extend(rewrite_args_unwrap_ghost_tracked(&erase_ghost, arg));
            sig.inputs.push(syn::parse_quote_spanned! { arg.span() => #arg })
        }
    }
    // ret.0 is executable returns.
    // ret.1.. is the tracked/ghost returns.
    if let Some((token, extra_ret)) = outputs {
        if extra_ret.len() > 0 {
            let span = extra_ret.span();
            let extra_ret_typs: Vec<_> = extra_ret.iter().map(|pt| pt.ty.clone()).collect();
            let mut elems = Punctuated::new();
            if let Some(pat) = ret_pat {
                elems.push(pat.clone());
            } else {
                elems.push(Pat::Wild(syn_verus::PatWild {
                    attrs: vec![],
                    underscore_token: Token![_](span),
                }));
            }
            for pt in extra_ret {
                elems.push(pt.pat.as_ref().clone());
            }
            *ret_pat = Some(Pat::Tuple(syn_verus::PatTuple {
                attrs: vec![],
                paren_token: Paren::default(),
                elems,
            }));
            match &mut sig.output {
                syn::ReturnType::Default => {
                    let ty = syn::Type::Verbatim(quote_spanned!(
                        sig.output.span() => (() #(,#extra_ret_typs)*)
                    ));
                    sig.output = syn::ReturnType::Type(syn::Token![->](token.span()), Box::new(ty));
                }
                syn::ReturnType::Type(_, ty) => {
                    **ty = syn::Type::Verbatim(quote_spanned!(
                        ty.span() => (#ty #(,#extra_ret_typs)*)
                    ));
                }
            }
        }
    };
    spec_stmts
}
pub(crate) fn sig_specs_attr(
    erase_ghost: EraseGhost,
    spec_attr: SignatureSpecAttr,
    sig: &mut syn::Signature,
) -> Vec<Stmt> {
    let SignatureSpecAttr { ret_pat, mut spec } = spec_attr;
    let mut spec_stmts = vec![];
    let ret_pat = ret_pat.map(|v| v.0);
    let mut final_ret_pat = ret_pat.clone();
    // If the provided ret_pat is not ident (e.g., A { a, b }),
    // we need to replace it with ident pat.
    // ensure_expr1 to
    // {let A{a, b} = _tmp_ret; ensure_expr1}
    if let Some(with) = spec.with {
        spec_stmts.extend(take_sig_with_spec(erase_ghost, with, sig, &mut final_ret_pat));
    }
    spec.with = None;
    let ret_pat = match (ret_pat, &sig.output) {
        (Some(pat), syn::ReturnType::Type(_, ty)) => {
            let pat = if !matches!(pat, Pat::Ident(_)) {
                Pat::Verbatim(quote_spanned! {pat.span() => __verus_tmp_ret})
            } else {
                pat
            };
            Some((pat, ty.clone()))
        }
        _ => None,
    };
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: 1,
        inside_type: 0,
        inside_external_code: 0,
        inside_const: false,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    let sig_span = sig.span().clone();
    spec_stmts.extend(visitor.take_sig_specs(
        &mut spec,
        ret_pat,
        final_ret_pat,
        sig.constness.is_some(),
        sig_span,
    ));
    spec_stmts
}

pub(crate) fn while_loop_spec_attr(
    erase_ghost: EraseGhost,
    spec_attr: syn_verus::LoopSpec,
) -> Vec<Stmt> {
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: 1,
        inside_type: 0,
        inside_external_code: 0,
        inside_const: false,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    let mut spec_attr = spec_attr;
    visitor.visit_loop_spec(&mut spec_attr);
    let syn_verus::LoopSpec { invariants, invariant_except_breaks, ensures, decreases, .. } =
        spec_attr;
    let mut stmt = vec![];
    visitor.add_loop_specs(
        &mut stmt,
        invariant_except_breaks,
        invariants,
        None,
        ensures,
        decreases,
    );
    stmt
}

pub(crate) fn for_loop_spec_attr(
    erase_ghost: EraseGhost,
    spec_attr: syn_verus::LoopSpec,
    forloop: syn::ExprForLoop,
) -> syn_verus::Expr {
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: 1,
        inside_type: 0,
        inside_external_code: 0,
        inside_const: false,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    let mut spec_attr = spec_attr;
    visitor.visit_loop_spec(&mut spec_attr);
    let syn_verus::LoopSpec { iter_name, invariants: invariant, decreases, .. } = spec_attr;
    let syn::ExprForLoop { attrs, label, for_token, pat, in_token, expr, body, .. } = forloop;
    let verus_forloop = ExprForLoop {
        attrs: attrs.into_iter().map(|a| parse_quote_spanned! {a.span() => #a}).collect(),
        label: label.map(|l| syn_verus::Label {
            name: syn_verus::Lifetime::new(l.name.ident.to_string().as_str(), l.name.span()),
            colon_token: Token![:](l.colon_token.span),
        }),
        for_token: Token![for](for_token.span),
        pat: Box::new(Pat::Verbatim(quote_spanned! {pat.span() => #pat})),
        in_token: Token![in](in_token.span),
        expr_name: iter_name.map(|(name, token)| Box::new((name, Token![:](token.span())))),
        expr: Box::new(Expr::Verbatim(quote_spanned! {expr.span() => #expr})),
        invariant,
        decreases,
        body: Block {
            brace_token: Brace(body.brace_token.span),
            stmts: vec![Stmt::Expr(Expr::Verbatim(quote_spanned! {body.span() => #body}), None)],
        },
    };
    visitor.desugar_for_loop(verus_forloop)
}

// Unfortunately, the macro_rules tt tokenizer breaks tokens like &&& and ==> into smaller tokens.
// Try to put the original tokens back together here.
#[cfg(verus_keep_ghost)]
pub(crate) fn rejoin_tokens(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use proc_macro::{Group, Punct, Spacing::*, Span, TokenTree};
    let mut tokens: Vec<TokenTree> = stream.into_iter().collect();
    let pun = |t: &TokenTree| match t {
        TokenTree::Punct(p) => Some((p.as_char(), p.spacing(), p.span())),
        _ => None,
    };
    let ident = |t: &TokenTree| match t {
        TokenTree::Ident(p) => Some((p.to_string(), p.span())),
        _ => None,
    };
    let adjacent = |s1: Span, s2: Span| {
        let l1 = s1.end();
        let l2 = s2.start();
        s1.source_file() == s2.source_file() && l1.eq(&l2)
    };
    fn mk_joint_punct(t: Option<(char, proc_macro::Spacing, Span)>) -> TokenTree {
        let (op, _, span) = t.unwrap();
        let mut punct = Punct::new(op, Joint);
        punct.set_span(span);
        TokenTree::Punct(punct)
    }
    let mut i = 0;
    let mut till = if tokens.len() >= 2 { tokens.len() - 2 } else { 0 };
    while i < till {
        let t0 = pun(&tokens[i]);
        let t1_ident = ident(&tokens[i + 1]);
        match (t0, t1_ident.as_ref().map(|(a, b)| (a.as_str(), *b))) {
            (Some(('!', Alone, s1)), Some(("is", s2))) => {
                if adjacent(s1, s2) {
                    tokens[i] =
                        TokenTree::Ident(proc_macro::Ident::new("isnt", s1.join(s2).unwrap()));
                    tokens.remove(i + 1);
                    i += 1;
                    till -= 1;
                    continue;
                }
            }
            (Some(('!', Alone, s1)), Some(("has", s2))) => {
                if adjacent(s1, s2) {
                    tokens[i] =
                        TokenTree::Ident(proc_macro::Ident::new("hasnt", s1.join(s2).unwrap()));
                    tokens.remove(i + 1);
                    i += 1;
                    till -= 1;
                    continue;
                }
            }
            _ => {}
        }
        let t1_pun = pun(&tokens[i + 1]);
        let t2 = pun(&tokens[i + 2]);
        let t3 = if i + 3 < tokens.len() { pun(&tokens[i + 3]) } else { None };
        match (t0, t1_pun, t2, t3) {
            (
                Some(('<', Joint, _)),
                Some(('=', Alone, s1)),
                Some(('=', Joint, s2)),
                Some(('>', Alone, _)),
            )
            | (Some(('=', Joint, _)), Some(('=', Alone, s1)), Some(('=', Alone, s2)), _)
            | (Some(('!', Joint, _)), Some(('=', Alone, s1)), Some(('=', Alone, s2)), _)
            | (Some(('=', Joint, _)), Some(('=', Alone, s1)), Some(('>', Alone, s2)), _)
            | (Some(('<', Joint, _)), Some(('=', Alone, s1)), Some(('=', Alone, s2)), _)
            | (Some(('&', Joint, _)), Some(('&', Alone, s1)), Some(('&', Alone, s2)), _)
            | (Some(('|', Joint, _)), Some(('|', Alone, s1)), Some(('|', Alone, s2)), _) => {
                if adjacent(s1, s2) {
                    tokens[i + 1] = mk_joint_punct(t1_pun);
                }
            }
            (Some(('=', Alone, _)), Some(('~', Alone, s1)), Some(('=', Alone, s2)), _)
            | (Some(('!', Alone, _)), Some(('~', Alone, s1)), Some(('=', Alone, s2)), _) => {
                if adjacent(s1, s2) {
                    tokens[i] = mk_joint_punct(t0);
                    tokens[i + 1] = mk_joint_punct(t1_pun);
                }
            }
            (
                Some(('=', Alone, _)),
                Some(('~', Alone, _)),
                Some(('~', Alone, s2)),
                Some(('=', Alone, s3)),
            )
            | (
                Some(('!', Alone, _)),
                Some(('~', Alone, _)),
                Some(('~', Alone, s2)),
                Some(('=', Alone, s3)),
            ) => {
                if adjacent(s2, s3) {
                    tokens[i] = mk_joint_punct(t0);
                    tokens[i + 1] = mk_joint_punct(t1_pun);
                    tokens[i + 2] = mk_joint_punct(t2);
                }
            }
            _ => {}
        }
        i += 1;
    }
    for tt in &mut tokens {
        match tt {
            TokenTree::Group(group) => {
                let mut new_group = Group::new(group.delimiter(), rejoin_tokens(group.stream()));
                new_group.set_span(group.span());
                *group = new_group;
            }
            _ => {}
        }
    }
    use std::iter::FromIterator;
    proc_macro::TokenStream::from_iter(tokens.into_iter())
}

#[cfg(not(verus_keep_ghost))]
// REVIEW: how much do we actually rely on rejoin_tokens?
fn rejoin_tokens(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    stream
}

pub(crate) fn proof_block(
    erase_ghost: EraseGhost,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let stream = rejoin_tokens(stream);
    let mut invoke: Block = parse_macro_input!(stream as Block);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: 1,
        inside_type: 0,
        inside_external_code: 0,
        inside_const: false,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    visitor.visit_block_mut(&mut invoke);
    invoke.to_tokens(&mut new_stream);
    proc_macro::TokenStream::from(new_stream)
}

pub(crate) fn proof_macro_exprs(
    erase_ghost: EraseGhost,
    inside_ghost: bool,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let stream = rejoin_tokens(stream);
    let mut invoke: MacroInvoke = parse_macro_input!(stream as MacroInvoke);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: if inside_ghost { 1 } else { 0 },
        inside_type: 0,
        inside_external_code: 0,
        inside_const: false,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    for element in &mut invoke.elements.elements {
        match element {
            MacroElement::Expr(expr) => visitor.visit_expr_mut(expr),
            _ => {}
        }
    }
    invoke.to_tokens(&mut new_stream);
    proc_macro::TokenStream::from(new_stream)
}

pub(crate) fn inv_macro_exprs(
    erase_ghost: EraseGhost,
    treat_elements_as_ghost: bool,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let stream = rejoin_tokens(stream);
    let mut invoke: MacroInvoke = parse_macro_input!(stream as MacroInvoke);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: 0,
        inside_type: 0,
        inside_external_code: 0,
        inside_const: false,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    for (idx, element) in invoke.elements.elements.iter_mut().enumerate() {
        match element {
            MacroElement::Expr(expr) => {
                // Always treat the third element ($eexpr) as ghost even if
                // `treat_elements_as_ghost` is false.
                visitor.inside_ghost =
                    if treat_elements_as_ghost || idx == 2 { 1u32 } else { 0u32 };
                visitor.visit_expr_mut(expr);
            }
            _ => {}
        };
    }
    invoke.to_tokens(&mut new_stream);
    proc_macro::TokenStream::from(new_stream)
}

pub(crate) fn proof_macro_explicit_exprs(
    erase_ghost: EraseGhost,
    inside_ghost: bool,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let stream = rejoin_tokens(stream);
    let mut invoke: MacroInvokeExplicitExpr = parse_macro_input!(stream as MacroInvokeExplicitExpr);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        inside_ghost: if inside_ghost { 1 } else { 0 },
        inside_type: 0,
        inside_external_code: 0,
        inside_const: false,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    for element in &mut invoke.elements.elements {
        match element {
            MacroElementExplicitExpr::ExplicitExpr(_at1, _at2, expr) => {
                visitor.visit_expr_mut(expr)
            }
            _ => {}
        }
    }
    invoke.to_tokens(&mut new_stream);
    proc_macro::TokenStream::from(new_stream)
}

pub(crate) fn has_external_code(attrs: &Vec<Attribute>) -> bool {
    attrs.iter().any(|attr| {
        // verifier::external
        attr.path().segments.len() == 2
            && attr.path().segments[0].ident.to_string() == "verifier"
            && (attr.path().segments[1].ident.to_string() == "external"
                || attr.path().segments[1].ident.to_string() == "external_body")
        // verifier(external)
        || attr.path().segments.len() == 1
            && attr.path().segments[0].ident.to_string() == "verifier"
            && match &attr.meta {
                syn_verus::Meta::List(list) => {
                    matches!(list.tokens.to_string().as_str(), "external" | "external_body")
                }
                _ => false,
            }
    })
}

/// Constructs #[name(tokens)]
macro_rules! declare_mk_rust_attr {
    ($name:ident, $s:ident) => {
        pub(crate) fn $name(span: Span, name: &str, tokens: TokenStream) -> $s::Attribute {
            let mut path_segments = $s::punctuated::Punctuated::new();
            path_segments.push($s::PathSegment {
                ident: $s::Ident::new(name, span),
                arguments: $s::PathArguments::None,
            });
            let path = $s::Path { leading_colon: None, segments: path_segments };
            let meta = if tokens.is_empty() {
                $s::Meta::Path(path)
            } else {
                $s::Meta::List($s::MetaList {
                    path,
                    delimiter: $s::MacroDelimiter::Paren($s::token::Paren {
                        span: into_spans(span),
                    }),
                    tokens: quote! { #tokens },
                })
            };
            $s::Attribute {
                pound_token: $s::token::Pound { spans: [span] },
                style: $s::AttrStyle::Outer,
                bracket_token: $s::token::Bracket { span: into_spans(span) },
                meta,
            }
        }
    };
}
declare_mk_rust_attr!(mk_rust_attr, syn_verus);
declare_mk_rust_attr!(mk_rust_attr_syn, syn);

/// Constructs #[verus::internal(tokens)]
macro_rules! declare_mk_verus_attr {
    ($name:ident, $s:ident) => {
        pub(crate) fn $name(span: Span, tokens: TokenStream) -> $s::Attribute {
            let mut path_segments = $s::punctuated::Punctuated::new();
            path_segments.push($s::PathSegment {
                ident: $s::Ident::new("verus", span),
                arguments: $s::PathArguments::None,
            });
            path_segments.push($s::PathSegment {
                ident: $s::Ident::new("internal", span),
                arguments: $s::PathArguments::None,
            });
            let path = $s::Path { leading_colon: None, segments: path_segments };
            let meta = if tokens.is_empty() {
                $s::Meta::Path(path)
            } else {
                $s::Meta::List($s::MetaList {
                    path,
                    delimiter: $s::MacroDelimiter::Paren($s::token::Paren {
                        span: into_spans(span),
                    }),
                    tokens: quote! { #tokens },
                })
            };
            $s::Attribute {
                pound_token: $s::token::Pound { spans: [span] },
                style: $s::AttrStyle::Outer,
                bracket_token: $s::token::Bracket { span: into_spans(span) },
                meta,
            }
        }
    };
}
declare_mk_verus_attr!(mk_verus_attr, syn_verus);
declare_mk_verus_attr!(mk_verus_attr_syn, syn);

fn is_ptr_type(typ: &Type) -> bool {
    match typ {
        Type::Ptr(_) => true,
        Type::Paren(t) => is_ptr_type(&t.elem),
        _ => false,
    }
}

fn is_probably_nat_or_int_type(typ: &Type) -> bool {
    match typ {
        Type::Path(TypePath { qself: None, path }) => match path.get_ident() {
            None => false,
            Some(ident) => {
                let t = ident.to_string();
                t == "int" || t == "nat"
            }
        },
        _ => false,
    }
}

pub(crate) struct Builtin(pub Span);

impl ToTokens for Builtin {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        if crate::cfg_verify_core() {
            tokens.extend(quote_spanned! { self.0 => crate::builtin });
        } else {
            tokens.extend(quote_spanned! { self.0 => ::builtin });
        }
    }
}

pub(crate) struct Vstd(pub Span);

impl ToTokens for Vstd {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        if crate::cfg_verify_core() {
            tokens.extend(quote_spanned! { self.0 => crate::vstd });
        } else if crate::cfg_verify_vstd() {
            tokens.extend(quote_spanned! { self.0 => crate });
        } else {
            tokens.extend(quote_spanned! { self.0 => ::vstd });
        }
    }
}

fn get_ex_ident_mangle_path(qself: &Option<syn_verus::QSelf>, path: &Path) -> Ident {
    static UID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let uid = UID.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

    let mut s = format!("_verus_external_fn_specification_{:}_", uid);

    let expr_path = syn_verus::ExprPath { attrs: vec![], qself: qself.clone(), path: path.clone() };
    let mut tokens = TokenStream::new();
    expr_path.to_tokens(&mut tokens);
    let toks = tokens.to_string();

    for c in toks.chars() {
        if c.is_ascii_alphanumeric() {
            s += &c.to_string();
        } else if c == '_' {
            s += "__";
        } else {
            s += &format!("_{:}_", c as u32);
        }
    }

    return Ident::new(&s, path.span());
}
