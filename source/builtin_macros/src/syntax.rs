use crate::rustdoc::env_rustdoc;
use crate::EraseGhost;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use proc_macro2::TokenTree;
use quote::format_ident;
use quote::ToTokens;
use quote::{quote, quote_spanned};
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::parse_quote_spanned;
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::token;
use syn_verus::token::Colon2;
use syn_verus::token::{Brace, Bracket, Paren, Semi};
use syn_verus::visit_mut::{
    visit_block_mut, visit_expr_loop_mut, visit_expr_mut, visit_expr_while_mut, visit_field_mut,
    visit_impl_item_method_mut, visit_item_const_mut, visit_item_enum_mut, visit_item_fn_mut,
    visit_item_static_mut, visit_item_struct_mut, visit_item_union_mut, visit_local_mut,
    visit_specification_mut, visit_trait_item_method_mut, VisitMut,
};
use syn_verus::BroadcastUse;
use syn_verus::ExprBlock;
use syn_verus::{
    braced, bracketed, parenthesized, parse_macro_input, AttrStyle, Attribute, BareFnArg, BinOp,
    Block, DataMode, Decreases, Ensures, Expr, ExprBinary, ExprCall, ExprLit, ExprLoop,
    ExprMatches, ExprTuple, ExprUnary, ExprWhile, Field, FnArgKind, FnMode, Global, Ident,
    ImplItem, ImplItemMethod, Invariant, InvariantEnsures, InvariantExceptBreak, InvariantNameSet,
    InvariantNameSetList, Item, ItemBroadcastGroup, ItemConst, ItemEnum, ItemFn, ItemImpl, ItemMod,
    ItemStatic, ItemStruct, ItemTrait, ItemUnion, Lit, Local, MatchesOpExpr, MatchesOpToken,
    ModeSpec, ModeSpecChecked, Pat, Path, PathArguments, PathSegment, Publish, Recommends,
    Requires, ReturnType, Signature, SignatureDecreases, SignatureInvariants, SignatureUnwind,
    Stmt, Token, TraitItem, TraitItemMethod, Type, TypeFnSpec, UnOp, Visibility,
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

    // if we are inside bit-vector assertion, warn users to use add/sub/mul for fixed-width operators,
    // rather than +/-/*, which will be promoted to integer operators
    inside_bitvector: bool,
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

macro_rules! stmt_with_semi {
    ($b:ident, $span:expr => $($tok:tt)*) => {
        {
            let sp = $span;
            let $b = crate::syntax::Builtin(sp);
            stmt_with_semi!{ sp => $($tok)* }
        }
    };
    ($span:expr => $($tok:tt)*) => {
        Stmt::Semi(
            Expr::Verbatim(quote_spanned!{ $span => $($tok)* }),
            Semi { spans: [ $span ] },
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

macro_rules! quote_builtin {
    ($b:ident => $($tt:tt)*) => {
        {
            let sp = ::proc_macro2::Span::call_site();
            let $b = crate::syntax::Builtin(sp);
            ::quote::quote!{ $($tt)* }
        }
    }
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
                let prefix = attr.path.segments[0].ident.to_string();
                prefix != "verus" && prefix != "verifier"
            });
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
            use syn_verus::PatType;
            if let FnArgKind::Typed(PatType { pat, .. }) = &mut arg.kind {
                let pat = &mut **pat;
                let mut tracked_wrapper = false;
                let mut wrapped_pat_id = None;
                if let Pat::TupleStruct(tup) = &*pat {
                    let ghost_wrapper = path_is_ident(&tup.path, "Ghost");
                    tracked_wrapper = path_is_ident(&tup.path, "Tracked");
                    if ghost_wrapper || tracked_wrapper || tup.pat.elems.len() == 1 {
                        if let Pat::Ident(id) = &tup.pat.elems[0] {
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
                    let tmp_id = Ident::new(
                        &format!("verus_tmp_{x}"),
                        Span::mixed_site().located_at(pat.span()),
                    );
                    wrapped_pat_id.ident = tmp_id.clone();
                    *pat = Pat::Ident(wrapped_pat_id);
                    if self.erase_ghost.keep() {
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

        if matches!(sig.mode, FnMode::Default | FnMode::Exec(_) | FnMode::Proof(_))
            && !matches!(sig.publish, Publish::Default)
        {
            let publish_span = sig.publish.span();
            stmts.push(stmt_with_semi!(
                publish_span =>
                compile_error!("only `spec` functions can be marked `open` or `closed`")
            ));
        }

        if sig.broadcast.is_some() && !matches!(sig.mode, FnMode::Proof(_)) {
            let broadcast_span = sig.broadcast.span();
            stmts.push(stmt_with_semi!(
                broadcast_span =>
                compile_error!("only `proof` functions can be marked `broadcast`")
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
            Publish::OpenRestricted(_) => {
                unimplemented!("TODO: support open(...)")
            }
        };

        let (unimpl, ext_attrs) = match (&sig.mode, semi_token, is_trait) {
            (FnMode::Spec(_) | FnMode::SpecChecked(_), Some(semi), false) => (
                vec![Stmt::Expr(Expr::Verbatim(quote_spanned!(semi.span => unimplemented!())))],
                vec![mk_verus_attr(semi.span, quote! { external_body })],
            ),
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
            FnMode::Exec(token) => (0, vec![mk_verus_attr(token.exec_token.span, quote! { exec })]),
        };
        self.inside_ghost = inside_ghost;

        let prover_attr = sig.prover.as_ref().map(|(_, _, prover_ident)| {
            mk_verus_attr(prover_ident.span(), quote! { prover(#prover_ident) })
        });

        self.inside_ghost += 1; // for requires, ensures, etc.
        self.inside_bitvector =
            sig.prover.as_ref().map_or(false, |(_, _, attr)| attr == "bit_vector");

        let requires = self.take_ghost(&mut sig.requires);
        let recommends = self.take_ghost(&mut sig.recommends);
        let ensures = self.take_ghost(&mut sig.ensures);
        let decreases = self.take_ghost(&mut sig.decreases);
        let opens_invariants = self.take_ghost(&mut sig.invariants);
        let unwind = self.take_ghost(&mut sig.unwind);
        // TODO: wrap specs inside ghost blocks
        if let Some(Requires { token, mut exprs }) = requires {
            if exprs.exprs.len() > 0 {
                for expr in exprs.exprs.iter_mut() {
                    self.visit_expr_mut(expr);
                }
                stmts.push(Stmt::Semi(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, token.span => #builtin::requires([#exprs])),
                    ),
                    Semi { spans: [token.span] },
                ));
            }
        }
        if let Some(Recommends { token, mut exprs, via }) = recommends {
            if exprs.exprs.len() > 0 {
                for expr in exprs.exprs.iter_mut() {
                    self.visit_expr_mut(expr);
                }
                stmts.push(Stmt::Semi(
                    Expr::Verbatim(quote_spanned_builtin!(builtin, token.span => #builtin::recommends([#exprs]))),
                    Semi { spans: [token.span] },
                ));
            }
            if let Some((via_token, via_expr)) = via {
                stmts.push(Stmt::Semi(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, via_expr.span() => #builtin::recommends_by(#via_expr)),
                    ),
                    Semi { spans: [via_token.span] },
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
                            stmts.push(Stmt::Semi(expr, Semi { spans: [token.span] }));
                            false
                        } else {
                            let e = take_expr(&mut exprs.exprs[0]);
                            match found {
                                ExtractQuantTriggersFound::Auto => {
                                    exprs.exprs[0] = Expr::Verbatim(
                                        quote_spanned!(exprs.exprs[0].span() => #[verus::internal(auto_trigger)] (#e)),
                                    );
                                }
                                ExtractQuantTriggersFound::AllTriggers => {
                                    exprs.exprs[0] = Expr::Verbatim(
                                        quote_spanned!(exprs.exprs[0].span() => #[verus::internal(all_triggers)] (#e)),
                                    );
                                }
                                ExtractQuantTriggersFound::Triggers(tuple) => {
                                    exprs.exprs[0] = Expr::Verbatim(
                                        quote_spanned_builtin!(builtin, exprs.exprs[0].span() => #builtin::with_triggers(#tuple, #e)),
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
                        stmts.push(Stmt::Semi(
                            Expr::Verbatim(
                                quote_spanned_builtin!(builtin, token.span => #builtin::ensures(|#p: #ty| [#exprs])),
                            ),
                            Semi { spans: [token.span] },
                        ));
                    } else {
                        stmts.push(Stmt::Semi(
                            Expr::Verbatim(
                                quote_spanned_builtin!(builtin, token.span => #builtin::ensures([#exprs])),
                            ),
                            Semi { spans: [token.span] },
                        ));
                    }
                }
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
                    stmts.push(Stmt::Semi(expr, Semi { spans: [token.span] }));
                }
            }
            stmts.push(Stmt::Semi(
                Expr::Verbatim(
                    quote_spanned_builtin!(builtin, token.span => #builtin::decreases((#exprs))),
                ),
                Semi { spans: [token.span] },
            ));
            if let Some((when_token, mut when_expr)) = when {
                self.visit_expr_mut(&mut when_expr);
                stmts.push(Stmt::Semi(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, when_expr.span() => #builtin::decreases_when(#when_expr)),
                    ),
                    Semi { spans: [when_token.span] },
                ));
            }
            if let Some((via_token, via_expr)) = via {
                stmts.push(Stmt::Semi(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, via_expr.span() => #builtin::decreases_by(#via_expr)),
                    ),
                    Semi { spans: [via_token.span] },
                ));
            }
        }
        if let Some(SignatureInvariants { token: _, set }) = opens_invariants {
            match set {
                InvariantNameSet::Any(any) => {
                    stmts.push(Stmt::Semi(
                        Expr::Verbatim(
                            quote_spanned_builtin!(builtin, any.span() => #builtin::opens_invariants_any()),
                        ),
                        Semi { spans: [any.span()] },
                    ));
                }
                InvariantNameSet::None(none) => {
                    stmts.push(Stmt::Semi(
                        Expr::Verbatim(
                            quote_spanned_builtin!(builtin, none.span() => #builtin::opens_invariants_none()),
                        ),
                        Semi { spans: [none.span()] },
                    ));
                }
                InvariantNameSet::List(InvariantNameSetList { bracket_token, mut exprs }) => {
                    for expr in exprs.iter_mut() {
                        self.visit_expr_mut(expr);
                    }
                    stmts.push(Stmt::Semi(
                        Expr::Verbatim(
                            quote_spanned_builtin!(builtin, bracket_token.span => #builtin::opens_invariants([#exprs])),
                        ),
                        Semi { spans: [bracket_token.span] },
                    ));
                }
            }
        }
        if let Some(SignatureUnwind { token, when }) = unwind {
            if let Some((when_token, mut when_expr)) = when {
                self.visit_expr_mut(&mut when_expr);
                stmts.push(Stmt::Semi(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, when_expr.span() => #builtin::no_unwind_when(#when_expr)),
                    ),
                    Semi { spans: [when_token.span] },
                ));
            } else {
                stmts.push(Stmt::Semi(
                    Expr::Verbatim(
                        quote_spanned_builtin!(builtin, token.span() => #builtin::no_unwind()),
                    ),
                    Semi { spans: [token.span] },
                ));
            }
        }

        self.inside_ghost -= 1;
        self.inside_bitvector = false;

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
        con_ensures: &mut Option<Ensures>,
        con_block: &mut Option<Box<Block>>,
        con_expr: &mut Option<Box<Expr>>,
        con_eq_token: &mut Option<Token![=]>,
        con_semi_token: &mut Option<Token![;]>,
        con_span: Span,
    ) {
        let ensures = self.take_ghost(con_ensures);
        if let Some(Ensures { token, mut exprs, attrs }) = ensures {
            self.inside_ghost += 1;
            let mut stmts: Vec<Stmt> = Vec::new();
            if attrs.len() > 0 {
                let err = "outer attributes only allowed on function's ensures";
                let expr = Expr::Verbatim(quote_spanned!(token.span => compile_error!(#err)));
                stmts.push(Stmt::Semi(expr, Semi { spans: [token.span] }));
            } else if exprs.exprs.len() > 0 {
                for expr in exprs.exprs.iter_mut() {
                    self.visit_expr_mut(expr);
                }
                // Use a closure in the ensures to avoid circular const definition.
                // Note: we can't use con.ident as the closure pattern,
                // because Rust would treat this as a const path pattern.
                // So we use a 0-parameter closure.
                stmts.push(stmt_with_semi!(builtin, token.span => #builtin::ensures(|| [#exprs])));
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

    fn visit_const_or_static(
        &mut self,
        span: proc_macro2::Span,
        attrs: &mut Vec<Attribute>,
        vis: Option<&Visibility>,
        publish: &mut Publish,
        mode: &mut FnMode,
    ) {
        if self.erase_ghost.keep() {
            attrs.push(mk_verus_attr(span, quote! { verus_macro }));
        }

        let publish_attrs = match (&mode, vis, &publish) {
            (FnMode::Exec(_) | FnMode::Proof(_), _, _) => vec![],
            (_, Some(Visibility::Inherited), _) => vec![],
            (_, _, Publish::Default) => vec![mk_verus_attr(span, quote! { open })],
            (_, _, Publish::Closed(o)) => vec![mk_verus_attr(o.token.span, quote! { closed })],
            (_, _, Publish::Open(o)) => vec![mk_verus_attr(o.token.span, quote! { open })],
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
            FnMode::Exec(token) => (0, vec![mk_verus_attr(token.exec_token.span, quote! { exec })]),
        };
        self.inside_ghost = inside_ghost;
        self.inside_const = true;
        *publish = Publish::Default;
        *mode = FnMode::Default;
        attrs.extend(publish_attrs);
        attrs.extend(mode_attrs);
        self.filter_attrs(attrs);
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
                if pts.pat.elems.len() == 1
                    && (path_is_ident(&pts.path, "Tracked")
                        || path_is_ident(&pts.path, "Ghost")) =>
            {
                if let Pat::Ident(id) = &mut pts.pat.elems[0] {
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
                        let assign = Stmt::Semi(Expr::Verbatim(assign), Semi { spans: [span] });
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
                self.x_assigns.push(Stmt::Semi(Expr::Verbatim(assign), Semi { spans: [span] }));
                return;
            }
            _ => {}
        }
        syn_verus::visit_mut::visit_pat_mut(self, pat);
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
            stmts.push(Stmt::Semi(mk_proof_block(block), Semi { spans: [span] }));
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
            let init = take_expr(&mut local.init.as_mut().expect("init").1);
            let block1 = parse_quote_spanned!(span => { #tmp = #init });
            stmts.push(Stmt::Semi(mk_proof_block(block1), Semi { spans: [span] }));
            stmts.extend(visit_pat.x_decls);
            let let_pat = if local.tracked.is_some() {
                parse_quote_spanned!(span => #[verus::internal(proof)] let #pat = #tmp;)
            } else {
                parse_quote_spanned!(span => #[verus::internal(spec)] let #pat = #tmp;)
            };
            let mut block_stmts = vec![let_pat];
            block_stmts.extend(visit_pat.x_assigns);
            let block2 = Block { brace_token: Brace(span), stmts: block_stmts };
            stmts.push(Stmt::Semi(mk_proof_block(block2), Semi { spans: [span] }));
            (true, stmts)
        }
    }

    fn visit_stmt_extend(&mut self, stmt: &mut Stmt) -> (bool, Vec<Stmt>) {
        let span = stmt.span();
        match stmt {
            Stmt::Local(local) => self.visit_local_extend(local),
            Stmt::Item(Item::BroadcastUse(broadcast_use)) => {
                let BroadcastUse { attrs, broadcast_use_tokens: _, paths, semi: _ } = broadcast_use;
                if self.erase_ghost.erase() {
                    (true, vec![])
                } else {
                    let stmts: Vec<Stmt> = paths.iter().map(|path| Stmt::Expr(Expr::Verbatim(
                        quote_spanned_builtin!(builtin, span => #builtin::reveal_hide_({#[verus::internal(reveal_fn)] fn __VERUS_REVEAL_INTERNAL__() { #builtin::reveal_hide_internal_path_(#path) } #[verus::internal(broadcast_use_reveal)] __VERUS_REVEAL_INTERNAL__}, 1); )
                    ))).collect();
                    let mut attrs = attrs.clone();
                    if self.inside_ghost == 0 {
                        attrs.push(mk_verus_attr(span, quote! { proof_block }));
                    }
                    let block = Stmt::Expr(Expr::Block(ExprBlock {
                        attrs: attrs,
                        label: None,
                        block: Block { brace_token: token::Brace(span), stmts },
                    }));
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
                    FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) => false,
                    FnMode::Exec(_) | FnMode::Default => true,
                },
                Item::Const(c) => match c.mode {
                    FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) => false,
                    FnMode::Exec(_) | FnMode::Default => true,
                },
                _ => true,
            });
            // We can't erase ghost datatypes D, because they can be used
            // as Ghost<D> or Tracked<D>.
        }
        let erase_ghost = self.erase_ghost.erase();
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
                        FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_),
                    ) if erase_ghost => {
                        // replace body with panic!()
                        let expr: Expr = Expr::Verbatim(quote_spanned! {
                            span => { panic!() }
                        });
                        let stmt = Stmt::Expr(expr);
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
                    FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) if erase_ghost => {
                        Some((fun.sig.ident.clone(), fun.vis.clone()))
                    }
                    _ => None,
                },
                Item::Const(c) => match (&c.vis, &c.mode) {
                    (Visibility::Public(_), _) => None,
                    (_, FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_))
                        if erase_ghost =>
                    {
                        Some((c.ident.clone(), c.vis.clone()))
                    }
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
                    let static_assert_size = quote! {
                        if ::core::mem::size_of::<#type_>() != #size_lit {
                            panic!("does not have the expected size");
                        }
                    };
                    let static_assert_align = if let Some(align_lit) = align_lit {
                        quote! {
                            if ::core::mem::align_of::<#type_>() != #align_lit {
                                panic!("does not have the expected alignment");
                            }
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
                                quote! { ::vstd::layout::align_of::<#type_>() == #align_lit, }
                            } else {
                                quote! {}
                            };

                            *item = Item::Verbatim(quote_spanned_builtin! { builtin, span =>
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
                                        #[trigger] ::vstd::layout::size_of::<#type_>() == #size_lit,
                                        #ensures_align
                                {
                                }
                            }
                            });
                        }
                    }
                }
                Item::BroadcastUse(item_broadcast_use) => {
                    let span = item.span();
                    let paths = &item_broadcast_use.paths;
                    if self.erase_ghost.erase() {
                        *item = Item::Verbatim(quote! { const _: () = (); });
                    } else {
                        let stmts: Vec<Stmt> = paths.iter().map(|path| Stmt::Expr(Expr::Verbatim(
                            quote_spanned_builtin!(builtin, span => #builtin::reveal_hide_({#[verus::internal(reveal_fn)] fn __VERUS_REVEAL_INTERNAL__() { #builtin::reveal_hide_internal_path_(#path) } #[verus::internal(broadcast_use_reveal)] __VERUS_REVEAL_INTERNAL__}, 1); )
                        ))).collect();
                        let block = Block { brace_token: token::Brace { span }, stmts };
                        *item = Item::Verbatim(quote_spanned! { span =>
                            #[verus::internal(item_broadcast_use)] const _: () = #block;
                        });
                    }
                }
                Item::BroadcastGroup(item_broadcast_group) => {
                    *item = Item::Verbatim(
                        self.handle_broadcast_group(item_broadcast_group, item.span()),
                    );
                }
                _ => (),
            }
        }
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
                #builtin::reveal_hide_({#[verus::internal(reveal_fn)] fn __VERUS_REVEAL_INTERNAL__() { #builtin::reveal_hide_internal_path_(#path) } __VERUS_REVEAL_INTERNAL__}, 1); })))
                .collect();
            let block = Block { brace_token: token::Brace { span }, stmts };
            let mut item_fn: ItemFn = parse_quote_spanned! { span =>
                #[verus::internal(reveal_group)]
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
                ImplItem::Method(fun) => match fun.sig.mode {
                    FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) => false,
                    FnMode::Exec(_) | FnMode::Default => true,
                },
                ImplItem::Const(c) => match c.mode {
                    FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) => false,
                    FnMode::Exec(_) | FnMode::Default => true,
                },
                _ => true,
            });
        }
        let erase_ghost = self.erase_ghost.erase();
        // Unfortunately, we just have to assume that if for_trait == true,
        // the methods might be public
        items.retain(|item| match item {
            ImplItem::Method(fun) => match ((&fun.vis, for_trait), &fun.sig.mode) {
                (
                    (Visibility::Public(_), _) | (_, true),
                    FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_),
                ) => true,
                (_, FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_)) => !erase_ghost,
                (_, FnMode::Exec(_) | FnMode::Default) => true,
            },
            ImplItem::Const(c) => match (&c.vis, &c.mode) {
                (Visibility::Public(_), _) => true,
                (_, FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_)) => !erase_ghost,
                (_, FnMode::Exec(_) | FnMode::Default) => true,
            },
            _ => true,
        });
        for item in items.iter_mut() {
            let span = item.span();
            match item {
                ImplItem::Method(fun) => match ((&fun.vis, for_trait), &fun.sig.mode) {
                    (
                        (Visibility::Public(_), _) | (_, true),
                        FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_),
                    ) if erase_ghost => {
                        // replace body with panic!()
                        let expr: Expr = Expr::Verbatim(quote_spanned! {
                            span => { panic!() }
                        });
                        let stmt = Stmt::Expr(expr);
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
        if self.erase_ghost.erase_all() {
            items.retain(|item| match item {
                TraitItem::Method(fun) => match fun.sig.mode {
                    FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) => false,
                    FnMode::Exec(_) | FnMode::Default => true,
                },
                _ => true,
            });
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
        let erase_ghost = self.erase_ghost.erase();
        let mut spec_items: Vec<TraitItem> = Vec::new();
        for item in items.iter_mut() {
            match item {
                TraitItem::Method(ref mut fun) if !erase_ghost && fun.default.is_none() => {
                    // Copy into separate spec method, then remove spec from original method
                    let mut spec_fun = fun.clone();
                    let x = &fun.sig.ident;
                    let span = x.span();
                    spec_fun.sig.ident = Ident::new(&format!("{VERUS_SPEC}{x}"), span);
                    spec_fun.attrs.push(mk_rust_attr(span, "doc", quote! { hidden }));
                    fun.sig.erase_spec_fields();
                    spec_items.push(TraitItem::Method(spec_fun));
                }
                TraitItem::Method(fun) if erase_ghost => match (&mut fun.default, &fun.sig.mode) {
                    (
                        Some(default),
                        FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_),
                    ) => {
                        // replace body with panic!()
                        let span = default.span();
                        let expr: Expr = Expr::Verbatim(quote_spanned! {
                            span => { panic!() }
                        });
                        let stmt = Stmt::Expr(expr);
                        default.stmts = vec![stmt];
                    }
                    _ => {}
                },
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
                    .map(|arg| match arg {
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
                stmts.push(Stmt::Semi(expr, Semi { spans: [token.span] }));
            } else if exprs.exprs.len() > 0 {
                stmts.push(stmt_with_semi!(builtin, token.span => #builtin::ensures([#exprs])));
            }
        }
        if let Some(Decreases { token, exprs }) = decreases {
            for expr in exprs.exprs.iter() {
                if matches!(expr, Expr::Tuple(..)) {
                    let err = "decreases cannot be a tuple; use `decreases x, y` rather than `decreases (x, y)`";
                    let expr = Expr::Verbatim(quote_spanned!(token.span => compile_error!(#err)));
                    stmts.push(Stmt::Semi(expr, Semi { spans: [token.span] }));
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
        //      let VERUS_loop_result = match ::core::iter::IntoIterator::into_iter(e) {
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
        //                                  &::core::iter::IntoIterator::into_iter(e)))),
        //                      { let x =
        //                          ::vstd::pervasive::ForLoopGhostIterator::ghost_peek_next(&y)
        //                          .unwrap_or(vstd::pervasive::arbitrary());
        //                        inv },
        //                  ensures
        //                      ::vstd::pervasive::ForLoopGhostIterator::ghost_ensures(&y),
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
            decreases,
            body,
        } = for_loop;

        let no_loop_invariant = attrs.iter().position(|attr| {
            attr.path.segments.len() == 2
                && attr.path.segments[0].ident.to_string() == "verifier"
                && attr.path.segments[1].ident.to_string() == "no_loop_invariant"
        });
        if let Some(i) = no_loop_invariant {
            attrs.remove(i);
        }
        // Note: in principle, the automatically generated loop invariant
        // should always succeed.  In case something goes unexpectedly wrong, though,
        // give people a reasonable way to disable it:
        let no_auto_loop_invariant = attrs.iter().position(|attr| {
            attr.path.segments.len() == 2
                && attr.path.segments[0].ident.to_string() == "verifier"
                && attr.path.segments[1].ident.to_string() == "no_auto_loop_invariant"
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
        //                          &::core::iter::IntoIterator::into_iter(e)))),
        let exec_inv: Expr = Expr::Verbatim(quote_spanned!(expr.span() =>
            #[verifier::custom_err(#exec_inv_msg)]
            ::vstd::pervasive::ForLoopGhostIterator::exec_invariant(&#x_ghost_iter, &#x_exec_iter)
        ));
        let ghost_inv: Expr = Expr::Verbatim(quote_spanned!(expr.span() =>
            #[verifier::custom_err(#ghost_inv_msg)]
            ::vstd::pervasive::ForLoopGhostIterator::ghost_invariant(&#x_ghost_iter,
                builtin::infer_spec_for_loop_iter(
                    &::vstd::pervasive::ForLoopGhostIteratorNew::ghost_iter(
                        &::core::iter::IntoIterator::into_iter(#expr_inv)),
                    #print_hint,
                ))
        ));
        let invariant_for = if let Some(mut invariant) = invariant {
            for inv in &mut invariant.exprs.exprs {
                *inv = Expr::Verbatim(quote_spanned!(inv.span() => {
                    let #pat =
                        ::vstd::pervasive::ForLoopGhostIterator::ghost_peek_next(&#x_ghost_iter)
                        .unwrap_or(::vstd::pervasive::arbitrary());
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
        // REVIEW: we might also want no_auto_loop_invariant to suppress the ensures,
        // but at the moment, user-supplied ensures aren't supported, so this would be hard to use.
        let ensure = if no_loop_invariant.is_none() {
            Some(parse_quote_spanned!(span =>
                ensures ::vstd::pervasive::ForLoopGhostIterator::ghost_ensures(&#x_ghost_iter),
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
            let body_ghost = Expr::Verbatim(quote_spanned!(span =>
                #[verifier::proof_block] {
                    #x_ghost_iter = ::vstd::pervasive::ForLoopGhostIterator::ghost_advance(
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
            Expr::Verbatim(quote_spanned!(span => {
                #[allow(non_snake_case)]
                #[verus::internal(spec)]
                let mut #x_ghost_iter;
                #[verifier::proof_block] {
                    #x_ghost_iter =
                        ::vstd::pervasive::ForLoopGhostIteratorNew::ghost_iter(&#x_exec_iter);
                }
                #loop_expr
            }))
        } else {
            Expr::Verbatim(quote_spanned!(span => { #loop_expr }))
        };
        Expr::Verbatim(quote_spanned!(span => {
            #[allow(non_snake_case)]
            let VERUS_loop_result = match ::core::iter::IntoIterator::into_iter(#expr) {
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
            let trigger: syn_verus::Result<syn_verus::Specification> =
                syn_verus::parse2(attr.tokens.clone());
            let path_segments_str =
                attr.path.segments.iter().map(|x| x.ident.to_string()).collect::<Vec<_>>();
            let ident_str = match &path_segments_str[..] {
                [attr_name] => Some(attr_name),
                _ => None,
            };
            match (trigger, ident_str) {
                (Ok(trigger), Some(id)) if id == &"auto" && trigger.exprs.len() == 0 => {
                    return Ok(ExtractQuantTriggersFound::Auto);
                }
                (Ok(trigger), Some(id)) if id == &"all_triggers" && trigger.exprs.len() == 0 => {
                    return Ok(ExtractQuantTriggersFound::AllTriggers);
                }
                (Ok(trigger), Some(id)) if id == &"trigger" => {
                    let mut exprs = trigger.exprs;
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
        if self.chain_operators(expr) {
            return;
        } else if self.closure_quant_operators(expr) {
            return;
        }

        if let Expr::Binary(ExprBinary { op, right, .. }) = &expr {
            if let Expr::Matches(ExprMatches {
                op_expr: Some(MatchesOpExpr { op_token, .. }),
                ..
            }) = &**right
            {
                match (op, op_token) {
                    (_, MatchesOpToken::BigAnd) => (),
                    (_, MatchesOpToken::Implies(_)) => {
                        *expr = Expr::Verbatim(
                            quote_spanned! { expr.span() => compile_error!("matches with ==> is currently not allowed on the right-hand-side of most binary operators (use parentheses)") },
                        );
                    }
                    (_, MatchesOpToken::AndAnd(_)) => {
                        *expr = Expr::Verbatim(
                            quote_spanned! { expr.span() => compile_error!("matches with && is currently not allowed on the right-hand-side of most binary operators (use parentheses)") },
                        );
                    }
                }
            }
        }

        let is_inside_bitvector = match &expr {
            Expr::Assert(a) => match &a.prover {
                Some((_, id)) => {
                    if id.to_string() == "bit_vector" {
                        self.inside_bitvector = true;
                        true
                    } else {
                        false
                    }
                }
                None => false,
            },
            _ => false,
        };

        let is_auto_proof_block = if self.inside_ghost == 0 {
            match &expr {
                Expr::Assume(a) => Some(a.assume_token.span),
                Expr::Assert(a) => Some(a.assert_token.span),
                Expr::AssertForall(a) => Some(a.assert_token.span),
                Expr::RevealHide(a) if a.hide_token.is_none() => Some(
                    a.reveal_token
                        .map(|x| x.span)
                        .or(a.reveal_with_fuel_token.map(|x| x.span))
                        .expect("missing span for Reveal"),
                ),
                _ => None,
            }
        } else {
            None
        };
        if let Some(_) = is_auto_proof_block {
            self.inside_ghost += 1;
        }

        let mode_block = match expr {
            Expr::Unary(ExprUnary { op: UnOp::Proof(..), .. }) => Some((false, false)),
            Expr::Call(ExprCall { func, args, .. }) => match &**func {
                Expr::Path(path) if path.qself.is_none() && args.len() == 1 => {
                    if path_is_ident(&path.path, "Ghost") {
                        Some((true, false))
                    } else if path_is_ident(&path.path, "Tracked") {
                        Some((true, true))
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        };

        let sub_inside_arith = match expr {
            Expr::Paren(..) | Expr::Block(..) | Expr::Group(..) => self.inside_arith,
            Expr::Cast(..) => InsideArith::Widen,
            Expr::Unary(unary) => match unary.op {
                UnOp::Neg(..) => InsideArith::Widen,
                UnOp::Not(..) => InsideArith::Fixed,
                _ => InsideArith::None,
            },
            Expr::Binary(binary) => match binary.op {
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
            },
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
        let use_spec_traits = self.use_spec_traits && is_inside_ghost;
        if mode_block.is_some() {
            self.inside_ghost += 1;
        }
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
        if mode_block.is_some() {
            self.inside_ghost -= 1;
        }
        self.inside_arith = is_inside_arith;
        self.assign_to = is_assign_to;

        if let Expr::Call(call) = expr {
            if let Some((_, is_tracked)) = mode_block {
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
            }
        } else if let Expr::Unary(unary) = expr {
            let span = unary.span();
            if let Some(mode_block) = mode_block {
                match (is_inside_ghost, mode_block, &*unary.expr) {
                    (false, (false, _), Expr::Block(..)) => {
                        // proof { ... }
                        let inner = take_expr(&mut *unary.expr);
                        *expr = self.maybe_erase_expr(
                            span,
                            Expr::Verbatim(
                                quote_spanned!(span => #[verifier::proof_block] /* vattr */ #inner),
                            ),
                        );
                    }
                    _ => {
                        *expr = Expr::Verbatim(
                            quote_spanned!(span => compile_error!("unexpected proof block")),
                        );
                        return;
                    }
                }
            }
        } else if let Expr::Binary(binary) = expr {
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
                let func = Box::new(Expr::Verbatim(
                    quote_spanned_builtin!(builtin, span => #builtin::imply),
                ));
                let paren_token = Paren { span };
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
                let paren_token = Paren { span };
                let mut args = Punctuated::new();
                args.push(take_expr(&mut *binary.left));
                args.push(take_expr(&mut *binary.right));
                let call = Expr::Call(ExprCall { attrs, func, paren_token, args });
                if eq {
                    *expr = call;
                } else {
                    *expr = Expr::Verbatim(quote_spanned!(span => ! #call));
                }
            }
        } else if let Expr::BigAnd(exprs) = expr {
            let mut new_expr = take_expr(&mut exprs.exprs[0].1);
            for i in 1..exprs.exprs.len() {
                let span = exprs.exprs[i].0.span();
                let spans = [span, span];
                let right = take_expr(&mut exprs.exprs[i].1);
                let left = Box::new(Expr::Verbatim(quote_spanned!(new_expr.span() => (#new_expr))));
                let right = Box::new(Expr::Verbatim(quote_spanned!(right.span() => (#right))));
                let attrs = Vec::new();
                let op = BinOp::And(syn_verus::token::AndAnd { spans });
                let bin = ExprBinary { attrs, op, left, right };
                new_expr = Expr::Binary(bin);
            }
            *expr = new_expr;
        } else if let Expr::BigOr(exprs) = expr {
            let mut new_expr = take_expr(&mut exprs.exprs[0].1);
            for i in 1..exprs.exprs.len() {
                let span = exprs.exprs[i].0.span();
                let spans = [span, span];
                let right = take_expr(&mut exprs.exprs[i].1);
                let left = Box::new(Expr::Verbatim(quote_spanned!(new_expr.span() => (#new_expr))));
                let right = Box::new(Expr::Verbatim(quote_spanned!(right.span() => (#right))));
                let attrs = Vec::new();
                let op = BinOp::Or(syn_verus::token::OrOr { spans });
                let bin = ExprBinary { attrs, op, left, right };
                new_expr = Expr::Binary(bin);
            }
            *expr = new_expr;
        } else if let Expr::Macro(macro_expr) = expr {
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
            Expr::Lit(ExprLit { lit: Lit::Int(..), .. }) if use_spec_traits => true,
            Expr::Cast(cast) if use_spec_traits && !is_ptr_type(&cast.ty) => true,
            Expr::Index(..) if use_spec_traits => true,
            Expr::Unary(ExprUnary { op: UnOp::Forall(..), .. }) => true,
            Expr::Unary(ExprUnary { op: UnOp::Exists(..), .. }) => true,
            Expr::Unary(ExprUnary { op: UnOp::Choose(..), .. }) => true,
            Expr::Unary(ExprUnary { op: UnOp::Neg(..), .. }) if use_spec_traits => true,
            Expr::Binary(ExprBinary {
                op:
                    BinOp::Eq(..)
                    | BinOp::Ne(..)
                    | BinOp::Le(..)
                    | BinOp::Lt(..)
                    | BinOp::Ge(..)
                    | BinOp::Gt(..)
                    | BinOp::Add(..)
                    | BinOp::Sub(..)
                    | BinOp::Mul(..)
                    | BinOp::Div(..)
                    | BinOp::Rem(..)
                    | BinOp::BitAnd(..)
                    | BinOp::BitOr(..)
                    | BinOp::BitXor(..)
                    | BinOp::Shl(..)
                    | BinOp::Shr(..),
                ..
            }) if use_spec_traits => true,
            Expr::Assume(..) | Expr::Assert(..) | Expr::AssertForall(..) | Expr::RevealHide(..) => {
                true
            }
            Expr::View(..) => true,
            Expr::Closure(..) => true,
            Expr::Is(..) => true,
            Expr::Has(..) => true,
            Expr::ForLoop(..) => true,
            Expr::Matches(..) => true,
            Expr::GetField(..) => true,
            _ => false,
        };
        if do_replace && self.inside_type == 0 {
            match take_expr(expr) {
                Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs }) => {
                    let span = lit.span();
                    let n = lit.base10_digits().to_string();
                    if lit.suffix() == "" {
                        match is_inside_arith {
                            InsideArith::None => {
                                // We don't know which integer type to use,
                                // so defer the decision to type inference.
                                *expr = quote_verbatim!(builtin, span, attrs => #builtin::spec_literal_integer(#n));
                            }
                            InsideArith::Widen if n.starts_with("-") => {
                                // Use int inside +, -, etc., since these promote to int anyway
                                *expr = quote_verbatim!(builtin, span, attrs => #builtin::spec_literal_int(#n));
                            }
                            InsideArith::Widen => {
                                // Use int inside +, -, etc., since these promote to int anyway
                                *expr = quote_verbatim!(builtin, span, attrs => #builtin::spec_literal_nat(#n));
                            }
                            InsideArith::Fixed => {
                                // We generally won't want int/nat literals for bitwise ops,
                                // so use Rust's native integer literals
                                *expr = Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs });
                            }
                        }
                    } else if lit.suffix() == "int" {
                        *expr =
                            quote_verbatim!(builtin, span, attrs => #builtin::spec_literal_int(#n));
                    } else if lit.suffix() == "nat" {
                        *expr =
                            quote_verbatim!(builtin, span, attrs => #builtin::spec_literal_nat(#n));
                    } else {
                        // Has a native Rust integer suffix, so leave it as a native Rust literal
                        *expr = Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs });
                    }
                }
                Expr::Cast(cast) => {
                    let span = cast.span();
                    let src = cast.expr;
                    let attrs = cast.attrs;
                    let ty = cast.ty;
                    *expr = quote_verbatim!(builtin, span, attrs => #builtin::spec_cast_integer::<_, #ty>(#src));
                }
                Expr::Index(idx) => {
                    let span = idx.span();
                    let src = idx.expr;
                    let attrs = idx.attrs;
                    let index = idx.index;
                    *expr = quote_verbatim!(span, attrs => #src.spec_index(#index));
                }
                Expr::Unary(unary) => {
                    let span = unary.span();
                    let attrs = unary.attrs;
                    match unary.op {
                        UnOp::Neg(neg) => {
                            let arg = unary.expr;
                            if let Expr::Lit(..) = &*arg {
                                // leave native Rust literal with native Rust negation
                                *expr =
                                    Expr::Unary(ExprUnary { op: UnOp::Neg(neg), expr: arg, attrs });
                            } else {
                                *expr = quote_verbatim!(span, attrs => (#arg).spec_neg());
                            }
                        }
                        _ => panic!("unary"),
                    }
                }
                Expr::Binary(binary) => {
                    let span = binary.span();
                    let attrs = binary.attrs;
                    let left = binary.left;
                    let right = binary.right;
                    match binary.op {
                        BinOp::Eq(..) => {
                            *expr = quote_verbatim!(builtin, span, attrs => #builtin::spec_eq(#left, #right));
                        }
                        BinOp::Ne(..) => {
                            *expr = quote_verbatim!(builtin, span, attrs => ! #builtin::spec_eq(#left, #right));
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
                            *expr =
                                quote_verbatim!(span, attrs => #left.spec_euclidean_div(#right));
                        }
                        BinOp::Rem(..) => {
                            let left = quote_spanned! { left.span() => (#left) };
                            *expr =
                                quote_verbatim!(span, attrs => #left.spec_euclidean_mod(#right));
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
                        _ => panic!("binary"),
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
                    let borrowed: Expr =
                        Expr::Verbatim(quote_spanned!(span1 => #base.borrow_mut()));
                    *expr = quote_verbatim!(span2, attrs => (*(#borrowed)));
                }
                Expr::Assume(assume) => {
                    let span = assume.assume_token.span;
                    let arg = assume.expr;
                    let attrs = assume.attrs;
                    *expr = quote_verbatim!(builtin, span, attrs => #builtin::assume_(#arg));
                }
                Expr::Assert(assert) => {
                    let span = assert.assert_token.span;
                    let arg = assert.expr;
                    let attrs = assert.attrs;

                    if let Some(prover) = assert.prover {
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
                                    Block { brace_token: token::Brace { span }, stmts: vec![] }
                                };
                                let mut stmts: Vec<Stmt> = Vec::new();
                                if let Some(Requires { token, exprs }) = assert.requires {
                                    stmts.push(Stmt::Semi(
                                        Expr::Verbatim(
                                            quote_spanned_builtin!(builtin, token.span => #builtin::requires([#exprs])),
                                        ),
                                        Semi { spans: [token.span] },
                                    ));
                                }
                                stmts.push(Stmt::Semi(
                                    Expr::Verbatim(
                                        quote_spanned_builtin!(builtin, span => #builtin::ensures(#arg)),
                                    ),
                                    Semi { spans: [span] },
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
                    } else if let Some(block) = assert.body {
                        // assert-by
                        if assert.requires.is_some() {
                            *expr = quote_verbatim!(span, attrs => compile_error!("the 'requires' clause is only used with the 'bit_vector' and 'nonlinear_arith' solvers (use `by(bit_vector)` or `by(nonlinear_arith)"));
                        } else {
                            *expr = quote_verbatim!(builtin, span, attrs => {#builtin::assert_by(#arg, #block);});
                        }
                    } else {
                        // Normal 'assert'
                        *expr = quote_verbatim!(builtin, span, attrs => #builtin::assert_(#arg));
                    }
                }
                Expr::AssertForall(assert) => {
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
                            return;
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
                }
                Expr::RevealHide(reveal) => {
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
                    let expr_replacement = if path
                        .path
                        .segments
                        .first()
                        .map(|x| x.ident.to_string())
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
                }
                Expr::ForLoop(for_loop) => {
                    *expr = self.desugar_for_loop(for_loop);
                }
                Expr::Closure(mut clos) => {
                    if is_inside_ghost {
                        let span = clos.span();
                        if clos.requires.is_some() || clos.ensures.is_some() {
                            let err = "ghost closures cannot have requires/ensures";
                            *expr = Expr::Verbatim(quote_spanned!(span => compile_error!(#err)));
                            return;
                        }
                        *expr = Expr::Verbatim(quote_spanned_builtin!(builtin, span =>
                            #builtin::closure_to_fn_spec(#clos)
                        ));
                    } else {
                        let ret_pat = match &mut clos.output {
                            ReturnType::Default => None,
                            ReturnType::Type(_, ref mut tracked, ref mut ret_opt, ty) => {
                                self.visit_type_mut(ty);
                                if let Some(tracked) = tracked {
                                    *expr = Expr::Verbatim(quote_spanned!(tracked.span() =>
                                        compile_error!("'tracked' not supported here")
                                    ));
                                    return;
                                }
                                match std::mem::take(ret_opt) {
                                    None => None,
                                    Some(ret) => Some((ret.1.clone(), ty.clone())),
                                }
                            }
                        };
                        let requires = self.take_ghost(&mut clos.requires);
                        let ensures = self.take_ghost(&mut clos.ensures);
                        let mut stmts: Vec<Stmt> = Vec::new();
                        // TODO: wrap specs inside ghost blocks
                        self.inside_ghost += 1;
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
                                let expr = Expr::Verbatim(
                                    quote_spanned!(token.span => compile_error!(#err)),
                                );
                                stmts.push(Stmt::Semi(expr, Semi { spans: [token.span] }));
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
                        *expr = Expr::Closure(clos);
                    }
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
                Expr::Has(has) => {
                    let has_token = has.has_token;
                    let span = has.span();
                    let rhs = has.rhs;
                    let has_call = quote_spanned!(has_token.span => .spec_has(#rhs));
                    let lhs = has.lhs;
                    *expr = Expr::Verbatim(quote_spanned!(span => (#lhs#has_call)));
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
                _ => panic!("expected to replace expression"),
            }
        }

        if let Some(span) = is_auto_proof_block {
            // automatically put assert/assume in a proof block
            self.inside_ghost -= 1;
            let inner = take_expr(expr);
            *expr = self.maybe_erase_expr(
                span,
                Expr::Verbatim(
                    quote_spanned!(span => #[verifier::proof_block] /* vattr */ { #inner } ),
                ),
            );
        }
        if is_inside_bitvector {
            self.inside_bitvector = false;
        }
    }

    fn visit_attribute_mut(&mut self, attr: &mut Attribute) {
        if let syn_verus::AttrStyle::Outer = attr.style {
            match &attr.path.segments.iter().map(|x| &x.ident).collect::<Vec<_>>()[..] {
                [attr_name] if attr_name.to_string() == "trigger" => {
                    *attr = mk_verus_attr(attr.span(), quote! { trigger });
                }
                [attr_name] if attr_name.to_string() == "via_fn" => {
                    *attr = mk_verus_attr(attr.span(), quote! { via });
                }
                [attr_name] if attr_name.to_string() == "verifier" => {
                    let Ok(parsed) = attr.parse_meta() else {
                        return;
                    };
                    let span = attr.span();
                    fn path_verifier(span: Span) -> Punctuated<PathSegment, Colon2> {
                        let mut path_segments = Punctuated::new();
                        path_segments.push(PathSegment {
                            ident: Ident::new("verifier", span),
                            arguments: PathArguments::None,
                        });
                        path_segments
                    }
                    fn invalid_attribute(span: Span) -> Attribute {
                        let mut path_segments = path_verifier(span);
                        path_segments.push(PathSegment {
                            ident: Ident::new("invalid_attribute", span),
                            arguments: PathArguments::None,
                        });
                        Attribute {
                            pound_token: token::Pound { spans: [span] },
                            style: AttrStyle::Outer,
                            bracket_token: token::Bracket { span },
                            path: Path { leading_colon: None, segments: path_segments },
                            tokens: quote!(),
                        }
                    }
                    match parsed {
                        syn_verus::Meta::List(meta_list) if meta_list.nested.len() == 1 => {
                            let (second_segment, nested) = match &meta_list.nested[0] {
                                syn_verus::NestedMeta::Meta(syn_verus::Meta::List(meta_list)) => {
                                    let rest = &meta_list.nested[0];
                                    (&meta_list.path.segments[0], Some(quote! { (#rest) }))
                                }
                                syn_verus::NestedMeta::Meta(syn_verus::Meta::Path(meta_path)) => {
                                    (&meta_path.segments[0], None)
                                }
                                _ => {
                                    *attr = invalid_attribute(span);
                                    return;
                                }
                            };
                            let mut path_segments = path_verifier(span);
                            path_segments.push(second_segment.clone());
                            *attr = Attribute {
                                pound_token: token::Pound { spans: [span] },
                                style: AttrStyle::Outer,
                                bracket_token: token::Bracket { span },
                                path: Path { leading_colon: None, segments: path_segments },
                                tokens: if let Some(nested) = nested {
                                    quote! { #nested }
                                } else {
                                    quote! {}
                                },
                            };
                        }
                        _ => {
                            *attr = invalid_attribute(span);
                            return;
                        }
                    }
                }
                _ => (),
            }
        }

        if let syn_verus::AttrStyle::Inner(_) = attr.style {
            match &attr.path.segments.iter().map(|x| &x.ident).collect::<Vec<_>>()[..] {
                [attr_name] if attr_name.to_string() == "trigger" => {
                    // process something like: #![trigger f(a, b), g(c, d)]
                    // attr.tokens is f(a, b), g(c, d)
                    // turn this into a tuple (f(a, b), g(c, d)),
                    // parse it into an Expr, visit the Expr, turn the Expr back into tokens,
                    // remove the ( and ).
                    let old_stream = proc_macro::TokenStream::from(attr.tokens.clone());
                    let mut tuple_stream = proc_macro::TokenStream::new();
                    let group =
                        proc_macro::Group::new(proc_macro::Delimiter::Parenthesis, old_stream);
                    tuple_stream.extend(vec![proc_macro::TokenTree::Group(group)]);
                    let mut new_tuples = self.visit_stream_expr(tuple_stream).into_iter();
                    let new_tuple = new_tuples.next().expect("visited tuple");
                    assert!(new_tuples.next().is_none());
                    if let proc_macro::TokenTree::Group(group) = new_tuple {
                        assert!(group.delimiter() == proc_macro::Delimiter::Parenthesis);
                        attr.tokens = proc_macro2::TokenStream::from(group.stream());
                    } else {
                        panic!("expected tuple");
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

    fn visit_impl_item_method_mut(&mut self, method: &mut ImplItemMethod) {
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
        visit_impl_item_method_mut(self, method);
        if is_external_code {
            self.inside_external_code -= 1;
        }
    }

    fn visit_trait_item_method_mut(&mut self, method: &mut TraitItemMethod) {
        if self.rustdoc {
            crate::rustdoc::process_trait_item_method(method);
        }

        let is_spec_method = method.sig.ident.to_string().starts_with(VERUS_SPEC);
        let mut stmts =
            self.visit_fn(&mut method.attrs, None, &mut method.sig, method.semi_token, true);
        if let Some(block) = &mut method.default {
            block.stmts.splice(0..0, stmts);
        } else if self.erase_ghost.keep() && is_spec_method {
            let span = method.sig.fn_token.span;
            stmts.push(Stmt::Expr(Expr::Verbatim(
                quote_spanned_builtin!(builtin, span => #builtin::no_method_body()),
            )));
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
        visit_trait_item_method_mut(self, method);
        if is_external_code {
            self.inside_external_code -= 1;
        }
    }

    fn visit_item_const_mut(&mut self, con: &mut ItemConst) {
        self.visit_const_or_static(
            con.const_token.span,
            &mut con.attrs,
            Some(&con.vis),
            &mut con.publish,
            &mut con.mode,
        );
        self.desugar_const_or_static(
            &mut con.ensures,
            &mut con.block,
            &mut con.expr,
            &mut con.eq_token,
            &mut con.semi_token,
            con.const_token.span,
        );
        visit_item_const_mut(self, con);
    }

    fn visit_item_static_mut(&mut self, sta: &mut ItemStatic) {
        self.visit_const_or_static(
            sta.static_token.span,
            &mut sta.attrs,
            Some(&sta.vis),
            &mut sta.publish,
            &mut sta.mode,
        );
        self.desugar_const_or_static(
            &mut sta.ensures,
            &mut sta.block,
            &mut sta.expr,
            &mut sta.eq_token,
            &mut sta.semi_token,
            sta.static_token.span,
        );
        visit_item_static_mut(self, sta);
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

    fn visit_generic_method_argument_mut(&mut self, arg: &mut syn_verus::GenericMethodArgument) {
        self.inside_type += 1;
        syn_verus::visit_mut::visit_generic_method_argument_mut(self, arg);
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
    Expr(Expr),
}

#[derive(Debug)]
enum MacroElementExplicitExpr {
    Comma(Token![,]),
    Semi(Token![;]),
    FatArrow(Token![=>]),
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
        inside_bitvector: false,
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
        inside_bitvector: false,
    };
    visitor.visit_expr_mut(&mut expr);
    expr.to_tokens(&mut new_stream);
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
        inside_bitvector: false,
    };
    visitor.visit_expr_mut(expr);
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
    for i in 0..(if tokens.len() >= 2 { tokens.len() - 2 } else { 0 }) {
        let t0 = pun(&tokens[i]);
        let t1 = pun(&tokens[i + 1]);
        let t2 = pun(&tokens[i + 2]);
        let t3 = if i + 3 < tokens.len() { pun(&tokens[i + 3]) } else { None };
        match (t0, t1, t2, t3) {
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
                    tokens[i + 1] = mk_joint_punct(t1);
                }
            }
            (Some(('=', Alone, _)), Some(('~', Alone, s1)), Some(('=', Alone, s2)), _)
            | (Some(('!', Alone, _)), Some(('~', Alone, s1)), Some(('=', Alone, s2)), _) => {
                if adjacent(s1, s2) {
                    tokens[i] = mk_joint_punct(t0);
                    tokens[i + 1] = mk_joint_punct(t1);
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
                    tokens[i + 1] = mk_joint_punct(t1);
                    tokens[i + 2] = mk_joint_punct(t2);
                }
            }
            _ => {}
        }
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
        inside_bitvector: false,
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
        inside_bitvector: false,
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
        inside_bitvector: false,
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

fn has_external_code(attrs: &Vec<Attribute>) -> bool {
    attrs.iter().any(|attr| {
        // verifier::external
        attr.path.segments.len() == 2
            && attr.path.segments[0].ident.to_string() == "verifier"
            && (attr.path.segments[1].ident.to_string() == "external"
                || attr.path.segments[1].ident.to_string() == "external_body")
        // verifier(external)
        || attr.path.segments.len() == 1
            && attr.path.segments[0].ident.to_string() == "verifier"
            && matches!(attr.tokens.to_string().as_str(), "(external)" | "(external_body)")
    })
}

/// Constructs #[name(tokens)]
fn mk_rust_attr(span: Span, name: &str, tokens: TokenStream) -> Attribute {
    let mut path_segments = Punctuated::new();
    path_segments
        .push(PathSegment { ident: Ident::new(name, span), arguments: PathArguments::None });
    Attribute {
        pound_token: token::Pound { spans: [span] },
        style: AttrStyle::Outer,
        bracket_token: token::Bracket { span },
        path: Path { leading_colon: None, segments: path_segments },
        tokens: quote! { (#tokens) },
    }
}

/// Constructs #[verus::internal(tokens)]
fn mk_verus_attr(span: Span, tokens: TokenStream) -> Attribute {
    let mut path_segments = Punctuated::new();
    path_segments
        .push(PathSegment { ident: Ident::new("verus", span), arguments: PathArguments::None });
    path_segments
        .push(PathSegment { ident: Ident::new("internal", span), arguments: PathArguments::None });
    Attribute {
        pound_token: token::Pound { spans: [span] },
        style: AttrStyle::Outer,
        bracket_token: token::Bracket { span },
        path: Path { leading_colon: None, segments: path_segments },
        tokens: quote! { (#tokens) },
    }
}

fn is_ptr_type(typ: &Type) -> bool {
    match typ {
        Type::Ptr(_) => true,
        Type::Paren(t) => is_ptr_type(&t.elem),
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
