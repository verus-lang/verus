use crate::rustdoc::env_rustdoc;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use std::iter::FromIterator;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::token;
use syn_verus::token::{Brace, Bracket, Paren, Semi};
use syn_verus::visit_mut::{
    visit_block_mut, visit_expr_loop_mut, visit_expr_mut, visit_expr_while_mut, visit_field_mut,
    visit_impl_item_method_mut, visit_item_const_mut, visit_item_enum_mut, visit_item_fn_mut,
    visit_item_struct_mut, visit_local_mut, visit_trait_item_method_mut, VisitMut,
};
use syn_verus::{
    braced, bracketed, parenthesized, parse_macro_input, AttrStyle, Attribute, BareFnArg, BinOp,
    Block, DataMode, Decreases, Ensures, Expr, ExprBinary, ExprCall, ExprLit, ExprLoop, ExprTuple,
    ExprUnary, ExprWhile, Field, FnArgKind, FnMode, Ident, ImplItem, ImplItemMethod, Invariant,
    InvariantEnsures, Item, ItemConst, ItemEnum, ItemFn, ItemImpl, ItemMod, ItemStruct, ItemTrait,
    Lit, Local, Meta, ModeSpec, ModeSpecChecked, Pat, Path, PathArguments, PathSegment, Publish,
    Recommends, Requires, ReturnType, Signature, SignatureDecreases, Stmt, Token, TraitItem,
    TraitItemMethod, Type, TypeFnSpec, UnOp, Visibility,
};

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

fn take_ghost<T: Default>(erase_ghost: bool, dest: &mut T) -> T {
    if erase_ghost {
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
    erase_ghost: bool,
    // TODO: this should always be true
    use_spec_traits: bool,
    // TODO: this should always be true
    verus_macro_attr: bool,
    // inside_ghost > 0 means we're currently visiting ghost code
    inside_ghost: u32,
    // inside_type > 0 means we're currently visiting a type
    inside_type: u32,
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

    // Temporary hack (see https://github.com/rust-lang/rust/issues/54363 ) for backward compatability
    // When we fully commit to having pervasive in a separate crate, we can eliminate this:
    pervasive_in_same_crate: bool,
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
    ($span:expr => $($tok:tt)*) => {
        Stmt::Semi(
            Expr::Verbatim(quote_spanned!{ $span => $($tok)* }),
            Semi { spans: [ $span ] },
        )
    };
}

macro_rules! quote_verbatim {
    ($span:expr, $attrs:tt => $($tok:tt)*) => {
        Expr::Verbatim(quote_spanned!{ $span => #(#$attrs)* $($tok)* })
    }
}

impl Visitor {
    fn take_ghost<T: Default>(&self, dest: &mut T) -> T {
        take_ghost(self.erase_ghost, dest)
    }

    fn maybe_erase_expr(&self, span: Span, e: Expr) -> Expr {
        if self.erase_ghost { Expr::Verbatim(quote_spanned!(span => {})) } else { e }
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

        let inside_bitvector = if attrs.len() == 1 {
            let attr = attrs.first().unwrap();
            let arg = get_arg_from_verifier_attr(&attr);
            if arg.is_some() { arg.unwrap() == "bit_vector".to_string() } else { false }
        } else {
            false
        };

        if self.verus_macro_attr {
            attrs.push(mk_verus_attr(sig.fn_token.span, quote! { verus_macro }));
        }

        for arg in &mut sig.inputs {
            match (arg.tracked, &mut arg.kind) {
                (None, _) => {}
                (Some(token), FnArgKind::Receiver(receiver)) => {
                    receiver.attrs.push(mk_verus_attr(token.span, quote! { proof }));
                }
                (Some(token), FnArgKind::Typed(typed)) => {
                    typed.attrs.push(mk_verus_attr(token.span, quote! { proof }));
                }
            }
            arg.tracked = None;
        }
        let ret_pat = match &mut sig.output {
            ReturnType::Default => None,
            ReturnType::Type(_, ref mut tracked, ref mut ret_opt, ty) => {
                if let Some(token) = tracked {
                    attrs.push(mk_verus_attr(token.span, quote! { returns(proof) }));
                    *tracked = None;
                }
                match std::mem::take(ret_opt) {
                    None => None,
                    Some(box (_, p, _)) => Some((p.clone(), ty.clone())),
                }
            }
        };

        match (vis, &sig.publish, &sig.mode, &semi_token, self.erase_ghost) {
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

        let publish_attrs = match &sig.publish {
            Publish::Default => vec![],
            Publish::Closed(_) => vec![],
            Publish::Open(o) => vec![mk_verus_attr(o.token.span, quote! { publish })],
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
        self.inside_bitvector = inside_bitvector;

        let requires = self.take_ghost(&mut sig.requires);
        let recommends = self.take_ghost(&mut sig.recommends);
        let ensures = self.take_ghost(&mut sig.ensures);
        let decreases = self.take_ghost(&mut sig.decreases);
        // TODO: wrap specs inside ghost blocks
        if let Some(Requires { token, mut exprs }) = requires {
            for expr in exprs.exprs.iter_mut() {
                self.visit_expr_mut(expr);
            }
            stmts.push(Stmt::Semi(
                Expr::Verbatim(quote_spanned!(token.span => ::builtin::requires([#exprs]))),
                Semi { spans: [token.span] },
            ));
        }
        if let Some(Recommends { token, mut exprs, via }) = recommends {
            for expr in exprs.exprs.iter_mut() {
                self.visit_expr_mut(expr);
            }
            stmts.push(Stmt::Semi(
                Expr::Verbatim(quote_spanned!(token.span => ::builtin::recommends([#exprs]))),
                Semi { spans: [token.span] },
            ));
            if let Some((via_token, via_expr)) = via {
                stmts.push(Stmt::Semi(
                    Expr::Verbatim(
                        quote_spanned!(via_expr.span() => ::builtin::recommends_by(#via_expr)),
                    ),
                    Semi { spans: [via_token.span] },
                ));
            }
        }
        if let Some(Ensures { token, mut exprs }) = ensures {
            for expr in exprs.exprs.iter_mut() {
                self.visit_expr_mut(expr);
            }
            if let Some((p, ty)) = ret_pat {
                stmts.push(Stmt::Semi(
                    Expr::Verbatim(
                        quote_spanned!(token.span => ::builtin::ensures(|#p: #ty| [#exprs])),
                    ),
                    Semi { spans: [token.span] },
                ));
            } else {
                stmts.push(Stmt::Semi(
                    Expr::Verbatim(quote_spanned!(token.span => ::builtin::ensures([#exprs]))),
                    Semi { spans: [token.span] },
                ));
            }
        }
        if let Some(SignatureDecreases { decreases: Decreases { token, mut exprs }, when, via }) =
            decreases
        {
            for expr in exprs.exprs.iter_mut() {
                self.visit_expr_mut(expr);
            }
            stmts.push(Stmt::Semi(
                Expr::Verbatim(quote_spanned!(token.span => ::builtin::decreases((#exprs)))),
                Semi { spans: [token.span] },
            ));
            if let Some((when_token, mut when_expr)) = when {
                self.visit_expr_mut(&mut when_expr);
                stmts.push(Stmt::Semi(
                    Expr::Verbatim(
                        quote_spanned!(when_expr.span() => ::builtin::decreases_when(#when_expr)),
                    ),
                    Semi { spans: [when_token.span] },
                ));
            }
            if let Some((via_token, via_expr)) = via {
                stmts.push(Stmt::Semi(
                    Expr::Verbatim(
                        quote_spanned!(via_expr.span() => ::builtin::decreases_by(#via_expr)),
                    ),
                    Semi { spans: [via_token.span] },
                ));
            }
        }

        self.inside_ghost -= 1;
        self.inside_bitvector = false;

        sig.publish = Publish::Default;
        sig.mode = FnMode::Default;
        attrs.extend(publish_attrs);
        attrs.extend(mode_attrs);
        attrs.extend(prover_attr.into_iter());
        attrs.extend(ext_attrs);
        stmts.extend(unimpl);
        stmts
    }

    fn visit_const(
        &mut self,
        span: proc_macro2::Span,
        attrs: &mut Vec<Attribute>,
        vis: Option<&Visibility>,
        publish: &mut Publish,
        mode: &mut FnMode,
    ) {
        attrs.push(mk_verus_attr(span, quote! { verus_macro }));

        let publish_attrs = match (vis, &publish) {
            (Some(Visibility::Inherited), _) => vec![],
            (_, Publish::Default) => vec![mk_verus_attr(span, quote! { publish })],
            (_, Publish::Closed(_)) => vec![],
            (_, Publish::Open(o)) => vec![mk_verus_attr(o.token.span, quote! { publish })],
            (_, Publish::OpenRestricted(_)) => {
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
        *publish = Publish::Default;
        *mode = FnMode::Default;
        attrs.extend(publish_attrs);
        attrs.extend(mode_attrs);
    }

    fn exec_ghost_match(
        &mut self,
        pat: &mut Pat,
        splitter: &mut Option<&str>,
        stmts: &mut Vec<Stmt>,
        n: &mut u64,
    ) {
        let mut replace: Option<Pat> = None;
        match pat {
            Pat::TupleStruct(pts)
                if self.inside_ghost == 0
                    && pts.pat.elems.len() == 1
                    && (path_is_ident(&pts.path, "Ghost")
                        || path_is_ident(&pts.path, "Tracked")) =>
            {
                // change
                //   let Tracked((Trk(x), Gho(y))) = e;
                // to
                //   let (x, y) = tracked_split_tuple2(e);
                //   let x = tracked_unwrap_trk(x);
                //   let y = tracked_unwrap_gho(y);
                let mut tuple_pat = take_pat(&mut pts.pat.elems[0]);
                if let Pat::Tuple(pt) = &mut tuple_pat {
                    for elem in &mut pt.elems {
                        match elem {
                            Pat::TupleStruct(trk)
                                if trk.pat.elems.len() == 1
                                    && (path_is_ident(&trk.path, "Gho")
                                        || path_is_ident(&trk.path, "Trk")) =>
                            {
                                if let Pat::Ident(x) = &trk.pat.elems[0] {
                                    let x = x.ident.clone();
                                    let span = x.span();
                                    let f: TokenStream = if path_is_ident(&trk.path, "Gho") {
                                        if self.pervasive_in_same_crate {
                                            quote_spanned!(span => crate::pervasive::modes::tracked_unwrap_gho)
                                        } else {
                                            quote_spanned!(span => vstd::modes::tracked_unwrap_gho)
                                        }
                                    } else {
                                        if self.pervasive_in_same_crate {
                                            quote_spanned!(span => crate::pervasive::modes::tracked_unwrap_trk)
                                        } else {
                                            quote_spanned!(span => vstd::modes::tracked_unwrap_trk)
                                        }
                                    };
                                    stmts.push(Stmt::Semi(
                                        Expr::Verbatim(quote_spanned!(span => let #x = #f(#x))),
                                        Semi { spans: [span] },
                                    ));
                                    *elem = trk.pat.elems[0].clone();
                                }
                            }
                            _ => {}
                        }
                        *n += 1;
                    }
                }
                if path_is_ident(&pts.path, "Ghost") {
                    *splitter = Some("ghost_split_tuple");
                } else {
                    *splitter = Some("tracked_split_tuple");
                };
                replace = Some(tuple_pat);
            }
            _ => {}
        }
        if let Some(replace) = replace {
            *pat = replace;
        }
    }

    fn visit_local_extend(&mut self, local: &mut Local) -> Vec<Stmt> {
        let mut splitter: Option<&str> = None;
        let mut stmts: Vec<Stmt> = Vec::new();
        let mut n: u64 = 0;
        match &mut local.pat {
            Pat::Type(pt) => {
                self.exec_ghost_match(&mut pt.pat, &mut splitter, &mut stmts, &mut n);
            }
            pat => {
                self.exec_ghost_match(pat, &mut splitter, &mut stmts, &mut n);
            }
        }
        if let Some(splitter) = splitter {
            if let Some((eq, mut box_init)) = std::mem::replace(&mut local.init, None) {
                let span = eq.span;
                let name = format!("{splitter}{n}");
                let ident = Ident::new(&name, span);
                self.visit_expr_mut(&mut box_init);
                let init = Expr::Verbatim(quote_spanned!(span => ::builtin::#ident(#box_init)));
                local.init = Some((eq, Box::new(init)));
            }
        }
        stmts
    }

    fn visit_stmt_extend(&mut self, stmt: &mut Stmt) -> Vec<Stmt> {
        match stmt {
            Stmt::Local(local) => self.visit_local_extend(local),
            _ => vec![],
        }
    }

    fn visit_stream_expr(&mut self, stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
        use quote::ToTokens;
        let mut expr: Expr = parse_macro_input!(stream as Expr);
        let mut new_stream = TokenStream::new();
        self.visit_expr_mut(&mut expr);
        expr.to_tokens(&mut new_stream);
        proc_macro::TokenStream::from(new_stream)
    }

    fn visit_items_prefilter(&mut self, items: &mut Vec<Item>) {
        let erase_ghost = self.erase_ghost;
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
                    span => #[allow(unused_imports)] #vis use bool as #name;
                });
            }
        }
    }

    fn visit_impl_items_prefilter(&mut self, items: &mut Vec<ImplItem>, for_trait: bool) {
        let erase_ghost = self.erase_ghost;
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
                _ => {}
            }
        }
    }

    fn visit_trait_items_prefilter(&mut self, items: &mut Vec<TraitItem>) {
        let erase_ghost = self.erase_ghost;
        for item in items.iter_mut() {
            match item {
                TraitItem::Method(fun) => match fun.sig.mode {
                    FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) if erase_ghost => {
                        fun.default = None;
                        continue;
                    }
                    _ => {}
                },
                _ => {}
            }
        }
    }
}

fn chain_count(expr: &Expr) -> u32 {
    if let Expr::Binary(binary) = expr {
        match binary.op {
            BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_) => {
                1 + chain_count(&binary.left)
            }
            _ => 0,
        }
    } else {
        0
    }
}

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
        let mut toks = quote_spanned!(span => ::builtin::spec_chained_value(#cur_expr));
        for (right, op, span) in rights.iter().rev() {
            let ident = Ident::new(op, *span);
            toks = quote_spanned!(*span => ::builtin::#ident(#toks, #right));
        }
        toks = quote_spanned!(span => ::builtin::spec_chained_cmp(#toks));

        *expr = Expr::Verbatim(toks);

        true
    }

    /// Turn `forall |x| { ... }`
    /// into `::builtin::forall(|x| { ... })`
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
        let (inner_attrs, n_inputs) = match &mut *arg {
            Expr::Closure(closure) => {
                (std::mem::take(&mut closure.inner_attrs), closure.inputs.len())
            }
            _ => panic!("expected closure for quantifier"),
        };

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
                    match &mut *arg {
                        Expr::Closure(closure) => {
                            let body = take_expr(&mut closure.body);
                            closure.body = Box::new(Expr::Verbatim(
                                quote_spanned!(span => #[verus::internal(auto_trigger)] (#body)),
                            ));
                        }
                        _ => panic!("expected closure for quantifier"),
                    }
                }
                (Ok(trigger), Some(id)) if id == &"trigger" => {
                    let tuple =
                        ExprTuple { attrs: vec![], paren_token: Paren(span), elems: trigger.exprs };
                    triggers.push(Expr::Tuple(tuple));
                }
                (Err(err), _) => {
                    let span = attr.span();
                    let err = err.to_string();
                    *expr = Expr::Verbatim(quote_spanned!(span => compile_error!(#err)));
                    return true;
                }
                _ => {
                    let span = attr.span();
                    *expr =
                        Expr::Verbatim(quote_spanned!(span => compile_error!("expected trigger")));
                    return true;
                }
            }
        }

        if triggers.len() > 0 {
            let mut elems = Punctuated::new();
            for elem in triggers {
                elems.push(elem);
                elems.push_punct(Token![,](span));
            }
            let tuple = ExprTuple { attrs: vec![], paren_token: Paren(span), elems };
            match &mut *arg {
                Expr::Closure(closure) => {
                    let body = take_expr(&mut closure.body);
                    closure.body = Box::new(Expr::Verbatim(
                        quote_spanned!(span => ::builtin::with_triggers(#tuple, #body)),
                    ));
                }
                _ => panic!("expected closure for quantifier"),
            }
        }

        match unary.op {
            UnOp::Forall(..) => {
                *expr = quote_verbatim!(span, attrs => ::builtin::forall(#arg));
            }
            UnOp::Exists(..) => {
                *expr = quote_verbatim!(span, attrs => ::builtin::exists(#arg));
            }
            UnOp::Choose(..) => {
                if n_inputs == 1 {
                    *expr = quote_verbatim!(span, attrs => ::builtin::choose(#arg));
                } else {
                    *expr = quote_verbatim!(span, attrs => ::builtin::choose_tuple(#arg));
                }
            }
            _ => panic!("unary"),
        }

        true
    }

    fn add_loop_specs(
        &mut self,
        stmts: &mut Vec<Stmt>,
        invariants: Option<Invariant>,
        invariant_ensures: Option<InvariantEnsures>,
        ensures: Option<Ensures>,
        decreases: Option<Decreases>,
    ) {
        // TODO: wrap specs inside ghost blocks
        self.inside_ghost += 1;
        if let Some(Invariant { token, mut exprs }) = invariants {
            for expr in exprs.exprs.iter_mut() {
                self.visit_expr_mut(expr);
            }
            stmts.push(stmt_with_semi!(token.span => ::builtin::invariant([#exprs])));
        }
        if let Some(InvariantEnsures { token, mut exprs }) = invariant_ensures {
            for expr in exprs.exprs.iter_mut() {
                self.visit_expr_mut(expr);
            }
            stmts.push(stmt_with_semi!(token.span => ::builtin::invariant_ensures([#exprs])));
        }
        if let Some(Ensures { token, mut exprs }) = ensures {
            for expr in exprs.exprs.iter_mut() {
                self.visit_expr_mut(expr);
            }
            stmts.push(stmt_with_semi!(token.span => ::builtin::ensures([#exprs])));
        }
        if let Some(Decreases { token, mut exprs }) = decreases {
            for expr in exprs.exprs.iter_mut() {
                self.visit_expr_mut(expr);
            }
            stmts.push(stmt_with_semi!(token.span => ::builtin::decreases((#exprs))));
        }
        self.inside_ghost -= 1;
    }
}

impl VisitMut for Visitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        if self.chain_operators(expr) {
            return;
        } else if self.closure_quant_operators(expr) {
            return;
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
                _ => None,
            }
        } else {
            None
        };
        if let Some(_) = is_auto_proof_block {
            self.inside_ghost += 1;
        }

        let mode_block = if let Expr::Unary(unary) = expr {
            match unary.op {
                UnOp::Proof(..) => Some((false, false)),
                UnOp::Ghost(..) => Some((true, false)),
                UnOp::Tracked(..) => Some((true, true)),
                _ => None,
            }
        } else {
            None
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
        if !(is_inside_ghost && self.erase_ghost) {
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

        if let Expr::Unary(unary) = expr {
            let span = unary.span();
            let low_prec_op = match unary.op {
                UnOp::BigAnd(..) => true,
                UnOp::BigOr(..) => true,
                _ => false,
            };

            if low_prec_op {
                *expr = take_expr(&mut *unary.expr);
            } else if let Some(mode_block) = mode_block {
                match (is_inside_ghost, mode_block, &*unary.expr) {
                    (false, (false, _), Expr::Block(..)) => {
                        // proof { ... }
                        let inner = take_expr(&mut *unary.expr);
                        *expr = self.maybe_erase_expr(
                            span,
                            Expr::Verbatim(
                                quote_spanned!(span => #[verifier(proof_block)] /* vattr */ #inner),
                            ),
                        );
                    }
                    (false, (true, false), Expr::Paren(..)) => {
                        // ghost(...)
                        let inner = take_expr(&mut *unary.expr);
                        *expr = Expr::Verbatim(if self.erase_ghost {
                            quote_spanned!(span => Ghost::assume_new())
                        } else if self.pervasive_in_same_crate {
                            quote_spanned!(span => #[verifier(ghost_wrapper)] /* vattr */ crate::pervasive::modes::ghost_exec(#[verifier(ghost_block_wrapped)] /* vattr */ #inner))
                        } else {
                            quote_spanned!(span => #[verifier(ghost_wrapper)] /* vattr */ vstd::modes::ghost_exec(#[verifier(ghost_block_wrapped)] /* vattr */ #inner))
                        });
                    }
                    (false, (true, false), _) => {
                        *expr = Expr::Verbatim(
                            quote_spanned!(span => compile_error!("Expected parentheses")),
                        );
                        return;
                    }
                    (false, (true, true), Expr::Paren(..)) => {
                        // tracked(...)
                        let inner = take_expr(&mut *unary.expr);
                        *expr = Expr::Verbatim(if self.erase_ghost {
                            quote_spanned!(span => Tracked::assume_new())
                        } else if self.pervasive_in_same_crate {
                            quote_spanned!(span => #[verifier(ghost_wrapper)] /* vattr */ crate::pervasive::modes::tracked_exec(#[verifier(tracked_block_wrapped)] /* vattr */ #inner))
                        } else {
                            quote_spanned!(span => #[verifier(ghost_wrapper)] /* vattr */ vstd::modes::tracked_exec(#[verifier(tracked_block_wrapped)] /* vattr */ #inner))
                        });
                    }
                    (true, (true, true), _) => {
                        // TODO: once we migrate all the code, this case can be eliminated
                        // tracked ...
                        let inner = take_expr(&mut *unary.expr);
                        *expr = Expr::Verbatim(
                            quote_spanned!(span => #[verifier(tracked_block)] /* vattr */ { #inner }),
                        );
                    }
                    _ => {
                        *expr = Expr::Verbatim(
                            quote_spanned!(span => compile_error!("unexpected proof/ghost/tracked")),
                        );
                        return;
                    }
                }
            }
        } else if let Expr::Binary(binary) = expr {
            let span = binary.span();
            let low_prec_op = match binary.op {
                BinOp::BigAnd(syn_verus::token::BigAnd { spans }) => {
                    let spans = [spans[0], spans[1]];
                    Some(BinOp::And(syn_verus::token::AndAnd { spans }))
                }
                BinOp::BigOr(syn_verus::token::BigOr { spans }) => {
                    let spans = [spans[0], spans[1]];
                    Some(BinOp::Or(syn_verus::token::OrOr { spans }))
                }
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
            let big_eq = match binary.op {
                BinOp::BigEq(_) => Some(true),
                BinOp::BigNe(_) => Some(false),
                _ => None,
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
                let func = Box::new(Expr::Verbatim(quote_spanned!(span => ::builtin::imply)));
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
            } else if let Some(eq) = big_eq {
                let attrs = std::mem::take(&mut binary.attrs);
                let func = Box::new(Expr::Verbatim(quote_spanned!(span => ::builtin::equal)));
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
        }

        let do_replace = match &expr {
            Expr::Lit(ExprLit { lit: Lit::Int(..), .. }) if use_spec_traits => true,
            Expr::Cast(..) if use_spec_traits => true,
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
            Expr::Assume(..) | Expr::Assert(..) | Expr::AssertForall(..) => true,
            Expr::View(..) => true,
            Expr::Closure(..) if self.inside_ghost > 0 => true,
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
                                *expr = quote_verbatim!(span, attrs => ::builtin::spec_literal_integer(#n));
                            }
                            InsideArith::Widen if n.starts_with("-") => {
                                // Use int inside +, -, etc., since these promote to int anyway
                                *expr =
                                    quote_verbatim!(span, attrs => ::builtin::spec_literal_int(#n));
                            }
                            InsideArith::Widen => {
                                // Use int inside +, -, etc., since these promote to int anyway
                                *expr =
                                    quote_verbatim!(span, attrs => ::builtin::spec_literal_nat(#n));
                            }
                            InsideArith::Fixed => {
                                // We generally won't want int/nat literals for bitwise ops,
                                // so use Rust's native integer literals
                                *expr = Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs });
                            }
                        }
                    } else if lit.suffix() == "int" {
                        *expr = quote_verbatim!(span, attrs => ::builtin::spec_literal_int(#n));
                    } else if lit.suffix() == "nat" {
                        *expr = quote_verbatim!(span, attrs => ::builtin::spec_literal_nat(#n));
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
                    *expr = quote_verbatim!(span, attrs => ::builtin::spec_cast_integer::<_, #ty>(#src));
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
                            *expr =
                                quote_verbatim!(span, attrs => ::builtin::spec_eq(#left, #right));
                        }
                        BinOp::Ne(..) => {
                            *expr =
                                quote_verbatim!(span, attrs => ! ::builtin::spec_eq(#left, #right));
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
                        BinOp::Add(..) if !self.inside_bitvector => {
                            let left = quote_spanned! { left.span() => (#left) };
                            *expr = quote_verbatim!(span, attrs => #left.spec_add(#right));
                        }
                        BinOp::Sub(..) if !self.inside_bitvector => {
                            let left = quote_spanned! { left.span() => (#left) };
                            *expr = quote_verbatim!(span, attrs => #left.spec_sub(#right));
                        }
                        BinOp::Mul(..) if !self.inside_bitvector => {
                            let left = quote_spanned! { left.span() => (#left) };
                            *expr = quote_verbatim!(span, attrs => #left.spec_mul(#right));
                        }
                        BinOp::Add(..) | BinOp::Sub(..) | BinOp::Mul(..) => {
                            *expr = quote_verbatim!(span, attrs => compile_error!("Inside bit-vector assertion, use `add` `sub` `mul` for fixed-bit operators, instead of `+` `-` `*`. (see the functions builtin::add(left, right), builtin::sub(left, right), and builtin::mul(left, right))"));
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
                    let base = view.expr;
                    *expr = Expr::Verbatim(quote_spanned!(span => (#base#view_call)));
                }
                Expr::View(view) => {
                    assert!(self.assign_to);
                    let at_token = view.at_token;
                    let span1 = at_token.span;
                    let span2 = view.span();
                    let base = view.expr;
                    let borrowed: Expr =
                        Expr::Verbatim(quote_spanned!(span1 => #base.borrow_mut()));
                    *expr = Expr::Verbatim(quote_spanned!(span2 => (*(#borrowed))));
                }
                Expr::Assume(assume) => {
                    let span = assume.assume_token.span;
                    let arg = assume.expr;
                    let attrs = assume.attrs;
                    *expr = quote_verbatim!(span, attrs => ::builtin::assume_(#arg));
                }
                Expr::Assert(assert) => {
                    let span = assert.assert_token.span;
                    let arg = assert.expr;
                    let attrs = assert.attrs;
                    match (assert.by_token, assert.prover, assert.requires, assert.body) {
                        (None, None, None, None) => {
                            *expr = quote_verbatim!(span, attrs => ::builtin::assert_(#arg));
                        }
                        (None, _, _, _) => panic!("missing by token"),
                        (Some(_), None, None, None) => panic!("extra by token"),
                        (Some(_), None, None, Some(box block)) => {
                            *expr = quote_verbatim!(span, attrs => {::builtin::assert_by(#arg, #block);});
                        }
                        (Some(_), Some((_, id)), None, None) if id.to_string() == "compute" => {
                            *expr = Expr::Verbatim(
                                quote_spanned!(span => ::builtin::assert_by_compute(#arg)),
                            );
                        }
                        (Some(_), Some((_, id)), None, None)
                            if id.to_string() == "compute_only" =>
                        {
                            *expr = Expr::Verbatim(
                                quote_spanned!(span => ::builtin::assert_by_compute_only(#arg)),
                            );
                        }
                        (Some(_), Some((_, id)), None, None) if id.to_string() == "bit_vector" => {
                            *expr = quote_verbatim!(span, attrs => ::builtin::assert_bitvector_by({::builtin::ensures(#arg);}));
                        }
                        (Some(_), Some((_, id)), requires, block)
                            if id.to_string() == "bit_vector" =>
                        {
                            let mut block = if let Some(box block) = block {
                                block
                            } else {
                                Block { brace_token: token::Brace { span }, stmts: vec![] }
                            };
                            let mut stmts: Vec<Stmt> = Vec::new();
                            if let Some(Requires { token, exprs }) = requires {
                                stmts.push(Stmt::Semi(
                                    Expr::Verbatim(
                                        quote_spanned!(token.span => ::builtin::requires([#exprs])),
                                    ),
                                    Semi { spans: [token.span] },
                                ));
                            }
                            stmts.push(Stmt::Semi(
                                Expr::Verbatim(quote_spanned!(span => ::builtin::ensures(#arg))),
                                Semi { spans: [span] },
                            ));
                            block.stmts.splice(0..0, stmts);
                            let assert_bitvector_by: Expr = quote_verbatim!(span, attrs => ::builtin::assert_bitvector_by(#block));
                            *expr = Expr::Verbatim(quote_spanned!(span => {#assert_bitvector_by}));
                        }
                        (Some(_), Some((_, id)), None, None)
                            if id.to_string() == "nonlinear_arith" =>
                        {
                            *expr = quote_verbatim!(span, attrs => ::builtin::assert_nonlinear_by({::builtin::ensures(#arg);}));
                        }
                        (Some(_), Some((_, id)), requires, Some(box mut block))
                            if id.to_string() == "nonlinear_arith" =>
                        {
                            let mut stmts: Vec<Stmt> = Vec::new();
                            if let Some(Requires { token, exprs }) = requires {
                                stmts.push(Stmt::Semi(
                                    Expr::Verbatim(
                                        quote_spanned!(token.span => ::builtin::requires([#exprs])),
                                    ),
                                    Semi { spans: [token.span] },
                                ));
                            }
                            stmts.push(Stmt::Semi(
                                Expr::Verbatim(quote_spanned!(span => ::builtin::ensures(#arg))),
                                Semi { spans: [span] },
                            ));
                            block.stmts.splice(0..0, stmts);
                            let assert_nonlinear_by: Expr = quote_verbatim!(span, attrs => ::builtin::assert_nonlinear_by(#block));
                            *expr = Expr::Verbatim(quote_spanned!(span => {#assert_nonlinear_by}));
                        }
                        (Some(_), Some((_, id)), _, _) => {
                            let span = id.span();
                            *expr = quote_verbatim!(span, attrs => compile_error!("unknown prover name for assert-by (supported provers: 'compute_only', 'compute', 'bit_vector', and 'nonlinear_arith')"));
                        }
                        (Some(_), None, Some(_), _) => {
                            *expr = quote_verbatim!(span, attrs => compile_error!("assert-by has 'requires' clause but no prover specified (supported provers: 'compute_only', 'compute', 'bit_vector', and 'nonlinear_arith')"));
                        }
                    }
                }
                Expr::AssertForall(assert) => {
                    let span = assert.assert_token.span;
                    let attrs = assert.attrs;
                    let arg = assert.expr;
                    let inputs = assert.inputs;
                    let mut block = assert.body;
                    let mut stmts: Vec<Stmt> = Vec::new();
                    if let Some((_, rhs)) = assert.implies {
                        stmts.push(stmt_with_semi!(span => ::builtin::requires(#arg)));
                        stmts.push(stmt_with_semi!(span => ::builtin::ensures(#rhs)));
                    } else {
                        stmts.push(stmt_with_semi!(span => ::builtin::ensures(#arg)));
                    }
                    block.stmts.splice(0..0, stmts);
                    *expr = quote_verbatim!(span, attrs => {::builtin::assert_forall_by(|#inputs| #block);});
                }
                Expr::Closure(clos) => {
                    if is_inside_ghost {
                        let span = clos.span();
                        *expr = Expr::Verbatim(quote_spanned!(span =>
                            ::builtin::closure_to_fn_spec(#clos)
                        ));
                    } else {
                        *expr = Expr::Closure(clos);
                    }
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
                    quote_spanned!(span => #[verifier(proof_block)] /* vattr */ { #inner } ),
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
        let invariants = self.take_ghost(&mut expr_while.invariant);
        let invariant_ensures = self.take_ghost(&mut expr_while.invariant_ensures);
        let ensures = self.take_ghost(&mut expr_while.ensures);
        let decreases = self.take_ghost(&mut expr_while.decreases);
        let mut stmts: Vec<Stmt> = Vec::new();
        self.add_loop_specs(&mut stmts, invariants, invariant_ensures, ensures, decreases);
        expr_while.body.stmts.splice(0..0, stmts);
        visit_expr_while_mut(self, expr_while);
    }

    fn visit_expr_loop_mut(&mut self, expr_loop: &mut ExprLoop) {
        let invariants = self.take_ghost(&mut expr_loop.invariant);
        let invariant_ensures = self.take_ghost(&mut expr_loop.invariant_ensures);
        let ensures = self.take_ghost(&mut expr_loop.ensures);
        let decreases = self.take_ghost(&mut expr_loop.decreases);
        let mut stmts: Vec<Stmt> = Vec::new();
        self.add_loop_specs(&mut stmts, invariants, invariant_ensures, ensures, decreases);
        expr_loop.body.stmts.splice(0..0, stmts);
        visit_expr_loop_mut(self, expr_loop);
    }

    fn visit_local_mut(&mut self, local: &mut Local) {
        visit_local_mut(self, local);
        if let Some(tracked) = std::mem::take(&mut local.tracked) {
            local.attrs.push(mk_verus_attr(tracked.span, quote! { proof }));
        }
    }

    fn visit_block_mut(&mut self, block: &mut Block) {
        let mut stmts: Vec<Stmt> = Vec::new();
        let block_stmts = std::mem::replace(&mut block.stmts, vec![]);
        for mut stmt in block_stmts {
            let extra_stmts = self.visit_stmt_extend(&mut stmt);
            stmts.push(stmt);
            stmts.extend(extra_stmts);
        }
        block.stmts = stmts;
        visit_block_mut(self, block);
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
        visit_item_fn_mut(self, fun);
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
        visit_impl_item_method_mut(self, method);
    }

    fn visit_trait_item_method_mut(&mut self, method: &mut TraitItemMethod) {
        if self.rustdoc {
            crate::rustdoc::process_trait_item_method(method);
        }

        let mut stmts =
            self.visit_fn(&mut method.attrs, None, &mut method.sig, method.semi_token, true);
        if let Some(block) = &mut method.default {
            block.stmts.splice(0..0, stmts);
        } else if !self.erase_ghost {
            let span = method.sig.fn_token.span;
            stmts.push(Stmt::Expr(Expr::Verbatim(
                quote_spanned!(span => ::builtin::no_method_body()),
            )));
            let block = Block { brace_token: Brace(span), stmts };
            method.default = Some(block);
        }
        if !self.erase_ghost {
            method.semi_token = None;
        }
        visit_trait_item_method_mut(self, method);
    }

    fn visit_item_const_mut(&mut self, con: &mut ItemConst) {
        self.visit_const(
            con.const_token.span,
            &mut con.attrs,
            Some(&con.vis),
            &mut con.publish,
            &mut con.mode,
        );
        visit_item_const_mut(self, con);
    }

    fn visit_field_mut(&mut self, field: &mut Field) {
        visit_field_mut(self, field);
        field.attrs.extend(data_mode_attrs(&field.mode));
        field.mode = DataMode::Default;
    }

    fn visit_item_enum_mut(&mut self, item: &mut ItemEnum) {
        visit_item_enum_mut(self, item);
        item.attrs.extend(data_mode_attrs(&item.mode));
        item.mode = DataMode::Default;
    }

    fn visit_item_struct_mut(&mut self, item: &mut ItemStruct) {
        visit_item_struct_mut(self, item);
        item.attrs.extend(data_mode_attrs(&item.mode));
        item.mode = DataMode::Default;
    }

    fn visit_type_mut(&mut self, ty: &mut Type) {
        self.inside_type += 1;
        syn_verus::visit_mut::visit_type_mut(self, ty);
        self.inside_type -= 1;

        let span = ty.span();
        let tmp_ty = take_type(ty);

        match tmp_ty {
            Type::FnSpec(TypeFnSpec { fn_spec_token: _, paren_token: _, inputs, output }) => {
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

                *ty = Type::Verbatim(quote_spanned! { span =>
                    ::builtin::FnSpec<(#(#param_types ,)*), #out_type>
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
        if let Some((_, items)) = &mut item.content {
            self.visit_items_prefilter(items);
        }
        syn_verus::visit_mut::visit_item_mod_mut(self, item);
    }

    fn visit_item_impl_mut(&mut self, imp: &mut ItemImpl) {
        self.visit_impl_items_prefilter(&mut imp.items, imp.trait_.is_some());
        syn_verus::visit_mut::visit_item_impl_mut(self, imp);
    }

    fn visit_item_trait_mut(&mut self, tr: &mut ItemTrait) {
        self.visit_trait_items_prefilter(&mut tr.items);
        syn_verus::visit_mut::visit_item_trait_mut(self, tr);
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
struct MacroElements {
    elements: Vec<MacroElement>,
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

impl Parse for MacroElements {
    fn parse(input: ParseStream) -> syn_verus::parse::Result<MacroElements> {
        let mut elements = Vec::new();
        while !input.is_empty() {
            elements.push(input.parse()?);
        }
        Ok(MacroElements { elements })
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

impl quote::ToTokens for MacroElement {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            MacroElement::Comma(e) => e.to_tokens(tokens),
            MacroElement::Semi(e) => e.to_tokens(tokens),
            MacroElement::FatArrow(e) => e.to_tokens(tokens),
            MacroElement::Expr(e) => e.to_tokens(tokens),
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

pub(crate) fn rewrite_items(
    stream: proc_macro::TokenStream,
    erase_ghost: bool,
    use_spec_traits: bool,
    verus_macro_attr: bool,
    pervasive_in_same_crate: bool,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let stream = rejoin_tokens(stream);
    let mut items: Items = parse_macro_input!(stream as Items);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits,
        inside_ghost: 0,
        inside_type: 0,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
        inside_bitvector: false,
        verus_macro_attr,
        pervasive_in_same_crate,
    };
    visitor.visit_items_prefilter(&mut items.items);
    for mut item in items.items {
        visitor.visit_item_mut(&mut item);
        visitor.inside_ghost = 0;
        visitor.inside_arith = InsideArith::None;
        item.to_tokens(&mut new_stream);
    }
    proc_macro::TokenStream::from(new_stream)
}

pub(crate) fn rewrite_expr(
    erase_ghost: bool,
    inside_ghost: bool,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let stream = rejoin_tokens(stream);
    let mut expr: Expr = parse_macro_input!(stream as Expr);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        verus_macro_attr: true,
        inside_ghost: if inside_ghost { 1 } else { 0 },
        inside_type: 0,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
        inside_bitvector: false,
        pervasive_in_same_crate: true,
    };
    visitor.visit_expr_mut(&mut expr);
    expr.to_tokens(&mut new_stream);
    proc_macro::TokenStream::from(new_stream)
}

// Unfortunately, the macro_rules tt tokenizer breaks tokens like &&& and ==> into smaller tokens.
// Try to put the original tokens back together here.
fn rejoin_tokens(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use proc_macro::{Group, Punct, Spacing::*, Span, TokenTree};
    let mut tokens: Vec<TokenTree> = stream.into_iter().collect();
    let pun = |t: &TokenTree| match t {
        TokenTree::Punct(p) => Some((p.as_char(), p.spacing(), p.span())),
        _ => None,
    };
    let adjacent = |s1: Span, s2: Span| {
        let l1 = s1.end();
        let l2 = s2.start();
        s1.source_file() == s2.source_file() && l1 == l2
    };
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
                    let (op, _, span) = t1.unwrap();
                    let mut punct = Punct::new(op, Joint);
                    punct.set_span(span);
                    tokens[i + 1] = TokenTree::Punct(punct);
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
    proc_macro::TokenStream::from_iter(tokens.into_iter())
}

pub(crate) fn proof_macro_exprs(
    erase_ghost: bool,
    inside_ghost: bool,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let stream = rejoin_tokens(stream);
    let mut invoke: MacroInvoke = parse_macro_input!(stream as MacroInvoke);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        erase_ghost,
        use_spec_traits: true,
        verus_macro_attr: true,
        inside_ghost: if inside_ghost { 1 } else { 0 },
        inside_type: 0,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
        inside_bitvector: false,
        pervasive_in_same_crate: true,
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

/// Constructs #[name tokens]
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

/// Get `arg` from `#[verifier(arg)]`, and if `attr` is not a verifier attribute, return `None`
fn get_arg_from_verifier_attr(attr: &Attribute) -> Option<String> {
    let parsed = attr.parse_meta();
    if parsed.is_err() {
        return None;
    }
    let parsed = parsed.unwrap();
    let ids = get_idents_from_meta(&parsed);
    if ids.len() == 2 && ids.contains(&"verifier".to_string()) {
        let mut id: Vec<String> =
            ids.into_iter().filter(|x| x != &"verifier".to_string()).collect();
        if id.len() == 1 { id.pop() } else { None }
    } else {
        None
    }
}

/// Get idents from all "Path" in attributes(e.g. collect "verifier"` and `arg` from  `#[verifier(arg)]`)
fn get_idents_from_meta(parsed: &Meta) -> Vec<String> {
    match parsed {
        syn_verus::Meta::List(meta_list) => {
            let mut ids = get_ident_from_path(&meta_list.path);
            for meta in &meta_list.nested {
                match meta {
                    syn_verus::NestedMeta::Meta(meta) => {
                        ids.append(&mut get_idents_from_meta(&meta));
                    }
                    syn_verus::NestedMeta::Lit(_) => (),
                }
            }
            ids
        }
        syn_verus::Meta::Path(path) => get_ident_from_path(&path),
        syn_verus::Meta::NameValue(meta_name_value) => get_ident_from_path(&meta_name_value.path),
    }
}

fn get_ident_from_path(path: &Path) -> Vec<String> {
    let mut ids = vec![];
    for seg in &path.segments {
        ids.push(seg.ident.to_string().clone());
    }
    ids
}
