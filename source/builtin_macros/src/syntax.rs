use proc_macro2::TokenStream;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::punctuated::Punctuated;
use syn_verus::token::{Brace, Paren};
use syn_verus::visit_mut::{
    visit_expr_loop_mut, visit_expr_mut, visit_expr_while_mut, visit_field_mut,
    visit_impl_item_method_mut, visit_item_enum_mut, visit_item_fn_mut, visit_item_struct_mut,
    visit_local_mut, visit_trait_item_method_mut, VisitMut,
};
use syn_verus::{
    parse_macro_input, parse_quote_spanned, Attribute, BinOp, Block, DataMode, Decreases, Ensures,
    Expr, ExprBinary, ExprCall, ExprLoop, ExprTuple, ExprUnary, ExprWhile, Field, FnArgKind,
    FnMode, ImplItemMethod, Invariant, Item, ItemEnum, ItemFn, ItemStruct, Local, ModeSpec,
    ModeSpecChecked, Path, Publish, Recommends, Requires, ReturnType, Signature, Stmt,
    TraitItemMethod, UnOp, Visibility,
};

fn take_expr(expr: &mut Expr) -> Expr {
    let dummy: Expr = syn_verus::parse_quote!(());
    std::mem::replace(expr, dummy)
}

struct Visitor {
    // inside_ghost > 0 means we're currently visiting ghost code
    inside_ghost: u32,
}

fn data_mode_attrs(mode: &DataMode) -> Vec<Attribute> {
    match mode {
        DataMode::Default => vec![],
        DataMode::Ghost(token) => {
            vec![parse_quote_spanned!(token.ghost_token.span => #[spec])]
        }
        DataMode::Tracked(token) => {
            vec![parse_quote_spanned!(token.tracked_token.span => #[proof])]
        }
        DataMode::Exec(token) => {
            vec![parse_quote_spanned!(token.exec_token.span => #[exec])]
        }
    }
}

impl Visitor {
    fn visit_fn(
        &mut self,
        attrs: &mut Vec<Attribute>,
        vis: Option<&Visibility>,
        sig: &mut Signature,
        semi_token: Option<syn_verus::Token![;]>,
        is_trait: bool,
    ) -> Vec<Stmt> {
        let mut stmts: Vec<Stmt> = Vec::new();

        attrs.push(parse_quote_spanned!(sig.fn_token.span => #[verifier(verus_macro)]));

        for arg in &mut sig.inputs {
            match (arg.tracked, &mut arg.kind) {
                (None, _) => {}
                (Some(token), FnArgKind::Receiver(receiver)) => {
                    receiver.attrs.push(parse_quote_spanned!(token.span => #[proof]));
                }
                (Some(token), FnArgKind::Typed(typed)) => {
                    typed.attrs.push(parse_quote_spanned!(token.span => #[proof]));
                }
            }
            arg.tracked = None;
        }
        let ret_pat = match &mut sig.output {
            ReturnType::Default => None,
            ReturnType::Type(_, ref mut tracked, ref mut ret_opt, ty) => {
                if let Some(token) = tracked {
                    attrs.push(parse_quote_spanned!(token.span => #[verifier(returns(proof))]));
                    *tracked = None;
                }
                match std::mem::take(ret_opt) {
                    None => None,
                    Some(box (_, p, _)) => Some((p.clone(), ty.clone())),
                }
            }
        };

        match (vis, &sig.publish, &sig.mode, &semi_token) {
            (Some(Visibility::Inherited), _, _, _) => {}
            (
                Some(_),
                Publish::Default,
                FnMode::Spec(ModeSpec { spec_token })
                | FnMode::SpecChecked(ModeSpecChecked { spec_token, .. }),
                None,
            ) => {
                let e: Expr = parse_quote_spanned!(spec_token.span =>
                    compile_error!("non-private spec function must be marked open or closed to indicate whether the function body is public (pub open) or private (pub closed)"));
                stmts.push(parse_quote_spanned!(spec_token.span => {#e}));
            }
            _ => {}
        }

        let publish_attrs = match &sig.publish {
            Publish::Default => vec![],
            Publish::Closed(_) => vec![],
            Publish::Open(o) => vec![parse_quote_spanned!(o.token.span => #[verifier(publish)])],
            Publish::OpenRestricted(_) => {
                unimplemented!("TODO: support open(...)")
            }
        };

        let (unimpl, ext_attrs) = match (&sig.mode, semi_token, is_trait) {
            (FnMode::Spec(_) | FnMode::SpecChecked(_), Some(semi), false) => (
                vec![Stmt::Expr(parse_quote_spanned!(semi.span => unimplemented!()))],
                vec![parse_quote_spanned!(semi.span => #[verifier(external_body)])],
            ),
            _ => (vec![], vec![]),
        };

        let (inside_ghost, mode_attrs): (u32, Vec<Attribute>) = match &sig.mode {
            FnMode::Default => (0, vec![]),
            FnMode::Spec(token) => {
                (1, vec![parse_quote_spanned!(token.spec_token.span => #[spec])])
            }
            FnMode::SpecChecked(token) => {
                (1, vec![parse_quote_spanned!(token.spec_token.span => #[spec(checked)])])
            }
            FnMode::Proof(token) => {
                (1, vec![parse_quote_spanned!(token.proof_token.span => #[proof])])
            }
            FnMode::Exec(token) => {
                (0, vec![parse_quote_spanned!(token.exec_token.span => #[exec])])
            }
        };
        self.inside_ghost = inside_ghost;

        let requires = std::mem::take(&mut sig.requires);
        let recommends = std::mem::take(&mut sig.recommends);
        let ensures = std::mem::take(&mut sig.ensures);
        let decreases = std::mem::take(&mut sig.decreases);
        // TODO: wrap specs inside ghost blocks
        if let Some(Requires { token, exprs }) = requires {
            stmts.push(parse_quote_spanned!(token.span => requires([#exprs]);));
        }
        if let Some(Recommends { token, exprs }) = recommends {
            stmts.push(parse_quote_spanned!(token.span => recommends([#exprs]);));
        }
        if let Some(Ensures { token, exprs }) = ensures {
            if let Some((p, ty)) = ret_pat {
                stmts.push(parse_quote_spanned!(token.span => ensures(|#p: #ty| [#exprs]);));
            } else {
                stmts.push(parse_quote_spanned!(token.span => ensures([#exprs]);));
            }
        }
        if let Some(Decreases { token, exprs }) = decreases {
            stmts.push(parse_quote_spanned!(token.span => decreases((#exprs));));
        }
        sig.publish = Publish::Default;
        sig.mode = FnMode::Default;
        attrs.extend(publish_attrs);
        attrs.extend(mode_attrs);
        attrs.extend(ext_attrs);
        stmts.extend(unimpl);
        stmts
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

fn chain_operators(expr: &mut Expr) {
    use syn_verus::spanned::Spanned;
    let count = chain_count(expr);
    if count < 2 {
        return;
    }
    let mut rights: Vec<(Expr, Path, proc_macro2::Span)> = Vec::new();
    for _ in 0..count {
        if let Expr::Binary(binary) = take_expr(expr) {
            let span = binary.span();
            let op = match binary.op {
                BinOp::Le(_) => parse_quote_spanned!(span => ::builtin::chained_le),
                BinOp::Lt(_) => parse_quote_spanned!(span => ::builtin::chained_lt),
                BinOp::Ge(_) => parse_quote_spanned!(span => ::builtin::chained_ge),
                BinOp::Gt(_) => parse_quote_spanned!(span => ::builtin::chained_gt),
                _ => panic!("chain_operators"),
            };
            rights.push((*binary.right, op, span));
            *expr = *binary.left;
        } else {
            panic!("chain_operators");
        }
    }
    // example:
    //   ((e0 <= e1) <= e2) <= e3
    //   count == 3
    //   expr = e0
    //   rights = [e3, e2, e1]
    // goal:
    //   chained_cmp(chained_le(chained_le(chained_le(chained_value(e0), e1), e2), e3))
    let span = expr.span();
    *expr = parse_quote_spanned!(span => ::builtin::chained_value(#expr));
    while let Some((right, op, span)) = rights.pop() {
        *expr = parse_quote_spanned!(span => #op(#expr, #right));
    }
    *expr = parse_quote_spanned!(span => ::builtin::chained_cmp(#expr));
}

impl VisitMut for Visitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        chain_operators(expr);

        if self.inside_ghost == 0 {
            let is_auto_proof_block = match &expr {
                Expr::Assume(a) => Some(a.assume_token.span),
                Expr::Assert(a) => Some(a.assert_token.span),
                Expr::AssertForall(a) => Some(a.assert_token.span),
                _ => None,
            };
            if let Some(span) = is_auto_proof_block {
                // automatically put assert/assume in a proof block
                let inner = take_expr(expr);
                *expr = parse_quote_spanned!(span => proof { #inner });
            }
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

        let is_inside_ghost = self.inside_ghost > 0;
        if mode_block.is_some() {
            self.inside_ghost += 1;
        }
        visit_expr_mut(self, expr);
        if mode_block.is_some() {
            self.inside_ghost -= 1;
        }

        if let Expr::Unary(unary) = expr {
            use syn_verus::spanned::Spanned;
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
                        *expr = parse_quote_spanned!(span => #[verifier(proof_block)] #inner);
                    }
                    (false, (true, false), Expr::Paren(..)) => {
                        // ghost(...)
                        let inner = take_expr(&mut *unary.expr);
                        *expr = parse_quote_spanned!(span => #[verifier(ghost_wrapper)] crate::pervasive::modes::Ghost::exec(#[verifier(ghost_block_wrapped)] #inner));
                    }
                    (false, (true, true), Expr::Paren(..)) => {
                        // tracked(...)
                        let inner = take_expr(&mut *unary.expr);
                        *expr = parse_quote_spanned!(span => #[verifier(ghost_wrapper)] crate::pervasive::modes::Tracked::exec(#[verifier(tracked_block_wrapped)] #inner));
                    }
                    (true, (true, true), _) => {
                        // tracked ...
                        let inner = take_expr(&mut *unary.expr);
                        *expr = parse_quote_spanned!(span => #[verifier(tracked_block)] { #inner });
                    }
                    _ => {
                        *expr = parse_quote_spanned!(span => compile_error!("unexpected proof/ghost/tracked"));
                        return;
                    }
                }
            }
        } else if let Expr::Binary(binary) = expr {
            use syn_verus::spanned::Spanned;
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
                let left = Box::new(take_expr(&mut *binary.left));
                let right = Box::new(take_expr(&mut *binary.right));
                let left = parse_quote_spanned!(span => (#left));
                let right = parse_quote_spanned!(span => (#right));
                let bin = ExprBinary { attrs, op, left, right };
                *expr = Expr::Binary(bin);
            } else if let Some(imply) = ply {
                let attrs = std::mem::take(&mut binary.attrs);
                let func = parse_quote_spanned!(span => ::builtin::imply);
                let paren_token = Paren { span };
                let mut args = Punctuated::new();
                if imply {
                    args.push(take_expr(&mut *binary.left));
                    args.push(take_expr(&mut *binary.right));
                } else {
                    args.push(take_expr(&mut *binary.right));
                    args.push(take_expr(&mut *binary.left));
                }
                *expr = Expr::Call(ExprCall { attrs, func, paren_token, args });
            } else if let Some(eq) = big_eq {
                let attrs = std::mem::take(&mut binary.attrs);
                let func = parse_quote_spanned!(span => ::builtin::equal);
                let paren_token = Paren { span };
                let mut args = Punctuated::new();
                args.push(take_expr(&mut *binary.left));
                args.push(take_expr(&mut *binary.right));
                let call = Expr::Call(ExprCall { attrs, func, paren_token, args });
                if eq {
                    *expr = call;
                } else {
                    *expr = parse_quote_spanned!(span => ! #call);
                }
            }
        }

        let (do_replace, quant) = match &expr {
            Expr::Unary(ExprUnary { op: UnOp::Forall(..), .. }) => (true, true),
            Expr::Unary(ExprUnary { op: UnOp::Exists(..), .. }) => (true, true),
            Expr::Unary(ExprUnary { op: UnOp::Choose(..), .. }) => (true, true),
            Expr::Assume(..) | Expr::Assert(..) | Expr::AssertForall(..) => (true, false),
            _ => (false, false),
        };
        if do_replace {
            match take_expr(expr) {
                Expr::Unary(unary) if quant => {
                    use syn_verus::spanned::Spanned;
                    let span = unary.span();
                    let mut arg = unary.expr;
                    let attrs = unary.attrs;
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
                        match (trigger, attr.path.get_ident()) {
                            (Ok(trigger), Some(id)) if id == "auto" && trigger.exprs.len() == 0 => {
                                match &mut *arg {
                                    Expr::Closure(closure) => {
                                        let body = take_expr(&mut closure.body);
                                        closure.body =
                                            parse_quote_spanned!(span => #[auto_trigger] #body);
                                    }
                                    _ => panic!("expected closure for quantifier"),
                                }
                            }
                            (Ok(trigger), Some(id)) if id == "trigger" => {
                                let tuple = ExprTuple {
                                    attrs: vec![],
                                    paren_token: Paren(span),
                                    elems: trigger.exprs,
                                };
                                triggers.push(Expr::Tuple(tuple));
                            }
                            (Err(err), _) => {
                                let span = attr.span();
                                let err = err.to_string();
                                *expr = parse_quote_spanned!(span => compile_error!(#err));
                                return;
                            }
                            _ => {
                                let span = attr.span();
                                *expr = parse_quote_spanned!(span => compile_error!("expected trigger"));
                                return;
                            }
                        }
                    }
                    if triggers.len() > 0 {
                        let mut elems = Punctuated::new();
                        for elem in triggers {
                            elems.push(elem);
                            elems.push_punct(syn_verus::Token![,](span));
                        }
                        let tuple = ExprTuple { attrs: vec![], paren_token: Paren(span), elems };
                        match &mut *arg {
                            Expr::Closure(closure) => {
                                let body = take_expr(&mut closure.body);
                                closure.body =
                                    parse_quote_spanned!(span => with_triggers(#tuple, #body));
                            }
                            _ => panic!("expected closure for quantifier"),
                        }
                    }
                    match unary.op {
                        UnOp::Forall(..) => {
                            *expr = parse_quote_spanned!(span => ::builtin::forall(#arg));
                        }
                        UnOp::Exists(..) => {
                            *expr = parse_quote_spanned!(span => ::builtin::exists(#arg));
                        }
                        UnOp::Choose(..) => {
                            if n_inputs == 1 {
                                *expr = parse_quote_spanned!(span => ::builtin::choose(#arg));
                            } else {
                                *expr = parse_quote_spanned!(span => ::builtin::choose_tuple(#arg));
                            }
                        }
                        _ => panic!("unary"),
                    }
                    expr.replace_attrs(attrs);
                }
                Expr::Assume(assume) => {
                    let span = assume.assume_token.span;
                    let arg = assume.expr;
                    let attrs = assume.attrs;
                    *expr = parse_quote_spanned!(span => crate::pervasive::assume(#arg));
                    expr.replace_attrs(attrs);
                }
                Expr::Assert(assert) => {
                    let span = assert.assert_token.span;
                    let arg = assert.expr;
                    let attrs = assert.attrs;
                    match (assert.by_token, assert.prover, assert.body) {
                        (None, None, None) => {
                            *expr = parse_quote_spanned!(span => crate::pervasive::assert(#arg));
                        }
                        (None, _, _) => panic!("missing by token"),
                        (Some(_), None, None) => panic!("extra by token"),
                        (Some(_), None, Some(box (None, block))) => {
                            *expr =
                                parse_quote_spanned!(span => {::builtin::assert_by(#arg, #block);});
                        }
                        (Some(_), Some((_, id)), None) if id.to_string() == "bit_vector" => {
                            *expr =
                                parse_quote_spanned!(span => ::builtin::assert_bit_vector(#arg));
                        }
                        (Some(_), Some((_, id)), None) if id.to_string() == "nonlinear_arith" => {
                            *expr = parse_quote_spanned!(span => ::builtin::assert_nonlinear_by({ensures(#arg);}));
                        }
                        (Some(_), Some((_, id)), Some(box (requires, mut block)))
                            if id.to_string() == "nonlinear_arith" =>
                        {
                            let mut stmts: Vec<Stmt> = Vec::new();
                            if let Some(Requires { token, exprs }) = requires {
                                stmts.push(parse_quote_spanned!(token.span => requires([#exprs]);));
                            }
                            stmts.push(parse_quote_spanned!(span => ensures(#arg);));
                            block.stmts.splice(0..0, stmts);
                            *expr = parse_quote_spanned!(span => {::builtin::assert_nonlinear_by(#block);});
                        }
                        (Some(_), Some((_, id)), _) => {
                            let span = id.span();
                            *expr = parse_quote_spanned!(span => compile_error!("unsupported kind of assert-by"));
                        }
                        _ => {
                            *expr = parse_quote_spanned!(span => compile_error!("unsupported kind of assert-by"));
                        }
                    }
                    expr.replace_attrs(attrs);
                }
                Expr::AssertForall(assert) => {
                    let span = assert.assert_token.span;
                    let attrs = assert.attrs;
                    let arg = assert.expr;
                    let inputs = assert.inputs;
                    let mut block = assert.body;
                    let mut stmts: Vec<Stmt> = Vec::new();
                    if let Some((_, rhs)) = assert.implies {
                        stmts.push(parse_quote_spanned!(span => requires(#arg);));
                        stmts.push(parse_quote_spanned!(span => ensures(#rhs);));
                    } else {
                        stmts.push(parse_quote_spanned!(span => ensures(#arg);));
                    }
                    block.stmts.splice(0..0, stmts);
                    *expr = parse_quote_spanned!(span => {::builtin::assert_forall_by(|#inputs| #block);});
                    expr.replace_attrs(attrs);
                }
                _ => panic!("expected assert/assume"),
            }
        }
    }

    fn visit_expr_while_mut(&mut self, expr_while: &mut ExprWhile) {
        visit_expr_while_mut(self, expr_while);
        let invariants = std::mem::take(&mut expr_while.invariant);
        let decreases = std::mem::take(&mut expr_while.decreases);
        let mut stmts: Vec<Stmt> = Vec::new();
        // TODO: wrap specs inside ghost blocks
        if let Some(Invariant { token, exprs }) = invariants {
            stmts.push(parse_quote_spanned!(token.span => invariant([#exprs]);));
        }
        if let Some(Decreases { token, exprs }) = decreases {
            stmts.push(parse_quote_spanned!(token.span => decreases((#exprs));));
        }
        expr_while.body.stmts.splice(0..0, stmts);
    }

    fn visit_expr_loop_mut(&mut self, expr_loop: &mut ExprLoop) {
        visit_expr_loop_mut(self, expr_loop);
        let requires = std::mem::take(&mut expr_loop.requires);
        let invariants = std::mem::take(&mut expr_loop.invariant);
        let ensures = std::mem::take(&mut expr_loop.ensures);
        let decreases = std::mem::take(&mut expr_loop.decreases);
        let mut stmts: Vec<Stmt> = Vec::new();
        // TODO: wrap specs inside ghost blocks
        if let Some(Requires { token, exprs }) = requires {
            stmts.push(parse_quote_spanned!(token.span => requires([#exprs]);));
        }
        if let Some(Invariant { token, exprs }) = invariants {
            stmts.push(parse_quote_spanned!(token.span => invariant([#exprs]);));
        }
        if let Some(Ensures { token, exprs }) = ensures {
            stmts.push(parse_quote_spanned!(token.span => ensures([#exprs]);));
        }
        if let Some(Decreases { token, exprs }) = decreases {
            stmts.push(parse_quote_spanned!(token.span => decreases((#exprs));));
        }
        expr_loop.body.stmts.splice(0..0, stmts);
    }

    fn visit_local_mut(&mut self, local: &mut Local) {
        visit_local_mut(self, local);
        if let Some(tracked) = std::mem::take(&mut local.tracked) {
            local.attrs.push(parse_quote_spanned!(tracked.span => #[proof]));
        }
    }

    fn visit_item_fn_mut(&mut self, fun: &mut ItemFn) {
        let stmts =
            self.visit_fn(&mut fun.attrs, Some(&fun.vis), &mut fun.sig, fun.semi_token, false);
        fun.block.stmts.splice(0..0, stmts);
        fun.semi_token = None;
        visit_item_fn_mut(self, fun);
    }

    fn visit_impl_item_method_mut(&mut self, method: &mut ImplItemMethod) {
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
        let mut stmts =
            self.visit_fn(&mut method.attrs, None, &mut method.sig, method.semi_token, true);
        if let Some(block) = &mut method.default {
            block.stmts.splice(0..0, stmts);
        } else {
            let span = method.sig.fn_token.span;
            stmts.push(Stmt::Expr(parse_quote_spanned!(span => ::builtin::no_method_body())));
            let block = Block { brace_token: Brace(span), stmts };
            method.default = Some(block);
        }
        method.semi_token = None;
        visit_trait_item_method_mut(self, method);
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

pub(crate) fn rewrite_items(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let items: Items = parse_macro_input!(stream as Items);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor { inside_ghost: 0 };
    for mut item in items.items {
        visitor.visit_item_mut(&mut item);
        item.to_tokens(&mut new_stream);
    }
    proc_macro::TokenStream::from(new_stream)
}
