use proc_macro2::TokenStream;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::punctuated::Punctuated;
use syn_verus::token::Paren;
use syn_verus::visit_mut::{
    visit_expr_mut, visit_field_mut, visit_item_enum_mut, visit_item_fn_mut, visit_item_struct_mut,
    VisitMut,
};
use syn_verus::{
    parse_macro_input, parse_quote_spanned, Attribute, BinOp, DataMode, Decreases, Ensures, Expr,
    ExprBinary, ExprCall, ExprTuple, ExprUnary, Field, FnArgKind, FnMode, Item, ItemEnum, ItemFn,
    ItemStruct, Pat, Recommends, Requires, ReturnType, Stmt, UnOp,
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

impl VisitMut for Visitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
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
                UnOp::Spec(..) | UnOp::Proof(..) => Some(false),
                UnOp::Tracked(..) => Some(true),
                _ => None,
            }
        } else {
            None
        };

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
                match (mode_block, &*unary.expr) {
                    (false, Expr::Paren(..)) => {
                        let inner = take_expr(&mut *unary.expr);
                        *expr = parse_quote_spanned!(span => #[spec] { #inner });
                    }
                    (false, Expr::Block(..)) => {
                        let inner = take_expr(&mut *unary.expr);
                        *expr = parse_quote_spanned!(span => #[spec] #inner);
                    }
                    (true, _) => {
                        let inner = take_expr(&mut *unary.expr);
                        *expr = parse_quote_spanned!(span => #[proof] { #inner });
                    }
                    _ => panic!("internal error: unexpected mode block"),
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
                            *expr = parse_quote_spanned!(span => builtin::forall(#arg));
                        }
                        UnOp::Exists(..) => {
                            *expr = parse_quote_spanned!(span => builtin::exists(#arg));
                        }
                        UnOp::Choose(..) => {
                            if n_inputs == 1 {
                                *expr = parse_quote_spanned!(span => builtin::choose(#arg));
                            } else {
                                *expr = parse_quote_spanned!(span => builtin::choose_tuple(#arg));
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

    fn visit_item_fn_mut(&mut self, fun: &mut ItemFn) {
        fun.attrs.push(parse_quote_spanned!(fun.sig.fn_token.span => #[verifier(verus_macro)]));

        for arg in &mut fun.sig.inputs {
            match (arg.tracked, &mut arg.kind) {
                (None, _) => {}
                (Some(_), FnArgKind::Receiver(..)) => todo!("support tracked self"),
                (Some(token), FnArgKind::Typed(typed)) => {
                    typed.attrs.push(parse_quote_spanned!(token.span => #[proof]));
                }
            }
            arg.tracked = None;
        }
        let ret_var = match &mut fun.sig.output {
            ReturnType::Default => None,
            ReturnType::Type(_, ref mut tracked, ref mut ret_opt, ty) => {
                if let Some(token) = tracked {
                    fun.attrs.push(parse_quote_spanned!(token.span => #[verifier(returns(proof))]));
                    *tracked = None;
                }
                match std::mem::take(ret_opt) {
                    None => None,
                    Some(box (_, Pat::Ident(id), _))
                        if id.by_ref.is_none()
                            && id.mutability.is_none()
                            && id.subpat.is_none() =>
                    {
                        Some((id.ident, ty.clone()))
                    }
                    Some(_) => {
                        unimplemented!("TODO: support return patterns")
                    }
                }
            }
        };

        let (inside_ghost, mode_attrs): (u32, Vec<Attribute>) = match &fun.sig.mode {
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

        let mut stmts: Vec<Stmt> = Vec::new();
        let requires = std::mem::take(&mut fun.sig.requires);
        let recommends = std::mem::take(&mut fun.sig.recommends);
        let ensures = std::mem::take(&mut fun.sig.ensures);
        let decreases = std::mem::take(&mut fun.sig.decreases);
        if let Some(Requires { token, exprs }) = requires {
            stmts.push(parse_quote_spanned!(token.span => requires([#exprs]);));
        }
        if let Some(Recommends { token, exprs }) = recommends {
            stmts.push(parse_quote_spanned!(token.span => recommends([#exprs]);));
        }
        if let Some(Ensures { token, exprs }) = ensures {
            if let Some((x, ty)) = ret_var {
                stmts.push(parse_quote_spanned!(token.span => ensures(|#x: #ty| [#exprs]);));
            } else {
                stmts.push(parse_quote_spanned!(token.span => ensures([#exprs]);));
            }
        }
        if let Some(Decreases { token, exprs }) = decreases {
            stmts.push(parse_quote_spanned!(token.span => decreases((#exprs));));
        }
        fun.block.stmts.splice(0..0, stmts);

        visit_item_fn_mut(self, fun);
        fun.attrs.extend(mode_attrs);
        fun.sig.mode = FnMode::Default;
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
