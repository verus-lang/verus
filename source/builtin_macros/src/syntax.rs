use crate::rustdoc::env_rustdoc;
use proc_macro2::TokenStream;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::punctuated::Punctuated;
use syn_verus::token::{Brace, Bracket, Paren};
use syn_verus::visit_mut::{
    visit_block_mut, visit_expr_loop_mut, visit_expr_mut, visit_expr_while_mut, visit_field_mut,
    visit_impl_item_method_mut, visit_item_const_mut, visit_item_enum_mut, visit_item_fn_mut,
    visit_item_struct_mut, visit_local_mut, visit_trait_item_method_mut, VisitMut,
};
use syn_verus::{
    braced, bracketed, parenthesized, parse_macro_input, parse_quote_spanned, Attribute, BinOp,
    Block, DataMode, Decreases, Ensures, Expr, ExprBinary, ExprCall, ExprLit, ExprLoop, ExprPath,
    ExprTuple, ExprUnary, ExprWhile, Field, FnArgKind, FnMode, Ident, ImplItemMethod, Invariant,
    Item, ItemConst, ItemEnum, ItemFn, ItemStruct, Lit, Local, ModeSpec, ModeSpecChecked, Pat,
    Path, Publish, Recommends, Requires, ReturnType, Signature, Stmt, Token, TraitItemMethod, UnOp,
    Visibility,
};

fn take_expr(expr: &mut Expr) -> Expr {
    let dummy: Expr = syn_verus::parse_quote!(());
    std::mem::replace(expr, dummy)
}

fn take_pat(pat: &mut Pat) -> Pat {
    let dummy: Pat = syn_verus::parse_quote!(());
    std::mem::replace(pat, dummy)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InsideArith {
    None,
    Widen,
    Fixed,
}

struct Visitor {
    // TODO: this should always be true
    use_spec_traits: bool,
    // inside_ghost > 0 means we're currently visiting ghost code
    inside_ghost: u32,
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

fn path_is_ident(path: &Path, s: &str) -> bool {
    let segments = &path.segments;
    segments.len() == 1 && segments.first().unwrap().ident.to_string() == s
}

impl Visitor {
    fn visit_fn(
        &mut self,
        attrs: &mut Vec<Attribute>,
        vis: Option<&Visibility>,
        sig: &mut Signature,
        semi_token: Option<Token![;]>,
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
            stmts.push(parse_quote_spanned!(token.span => ::builtin::requires([#exprs]);));
        }
        if let Some(Recommends { token, exprs }) = recommends {
            stmts.push(parse_quote_spanned!(token.span => ::builtin::recommends([#exprs]);));
        }
        if let Some(Ensures { token, exprs }) = ensures {
            if let Some((p, ty)) = ret_pat {
                stmts.push(
                    parse_quote_spanned!(token.span => ::builtin::ensures(|#p: #ty| [#exprs]);),
                );
            } else {
                stmts.push(parse_quote_spanned!(token.span => ::builtin::ensures([#exprs]);));
            }
        }
        if let Some(Decreases { token, exprs }) = decreases {
            stmts.push(parse_quote_spanned!(token.span => ::builtin::decreases((#exprs));));
        }
        sig.publish = Publish::Default;
        sig.mode = FnMode::Default;
        attrs.extend(publish_attrs);
        attrs.extend(mode_attrs);
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
        attrs.push(parse_quote_spanned!(span => #[verifier(verus_macro)]));

        let publish_attrs = match (vis, &publish) {
            (Some(Visibility::Inherited), _) => vec![],
            (_, Publish::Default) => vec![parse_quote_spanned!(span => #[verifier(publish)])],
            (_, Publish::Closed(_)) => vec![],
            (_, Publish::Open(o)) => {
                vec![parse_quote_spanned!(o.token.span => #[verifier(publish)])]
            }
            (_, Publish::OpenRestricted(_)) => {
                unimplemented!("TODO: support open(...)")
            }
        };

        let (inside_ghost, mode_attrs): (u32, Vec<Attribute>) = match &mode {
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
                                    let f: Path = if path_is_ident(&trk.path, "Gho") {
                                        parse_quote_spanned!(span => crate::pervasive::modes::tracked_unwrap_gho)
                                    } else {
                                        parse_quote_spanned!(span => crate::pervasive::modes::tracked_unwrap_trk)
                                    };
                                    stmts.push(parse_quote_spanned!(span => let #x = #f(#x);));
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
            if let Some((eq, box_init)) = std::mem::replace(&mut local.init, None) {
                let span = eq.span;
                let name = format!("{splitter}{n}");
                let mut f: Path = parse_quote_spanned!(span => ::builtin::__temp__);
                f.segments.last_mut().unwrap().ident = Ident::new(&name, span);
                let init = parse_quote_spanned!(span => #f(#box_init));
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
                BinOp::Le(_) => parse_quote_spanned!(span => ::builtin::spec_chained_le),
                BinOp::Lt(_) => parse_quote_spanned!(span => ::builtin::spec_chained_lt),
                BinOp::Ge(_) => parse_quote_spanned!(span => ::builtin::spec_chained_ge),
                BinOp::Gt(_) => parse_quote_spanned!(span => ::builtin::spec_chained_gt),
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
    //   spec_chained_cmp(spec_chained_le(spec_chained_le(spec_chained_le(spec_chained_value(e0), e1), e2), e3))
    let span = expr.span();
    *expr = parse_quote_spanned!(span => ::builtin::spec_chained_value(#expr));
    while let Some((right, op, span)) = rights.pop() {
        *expr = parse_quote_spanned!(span => #op(#expr, #right));
    }
    *expr = parse_quote_spanned!(span => ::builtin::spec_chained_cmp(#expr));
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

        let ghost_intrinsic = match &expr {
            Expr::Call(ExprCall {
                func: box Expr::Path(syn_verus::ExprPath { path: Path { segments, .. }, .. }),
                ..
            }) if segments.len() == 2 => {
                if segments.first().unwrap().ident.to_string() == "builtin" {
                    match segments.last().unwrap().ident.to_string().as_str() {
                        "requires" | "ensures" | "recommends" | "decreases" | "invariant" => true,
                        _ => false,
                    }
                } else {
                    false
                }
            }
            _ => false,
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
            Expr::Call(ExprCall {
                func: box Expr::Path(ExprPath { path: Path { segments, .. }, .. }),
                ..
            }) if segments.len() == 2 => {
                if segments.first().unwrap().ident.to_string() == "builtin" {
                    match segments.last().unwrap().ident.to_string().as_str() {
                        "spec_chained_value" | "spec_chained_cmp" | "spec_chained_le"
                        | "spec_chained_lt" | "spec_chained_ge" | "spec_chained_gt" => {
                            InsideArith::Widen
                        }
                        _ => InsideArith::None,
                    }
                } else {
                    InsideArith::None
                }
            }
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
        if mode_block.is_some() || ghost_intrinsic {
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
        visit_expr_mut(self, expr);
        if let Expr::Assign(assign) = expr {
            assign.left = Box::new(assign_left.expect("assign_left"));
        }
        if mode_block.is_some() || ghost_intrinsic {
            self.inside_ghost -= 1;
        }
        self.inside_arith = is_inside_arith;
        self.assign_to = is_assign_to;

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
                        *expr = parse_quote_spanned!(span => #[verifier(ghost_wrapper)] crate::pervasive::modes::ghost_exec(#[verifier(ghost_block_wrapped)] #inner));
                    }
                    (false, (true, true), Expr::Paren(..)) => {
                        // tracked(...)
                        let inner = take_expr(&mut *unary.expr);
                        *expr = parse_quote_spanned!(span => #[verifier(ghost_wrapper)] crate::pervasive::modes::tracked_exec(#[verifier(tracked_block_wrapped)] #inner));
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
            Expr::Lit(ExprLit { lit: Lit::Int(..), .. }) if use_spec_traits => (true, false),
            Expr::Cast(..) if use_spec_traits => (true, false),
            Expr::Index(..) if use_spec_traits => (true, false),
            Expr::Unary(ExprUnary { op: UnOp::Forall(..), .. }) => (true, true),
            Expr::Unary(ExprUnary { op: UnOp::Exists(..), .. }) => (true, true),
            Expr::Unary(ExprUnary { op: UnOp::Choose(..), .. }) => (true, true),
            Expr::Unary(ExprUnary { op: UnOp::Neg(..), .. }) if use_spec_traits => (true, false),
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
            }) if use_spec_traits => (true, false),
            Expr::Assume(..) | Expr::Assert(..) | Expr::AssertForall(..) => (true, false),
            Expr::View(..) => (true, false),
            _ => (false, false),
        };
        if do_replace {
            match take_expr(expr) {
                Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs }) => {
                    let span = lit.span();
                    let n = lit.base10_digits().to_string();
                    if lit.suffix() == "" {
                        match is_inside_arith {
                            InsideArith::None => {
                                // We don't know which integer type to use,
                                // so defer the decision to type inference.
                                *expr = parse_quote_spanned!(span => ::builtin::spec_literal_integer(#n));
                                expr.replace_attrs(attrs);
                            }
                            InsideArith::Widen if n.starts_with("-") => {
                                // Use int inside +, -, etc., since these promote to int anyway
                                *expr =
                                    parse_quote_spanned!(span => ::builtin::spec_literal_int(#n));
                                expr.replace_attrs(attrs);
                            }
                            InsideArith::Widen => {
                                // Use int inside +, -, etc., since these promote to int anyway
                                *expr =
                                    parse_quote_spanned!(span => ::builtin::spec_literal_nat(#n));
                                expr.replace_attrs(attrs);
                            }
                            InsideArith::Fixed => {
                                // We generally won't want int/nat literals for bitwise ops,
                                // so use Rust's native integer literals
                                *expr = Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs });
                            }
                        }
                    } else if lit.suffix() == "int" {
                        *expr = parse_quote_spanned!(span => ::builtin::spec_literal_int(#n));
                        expr.replace_attrs(attrs);
                    } else if lit.suffix() == "nat" {
                        *expr = parse_quote_spanned!(span => ::builtin::spec_literal_nat(#n));
                        expr.replace_attrs(attrs);
                    } else {
                        // Has a native Rust integer suffix, so leave it as a native Rust literal
                        *expr = Expr::Lit(ExprLit { lit: Lit::Int(lit), attrs });
                    }
                }
                Expr::Cast(cast) => {
                    use syn_verus::spanned::Spanned;
                    let span = cast.span();
                    let src = cast.expr;
                    let attrs = cast.attrs;
                    let ty = cast.ty;
                    *expr =
                        parse_quote_spanned!(span => ::builtin::spec_cast_integer::<_, #ty>(#src));
                    expr.replace_attrs(attrs);
                }
                Expr::Index(idx) => {
                    use syn_verus::spanned::Spanned;
                    let span = idx.span();
                    let src = idx.expr;
                    let attrs = idx.attrs;
                    let index = idx.index;
                    *expr = parse_quote_spanned!(span => #src.spec_index(#index));
                    expr.replace_attrs(attrs);
                }
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
                                            parse_quote_spanned!(span => #[auto_trigger] (#body));
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
                            elems.push_punct(Token![,](span));
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
                Expr::Unary(unary) if !quant => {
                    use syn_verus::spanned::Spanned;
                    let span = unary.span();
                    let attrs = unary.attrs;
                    match unary.op {
                        UnOp::Neg(..) => {
                            let arg = unary.expr;
                            *expr = parse_quote_spanned!(span => (#arg).spec_neg());
                        }
                        _ => panic!("unary"),
                    }
                    expr.replace_attrs(attrs);
                }
                Expr::Binary(binary) => {
                    use syn_verus::spanned::Spanned;
                    let span = binary.span();
                    let attrs = binary.attrs;
                    let left = binary.left;
                    let right = binary.right;
                    match binary.op {
                        BinOp::Eq(..) => {
                            *expr = parse_quote_spanned!(span => spec_eq(#left, #right));
                        }
                        BinOp::Ne(..) => {
                            *expr = parse_quote_spanned!(span => !spec_eq(#left, #right));
                        }
                        BinOp::Le(..) => {
                            *expr = parse_quote_spanned!(span => (#left).spec_le(#right));
                        }
                        BinOp::Lt(..) => {
                            *expr = parse_quote_spanned!(span => (#left).spec_lt(#right));
                        }
                        BinOp::Ge(..) => {
                            *expr = parse_quote_spanned!(span => (#left).spec_ge(#right));
                        }
                        BinOp::Gt(..) => {
                            *expr = parse_quote_spanned!(span => (#left).spec_gt(#right));
                        }
                        BinOp::Add(..) => {
                            *expr = parse_quote_spanned!(span => (#left).spec_add(#right));
                        }
                        BinOp::Sub(..) => {
                            *expr = parse_quote_spanned!(span => (#left).spec_sub(#right));
                        }
                        BinOp::Mul(..) => {
                            *expr = parse_quote_spanned!(span => (#left).spec_mul(#right));
                        }
                        BinOp::Div(..) => {
                            *expr =
                                parse_quote_spanned!(span => (#left).spec_euclidean_div(#right));
                        }
                        BinOp::Rem(..) => {
                            *expr =
                                parse_quote_spanned!(span => (#left).spec_euclidean_mod(#right));
                        }
                        BinOp::BitAnd(..) => {
                            *expr = parse_quote_spanned!(span => (#left).spec_bitand(#right));
                        }
                        BinOp::BitOr(..) => {
                            *expr = parse_quote_spanned!(span => (#left).spec_bitor(#right));
                        }
                        BinOp::BitXor(..) => {
                            *expr = parse_quote_spanned!(span => (#left).spec_bitxor(#right));
                        }
                        BinOp::Shl(..) => {
                            *expr = parse_quote_spanned!(span => (#left).spec_shl(#right));
                        }
                        BinOp::Shr(..) => {
                            *expr = parse_quote_spanned!(span => (#left).spec_shr(#right));
                        }
                        _ => panic!("binary"),
                    }
                    expr.replace_attrs(attrs);
                }
                Expr::View(view) if !self.assign_to => {
                    let at_token = view.at_token;
                    let span = at_token.span;
                    let base = view.expr;
                    *expr = parse_quote_spanned!(span => (#base.view()));
                }
                Expr::View(view) => {
                    use syn_verus::spanned::Spanned;
                    assert!(self.assign_to);
                    let at_token = view.at_token;
                    let span1 = at_token.span;
                    let span2 = view.span();
                    let base = view.expr;
                    let borrowed: Expr = parse_quote_spanned!(span1 => #base.borrow_mut());
                    *expr = parse_quote_spanned!(span2 => (*(#borrowed)));
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
                            *expr = parse_quote_spanned!(span => ::builtin::assert_nonlinear_by({::builtin::ensures(#arg);}));
                        }
                        (Some(_), Some((_, id)), Some(box (requires, mut block)))
                            if id.to_string() == "nonlinear_arith" =>
                        {
                            let mut stmts: Vec<Stmt> = Vec::new();
                            if let Some(Requires { token, exprs }) = requires {
                                stmts.push(parse_quote_spanned!(token.span => ::builtin::requires([#exprs]);));
                            }
                            stmts.push(parse_quote_spanned!(span => ::builtin::ensures(#arg);));
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
                        stmts.push(parse_quote_spanned!(span => ::builtin::requires(#arg);));
                        stmts.push(parse_quote_spanned!(span => ::builtin::ensures(#rhs);));
                    } else {
                        stmts.push(parse_quote_spanned!(span => ::builtin::ensures(#arg);));
                    }
                    block.stmts.splice(0..0, stmts);
                    *expr = parse_quote_spanned!(span => {::builtin::assert_forall_by(|#inputs| #block);});
                    expr.replace_attrs(attrs);
                }
                _ => panic!("expected to replace expression"),
            }
        }
    }

    fn visit_expr_while_mut(&mut self, expr_while: &mut ExprWhile) {
        let invariants = std::mem::take(&mut expr_while.invariant);
        let decreases = std::mem::take(&mut expr_while.decreases);
        let mut stmts: Vec<Stmt> = Vec::new();
        // TODO: wrap specs inside ghost blocks
        if let Some(Invariant { token, exprs }) = invariants {
            stmts.push(parse_quote_spanned!(token.span => ::builtin::invariant([#exprs]);));
        }
        if let Some(Decreases { token, exprs }) = decreases {
            stmts.push(parse_quote_spanned!(token.span => ::builtin::decreases((#exprs));));
        }
        expr_while.body.stmts.splice(0..0, stmts);
        visit_expr_while_mut(self, expr_while);
    }

    fn visit_expr_loop_mut(&mut self, expr_loop: &mut ExprLoop) {
        let requires = std::mem::take(&mut expr_loop.requires);
        let invariants = std::mem::take(&mut expr_loop.invariant);
        let ensures = std::mem::take(&mut expr_loop.ensures);
        let decreases = std::mem::take(&mut expr_loop.decreases);
        let mut stmts: Vec<Stmt> = Vec::new();
        // TODO: wrap specs inside ghost blocks
        if let Some(Requires { token, exprs }) = requires {
            stmts.push(parse_quote_spanned!(token.span => ::builtin::requires([#exprs]);));
        }
        if let Some(Invariant { token, exprs }) = invariants {
            stmts.push(parse_quote_spanned!(token.span => ::builtin::invariant([#exprs]);));
        }
        if let Some(Ensures { token, exprs }) = ensures {
            stmts.push(parse_quote_spanned!(token.span => ::builtin::ensures([#exprs]);));
        }
        if let Some(Decreases { token, exprs }) = decreases {
            stmts.push(parse_quote_spanned!(token.span => ::builtin::decreases((#exprs));));
        }
        expr_loop.body.stmts.splice(0..0, stmts);
        visit_expr_loop_mut(self, expr_loop);
    }

    fn visit_local_mut(&mut self, local: &mut Local) {
        visit_local_mut(self, local);
        if let Some(tracked) = std::mem::take(&mut local.tracked) {
            local.attrs.push(parse_quote_spanned!(tracked.span => #[proof]));
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
        } else {
            let span = method.sig.fn_token.span;
            stmts.push(Stmt::Expr(parse_quote_spanned!(span => ::builtin::no_method_body())));
            let block = Block { brace_token: Brace(span), stmts };
            method.default = Some(block);
        }
        method.semi_token = None;
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
    use_spec_traits: bool,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let stream = rejoin_tokens(stream);
    let items: Items = parse_macro_input!(stream as Items);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        use_spec_traits,
        inside_ghost: 0,
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    for mut item in items.items {
        visitor.visit_item_mut(&mut item);
        visitor.inside_ghost = 0;
        visitor.inside_arith = InsideArith::None;
        item.to_tokens(&mut new_stream);
    }
    proc_macro::TokenStream::from(new_stream)
}

pub(crate) fn rewrite_expr(
    inside_ghost: bool,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let stream = rejoin_tokens(stream);
    let mut expr: Expr = parse_macro_input!(stream as Expr);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        use_spec_traits: true,
        inside_ghost: if inside_ghost { 1 } else { 0 },
        inside_arith: InsideArith::None,
        assign_to: false,
        rustdoc: env_rustdoc(),
    };
    visitor.visit_expr_mut(&mut expr);
    expr.to_tokens(&mut new_stream);
    proc_macro::TokenStream::from(new_stream)
}

// Unfortunatelly, the macro_rules tt tokenizer breaks tokens like &&& and ==> into smaller tokens.
// Try to put the original tokens back together here.
fn rejoin_tokens(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use proc_macro::{Group, Punct, Spacing::*, Span, TokenTree};
    use std::iter::FromIterator;
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
    inside_ghost: bool,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let stream = rejoin_tokens(stream);
    let mut invoke: MacroInvoke = parse_macro_input!(stream as MacroInvoke);
    let mut new_stream = TokenStream::new();
    let mut visitor = Visitor {
        use_spec_traits: true,
        inside_ghost: if inside_ghost { 1 } else { 0 },
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
