//! Source rewriter. For each .rs file of an instrumented crate, every maximal boolean expression
//! tree built from `&&` / `||` (looking through parentheses and `!` applied to such a tree) is a
//! decision. Its leaves are atoms. The decision is rewritten by inserting text at token boundaries,
//! so the line numbers of the original code do not change:
//!   ({let mut __mcdc_e: u128 = 0; let __mcdc_o: bool = TREE; crate::__mcdc::rec(ID, __mcdc_e, __mcdc_o); __mcdc_o})
//! where each atom A_i inside TREE becomes
//!   ({let __mcdc_c: bool = A_i; __mcdc_e |= if __mcdc_c {BITS_T} else {BITS_F}; __mcdc_c})
//! The operators of TREE are not changed, so evaluation order and short-circuiting are those of
//! the original code: an atom that is not evaluated leaves its 2 bits at 0.
//!
//! Let-chains in `if` and `while` conditions (`if a && let P = e && b`) are instrumented with a
//! marker after each `let` and the outcome recorded at the start of the then-branch (true) and in
//! the else-branch (false); see `handle_chain`.
//!
//! Skipped: let-chains in other positions (match guards), decisions with more than 64 atoms, const
//! contexts (const/static items, const fn, const blocks, array lengths, types, enum
//! discriminants), and code inside macro invocations (counted in `Stats::macro_logic_ops`).

use super::manifest::{Atom, Decision};
use super::{RUNTIME_FILE, Stats};
use crate::edit::{Insert, Kind, layer};
use proc_macro2::{LineColumn, TokenStream, TokenTree};
use quote::ToTokens;
use std::fmt::Write as _;
use syn::visit::{self, Visit};
use syn::{BinOp, Expr, UnOp};

struct Ctx<'a> {
    src: &'a str,
    line_starts: Vec<usize>,
    rel: String,
    krate: String,
    next_id: &'a mut u32,
    decisions: &'a mut Vec<Decision>,
    stats: &'a mut Stats,
    inserts: Vec<Insert>,
    seq: u32,
    depth: u32,
    in_const: u32,
    kind: Option<&'static str>,
    guarded: Option<String>,
    fn_stack: Vec<String>,
}

fn is_logic(e: &Expr) -> bool {
    match e {
        Expr::Binary(b) => matches!(b.op, BinOp::And(_) | BinOp::Or(_)),
        Expr::Paren(p) => is_logic(&p.expr),
        Expr::Unary(u) => matches!(u.op, UnOp::Not(_)) && is_logic(&u.expr),
        _ => false,
    }
}

/// Collects atoms left to right and writes the decision structure over atom indices
/// (`&&`, `||`, `!`, parentheses), for example `!(0&&1)||2`.
fn flatten<'e>(e: &'e Expr, out: &mut Vec<&'e Expr>, tree: &mut String) {
    match e {
        Expr::Binary(b) if matches!(b.op, BinOp::And(_) | BinOp::Or(_)) => {
            tree.push('(');
            flatten(&b.left, out, tree);
            tree.push_str(if matches!(b.op, BinOp::And(_)) { "&&" } else { "||" });
            flatten(&b.right, out, tree);
            tree.push(')');
        }
        Expr::Paren(p) if is_logic(&p.expr) => flatten(&p.expr, out, tree),
        Expr::Unary(u) if matches!(u.op, UnOp::Not(_)) && is_logic(&u.expr) => {
            tree.push('!');
            flatten(&u.expr, out, tree);
        }
        _ => {
            let _ = write!(tree, "{}", out.len());
            out.push(e)
        }
    }
}

/// A top-level `&&` chain with at least one `let` operand (Rust 2024 let-chain).
fn is_let_chain(e: &Expr) -> bool {
    let mut ops = Vec::new();
    chain_operands(e, &mut ops);
    ops.len() >= 2 && ops.iter().any(|o| matches!(o, Expr::Let(_)))
}

fn chain_operands<'e>(e: &'e Expr, out: &mut Vec<&'e Expr>) {
    match e {
        Expr::Binary(b) if matches!(b.op, BinOp::And(_)) => {
            chain_operands(&b.left, out);
            chain_operands(&b.right, out);
        }
        _ => out.push(e),
    }
}

fn span_range(ts: TokenStream, lo: &mut Option<LineColumn>, hi: &mut Option<LineColumn>) {
    fn upd(lo: &mut Option<LineColumn>, hi: &mut Option<LineColumn>, s: LineColumn, e: LineColumn) {
        if s == e || s.line == 0 {
            return;
        }
        let key = |p: LineColumn| (p.line, p.column);
        if lo.map_or(true, |l| key(s) < key(l)) {
            *lo = Some(s);
        }
        if hi.map_or(true, |h| key(e) > key(h)) {
            *hi = Some(e);
        }
    }
    for tt in ts {
        match tt {
            TokenTree::Group(g) => {
                upd(lo, hi, g.span_open().start(), g.span_open().end());
                upd(lo, hi, g.span_close().start(), g.span_close().end());
                span_range(g.stream(), lo, hi);
            }
            other => {
                let s = other.span();
                upd(lo, hi, s.start(), s.end());
            }
        }
    }
}

fn collapse_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

impl<'a> Ctx<'a> {
    fn off(&self, p: LineColumn) -> usize {
        let ls = self.line_starts[p.line - 1];
        let line_end = self.line_starts.get(p.line).copied().unwrap_or(self.src.len());
        let line = &self.src[ls..line_end];
        match line.char_indices().nth(p.column) {
            Some((b, _)) => ls + b,
            None => line_end,
        }
    }

    fn range_ts(&self, ts: TokenStream) -> Option<(usize, usize, LineColumn)> {
        let (mut lo, mut hi) = (None, None);
        span_range(ts, &mut lo, &mut hi);
        let (lo, hi) = (lo?, hi?);
        Some((self.off(lo), self.off(hi), lo))
    }

    fn range(&self, e: &Expr) -> Option<(usize, usize, LineColumn)> {
        self.range_ts(e.to_token_stream())
    }

    fn text_of(&self, ts: TokenStream) -> Option<String> {
        let (s, e, _) = self.range_ts(ts)?;
        Some(collapse_ws(&self.src[s..e]).chars().take(400).collect())
    }

    fn ins(
        &mut self,
        off: usize,
        kind: Kind,
        span: (usize, usize),
        layer: u8,
        depth: u32,
        text: String,
    ) {
        self.seq += 1;
        self.inserts.push(Insert { off, del: 0, kind, span, layer, depth, seq: self.seq, text });
    }

    /// A statement inserted right after a `{` at `off`.
    fn point(&mut self, off: usize, depth: u32, text: String) {
        self.ins(off, Kind::Open, (off, usize::MAX), layer::POINT, depth, text);
    }

    /// A wrapper around [s, e).
    fn wrap(&mut self, s: usize, e: usize, layer: u8, depth: u32, open: String, close: String) {
        self.ins(s, Kind::Open, (s, e), layer, depth, open);
        self.ins(e, Kind::Close, (s, e), layer, depth, close);
    }

    fn push_decision(
        &mut self,
        id: u32,
        lc: LineColumn,
        kind: &str,
        tree: String,
        guarded: String,
        text: String,
        atoms: Vec<Atom>,
    ) {
        let func = self.fn_stack.last().cloned().unwrap_or_default();
        self.decisions.push(Decision {
            id,
            krate: self.krate.clone(),
            file: self.rel.clone(),
            line: lc.line,
            col: lc.column + 1,
            kind: kind.to_string(),
            func,
            tree,
            guarded,
            text,
            atoms,
        });
    }

    fn atom(&self, s: usize, en: usize, lc: LineColumn) -> Atom {
        Atom { line: lc.line, col: lc.column + 1, text: collapse_ws(&self.src[s..en]) }
    }

    /// Let-chain decision: atoms are the top-level `&&` operands. A leading marker operand sets bit
    /// 127 (evaluation started); bool atoms are wrapped as usual; after each `let` atom a marker
    /// operand records it as evaluated-true (it runs only if the pattern matched). The runtime
    /// `rec_chain` marks the first unrecorded atom as evaluated-false when the outcome is false and
    /// no atom recorded false. In a match guard (`guard` true) the vector lives in thread-local
    /// storage of the runtime (`g_start`, `g_atom`, `g_end`), because a guard cannot be wrapped in
    /// a block that declares a variable. Returns the decision id. Atoms are visited for nested
    /// decisions at depth + 2.
    fn handle_chain(
        &mut self,
        cond: &Expr,
        kind: &'static str,
        guarded: String,
        guard: bool,
    ) -> u32 {
        let mut ops = Vec::new();
        chain_operands(cond, &mut ops);
        let d = self.depth;
        let id = *self.next_id;
        *self.next_id += 1;
        let (cs, ce, clc) = self.range(cond).unwrap();
        let start = if guard {
            format!("({{crate::__mcdc::g_start({}); true}}) && ", id)
        } else {
            "({__mcdc_e = 1u128 << 127; true}) && ".to_string()
        };
        self.ins(cs, Kind::Open, (cs, ce), layer::MCDC_DECISION, d + 1, start);
        let mut atoms = Vec::new();
        let mut tree = String::new();
        for (i, a) in ops.iter().enumerate() {
            let (s, en, lc) = self.range(a).unwrap();
            let bt: u128 = 3u128 << (2 * i);
            let bf: u128 = 1u128 << (2 * i);
            if matches!(a, Expr::Let(_)) {
                let t = if guard {
                    format!(" && ({{crate::__mcdc::g_atom({}, {}, true); true}})", id, i)
                } else {
                    format!(" && ({{__mcdc_e |= {}u128; true}})", bt)
                };
                self.ins(en, Kind::Close, (s, en), layer::MCDC_DECISION, d + 1, t);
            } else {
                let close = if guard {
                    format!("; crate::__mcdc::g_atom({}, {}, __mcdc_c); __mcdc_c}})", id, i)
                } else {
                    format!(
                        "; __mcdc_e |= if __mcdc_c {{{}u128}} else {{{}u128}}; __mcdc_c}})",
                        bt, bf
                    )
                };
                self.wrap(
                    s,
                    en,
                    layer::MCDC_ATOM,
                    d + 1,
                    "({let __mcdc_c: bool = ".to_string(),
                    close,
                );
            }
            if i == 0 {
                let _ = write!(tree, "{}", i);
            } else {
                tree = format!("({}&&{})", tree, i);
            }
            atoms.push(self.atom(s, en, lc));
        }
        let text = collapse_ws(&self.src[cs..ce]);
        self.push_decision(id, clc, kind, tree, guarded, text, atoms);
        self.stats.decisions += 1;
        self.stats.letchains += 1;
        self.stats.atoms += ops.len();
        self.depth = d + 2;
        for a in &ops {
            self.kind = None;
            self.visit_expr(a);
        }
        self.depth = d;
        id
    }

    fn handle(&mut self, e: &Expr, kind: &'static str) {
        let mut atoms = Vec::new();
        let mut tree = String::new();
        flatten(e, &mut atoms, &mut tree);
        let guarded = self.guarded.take().unwrap_or_default();
        let has_let = atoms.iter().any(|a| matches!(a, Expr::Let(_)));
        let d = self.depth;
        let instrument = if has_let {
            self.stats.skipped_letchain += 1;
            false
        } else if atoms.len() > 64 {
            self.stats.skipped_too_many += 1;
            false
        } else {
            true
        };
        let whole = self.range(e);
        let ranges: Vec<_> =
            if instrument { atoms.iter().map(|a| self.range(a)).collect() } else { Vec::new() };
        if instrument && whole.is_some() && ranges.iter().all(|r| r.is_some()) {
            let id = *self.next_id;
            *self.next_id += 1;
            let (ws, we, wlc) = whole.unwrap();
            self.wrap(
                ws,
                we,
                layer::MCDC_DECISION,
                d,
                "({let mut __mcdc_e: u128 = 0; let __mcdc_o: bool = ".to_string(),
                format!("; crate::__mcdc::rec({}, __mcdc_e, __mcdc_o); __mcdc_o}})", id),
            );
            let mut atom_list = Vec::new();
            for (i, r) in ranges.iter().enumerate() {
                let (s, en, lc) = r.unwrap();
                let bt: u128 = 3u128 << (2 * i);
                let bf: u128 = 1u128 << (2 * i);
                self.wrap(
                    s,
                    en,
                    layer::MCDC_ATOM,
                    d + 1,
                    "({let __mcdc_c: bool = ".to_string(),
                    format!(
                        "; __mcdc_e |= if __mcdc_c {{{}u128}} else {{{}u128}}; __mcdc_c}})",
                        bt, bf
                    ),
                );
                atom_list.push(self.atom(s, en, lc));
            }
            let text = collapse_ws(&self.src[ws..we]);
            self.push_decision(id, wlc, kind, tree, guarded, text, atom_list);
            self.stats.decisions += 1;
            self.stats.atoms += atoms.len();
            self.depth = d + 2;
            for a in &atoms {
                self.visit_expr(a);
            }
            self.depth = d;
        } else {
            for a in &atoms {
                self.visit_expr(a);
            }
        }
    }
    fn count_macro_ops(&mut self, ts: TokenStream) {
        let mut prev: Option<(char, proc_macro2::Spacing)> = None;
        for tt in ts {
            match tt {
                TokenTree::Punct(p) => {
                    let c = p.as_char();
                    if let Some((pc, sp)) = prev {
                        if sp == proc_macro2::Spacing::Joint && pc == c && (c == '&' || c == '|') {
                            self.stats.macro_logic_ops += 1;
                            prev = None;
                            continue;
                        }
                    }
                    prev = Some((c, p.spacing()));
                }
                TokenTree::Group(g) => {
                    prev = None;
                    self.count_macro_ops(g.stream());
                }
                _ => prev = None,
            }
        }
    }

    fn visit_fn_body(&mut self, sig: &syn::Signature, block: &syn::Block) {
        let c = sig.constness.is_some() as u32;
        self.in_const += c;
        self.fn_stack.push(sig.ident.to_string());
        self.visit_block(block);
        self.fn_stack.pop();
        self.in_const -= c;
    }
}

impl<'a, 'ast> Visit<'ast> for Ctx<'a> {
    fn visit_expr(&mut self, e: &'ast Expr) {
        let kind = self.kind.take();
        if kind.is_none() {
            self.guarded = None;
        }
        if self.in_const > 0 {
            if is_logic(e) {
                self.stats.skipped_const += 1;
            }
            return visit::visit_expr(self, e);
        }
        if is_logic(e) {
            self.handle(e, kind.unwrap_or("expr"));
        } else {
            self.guarded = None;
            visit::visit_expr(self, e);
        }
    }
    fn visit_expr_if(&mut self, e: &'ast syn::ExprIf) {
        if self.in_const == 0 && is_let_chain(&e.cond) {
            let then_open = self.off(e.then_branch.brace_token.span.open().end());
            let then_end = self.off(e.then_branch.brace_token.span.close().end());
            let guarded = self.text_of(e.then_branch.to_token_stream()).unwrap_or_default();
            let whole = self.range_ts(e.to_token_stream());
            let d = self.depth;
            let Some((ws, we, _)) = whole else { return visit::visit_expr_if(self, e) };
            let id = self.handle_chain(&e.cond, "if-letchain", guarded, false);
            self.wrap(
                ws,
                we,
                layer::MCDC_DECISION,
                d,
                "{ let mut __mcdc_e: u128 = 0; ".to_string(),
                " }".to_string(),
            );
            self.point(
                then_open,
                d + 1,
                format!(" crate::__mcdc::rec_chain({}, __mcdc_e, true); ", id),
            );
            self.depth = d + 2;
            self.visit_block(&e.then_branch);
            match &e.else_branch {
                Some((_, el)) => {
                    if let Some((es, ee, _)) = self.range(el) {
                        self.wrap(
                            es,
                            ee,
                            layer::MCDC_DECISION,
                            d + 1,
                            format!("{{ crate::__mcdc::rec_chain({}, __mcdc_e, false); ", id),
                            " }".to_string(),
                        );
                    }
                    self.visit_expr(el);
                }
                None => {
                    // after the then block, inside the wrapper of the whole `if`
                    self.ins(
                        then_end,
                        Kind::Close,
                        (then_open, then_end),
                        layer::MCDC_DECISION,
                        d + 1,
                        format!(" else {{ crate::__mcdc::rec_chain({}, __mcdc_e, false); }}", id),
                    );
                }
            }
            self.depth = d;
            return;
        }
        self.kind = Some("if");
        self.guarded = self.text_of(e.then_branch.to_token_stream());
        self.visit_expr(&e.cond);
        self.visit_block(&e.then_branch);
        if let Some((_, el)) = &e.else_branch {
            self.visit_expr(el);
        }
    }
    fn visit_expr_while(&mut self, e: &'ast syn::ExprWhile) {
        if self.in_const == 0 && is_let_chain(&e.cond) {
            let body_open = self.off(e.body.brace_token.span.open().end());
            let guarded = self.text_of(e.body.to_token_stream()).unwrap_or_default();
            let whole = self.range_ts(e.to_token_stream());
            let d = self.depth;
            let Some((ws, we, _)) = whole else { return visit::visit_expr_while(self, e) };
            let id = self.handle_chain(&e.cond, "while-letchain", guarded, false);
            self.wrap(
                ws,
                we,
                layer::MCDC_DECISION,
                d,
                "{ let mut __mcdc_e: u128 = 0; ".to_string(),
                format!("; crate::__mcdc::rec_chain({}, __mcdc_e, false); }}", id),
            );
            self.point(
                body_open,
                d + 1,
                format!(" crate::__mcdc::rec_chain({}, __mcdc_e, true); __mcdc_e = 0; ", id),
            );
            self.depth = d + 2;
            self.visit_block(&e.body);
            self.depth = d;
            return;
        }
        self.kind = Some("while");
        self.guarded = self.text_of(e.body.to_token_stream());
        self.visit_expr(&e.cond);
        self.visit_block(&e.body);
    }
    fn visit_expr_match(&mut self, m: &'ast syn::ExprMatch) {
        // let-chain guards: every arm body of the match ends the pending guard evaluation, with
        // outcome true in the guarded arm and false in the others (`g_end`)
        let chains: Vec<usize> = if self.in_const == 0 {
            (0..m.arms.len())
                .filter(|&k| m.arms[k].guard.as_ref().map_or(false, |(_, g)| is_let_chain(g)))
                .collect()
        } else {
            Vec::new()
        };
        if chains.is_empty() {
            return visit::visit_expr_match(self, m);
        }
        self.visit_expr(&m.expr);
        let d = self.depth;
        let mut ids = Vec::new();
        for (k, a) in m.arms.iter().enumerate() {
            if let (true, Some((_, g))) = (chains.contains(&k), &a.guard) {
                let guarded = self.text_of(a.body.to_token_stream()).unwrap_or_default();
                ids.push((k, self.handle_chain(g, "guard-letchain", guarded, true)));
            } else if let Some((_, g)) = &a.guard {
                self.kind = Some("guard");
                self.guarded = self.text_of(a.body.to_token_stream());
                self.visit_expr(g);
            }
        }
        for (k, a) in m.arms.iter().enumerate() {
            let text: String = ids
                .iter()
                .map(|(gk, id)| format!(" crate::__mcdc::g_end({}, {});", id, *gk == k))
                .collect();
            match &*a.body {
                Expr::Block(b) if b.label.is_none() => {
                    let o = self.off(b.block.brace_token.span.open().end());
                    self.point(o, d + 1, format!("{} ", text));
                }
                body => {
                    if let Some((s, e, _)) = self.range(body) {
                        self.wrap(
                            s,
                            e,
                            layer::MCDC_DECISION,
                            d + 1,
                            format!("{{{} ", text),
                            " }".to_string(),
                        );
                    }
                }
            }
            self.visit_expr(&a.body);
        }
    }
    fn visit_arm(&mut self, a: &'ast syn::Arm) {
        if let Some((_, g)) = &a.guard {
            self.kind = Some("guard");
            self.guarded = self.text_of(a.body.to_token_stream());
            self.visit_expr(g);
        }
        self.visit_expr(&a.body);
    }
    fn visit_local(&mut self, l: &'ast syn::Local) {
        if let Some(init) = &l.init {
            self.kind = Some("let");
            self.visit_expr(&init.expr);
            if let Some((_, el)) = &init.diverge {
                self.visit_expr(el);
            }
        }
    }
    fn visit_expr_return(&mut self, r: &'ast syn::ExprReturn) {
        if let Some(e) = &r.expr {
            self.kind = Some("return");
            self.visit_expr(e);
        }
    }
    fn visit_expr_closure(&mut self, c: &'ast syn::ExprClosure) {
        self.kind = Some("closure");
        self.visit_expr(&c.body);
    }
    // const contexts and syntax that is not evaluated at run time
    fn visit_type(&mut self, _: &'ast syn::Type) {}
    fn visit_pat(&mut self, _: &'ast syn::Pat) {}
    fn visit_attribute(&mut self, _: &'ast syn::Attribute) {}
    fn visit_generic_argument(&mut self, _: &'ast syn::GenericArgument) {}
    fn visit_generics(&mut self, _: &'ast syn::Generics) {}
    fn visit_expr_const(&mut self, _: &'ast syn::ExprConst) {}
    fn visit_expr_repeat(&mut self, r: &'ast syn::ExprRepeat) {
        self.visit_expr(&r.expr);
    }
    fn visit_variant(&mut self, _: &'ast syn::Variant) {}
    fn visit_macro(&mut self, m: &'ast syn::Macro) {
        let name = m.path.segments.last().map(|s| s.ident.to_string()).unwrap_or_default();
        if !name.starts_with("quote") && name != "parse_quote" && name != "parse_quote_spanned" {
            self.count_macro_ops(m.tokens.clone());
        }
    }
    fn visit_item_const(&mut self, i: &'ast syn::ItemConst) {
        self.in_const += 1;
        visit::visit_item_const(self, i);
        self.in_const -= 1;
    }
    fn visit_item_static(&mut self, i: &'ast syn::ItemStatic) {
        self.in_const += 1;
        visit::visit_item_static(self, i);
        self.in_const -= 1;
    }
    fn visit_impl_item_const(&mut self, i: &'ast syn::ImplItemConst) {
        self.in_const += 1;
        visit::visit_impl_item_const(self, i);
        self.in_const -= 1;
    }
    fn visit_trait_item_const(&mut self, i: &'ast syn::TraitItemConst) {
        self.in_const += 1;
        visit::visit_trait_item_const(self, i);
        self.in_const -= 1;
    }
    fn visit_item_fn(&mut self, f: &'ast syn::ItemFn) {
        self.visit_fn_body(&f.sig, &f.block);
    }
    fn visit_impl_item_fn(&mut self, f: &'ast syn::ImplItemFn) {
        self.visit_fn_body(&f.sig, &f.block);
    }
    fn visit_trait_item_fn(&mut self, f: &'ast syn::TraitItemFn) {
        if let Some(b) = &f.default {
            self.visit_fn_body(&f.sig, b);
        }
    }
}

/// Rewrites one source file. `rel` is the path recorded in the manifest, `krate` the crate
/// directory name. When `is_root` is true, the file gets the crate-level lint allowances and the
/// `mod __mcdc` declaration that includes `RUNTIME_FILE` from the same directory. Returns the
/// rewritten text, or `None` when nothing was inserted. Decisions are appended to `decisions`
/// with ids starting at `*next_id`.
pub fn instrument_source(
    src: &str,
    rel: &str,
    krate: &str,
    is_root: bool,
    next_id: &mut u32,
    decisions: &mut Vec<Decision>,
    stats: &mut Stats,
) -> Result<Option<String>, String> {
    match instrument_inserts(src, rel, krate, is_root, next_id, decisions, stats)? {
        Some(ins) if !ins.is_empty() => {
            stats.files_changed += 1;
            crate::edit::render(src, ins).map(Some).map_err(|e| format!("{}: {}", rel, e))
        }
        _ => Ok(None),
    }
}

/// The edits of `instrument_source`, not applied (`None` when the file does not parse), so that
/// the mutant rewriter can apply them together with its own.
pub fn instrument_inserts(
    src: &str,
    rel: &str,
    krate: &str,
    is_root: bool,
    next_id: &mut u32,
    decisions: &mut Vec<Decision>,
    stats: &mut Stats,
) -> Result<Option<Vec<Insert>>, String> {
    if src.contains("__mcdc") {
        return Err(format!("{} is already instrumented (contains `__mcdc`)", rel));
    }
    stats.files += 1;
    let file = match syn::parse_file(src) {
        Ok(x) => x,
        Err(e) => {
            stats.parse_failures.push(format!("{}: {}", rel, e));
            return Ok(None);
        }
    };
    let mut line_starts = vec![0usize];
    for (b, c) in src.char_indices() {
        if c == '\n' {
            line_starts.push(b + 1);
        }
    }
    let mut ctx = Ctx {
        src,
        line_starts,
        rel: rel.to_string(),
        krate: krate.to_string(),
        next_id,
        decisions,
        stats,
        inserts: Vec::new(),
        seq: 0,
        depth: 0,
        in_const: 0,
        kind: None,
        guarded: None,
        fn_stack: Vec::new(),
    };
    ctx.visit_file(&file);
    let mut inserts = std::mem::take(&mut ctx.inserts);
    if is_root {
        // Crate-level lint allowances at offset 0 (an inner attribute, no newline added).
        inserts.push(Insert {
            off: 0,
            del: 0,
            kind: Kind::Open,
            span: (0, usize::MAX),
            layer: layer::POINT,
            depth: 0,
            seq: 0,
            text: "#![allow(unused_parens, unused_braces, unreachable_code, unused_assignments)] "
                .to_string(),
        });
        // The runtime module goes after all original lines, so line numbers do not change.
        inserts.push(Insert {
            off: src.len(),
            del: 0,
            kind: Kind::Open,
            span: (src.len(), src.len()),
            layer: layer::END,
            depth: u32::MAX,
            seq: u32::MAX,
            text: format!(
                "\n#[allow(dead_code, unused)] mod __mcdc {{ include!({:?}); }}\n",
                RUNTIME_FILE
            ),
        });
    }
    Ok(Some(inserts))
}
