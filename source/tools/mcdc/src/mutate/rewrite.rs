//! Mutant-schemata rewriter with path-condition (guard) instrumentation.
//!
//! One pass assigns decision ids and mutant ids.
//! Decisions: every if / while / match-guard condition (single atom or `&&`/`||` tree), every
//! `if let`, every other `&&`/`||` tree, and every match (outcome = arm index). A decision whose start
//! (file, line, col) matches a decision of the MC/DC manifest gets that manifest id; the others get
//! ids from `FIRST_LOCAL_DECISION` up, in (file, line, col) order.
//! Mutants: ids from 1 up in (file order, line, col, operator order) order, so the map is a
//! deterministic function of the source, the file list and the disable list.
//!
//! Each guarded body (then / else block, while body, match arm) starts with
//!   let __mg = crate::__mut::guard(DECISION_ID, OUTCOME);
//! (RAII: pushes on a thread-local guard stack while logging, pops on drop, so early return, `?`,
//! break and unwinding all pop). Each mutation point calls a helper in `crate::__mut` with its base id.
//! The rewriter adds no MC/DC recording of its own: `mutate_sources_with` applies the edits of the
//! MC/DC rewriter to the same file (see `crate::edit` for how the two sets of edits nest), so a
//! mutated file records exactly what `mcdc instrument` records, let-chains included.
//!
//! Disable entries: `rel_file:line` (every point starting on that line) or `rel_file:line@op`
//! (points with that operator on that line; op `guard` disables the guard inserts of decisions on
//! that line).

use proc_macro2::{LineColumn, TokenStream, TokenTree};
use quote::ToTokens;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use syn::visit::{self, Visit};
use syn::{BinOp, Expr, Stmt, UnOp};

use crate::edit::{Insert, Kind, layer};

#[derive(Clone, Copy, PartialEq)]
enum CondCtx {
    None,
    If { has_else: bool },
    While,
    Guard,
}

struct Point {
    file_idx: usize,
    line: usize,
    col: usize,
    end_line: usize,
    end_col: usize,
    seq: usize,
    muts: Vec<(&'static str, String)>,
    orig: String,
    fn_path: String,
    krate: String,
    rel: String,
    atom: Option<usize>,
    atom_dec: Option<usize>,
    guards: Vec<(usize, u32)>,
}

struct Dec {
    file_idx: usize,
    rel: String,
    line: usize,
    col: usize,
    kind: &'static str,
    fn_path: String,
    text: String,
    narms: usize,
    natoms: usize,
}

struct Global {
    points: Vec<Point>,
    decs: Vec<Dec>,
    disabled: HashSet<String>,
    skipped_disabled: usize,
    guards_disabled: usize,
}

struct Ctx<'a> {
    src: &'a str,
    line_starts: Vec<usize>,
    rel: String,
    krate: String,
    file_idx: usize,
    g: &'a mut Global,
    inserts: Vec<Insert>,
    seq: u32,
    depth: u32,
    in_const: u32,
    in_fn: u32,
    cond_ctx: CondCtx,
    atom_flag: bool,
    ret_bool: Vec<bool>,
    path: Vec<String>,
    fn_stack: Vec<String>,
    guards: Vec<(usize, u32)>,
    cur_decision: Option<usize>,
    last_dec: Option<usize>,
    single: bool,
    stmt_top: bool,
}

fn is_logic(e: &Expr) -> bool {
    match e {
        Expr::Binary(b) => matches!(b.op, BinOp::And(_) | BinOp::Or(_)),
        Expr::Paren(p) => is_logic(&p.expr),
        Expr::Unary(u) => matches!(u.op, UnOp::Not(_)) && is_logic(&u.expr),
        _ => false,
    }
}

fn has_let(e: &Expr) -> bool {
    match e {
        Expr::Binary(b) if matches!(b.op, BinOp::And(_) | BinOp::Or(_)) => {
            has_let(&b.left) || has_let(&b.right)
        }
        Expr::Let(_) => true,
        _ => false,
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

fn is_err_call(e: &Expr) -> bool {
    if let Expr::Call(c) = e {
        if let Expr::Path(p) = &*c.func {
            return p.qself.is_none()
                && p.path.segments.len() == 1
                && p.path.segments[0].ident == "Err";
        }
    }
    false
}

const SKIP_MACROS: &[&str] = &[
    "println",
    "print",
    "eprintln",
    "eprint",
    "dbg",
    "assert",
    "assert_eq",
    "assert_ne",
    "debug_assert",
    "debug_assert_eq",
    "debug_assert_ne",
    "panic",
    "unreachable",
    "todo",
    "unimplemented",
    "write",
    "writeln",
    "format",
    "format_args",
];
const SKIP_METHODS: &[&str] = &["unwrap", "expect", "clone"];

fn macro_name(m: &syn::Macro) -> String {
    m.path.segments.last().map(|s| s.ident.to_string()).unwrap_or_default()
}

fn deletable(e: &Expr) -> bool {
    match e {
        Expr::MethodCall(m) => !SKIP_METHODS.contains(&m.method.to_string().as_str()),
        Expr::Call(c) => {
            if let Expr::Path(p) = &*c.func {
                let last = p.path.segments.last().map(|s| s.ident.to_string()).unwrap_or_default();
                !(last == "panic_any" || last == "unreachable" || last == "drop")
            } else {
                true
            }
        }
        Expr::Assign(_) => true,
        Expr::Binary(b) => matches!(
            b.op,
            BinOp::AddAssign(_)
                | BinOp::SubAssign(_)
                | BinOp::MulAssign(_)
                | BinOp::DivAssign(_)
                | BinOp::RemAssign(_)
                | BinOp::BitXorAssign(_)
                | BinOp::BitAndAssign(_)
                | BinOp::BitOrAssign(_)
                | BinOp::ShlAssign(_)
                | BinOp::ShrAssign(_)
        ),
        Expr::Macro(m) => !SKIP_MACROS.contains(&macro_name(&m.mac).as_str()),
        _ => false,
    }
}

fn is_some_call(e: &Expr) -> bool {
    if let Expr::Call(c) = e {
        if let Expr::Path(p) = &*c.func {
            return c.args.len() == 1
                && p.qself.is_none()
                && p.path.segments.len() == 1
                && p.path.segments[0].ident == "Some";
        }
    }
    false
}

/// Small Verus enums whose unit variants are swapped by `enum-variant`.
const ENUMS: &[(&str, &[&str])] = &[
    ("Mode", &["Spec", "Proof", "Exec"]),
    ("Ghost", &["Exec", "Ghost"]),
    ("InvAtomicity", &["Atomic", "NonAtomic"]),
    ("InequalityOp", &["Le", "Ge", "Lt", "Gt"]),
    ("IntRange", &["Int", "Nat", "Char", "USize", "ISize"]),
];

fn variant_alts(segs: &[String]) -> Option<(String, String, Vec<String>)> {
    if segs.len() != 2 {
        return None;
    }
    for (e, vs) in ENUMS {
        if segs[0] == *e && vs.contains(&segs[1].as_str()) {
            let alts = vs.iter().filter(|v| **v != segs[1]).map(|v| v.to_string()).collect();
            return Some((e.to_string(), segs[1].clone(), alts));
        }
    }
    None
}

fn enum_alts(p: &syn::ExprPath) -> Option<(String, String, Vec<String>)> {
    if p.qself.is_some() || p.path.segments.iter().any(|s| !s.arguments.is_none()) {
        return None;
    }
    let segs: Vec<String> = p.path.segments.iter().map(|s| s.ident.to_string()).collect();
    variant_alts(&segs)
}

fn simple_receiver(e: &Expr) -> bool {
    match e {
        Expr::Path(_) => true,
        Expr::Field(f) => simple_receiver(&f.base),
        Expr::Paren(p) => simple_receiver(&p.expr),
        _ => false,
    }
}

fn type_name(t: &syn::Type) -> String {
    match t {
        syn::Type::Path(p) => {
            p.path.segments.last().map(|s| s.ident.to_string()).unwrap_or_default()
        }
        syn::Type::Reference(r) => type_name(&r.elem),
        other => collapse_ws(&other.to_token_stream().to_string()),
    }
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

    fn lc_of(&self, off: usize) -> (usize, usize) {
        let l = match self.line_starts.binary_search(&off) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        (l + 1, self.src[self.line_starts[l]..off].chars().count() + 1)
    }

    fn range_ts(&self, ts: TokenStream) -> Option<(usize, usize, LineColumn)> {
        let (mut lo, mut hi) = (None, None);
        span_range(ts, &mut lo, &mut hi);
        let (lo, hi) = (lo?, hi?);
        Some((self.off(lo), self.off(hi), lo))
    }

    fn range<T: ToTokens>(&self, e: &T) -> Option<(usize, usize, LineColumn)> {
        self.range_ts(e.to_token_stream())
    }

    fn active(&self) -> bool {
        self.in_const == 0 && self.in_fn > 0
    }

    #[allow(clippy::too_many_arguments)]
    fn ins(
        &mut self,
        off: usize,
        del: usize,
        kind: Kind,
        span: (usize, usize),
        layer: u8,
        depth: u32,
        text: String,
    ) {
        self.seq += 1;
        self.inserts.push(Insert { off, del, kind, span, layer, depth, seq: self.seq, text });
    }

    /// A statement inserted right after a `{` at `off`.
    fn point_stmt(&mut self, off: usize, text: String) {
        self.ins(off, 0, Kind::Open, (off, usize::MAX), layer::POINT, 0, text);
    }

    fn is_disabled(&self, line: usize, ops: &[(&'static str, String)]) -> bool {
        self.g.disabled.contains(&format!("{}:{}", self.rel, line))
            || ops
                .iter()
                .any(|(op, _)| self.g.disabled.contains(&format!("{}:{}@{}", self.rel, line, op)))
    }

    fn fn_path(&self) -> String {
        self.fn_stack.last().cloned().unwrap_or_else(|| self.path.join("::"))
    }

    /// Registers a decision; returns its local index.
    fn new_dec(
        &mut self,
        lc: LineColumn,
        kind: &'static str,
        text: &str,
        narms: usize,
        natoms: usize,
    ) -> usize {
        let fp = self.fn_path();
        self.g.decs.push(Dec {
            file_idx: self.file_idx,
            rel: self.rel.clone(),
            line: lc.line,
            col: lc.column + 1,
            kind,
            fn_path: fp,
            text: collapse_ws(text).chars().take(200).collect(),
            narms,
            natoms,
        });
        self.g.decs.len() - 1
    }

    /// Inserts `let __mg = guard(D, O);` right after the `{` at byte `brace_end`.
    fn guard_at(&mut self, brace_end: usize, dec: usize, outcome: u32) {
        let dl = self.g.decs[dec].line;
        if self.g.disabled.contains(&format!("{}:{}@guard", self.rel, dl)) {
            self.g.guards_disabled += 1;
            return;
        }
        self.point_stmt(
            brace_end,
            format!(" let __mg = crate::__mut::guard(@@D{}@@, {}); ", dec, outcome),
        );
    }

    /// Wraps an expression body as `{ let __mg = guard(D, O); BODY }`.
    fn guard_wrap(&mut self, body: &Expr, dec: usize, outcome: u32) {
        let dl = self.g.decs[dec].line;
        if self.g.disabled.contains(&format!("{}:{}@guard", self.rel, dl)) {
            self.g.guards_disabled += 1;
            return;
        }
        if let Expr::Block(b) = body {
            if b.label.is_none() {
                let o = self.off(b.block.brace_token.span.open().end());
                self.point_stmt(
                    o,
                    format!(" let __mg = crate::__mut::guard(@@D{}@@, {}); ", dec, outcome),
                );
                return;
            }
        }
        if let Some((s, e, _)) = self.range(body) {
            self.wrap(
                s,
                e,
                format!("{{ let __mg = crate::__mut::guard(@@D{}@@, {}); ", dec, outcome),
                " }".into(),
            );
        }
    }

    /// Records a mutation point over source bytes [s, e). Returns the placeholder text for its base id.
    fn point(
        &mut self,
        s: usize,
        e: usize,
        orig: &str,
        muts: &[(&'static str, String)],
        atom: Option<usize>,
    ) -> Option<String> {
        let (line, col) = self.lc_of(s);
        if self.is_disabled(line, muts) {
            self.g.skipped_disabled += 1;
            return None;
        }
        let (end_line, end_col) = self.lc_of(e);
        let p = Point {
            file_idx: self.file_idx,
            line,
            col,
            end_line,
            end_col,
            seq: self.g.points.len(),
            muts: muts.to_vec(),
            orig: collapse_ws(orig).chars().take(300).collect(),
            fn_path: self.fn_path(),
            krate: self.krate.clone(),
            rel: self.rel.clone(),
            atom,
            atom_dec: if atom.is_some() { self.cur_decision } else { None },
            guards: self.guards.clone(),
        };
        self.g.points.push(p);
        Some(format!("@@P{}@@", self.g.points.len() - 1))
    }

    fn text(&self, s: usize, e: usize) -> String {
        collapse_ws(&self.src[s..e])
    }

    fn wrap(&mut self, s: usize, e: usize, open: String, close: String) {
        self.wrap_l(s, e, layer::MUT_WRAP, open, close);
    }

    fn wrap_l(&mut self, s: usize, e: usize, l: u8, open: String, close: String) {
        let d = self.depth;
        self.ins(s, 0, Kind::Open, (s, e), l, d, open);
        self.ins(e, 0, Kind::Close, (s, e), l, d, close);
    }

    /// A token in [os, os + del) replaced by `text`, inside a wrapper.
    fn mid(&mut self, os: usize, del: usize, text: String) {
        let d = self.depth;
        self.ins(os, del, Kind::Mid, (os, os + del), layer::MUT_SPLIT, d, text);
    }

    fn deeper<F: FnOnce(&mut Self)>(&mut self, f: F) {
        self.depth += 1;
        f(self);
        self.depth -= 1;
    }

    fn atom_point(&mut self, a: &Expr, idx: Option<usize>, ctx: CondCtx) {
        let Some((s, e, _)) = self.range(a) else {
            return visit::visit_expr(self, a);
        };
        let t = self.text(s, e);
        let single = std::mem::replace(&mut self.single, false);
        match ctx {
            CondCtx::While => {
                if let Some(b) = self.point(s, e, &t, &[("while-false", "false".into())], idx) {
                    self.wrap(s, e, format!("crate::__mut::bw({}, (", b), "))".into());
                }
            }
            _ => {
                let neg_name = match ctx {
                    CondCtx::If { has_else: true } if single => "decision-negate",
                    _ => "cond-negate",
                };
                let muts = [
                    ("cond-true", "true".to_string()),
                    ("cond-false", "false".to_string()),
                    (neg_name, format!("!({})", t)),
                ];
                if let Some(b) = self.point(s, e, &t, &muts, idx) {
                    self.wrap(s, e, format!("crate::__mut::b({}, (", b), "))".into());
                }
            }
        }
        self.deeper(|c| {
            c.atom_flag = true;
            c.cond_ctx = CondCtx::None;
            c.visit_expr(a);
        });
    }

    fn dnode(&mut self, e: &Expr, letchain: bool, idx: &mut usize) {
        match e {
            Expr::Binary(b) if matches!(b.op, BinOp::And(_) | BinOp::Or(_)) => {
                let is_and = matches!(b.op, BinOp::And(_));
                let lr = self.range(&*b.left);
                let rr = self.range(&*b.right);
                let opr = self.range(&b.op);
                if !letchain {
                    if let (Some((ls, _, _)), Some((_, re, _)), Some((os, oe, olc))) = (lr, rr, opr)
                    {
                        let t = self.text(ls, re);
                        let alt = if is_and { "||" } else { "&&" };
                        let lt = self.text(ls, os);
                        let rt = self.text(oe, re);
                        if let Some(id) = self.point(
                            os,
                            oe,
                            &t,
                            &[("and-or-swap", format!("{} {} {}", lt, alt, rt))],
                            None,
                        ) {
                            let _ = olc;
                            let cmp = if is_and { "==" } else { "!=" };
                            self.wrap_l(
                                ls,
                                re,
                                layer::MUT_SPLIT,
                                "({ let __l: bool = ".into(),
                                " } })".into(),
                            );
                            self.mid(
                                os,
                                oe - os,
                                format!(
                                    "; if __l {} crate::__mut::is({}) {{ __l }} else {{ ",
                                    cmp, id
                                ),
                            );
                        }
                    }
                }
                self.deeper(|c| {
                    c.dnode(&b.left, letchain, idx);
                    c.dnode(&b.right, letchain, idx);
                });
            }
            Expr::Paren(p) if is_logic(&p.expr) => self.dnode(&p.expr, letchain, idx),
            Expr::Unary(u) if matches!(u.op, UnOp::Not(_)) && is_logic(&u.expr) => {
                self.dnode(&u.expr, letchain, idx)
            }
            Expr::Let(l) => {
                *idx += 1;
                let saved = self.cur_decision.take();
                self.cond_ctx = CondCtx::None;
                self.visit_expr(&l.expr);
                self.cur_decision = saved;
            }
            a => {
                let i = *idx;
                *idx += 1;
                self.atom_point(a, Some(i), CondCtx::None);
            }
        }
    }

    fn count_atoms(e: &Expr) -> usize {
        match e {
            Expr::Binary(b) if matches!(b.op, BinOp::And(_) | BinOp::Or(_)) => {
                Self::count_atoms(&b.left) + Self::count_atoms(&b.right)
            }
            Expr::Paren(p) if is_logic(&p.expr) => Self::count_atoms(&p.expr),
            Expr::Unary(u) if matches!(u.op, UnOp::Not(_)) && is_logic(&u.expr) => {
                Self::count_atoms(&u.expr)
            }
            _ => 1,
        }
    }

    /// &&/|| tree (or let-chain). Returns the decision index.
    fn decision(&mut self, e: &Expr, ctx: CondCtx) -> Option<usize> {
        let Some((s, en, lc)) = self.range(e) else {
            visit::visit_expr(self, e);
            return None;
        };
        let letchain = has_let(e);
        let kind = match (ctx, letchain) {
            (CondCtx::If { .. }, true) => "if-letchain",
            (CondCtx::If { .. }, false) => "if",
            (CondCtx::While, true) => "while-letchain",
            (CondCtx::While, false) => "while",
            (CondCtx::Guard, _) => "guard",
            (CondCtx::None, _) => "expr",
        };
        let t = self.text(s, en);
        let dec = self.new_dec(lc, kind, &t, 0, Self::count_atoms(e));
        let saved = self.cur_decision.replace(dec);
        if let CondCtx::If { .. } = ctx {
            if !letchain {
                if let Some(b) =
                    self.point(s, en, &t, &[("decision-negate", format!("!({})", t))], None)
                {
                    self.wrap(s, en, format!("crate::__mut::n({}, (", b), "))".into());
                }
            }
        }
        if let CondCtx::While = ctx {
            if !letchain {
                if let Some(b) = self.point(s, en, &t, &[("while-false", "false".into())], None) {
                    self.wrap(s, en, format!("crate::__mut::bw({}, (", b), "))".into());
                }
            }
        }
        let mut idx = 0;
        self.deeper(|c| c.dnode(e, letchain, &mut idx));
        self.cur_decision = saved;
        Some(dec)
    }

    /// Container / Option operators on a method call. Returns false if `mc` is not one of them.
    fn container_op(
        &mut self,
        e: &Expr,
        mc: &syn::ExprMethodCall,
        atom_flag: bool,
        stmt_top: bool,
    ) -> bool {
        let name = mc.method.to_string();
        let nargs = mc.args.len();
        let Some((s, en, _)) = self.range(e) else { return false };
        let t = self.text(s, en);
        let recv_t = self.range(&*mc.receiver).map(|(a, b, _)| self.text(a, b)).unwrap_or_default();
        match (name.as_str(), nargs) {
            ("contains", 1) | ("is_empty", 0) if !atom_flag => {
                let op = if name == "contains" {
                    "container-contains-negate"
                } else {
                    "container-is-empty-negate"
                };
                if let Some(id) = self.point(s, en, &t, &[(op, format!("!{}", t))], None) {
                    self.wrap(s, en, format!("crate::__mut::nb({}, (", id), "))".into());
                }
            }
            ("len", 0) => {
                let muts = [
                    ("container-len-plus1", format!("{} + 1", t)),
                    ("container-len-minus1", format!("{}.saturating_sub(1)", t)),
                ];
                if let Some(id) = self.point(s, en, &t, &muts, None) {
                    self.wrap(s, en, format!("crate::__mut::ln({}, (", id), "))".into());
                }
            }
            ("get", 1) | ("get_mut", 1) => {
                if let Some(id) = self.point(s, en, &t, &[("option-get-none", "None".into())], None)
                {
                    self.wrap(s, en, format!("crate::__mut::none({}, (", id), "))".into());
                }
            }
            ("first", 0) | ("last", 0) if simple_receiver(&mc.receiver) => {
                let other = if name == "first" { "last" } else { "first" };
                let alt = format!("{}.{}()", recv_t, other);
                if let Some(id) =
                    self.point(s, en, &t, &[("container-first-last", alt.clone())], None)
                {
                    self.wrap(
                        s,
                        en,
                        format!("crate::__mut::fl({}, (", id),
                        format!("), ({}))", alt),
                    );
                }
            }
            ("iter", 0) => {
                if let Some(id) =
                    self.point(s, en, &t, &[("container-iter-rev", format!("{}.rev()", t))], None)
                {
                    self.wrap(s, en, format!("crate::__mut::it({}, (", id), "))".into());
                }
            }
            ("retain", 1) if matches!(mc.args.first(), Some(Expr::Closure(_))) => {
                let a = mc.args.first().unwrap();
                if let Some((as_, ae, _)) = self.range(a) {
                    let at = self.text(as_, ae);
                    if let Some(id) = self.point(
                        as_,
                        ae,
                        &at,
                        &[("container-retain-negate", format!("negated {}", at))],
                        None,
                    ) {
                        self.wrap(as_, ae, format!("crate::__mut::negp({}, (", id), "))".into());
                    }
                }
            }
            ("unwrap_or", 1) => {
                // UFCS: crate::__mut::MutUnwrapOr::m(RECV, ID, D); only when `.unwrap_or(` is on one line
                let rr = self.range(&*mc.receiver);
                let po = self.off(mc.paren_token.span.open().end());
                if let Some((_, re, _)) = rr {
                    if !self.src[re..po].contains('\n') {
                        let d = self
                            .range(mc.args.first().unwrap())
                            .map(|(a, b, _)| self.text(a, b))
                            .unwrap_or_default();
                        if let Some(id) =
                            self.point(s, en, &t, &[("option-unwrap-or-default", d)], None)
                        {
                            let dd = self.depth;
                            self.ins(
                                s,
                                0,
                                Kind::Open,
                                (s, en),
                                layer::MUT_SPLIT,
                                dd,
                                "crate::__mut::MutUnwrapOr::m(".into(),
                            );
                            self.mid(re, po - re, format!(", {}, ", id));
                        }
                    }
                }
            }
            ("insert", _) | ("remove", _) if !stmt_top => {
                let op = if name == "insert" {
                    "container-insert-absent"
                } else {
                    "container-remove-absent"
                };
                if let Some(id) = self.point(s, en, &t, &[(op, "None / false".into())], None) {
                    self.wrap(s, en, format!("crate::__mut::absent({}, (", id), "))".into());
                }
            }
            _ => return false,
        }
        self.deeper(|c| {
            c.visit_expr(&mc.receiver);
            for a in &mc.args {
                c.visit_expr(a);
            }
        });
        true
    }

    /// matches!(x, Enum::V) with a single unit-variant pattern of a listed enum: the pattern is swapped.
    fn matches_variant(&mut self, e: &Expr, m: &syn::ExprMacro) {
        let Some((s, en, _)) = self.range(e) else { return };
        let t = &self.src[s..en];
        if t.contains('\n') {
            return;
        }
        let parsed = m.mac.parse_body_with(|input: syn::parse::ParseStream| {
            let x: Expr = input.parse()?;
            let _: syn::Token![,] = input.parse()?;
            let p: syn::Path = input.parse()?;
            if !input.is_empty() {
                return Err(input.error("more"));
            }
            Ok((x, p))
        });
        let Ok((x, p)) = parsed else { return };
        let segs: Vec<String> = p.segments.iter().map(|s| s.ident.to_string()).collect();
        let Some((en_name, v, alts)) = variant_alts(&segs) else { return };
        let xt = collapse_ws(&x.to_token_stream().to_string());
        let tt = collapse_ws(t);
        let muts: Vec<(&'static str, String)> = alts
            .iter()
            .map(|a| ("enum-variant", format!("matches!({}, {}::{})", xt, en_name, a)))
            .collect();
        let Some((xs, xe, _)) = self.range(&x) else { return };
        let xsrc = self.src[xs..xe].to_string();
        if let Some(id) = self.point(s, en, &tt, &muts, None) {
            let mut r = format!(
                "{{ let __mv = &({}); match crate::__mut::seli({}, {}) {{ ",
                xsrc,
                id,
                alts.len()
            );
            for (k, a) in alts.iter().enumerate() {
                let _ = write!(r, "{} => matches!(__mv, {}::{}), ", k + 1, en_name, a);
            }
            let _ = write!(r, "_ => matches!(__mv, {}::{}) }} }}", en_name, v);
            let d = self.depth;
            self.ins(s, en - s, Kind::Open, (s, en), layer::MUT_REPLACE, d, r);
        }
    }

    /// Condition of an if / while / match guard. Returns the decision index.
    fn handle_cond(&mut self, cond: &Expr, ctx: CondCtx) -> Option<usize> {
        if is_logic(cond) || has_let(cond) && matches!(cond, Expr::Binary(_)) {
            self.decision(cond, ctx)
        } else if let Expr::Let(l) = cond {
            let lc = self.range(cond).map(|x| x.2);
            let t = self.range(cond).map(|(s, e, _)| self.text(s, e)).unwrap_or_default();
            let dec = lc.map(|lc| {
                let k = if let CondCtx::While = ctx { "while-let" } else { "if-let" };
                self.new_dec(lc, k, &t, 0, 1)
            });
            self.cond_ctx = CondCtx::None;
            self.visit_expr(&l.expr);
            dec
        } else {
            let r = self.range(cond);
            let dec = r.map(|(s, e, lc)| {
                let k = match ctx {
                    CondCtx::While => "while",
                    CondCtx::Guard => "guard",
                    _ => "if",
                };
                let t = self.text(s, e);
                self.new_dec(lc, k, &t, 0, 1)
            });
            let saved = std::mem::replace(&mut self.cur_decision, dec);
            self.single = true;
            self.atom_point(cond, if dec.is_some() { Some(0) } else { None }, ctx);
            self.cur_decision = saved;
            dec
        }
    }
}

impl<'a, 'ast> Visit<'ast> for Ctx<'a> {
    fn visit_expr(&mut self, e: &'ast Expr) {
        let ctx = std::mem::replace(&mut self.cond_ctx, CondCtx::None);
        let atom_flag = std::mem::replace(&mut self.atom_flag, false);
        let stmt_top = std::mem::replace(&mut self.stmt_top, false);
        if !self.active() {
            return visit::visit_expr(self, e);
        }
        if ctx != CondCtx::None {
            self.last_dec = self.handle_cond(e, ctx);
            return;
        }
        if is_logic(e) {
            self.decision(e, CondCtx::None);
            return;
        }
        match e {
            Expr::Binary(b)
                if matches!(
                    b.op,
                    BinOp::Lt(_)
                        | BinOp::Le(_)
                        | BinOp::Gt(_)
                        | BinOp::Ge(_)
                        | BinOp::Eq(_)
                        | BinOp::Ne(_)
                ) =>
            {
                let (code, func, name, alt): (u8, &str, &'static str, &str) = match b.op {
                    BinOp::Lt(_) => (0, "ord", "rel-boundary", "<="),
                    BinOp::Le(_) => (1, "ord", "rel-boundary", "<"),
                    BinOp::Gt(_) => (2, "ord", "rel-boundary", ">="),
                    BinOp::Ge(_) => (3, "ord", "rel-boundary", ">"),
                    BinOp::Eq(_) => (0, "eq", "eq-flip", "!="),
                    _ => (1, "eq", "eq-flip", "=="),
                };
                let skip = func == "eq" && atom_flag;
                let (lr, rr, opr) =
                    (self.range(&*b.left), self.range(&*b.right), self.range(&b.op));
                if let (false, Some((ls, _, _)), Some((_, re, _)), Some((os, oe, _))) =
                    (skip, lr, rr, opr)
                {
                    let t = self.text(ls, re);
                    let lsrc = self.text(ls, os);
                    let rsrc = self.text(oe, re);
                    if let Some(id) = self.point(
                        ls,
                        re,
                        &t,
                        &[(name, format!("{} {} {}", lsrc, alt, rsrc))],
                        None,
                    ) {
                        self.wrap_l(
                            ls,
                            re,
                            layer::MUT_SPLIT,
                            format!("crate::__mut::{}({}, {}, &(", func, id, code),
                            "))".into(),
                        );
                        self.mid(os, oe - os, "), &(".into());
                    }
                }
                self.deeper(|c| {
                    c.visit_expr(&b.left);
                    c.visit_expr(&b.right);
                });
            }
            Expr::Lit(l) => {
                if let syn::Lit::Int(_) = &l.lit {
                    if let Some((s, en, _)) = self.range(e) {
                        let t = self.text(s, en);
                        let muts = [
                            ("const-plus1", format!("{} + 1", t)),
                            ("const-minus1", format!("{} - 1", t)),
                        ];
                        if let Some(id) = self.point(s, en, &t, &muts, None) {
                            self.wrap(s, en, format!("crate::__mut::ob({}, ", id), ")".into());
                        }
                    }
                }
            }
            Expr::Index(ix) => {
                self.visit_expr(&ix.expr);
                let simple = !matches!(
                    &*ix.index,
                    Expr::Lit(_) | Expr::Range(_) | Expr::Reference(_)
                ) && !matches!(&*ix.index, Expr::Paren(p) if matches!(&*p.expr, Expr::Range(_)));
                if simple {
                    if let Some((s, en, _)) = self.range(&*ix.index) {
                        let t = self.text(s, en);
                        let muts = [
                            ("index-plus1", format!("[{} + 1]", t)),
                            ("index-minus1", format!("[{} - 1]", t)),
                        ];
                        if let Some(id) = self.point(s, en, &t, &muts, None) {
                            self.wrap(s, en, format!("crate::__mut::ob({}, (", id), "))".into());
                        }
                    }
                }
                self.deeper(|c| c.visit_expr(&ix.index));
            }
            Expr::Try(t) => {
                if let Some((s, en, _)) = self.range(&*t.expr) {
                    let tx = self.text(s, en);
                    if let Some(id) = self.point(
                        s,
                        en,
                        &format!("{}?", tx),
                        &[("drop-try", format!("{}? with Err replaced by Ok(Default)", tx))],
                        None,
                    ) {
                        self.wrap(s, en, format!("crate::__mut::q({}, (", id), "))".into());
                    }
                }
                self.deeper(|c| c.visit_expr(&t.expr));
            }
            Expr::Call(c) if is_err_call(e) => {
                if let Some((s, en, _)) = self.range(e) {
                    let tx = self.text(s, en);
                    if let Some(id) = self.point(
                        s,
                        en,
                        &tx,
                        &[("err-to-ok", "Ok(Default::default())".into())],
                        None,
                    ) {
                        self.wrap(s, en, format!("crate::__mut::okd({}, (", id), "))".into());
                    }
                }
                self.deeper(|cc| {
                    for a in &c.args {
                        cc.visit_expr(a);
                    }
                });
            }
            Expr::Macro(m) if macro_name(&m.mac) == "vec" => {
                use syn::punctuated::Punctuated;
                let parsed =
                    m.mac.parse_body_with(Punctuated::<Expr, syn::Token![,]>::parse_terminated);
                if let Ok(elems) = parsed {
                    let n = elems.len();
                    if n >= 2 && n <= 16 {
                        if let Some((s, en, _)) = self.range(e) {
                            let tx = self.text(s, en);
                            let muts: Vec<(&'static str, String)> = elems
                                .iter()
                                .enumerate()
                                .map(|(i, el)| {
                                    let et = collapse_ws(&el.to_token_stream().to_string());
                                    (
                                        "vec-remove",
                                        format!("vec![..] without element {} `{}`", i, et),
                                    )
                                })
                                .collect();
                            if let Some(id) = self.point(s, en, &tx, &muts, None) {
                                self.wrap(
                                    s,
                                    en,
                                    format!("crate::__mut::rv({}, {}, ", id, n),
                                    ")".into(),
                                );
                            }
                        }
                    }
                }
            }
            Expr::Return(r) => {
                if let Some(x) = &r.expr {
                    if *self.ret_bool.last().unwrap_or(&false) {
                        self.ret_bool_point(x);
                    } else {
                        self.visit_expr(x);
                    }
                }
            }
            Expr::If(i) => {
                let has_else = i.else_branch.is_some();
                self.cond_ctx = CondCtx::If { has_else };
                self.last_dec = None;
                self.visit_expr(&i.cond);
                let dec = self.last_dec.take();
                if let Some(d) = dec {
                    let o = self.off(i.then_branch.brace_token.span.open().end());
                    self.guard_at(o, d, 1);
                    self.guards.push((d, 1));
                }
                self.visit_block(&i.then_branch);
                if dec.is_some() {
                    self.guards.pop();
                }
                if let Some((_, el)) = &i.else_branch {
                    if let Some(d) = dec {
                        self.guard_wrap(el, d, 0);
                        self.guards.push((d, 0));
                    }
                    self.deeper(|c| c.visit_expr(el));
                    if dec.is_some() {
                        self.guards.pop();
                    }
                }
            }
            Expr::While(w) => {
                self.cond_ctx = CondCtx::While;
                self.last_dec = None;
                self.visit_expr(&w.cond);
                let dec = self.last_dec.take();
                if let Some(d) = dec {
                    let o = self.off(w.body.brace_token.span.open().end());
                    self.guard_at(o, d, 1);
                    self.guards.push((d, 1));
                }
                self.visit_block(&w.body);
                if dec.is_some() {
                    self.guards.pop();
                }
            }
            Expr::Match(m) => {
                self.visit_expr(&m.expr);
                let r = self.range(e);
                let dec = r.map(|(s, _, lc)| {
                    let st =
                        self.range(&*m.expr).map(|(a, b, _)| self.text(a, b)).unwrap_or_default();
                    let _ = s;
                    self.new_dec(lc, "match", &format!("match {}", st), m.arms.len(), 0)
                });
                for (k, arm) in m.arms.iter().enumerate() {
                    let mut gd = None;
                    if let Some((_, g)) = &arm.guard {
                        self.cond_ctx = CondCtx::Guard;
                        self.last_dec = None;
                        self.visit_expr(g);
                        gd = self.last_dec.take();
                    }
                    let d = self.depth;
                    if let Some(dd) = dec {
                        self.guard_wrap(&arm.body, dd, k as u32);
                        self.guards.push((dd, k as u32));
                    }
                    if let Some(g) = gd {
                        self.depth = d + 1;
                        self.guard_wrap(&arm.body, g, 1);
                        self.guards.push((g, 1));
                    }
                    self.depth = d + 2;
                    self.visit_expr(&arm.body);
                    self.depth = d;
                    if gd.is_some() {
                        self.guards.pop();
                    }
                    if dec.is_some() {
                        self.guards.pop();
                    }
                }
            }
            Expr::MethodCall(mc) if self.container_op(e, mc, atom_flag, stmt_top) => {}
            Expr::Call(c) if is_some_call(e) => {
                if let Some((s, en, _)) = self.range(e) {
                    let tx = self.text(s, en);
                    if let Some(id) =
                        self.point(s, en, &tx, &[("option-some-none", "None".into())], None)
                    {
                        self.wrap(s, en, format!("crate::__mut::none({}, (", id), "))".into());
                    }
                }
                self.deeper(|cc| {
                    for a in &c.args {
                        cc.visit_expr(a);
                    }
                });
            }
            Expr::Path(p) if enum_alts(p).is_some() => {
                let (en_name, v, alts) = enum_alts(p).unwrap();
                if let Some((s, en, _)) = self.range(e) {
                    let tx = self.text(s, en);
                    let muts: Vec<(&'static str, String)> = alts
                        .iter()
                        .map(|a| ("enum-variant", format!("{}::{}", en_name, a)))
                        .collect();
                    if let Some(id) = self.point(s, en, &tx, &muts, None) {
                        let mut open =
                            format!("(match crate::__mut::seli({}, {}) {{ ", id, alts.len());
                        for (k, a) in alts.iter().enumerate() {
                            let _ = write!(open, "{} => {}::{}, ", k + 1, en_name, a);
                        }
                        open.push_str("_ => ");
                        let _ = v;
                        self.wrap(s, en, open, " })".into());
                    }
                }
            }
            Expr::Macro(m) if macro_name(&m.mac) == "matches" => {
                self.matches_variant(e, m);
            }
            Expr::Closure(c) => {
                self.ret_bool.push(false);
                self.visit_expr(&c.body);
                self.ret_bool.pop();
            }
            Expr::Let(l) => {
                self.visit_expr(&l.expr);
            }
            _ => visit::visit_expr(self, e),
        }
    }

    fn visit_block(&mut self, b: &'ast syn::Block) {
        if !self.active() {
            return visit::visit_block(self, b);
        }
        for st in &b.stmts {
            match st {
                Stmt::Expr(Expr::Return(r), _) if r.expr.as_deref().map_or(false, is_err_call) => {
                    let call = r.expr.as_deref().unwrap();
                    if let Some((s, en, _)) = self.range(st) {
                        let t = self.text(s, en);
                        if let Some(id) = self.point(
                            s,
                            en,
                            &t,
                            &[("skip-err-return", "statement skipped (fall through)".into())],
                            None,
                        ) {
                            self.wrap(
                                s,
                                en,
                                format!("if !crate::__mut::is({}) {{ ", id),
                                " }".into(),
                            );
                        }
                    }
                    if let Expr::Call(c) = call {
                        self.deeper(|cc| {
                            for a in &c.args {
                                cc.visit_expr(a);
                            }
                        });
                    }
                }
                Stmt::Expr(e, Some(_)) if deletable(e) => {
                    if let Some((s, en, _)) = self.range(st) {
                        let t = self.text(s, en);
                        if let Some(id) = self.point(
                            s,
                            en,
                            &t,
                            &[("delete-stmt", "statement deleted".into())],
                            None,
                        ) {
                            self.wrap(
                                s,
                                en,
                                format!("if !crate::__mut::is({}) {{ ", id),
                                " }".into(),
                            );
                        }
                    }
                    self.deeper(|c| {
                        c.stmt_top = true;
                        c.visit_stmt(st)
                    });
                }
                Stmt::Expr(_, Some(_)) => {
                    self.stmt_top = true;
                    self.visit_stmt(st)
                }
                Stmt::Macro(m)
                    if m.semi_token.is_some()
                        && !SKIP_MACROS.contains(&macro_name(&m.mac).as_str()) =>
                {
                    if let Some((s, en, _)) = self.range(st) {
                        let t = self.text(s, en);
                        if let Some(id) = self.point(
                            s,
                            en,
                            &t,
                            &[("delete-stmt", "statement deleted".into())],
                            None,
                        ) {
                            self.wrap(
                                s,
                                en,
                                format!("if !crate::__mut::is({}) {{ ", id),
                                " }".into(),
                            );
                        }
                    }
                    self.deeper(|c| c.visit_stmt(st));
                }
                _ => self.visit_stmt(st),
            }
        }
    }

    fn visit_local(&mut self, l: &'ast syn::Local) {
        if let Some(init) = &l.init {
            self.visit_expr(&init.expr);
            if let Some((_, el)) = &init.diverge {
                self.visit_expr(el);
            }
        }
    }

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
    fn visit_macro(&mut self, _: &'ast syn::Macro) {}
    fn visit_item_mod(&mut self, m: &'ast syn::ItemMod) {
        let is_test = m
            .attrs
            .iter()
            .any(|a| a.path().is_ident("cfg") && a.to_token_stream().to_string().contains("test"));
        if !is_test {
            self.path.push(m.ident.to_string());
            visit::visit_item_mod(self, m);
            self.path.pop();
        }
    }
    fn visit_item_impl(&mut self, i: &'ast syn::ItemImpl) {
        let ty = type_name(&i.self_ty);
        let seg = match &i.trait_ {
            Some((_, p, _)) => {
                let tr = p.segments.last().map(|s| s.ident.to_string()).unwrap_or_default();
                format!("<impl {} for {}>", tr, ty)
            }
            None => ty,
        };
        self.path.push(seg);
        visit::visit_item_impl(self, i);
        self.path.pop();
    }
    fn visit_item_trait(&mut self, i: &'ast syn::ItemTrait) {
        self.path.push(format!("<trait {}>", i.ident));
        visit::visit_item_trait(self, i);
        self.path.pop();
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
        if f.attrs.iter().any(|a| a.path().is_ident("test")) {
            return;
        }
        self.fn_body(&f.sig, &f.block);
    }
    fn visit_impl_item_fn(&mut self, f: &'ast syn::ImplItemFn) {
        self.fn_body(&f.sig, &f.block);
    }
    fn visit_trait_item_fn(&mut self, f: &'ast syn::TraitItemFn) {
        if let Some(b) = &f.default {
            self.fn_body(&f.sig, b);
        }
    }
}

impl<'a> Ctx<'a> {
    fn fn_body(&mut self, sig: &syn::Signature, block: &syn::Block) {
        let c = sig.constness.is_some() as u32;
        self.in_const += c;
        self.in_fn += 1;
        let parent = match self.fn_stack.last() {
            Some(p) => p.clone(),
            None => self.path.join("::"),
        };
        self.fn_stack.push(format!("{}::{}", parent, sig.ident));
        let rb = matches!(&sig.output, syn::ReturnType::Type(_, t) if t.to_token_stream().to_string() == "bool");
        self.ret_bool.push(rb);
        let saved_guards = std::mem::take(&mut self.guards);
        if rb && self.in_const == 0 {
            if let Some(Stmt::Expr(tail, None)) = block.stmts.last() {
                let n = block.stmts.len();
                let head = syn::Block {
                    brace_token: block.brace_token,
                    stmts: block.stmts[..n - 1].to_vec(),
                };
                self.visit_block(&head);
                if let Expr::Return(_) = tail {
                    self.visit_expr(tail);
                } else {
                    self.ret_bool_point(tail);
                }
            } else {
                self.visit_block(block);
            }
        } else {
            self.visit_block(block);
        }
        self.guards = saved_guards;
        self.ret_bool.pop();
        self.fn_stack.pop();
        self.in_fn -= 1;
        self.in_const -= c;
    }

    fn ret_bool_point(&mut self, x: &Expr) {
        if let Some((s, en, _)) = self.range(x) {
            let t = self.text(s, en);
            let muts = [
                ("ret-negate", format!("!({})", t)),
                ("ret-true", "true".to_string()),
                ("ret-false", "false".to_string()),
            ];
            if let Some(id) = self.point(s, en, &t, &muts, None) {
                self.wrap(s, en, format!("crate::__mut::rb({}, (", id), "))".into());
            }
        }
        self.deeper(|c| c.visit_expr(x));
    }
}

/// Decision ids below this value are MC/DC manifest ids; the rewriter numbers the other decisions
/// (single-atom conditions, `if let`, match) from here.
pub const FIRST_LOCAL_DECISION: u32 = 100001;

/// One mutant of the map.
#[derive(Clone, Debug, PartialEq)]
pub struct Mutant {
    pub id: u32,
    pub point: u32,
    pub op: &'static str,
    pub krate: String,
    pub file: String,
    pub line: usize,
    pub col: usize,
    pub end_line: usize,
    pub end_col: usize,
    pub func: String,
    pub orig: String,
    pub mutated: String,
    /// For a condition mutant: its decision, the decision's line and the atom index.
    pub atom_decision: Option<(u32, usize)>,
    pub atom: Option<usize>,
    /// Static guard chain within the function, outermost first: (decision, outcome, file, line).
    pub guards: Vec<(u32, u32, String, usize)>,
}

/// One decision of the rewriter (superset of the MC/DC manifest decisions in the mutated files).
#[derive(Clone, Debug, PartialEq)]
pub struct MutDecision {
    pub id: u32,
    pub mcdc: bool,
    pub kind: &'static str,
    pub file: String,
    pub line: usize,
    pub col: usize,
    pub func: String,
    pub narms: usize,
    pub natoms: usize,
    pub text: String,
}

/// Result of `mutate_sources`.
pub struct Output {
    pub mutants: Vec<Mutant>,
    pub decisions: Vec<MutDecision>,
    /// Rewritten text of each input file, in input order.
    pub sources: Vec<String>,
    pub points: usize,
    pub points_disabled: usize,
    pub guards_disabled: usize,
    pub manifest_ids_used: usize,
}

fn module_path(rel: &str) -> Vec<String> {
    // vir/src/modes.rs -> [vir, modes]; x/src/lib.rs -> [x]; x/src/a/mod.rs -> [x, a]
    let parts: Vec<&str> = rel.split('/').collect();
    let mut v = vec![parts[0].to_string()];
    for p in parts.iter().skip(2) {
        let p = p.trim_end_matches(".rs");
        if p != "lib" && p != "main" && p != "mod" {
            v.push(p.to_string());
        }
    }
    v
}

/// Rewrites `files` (pairs of path relative to the source/ dir and file text). `manifest` maps
/// (rel file, line, col) to MC/DC decision ids; `disabled` holds disable entries.
pub fn mutate_sources(
    files: &[(String, String)],
    manifest: &HashMap<(String, usize, usize), u32>,
    disabled: &HashSet<String>,
) -> Result<Output, String> {
    mutate_sources_with(files, manifest, disabled, Vec::new())
}

/// `mutate_sources`, also applying to each file the MC/DC edits in `mcdc` (in file order; missing
/// entries mean none), so that the file keeps the MC/DC instrumentation of `mcdc instrument`.
pub fn mutate_sources_with(
    files: &[(String, String)],
    manifest: &HashMap<(String, usize, usize), u32>,
    disabled: &HashSet<String>,
    mut mcdc: Vec<Vec<Insert>>,
) -> Result<Output, String> {
    mcdc.resize_with(files.len(), Vec::new);
    let mut g = Global {
        points: Vec::new(),
        decs: Vec::new(),
        disabled: disabled.clone(),
        skipped_disabled: 0,
        guards_disabled: 0,
    };
    let mut rendered: Vec<Vec<Insert>> = Vec::new();
    for (fi, (rel, src)) in files.iter().enumerate() {
        if src.contains("crate::__mut::") {
            return Err(format!("{} is already mutated", rel));
        }
        let file = syn::parse_file(src).map_err(|e| format!("{}: {}", rel, e))?;
        let mut line_starts = vec![0usize];
        for (b, c) in src.char_indices() {
            if c == '\n' {
                line_starts.push(b + 1);
            }
        }
        let krate = rel.split('/').next().unwrap_or("").to_string();
        let mut ctx = Ctx {
            src,
            line_starts,
            rel: rel.clone(),
            krate,
            file_idx: fi,
            g: &mut g,
            inserts: Vec::new(),
            seq: 0,
            depth: 0,
            in_const: 0,
            in_fn: 0,
            cond_ctx: CondCtx::None,
            atom_flag: false,
            ret_bool: Vec::new(),
            path: module_path(rel),
            fn_stack: Vec::new(),
            guards: Vec::new(),
            cur_decision: None,
            last_dec: None,
            single: false,
            stmt_top: false,
        };
        ctx.visit_file(&file);
        rendered.push(std::mem::take(&mut ctx.inserts));
    }
    // decision ids: manifest id when the start matches, else FIRST_LOCAL_DECISION.. in (file, line, col) order
    let mut dec_ids = vec![0u32; g.decs.len()];
    let mut order: Vec<usize> = (0..g.decs.len()).collect();
    order.sort_by_key(|&k| (g.decs[k].file_idx, g.decs[k].line, g.decs[k].col, k));
    let mut next_dec = FIRST_LOCAL_DECISION;
    let mut used: HashSet<u32> = HashSet::new();
    for &k in &order {
        let d = &g.decs[k];
        let key = (d.rel.clone(), d.line, d.col);
        match manifest.get(&key) {
            Some(&id) if d.kind != "match" && !used.contains(&id) => {
                dec_ids[k] = id;
                used.insert(id);
            }
            _ => {
                dec_ids[k] = next_dec;
                next_dec += 1;
            }
        }
    }
    // mutant ids: (file order, line, col, seq)
    let mut porder: Vec<usize> = (0..g.points.len()).collect();
    porder.sort_by_key(|&k| {
        (g.points[k].file_idx, g.points[k].line, g.points[k].col, g.points[k].seq)
    });
    let mut base = vec![0u32; g.points.len()];
    let mut next = 1u32;
    for &k in &porder {
        base[k] = next;
        next += g.points[k].muts.len() as u32;
    }
    let mut mutants = Vec::new();
    for &k in &porder {
        let p = &g.points[k];
        let guards = p
            .guards
            .iter()
            .map(|(d, o)| (dec_ids[*d], *o, g.decs[*d].rel.clone(), g.decs[*d].line))
            .collect::<Vec<_>>();
        for (i, (op, mutated)) in p.muts.iter().enumerate() {
            mutants.push(Mutant {
                id: base[k] + i as u32,
                point: base[k],
                op,
                krate: p.krate.clone(),
                file: p.rel.clone(),
                line: p.line,
                col: p.col,
                end_line: p.end_line,
                end_col: p.end_col,
                func: p.fn_path.clone(),
                orig: p.orig.clone(),
                mutated: collapse_ws(mutated).chars().take(300).collect(),
                atom_decision: p.atom_dec.map(|d| (dec_ids[d], g.decs[d].line)),
                atom: p.atom,
                guards: guards.clone(),
            });
        }
    }
    let decisions = order
        .iter()
        .map(|&k| {
            let d = &g.decs[k];
            MutDecision {
                id: dec_ids[k],
                mcdc: dec_ids[k] < FIRST_LOCAL_DECISION,
                kind: d.kind,
                file: d.rel.clone(),
                line: d.line,
                col: d.col,
                func: d.fn_path.clone(),
                narms: d.narms,
                natoms: d.natoms,
                text: d.text.clone(),
            }
        })
        .collect();
    let mut sources = Vec::new();
    for (fi, ((rel, src), mut inserts)) in files.iter().zip(rendered).enumerate() {
        for ins in inserts.iter_mut() {
            while let Some(a) = ins.text.find("@@") {
                let b = a + 2 + ins.text[a + 2..].find("@@").unwrap();
                let tag = ins.text[a + 2..b].to_string();
                let v: usize = tag[1..].parse().unwrap();
                let rep = if tag.starts_with('P') { base[v] } else { dec_ids[v] };
                ins.text = format!("{}{}{}", &ins.text[..a], rep, &ins.text[b + 2..]);
            }
        }
        inserts.append(&mut mcdc[fi]);
        let o = crate::edit::render(src, inserts).map_err(|e| format!("{}: {}", rel, e))?;
        sources.push(o);
    }
    Ok(Output {
        mutants,
        decisions,
        sources,
        points: g.points.len(),
        points_disabled: g.skipped_disabled,
        guards_disabled: g.guards_disabled,
        manifest_ids_used: used.len(),
    })
}
