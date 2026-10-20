//! A "succinct" printer for VIR expressions, which prints an expression as a single line
//! of Rust-like syntax, eliding anything too long or too deeply nested with `...`.
//! For example: `foo(bar(1), baz(...))`.
//!
//! This is intended for debugging and logging (e.g., in the resolution_inference CFG logs),
//! not for any precise purpose; the output is not meant to be parseable.

use crate::ast::{
    ArithOp, BinaryOp, CallTarget, Constant, Dt, Expr, ExprX, InequalityOp, Place, PlaceX,
    ReadKind, UnaryOp, VarIdent,
};

/// Maximum nesting depth of the printed expression
const MAX_DEPTH: usize = 4;
/// Maximum length (in chars) of the printed expression; if the expression is longer,
/// we reduce the depth until it fits (or until the depth is 1)
const MAX_LEN: usize = 60;

const ELIDED: &str = "...";

/// Print the expression on one line, eliding deeply nested or long subexpressions
pub fn succinct_expr(e: &Expr) -> String {
    succinct(|depth| expr(e, depth))
}

/// Print the place on one line, eliding deeply nested or long subexpressions
pub fn succinct_place(p: &Place) -> String {
    succinct(|depth| place(p, depth))
}

fn succinct(f: impl Fn(usize) -> String) -> String {
    for depth in (2..=MAX_DEPTH).rev() {
        let s = f(depth);
        if s.chars().count() <= MAX_LEN {
            return s;
        }
    }
    f(1)
}

fn var(x: &VarIdent) -> String {
    (*x.0).clone()
}

fn last_segment(path: &crate::ast::Path) -> String {
    match path.segments.last() {
        Some(s) => (**s).clone(),
        None => ELIDED.to_string(),
    }
}

/// Print the items as a comma-separated list
fn list<A>(items: impl Iterator<Item = A>, f: impl Fn(A) -> String) -> String {
    items.map(f).collect::<Vec<_>>().join(", ")
}

fn constant(c: &Constant) -> String {
    match c {
        Constant::Bool(b) => format!("{b}"),
        Constant::Int(i) => format!("{i}"),
        Constant::Real(r) => r.clone(),
        Constant::StrSlice(s) => format!("{:?}", s),
        Constant::ByteStr(_) => format!("b\"{ELIDED}\""),
        Constant::Char(c) => format!("{:?}", c),
        Constant::Float32(f) => format!("{}", f32::from_bits(*f)),
        Constant::Float64(f) => format!("{}", f64::from_bits(*f)),
    }
}

fn binary_op(op: &BinaryOp) -> Option<&'static str> {
    Some(match op {
        BinaryOp::BoolAndNoSC => "&",
        BinaryOp::BoolOrNoSC => "|",
        BinaryOp::BoolXor => "^",
        BinaryOp::Eq(_) => "==",
        BinaryOp::Ne => "!=",
        BinaryOp::Inequality(InequalityOp::Le) => "<=",
        BinaryOp::Inequality(InequalityOp::Ge) => ">=",
        BinaryOp::Inequality(InequalityOp::Lt) => "<",
        BinaryOp::Inequality(InequalityOp::Gt) => ">",
        BinaryOp::Arith(ArithOp::Add(_)) => "+",
        BinaryOp::Arith(ArithOp::Sub(_)) => "-",
        BinaryOp::Arith(ArithOp::Mul(_)) => "*",
        BinaryOp::Arith(ArithOp::EuclideanDiv(_) | ArithOp::TruncatingDiv(..)) => "/",
        BinaryOp::Arith(ArithOp::EuclideanMod(_) | ArithOp::TruncatingMod(..)) => "%",
        _ => return None,
    })
}

/// Print `e`, where `depth` is the number of levels of nesting we're still allowed to print.
/// Leaves are always printed; anything else at depth 0 is elided.
fn expr(e: &Expr, depth: usize) -> String {
    // Leaves and transparent wrappers, which don't count towards the depth
    match &e.x {
        ExprX::Const(c) => return constant(c),
        ExprX::Var(x) | ExprX::VarAt(x, _) => return var(x),
        ExprX::ConstVar(f, _) | ExprX::StaticVar(f) | ExprX::ExecFnByName(f) => {
            return last_segment(&f.path);
        }
        ExprX::Unary(
            UnaryOp::Clip { .. } | UnaryOp::Trigger(_) | UnaryOp::CoerceMode { .. },
            e1,
        )
        | ExprX::UnaryOpr(_, e1)
        | ExprX::NeverToAny(e1)
        | ExprX::Old(e1)
        | ExprX::EvalAndResolve(e1, _)
        | ExprX::Ghost { expr: e1, .. } => return expr(e1, depth),
        ExprX::ReadPlace(p, rk) => {
            return match rk.preliminary_kind {
                ReadKind::ImmutBor => format!("&{}", place(p, depth)),
                _ => place(p, depth),
            };
        }
        ExprX::ImplicitReborrowOrSpecRead(p, _, _) => return place(p, depth),
        ExprX::Drop(_) => return "drop".to_string(),
        _ => {}
    }
    if depth == 0 {
        return ELIDED.to_string();
    }
    let d = depth - 1;
    match &e.x {
        ExprX::Call { target, args, .. } => {
            let args = list(args.iter(), |a| expr(a, d));
            match target {
                CallTarget::Fun(_, fun, ..) => format!("{}({args})", last_segment(&fun.path)),
                CallTarget::FnSpec(f) => format!("{}({args})", expr(f, d)),
                CallTarget::BuiltinSpecFun(f, ..) => format!("{:?}({args})", f),
                CallTarget::AssumeExternal => format!("{ELIDED}({args})"),
            }
        }
        ExprX::Ctor(dt, variant, binders, tail) => {
            let name = match dt {
                Dt::Path(_) => (**variant).clone(),
                Dt::Tuple(_) => "".to_string(),
            };
            let positional = binders.iter().enumerate().all(|(i, b)| *b.name == format!("{}", i));
            let tail = match tail {
                Some(tail) => format!(", ..{}", place(&tail.place, d)),
                None => "".to_string(),
            };
            if positional && binders.len() == 1 && tail.len() == 0 && name.len() == 0 {
                format!("({},)", expr(&binders[0].a, d))
            } else if positional {
                format!("{name}({}{tail})", list(binders.iter(), |b| expr(&b.a, d)))
            } else {
                let fields = list(binders.iter(), |b| format!("{}: {}", b.name, expr(&b.a, d)));
                format!("{name} {{ {fields}{tail} }}")
            }
        }
        ExprX::Unary(UnaryOp::Not, e1) => format!("!{}", expr(e1, d)),
        ExprX::Unary(op, e1) => format!("{:?}({})", op, expr(e1, d)),
        ExprX::Binary(op, e1, e2) => match binary_op(op) {
            Some(op) => format!("{} {op} {}", expr(e1, d), expr(e2, d)),
            None => format!("{:?}({}, {})", op, expr(e1, d), expr(e2, d)),
        },
        ExprX::Logical(op, e1, e2) => {
            let op = match op {
                crate::ast::LogicalOp::And => "&&",
                crate::ast::LogicalOp::Or => "||",
                crate::ast::LogicalOp::Implies => "==>",
            };
            format!("{} {op} {}", expr(e1, d), expr(e2, d))
        }
        ExprX::ArrayLiteral(es) => format!("[{}]", list(es.iter(), |a| expr(a, d))),
        ExprX::Assign { place: p, rhs, .. } => format!("{} = {}", place(p, d), expr(rhs, d)),
        ExprX::BorrowMut(p) | ExprX::TwoPhaseBorrowMut(p) | ExprX::BorrowMutTracked(p) => {
            format!("&mut {}", place(p, d))
        }
        ExprX::If(c, _, _) => format!("if {} {{{ELIDED}}}", expr(c, d)),
        ExprX::Match(p, _, _) => format!("match {} {{{ELIDED}}}", place(p, d)),
        ExprX::Loop { .. } => format!("loop {{{ELIDED}}}"),
        ExprX::Block(stmts, Some(e1)) if stmts.len() == 0 => format!("{{ {} }}", expr(e1, d)),
        ExprX::Block(..) => format!("{{{ELIDED}}}"),
        ExprX::Closure(..) | ExprX::NonSpecClosure { .. } => format!("|{ELIDED}| {ELIDED}"),
        ExprX::Return(Some(e1)) => format!("return {}", expr(e1, d)),
        ExprX::Return(None) => "return".to_string(),
        ExprX::BreakOrContinue { is_break: true, .. } => "break".to_string(),
        ExprX::BreakOrContinue { is_break: false, .. } => "continue".to_string(),
        _ => ELIDED.to_string(),
    }
}

/// Print `p`, with `depth` as in `expr`.
fn place(p: &Place, depth: usize) -> String {
    match &p.x {
        PlaceX::Local(x) => return var(x),
        PlaceX::Temporary(e) => return expr(e, depth),
        PlaceX::ModeUnwrap(p1, _) | PlaceX::UserDefinedTypInvariantObligation(p1, _) => {
            return place(p1, depth);
        }
        PlaceX::WithExpr(_, p1) => return place(p1, depth),
        _ => {}
    }
    if depth == 0 {
        return ELIDED.to_string();
    }
    let d = depth - 1;
    match &p.x {
        PlaceX::Field(opr, p1) => format!("{}.{}", place(p1, d), opr.field),
        PlaceX::DerefMut(p1) => format!("*{}", place(p1, d)),
        PlaceX::Index(p1, idx, _, _) => format!("{}[{}]", place(p1, d), expr(idx, d)),
        PlaceX::Local(_)
        | PlaceX::Temporary(_)
        | PlaceX::ModeUnwrap(..)
        | PlaceX::UserDefinedTypInvariantObligation(..)
        | PlaceX::WithExpr(..) => unreachable!(),
    }
}
