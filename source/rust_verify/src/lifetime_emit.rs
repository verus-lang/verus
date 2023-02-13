use crate::lifetime_ast::*;
use rustc_ast::Mutability;
use rustc_span::{BytePos, Span};

pub(crate) fn encode_id(kind: IdKind, rename_count: usize, raw_id: &String) -> String {
    match kind {
        IdKind::Datatype => format!("D{}_{}", rename_count, raw_id),
        IdKind::Variant => format!("C{}_{}", rename_count, raw_id),
        IdKind::TypParam => format!("A{}_{}", rename_count, raw_id),
        IdKind::Lifetime => format!("'a{}_{}", rename_count, raw_id),
        IdKind::Fun => format!("f{}_{}", rename_count, raw_id),
        IdKind::Local => format!("x{}_{}", rename_count, vir::def::user_local_name(raw_id)),
        IdKind::Builtin => raw_id.clone(),
    }
}

/*
pub(crate) fn encode_raw_id(rename_count: usize, raw_id: &String) -> String {
    format!("x_{}_{}", rename_count, vir::def::user_local_name(raw_id))
}

pub(crate) fn encode_typ_name(rename_count: usize, id: &String) -> String {
    format!("T_{}_{}", rename_count, id)
}
*/

#[derive(Debug)]
pub(crate) struct Line {
    pub(crate) text: String,
    // For each line in buffer, map column in buffer to position in original code
    pub(crate) positions: Vec<(usize, BytePos)>,
}

pub(crate) const INDENT_SIZE: usize = 4;

impl Line {
    pub(crate) fn new(indent: usize) -> Self {
        Line { text: " ".repeat(indent * INDENT_SIZE), positions: Vec::new() }
    }
}

fn lifetime_string(lifetime: &Option<Id>) -> String {
    match lifetime {
        None => "".to_string(),
        Some(id) => id.to_string() + " ",
    }
}

impl ToString for TypX {
    fn to_string(&self) -> String {
        match self {
            TypX::Primitive(s) => s.clone(),
            TypX::TypParam(id) => id.to_string(),
            TypX::Never => "!".to_string(),
            TypX::Ref(t, lifetime, Mutability::Not) => {
                "&".to_string() + &lifetime_string(lifetime) + &t.to_string()
            }
            TypX::Ref(t, lifetime, Mutability::Mut) => {
                "&".to_string() + &lifetime_string(lifetime) + " mut " + &t.to_string()
            }
            TypX::Phantom(t) => format!("PhantomData<{}>", t.to_string()),
            TypX::Slice(t) => format!("[{}]", t.to_string()),
            TypX::Tuple(typs) => {
                let mut buf = "(".to_string();
                for typ in typs {
                    buf += &typ.to_string();
                    buf += ", ";
                }
                buf.push(')');
                buf
            }
            TypX::Datatype(path, args) => {
                let mut buf = path.to_string();
                if args.len() > 0 {
                    buf.push('<');
                    for arg in args {
                        buf += &arg.to_string();
                        buf += ", ";
                    }
                    buf.push('>');
                }
                buf
            }
            TypX::Closure => "_".to_string(),
        }
    }
}

pub(crate) struct EmitState {
    pub(crate) indent: usize,
    // generated Rust code
    pub(crate) lines: Vec<Line>,
}

impl EmitState {
    pub(crate) fn new() -> Self {
        EmitState { indent: 0, lines: vec![Line::new(0)] }
    }

    pub(crate) fn get_pos(&self, line: usize, column: usize) -> BytePos {
        let mut offset: usize = 0;
        let lines = &self.lines;
        let found_line = loop {
            // Try to find nearest line with position information
            if offset <= line {
                if lines[line - offset].positions.len() > 0 {
                    break line - offset;
                }
            } else if line + offset <= lines.len() {
                if lines[line + offset].positions.len() > 0 {
                    break line + offset;
                }
            } else {
                // give up
                return BytePos(0);
            }
            // try again
            offset += 1;
        };
        let found = &lines[found_line];
        let positions = &found.positions;
        if offset == 0 {
            // example: positions = [(10, pos1), (20, pos2)]
            //   0 <= column < 20 ==> use pos1
            //   20 <= column ==> use pos2
            let mut i = 0;
            while i + 1 < positions.len() && positions[i + 1].0 <= column {
                i += 1;
            }
            let (c, pos) = positions[i];
            let p = pos.0 as isize + column as isize - c as isize;
            if p < 0 { BytePos(0) } else { BytePos(p as u32) }
        } else if found_line < line {
            // last pos on found_line is closest
            positions.last().expect("found_line").1
        } else {
            assert!(found_line > line);
            // first pos on found_line is closest
            positions.first().expect("found_line").1
        }
    }

    pub(crate) fn get_span(
        &self,
        line1: usize,
        column1: usize,
        line2: usize,
        column2: usize,
    ) -> Span {
        let pos1 = self.get_pos(line1, column1);
        let pos2 = self.get_pos(line2, column2);
        Span::with_root_ctxt(pos1, pos2)
    }

    pub(crate) fn newline(&mut self) {
        self.lines.push(Line::new(self.indent));
    }

    pub(crate) fn ensure_newline(&mut self) {
        if let Some(last) = self.lines.last() {
            if last.text.trim().len() == 0 {
                return;
            }
        }
        self.newline();
    }

    pub(crate) fn push_indent(&mut self) {
        self.indent += 1;
    }

    /*
    pub(crate) fn newline_indent(&mut self) {
        self.indent += 1;
        self.newline();
    }
    */

    pub(crate) fn newline_unindent(&mut self) {
        assert!(self.indent > 0);
        self.indent -= 1;
        self.newline();
    }

    pub(crate) fn write<S: Into<String>>(&mut self, str: S) {
        self.lines.last_mut().expect("write buffer").text.push_str(&str.into());
    }

    pub(crate) fn writeln<S: Into<String>>(&mut self, str: S) {
        self.write(str);
        self.newline();
    }

    pub(crate) fn begin_span(&mut self, span: Span) {
        let line = self.lines.last_mut().expect("write buffer");
        let column = line.text.len();
        if !span.is_dummy() {
            line.positions.push((column, span.lo()));
        }
    }

    pub(crate) fn end_span(&mut self, span: Span) {
        let line = self.lines.last_mut().expect("write buffer");
        let column = line.text.len();
        if !span.is_dummy() {
            line.positions.push((column, span.hi()));
        }
    }

    pub(crate) fn write_spanned<S: Into<String>>(&mut self, str: S, span: Span) {
        let s = str.into();
        let line = self.lines.last_mut().expect("write buffer");
        let column = line.text.len();
        if !span.is_dummy() {
            line.positions.push((column, span.lo()));
            line.positions.push((column + s.len(), span.hi()));
        }
        line.text.push_str(&s);
    }
}

fn un_mut_pattern(pat: &Pattern) -> Pattern {
    let (span, patx) = &**pat;
    let patx = match patx {
        PatternX::Wildcard => PatternX::Wildcard,
        PatternX::Binding(x, _) => PatternX::Binding(x.clone(), Mutability::Not),
        PatternX::Box(p) => PatternX::Box(un_mut_pattern(p)),
        PatternX::Or(ps) => PatternX::Or(ps.iter().map(un_mut_pattern).collect()),
        PatternX::Tuple(ps) => PatternX::Tuple(ps.iter().map(un_mut_pattern).collect()),
        PatternX::DatatypeTuple(x, y, ps) => {
            PatternX::DatatypeTuple(x.clone(), y.clone(), ps.iter().map(un_mut_pattern).collect())
        }
        PatternX::DatatypeStruct(x, y, ps) => {
            let ps = ps.iter().map(|(z, p)| (z.clone(), un_mut_pattern(p))).collect();
            PatternX::DatatypeStruct(x.clone(), y.clone(), ps)
        }
    };
    Box::new((*span, patx))
}

pub(crate) fn emit_pattern(state: &mut EmitState, pat: &Pattern) {
    let (span, patx) = &**pat;
    state.begin_span(*span);
    match patx {
        PatternX::Wildcard => {
            state.write("_");
        }
        PatternX::Binding(x, m) => {
            if *m == Mutability::Mut {
                state.write("mut ");
            }
            state.write(x.to_string());
        }
        PatternX::Box(p) => {
            state.write("box ");
            emit_pattern(state, p);
        }
        PatternX::Or(ps) => {
            state.write("(");
            for i in 0..ps.len() {
                emit_pattern(state, &ps[i]);
                if i + 1 < ps.len() {
                    state.write(" | ");
                }
            }
            state.write(")");
        }
        PatternX::Tuple(ps) => {
            state.write("(");
            for p in ps {
                emit_pattern(state, p);
                state.write(", ");
            }
            state.write(")");
        }
        PatternX::DatatypeTuple(x, v, ps) => {
            state.write(x.to_string());
            if let Some(v) = v {
                state.write("::");
                state.write(v.to_string());
            }
            state.write("(");
            for p in ps {
                emit_pattern(state, p);
                state.write(", ");
            }
            state.write(")");
        }
        PatternX::DatatypeStruct(x, v, ps) => {
            state.write(x.to_string());
            if let Some(v) = v {
                state.write("::");
                state.write(v.to_string());
            }
            state.write(" { ");
            for (field, p) in ps {
                state.write(field.to_string());
                state.write(": ");
                emit_pattern(state, p);
                state.write(", ");
            }
            state.write(" } ");
        }
    }
    state.end_span(*span);
}

pub(crate) fn emit_exp(state: &mut EmitState, exp: &Exp) {
    let (span, expx) = &**exp;
    match expx {
        ExpX::Block(..) => {}
        _ => {
            state.begin_span(*span);
        }
    }
    match expx {
        ExpX::Panic => state.write("panic!()"),
        ExpX::Var(x) => {
            state.write(x.to_string());
        }
        ExpX::Op(exps, result_typ) => {
            state.write("op::<_, ");
            state.write(result_typ.to_string());
            state.write(">((");
            for e in exps.iter() {
                emit_exp(state, e);
                state.write(", ");
            }
            state.write("))");
        }
        ExpX::Call(target, typ_args, exps) => {
            emit_exp(state, target);
            if typ_args.len() > 0 {
                state.write("::<");
                for typ_arg in typ_args {
                    state.write(typ_arg.to_string());
                    state.write(", ");
                }
                state.write(">");
            }
            state.write("(");
            for e in exps.iter() {
                emit_exp(state, e);
                state.write(", ");
            }
            state.write(")");
        }
        ExpX::BuiltinMethod(self_arg, method) => {
            emit_exp(state, self_arg);
            state.write(format!(".{method}()"));
        }
        ExpX::Tuple(es) => {
            state.write("(");
            for e in es.iter() {
                emit_exp(state, e);
                state.write(", ");
            }
            state.write(")");
        }
        ExpX::DatatypeTuple(x, v, typ_args, es) => {
            state.write(x.to_string());
            if let Some(v) = v {
                state.write("::");
                state.write(v.to_string());
            }
            if typ_args.len() > 0 {
                state.write("::<");
                for typ_arg in typ_args {
                    state.write(typ_arg.to_string());
                    state.write(", ");
                }
                state.write(">");
            }
            state.write("(");
            for e in es {
                emit_exp(state, e);
                state.write(", ");
            }
            state.write(")");
        }
        ExpX::DatatypeStruct(x, v, typ_args, es, spread) => {
            state.write(x.to_string());
            if let Some(v) = v {
                state.write("::");
                state.write(v.to_string());
            }
            if typ_args.len() > 0 {
                state.write("::<");
                for typ_arg in typ_args {
                    state.write(typ_arg.to_string());
                    state.write(", ");
                }
                state.write(">");
            }
            state.write(" { ");
            for (field, e) in es {
                state.write(field.to_string());
                state.write(": ");
                emit_exp(state, e);
                state.write(", ");
            }
            if let Some(spread) = spread {
                state.write(".. ");
                emit_exp(state, spread);
            }
            state.write(" } ");
        }
        ExpX::AddrOf(m, e) => {
            match m {
                Mutability::Not => state.write("&("),
                Mutability::Mut => state.write("&mut("),
            }
            emit_exp(state, e);
            state.write(")");
        }
        ExpX::Deref(e) => {
            state.write("*(");
            emit_exp(state, e);
            state.write(")");
        }
        ExpX::Assign(e1, e2) => {
            state.write("(");
            emit_exp(state, e1);
            state.write(") = (");
            emit_exp(state, e2);
            state.write(")");
        }
        ExpX::Field(e, field) => {
            state.write("(");
            emit_exp(state, e);
            state.write(").");
            state.write(field.to_string());
        }
        ExpX::If(e0, e1, e2) => {
            state.write("if ");
            emit_exp(state, e0);
            state.write(" ");
            emit_exp(state, e1);
            state.write(" else ");
            emit_exp(state, e2);
        }
        ExpX::Match(cond, arms) => {
            state.ensure_newline();
            state.write("match ");
            emit_exp(state, cond);
            state.write(" {");
            state.push_indent();
            for (pat, guard, body) in arms {
                state.newline();
                emit_pattern(state, pat);
                if let Some(guard) = guard {
                    state.write(" if ");
                    emit_exp(state, guard);
                }
                state.write(" => ");
                emit_exp(state, body);
            }
            state.newline_unindent();
            state.write("}");
        }
        ExpX::While(ec, eb, label) => {
            if let Some(label) = label {
                state.write(label.to_string());
                state.write(": ");
            }
            state.write("while ");
            emit_exp(state, ec);
            state.write(" ");
            emit_exp(state, eb);
        }
        ExpX::Loop(e, label) => {
            if let Some(label) = label {
                state.write(label.to_string());
                state.write(": ");
            }
            state.write("loop ");
            emit_exp(state, e);
        }
        ExpX::Break(label) => {
            state.write("break");
            if let Some(label) = label {
                state.write(" ");
                state.write(label.to_string());
            }
        }
        ExpX::Continue(label) => {
            state.write("continue");
            if let Some(label) = label {
                state.write(" ");
                state.write(label.to_string());
            }
        }
        ExpX::Ret(e) => {
            state.write("return");
            if let Some(e) = e {
                state.write(" ");
                emit_exp(state, e);
            }
        }
        ExpX::Closure(capture_by, movability, params, body) => {
            state.write("(");
            if let Some(rustc_ast::Movability::Static) = movability {
                state.write("static ");
            }
            if let rustc_ast::CaptureBy::Value = capture_by {
                state.write("move ");
            }
            state.write("|");
            for (span, x, typ) in params.iter() {
                state.write_spanned(x.to_string(), *span);
                state.write(": ");
                state.write(typ.to_string());
                state.write(",");
            }
            state.write("| ");
            emit_exp(state, body);
            state.write(")");
        }
        ExpX::OpenInvariant(atomicity, inner_pat, arg, pat_typ, body) => {
            state.ensure_newline();
            state.write("{");
            state.push_indent();
            state.newline();
            state.write("let (guard, ");
            emit_pattern(state, inner_pat);
            state.write("): (_, ");
            state.write(pat_typ.to_string());
            state.write(") = ");
            let f = match atomicity {
                vir::ast::InvAtomicity::Atomic => "open_atomic_invariant_begin(",
                vir::ast::InvAtomicity::NonAtomic => "open_local_invariant_begin(",
            };
            state.write(f);
            emit_exp(state, arg);
            state.writeln(");");
            for stm in body {
                state.newline();
                emit_stm(state, stm);
            }
            state.newline();
            state.write("open_invariant_end(guard, ");
            // macro_rules! open_local_invariant introduces "let (guard, mut $iident)"
            // call un_mut_pattern to remove the "mut" so we have a valid expression
            emit_pattern(state, &un_mut_pattern(inner_pat));
            state.write(");");
            state.newline_unindent();
            state.write("}");
        }
        ExpX::ExtraParens(exp) => {
            state.write("(");
            emit_exp(state, exp);
            state.write(")");
        }
        ExpX::Block(stms, exp) => {
            state.ensure_newline();
            state.begin_span(*span);
            state.write("{");
            state.push_indent();
            for stm in stms {
                state.newline();
                emit_stm(state, stm);
            }
            if let Some(e) = exp {
                state.newline();
                emit_exp(state, e);
            }
            state.newline_unindent();
            state.write("}");
        }
    }
    state.end_span(*span);
}

pub(crate) fn emit_stm(state: &mut EmitState, stm: &Stm) {
    let (span, stmx) = &**stm;
    state.begin_span(*span);
    match stmx {
        StmX::Expr(exp) => {
            emit_exp(state, exp);
            state.write(";");
        }
        StmX::Let(pat, typ, init) => {
            state.write("let ");
            emit_pattern(state, pat);
            state.write(": ");
            state.write(typ.to_string());
            if let Some(init) = init {
                state.write(" = ");
                emit_exp(state, init);
            }
            state.write(";");
        }
    }
    state.end_span(*span);
}

fn emit_generic_param(param: &GenericParam) -> String {
    let mut buf = String::new();
    if param.const_typ.is_some() {
        buf += "const ";
    }
    buf += &param.name.to_string();
    if let Some(typ) = &param.const_typ {
        buf += ": ";
        buf += &typ.to_string();
        assert!(param.bounds.len() == 0);
    }
    for i in 0..param.bounds.len() {
        if i == 0 {
            buf += ": ";
        } else {
            buf += " + ";
        }
        match &param.bounds[i] {
            Bound::Copy => {
                buf += "Copy";
            }
            Bound::Id(x) => {
                buf += &x.to_string();
            }
            Bound::Fn(kind, params, ret) => {
                buf += match kind {
                    ClosureKind::Fn => "Fn",
                    ClosureKind::FnMut => "FnMut",
                    ClosureKind::FnOnce => "FnOnce",
                };
                buf += &params.to_string();
                buf += " -> ";
                buf += &ret.to_string();
            }
        }
    }
    buf
}

pub(crate) fn emit_const_decl(state: &mut EmitState, f: &ConstDecl) {
    state.newline();
    state.newline();
    state.begin_span(f.span);
    state.write("const ");
    state.write(f.name.to_string());
    state.write(": ");
    state.write(f.typ.to_string());
    state.write(" = ");
    emit_exp(state, &f.body);
    state.write("; ");
    state.end_span(f.span);
}

pub(crate) fn emit_fun_decl(state: &mut EmitState, f: &FunDecl) {
    state.newline();
    state.newline();
    state.begin_span(f.sig_span);
    state.write("fn ");
    state.write_spanned(f.name.to_string(), f.name_span);
    if f.generics.len() > 0 {
        state.write("<");
        for gparam in f.generics.iter() {
            state.write(emit_generic_param(gparam));
            state.write(", ");
        }
        state.write(">");
    }
    state.write("(");
    state.push_indent();
    for (span, x, typ) in f.params.iter() {
        state.newline();
        if let Some(span) = span {
            state.write_spanned(x.to_string(), *span);
        } else {
            state.write(x.to_string());
        }
        state.write(": ");
        state.write(typ.to_string());
        state.write(",");
    }
    state.newline_unindent();
    state.write(")");
    if let Some((span, ret)) = &f.ret {
        state.write(" -> ");
        if let Some(span) = span {
            state.write_spanned(ret.to_string(), *span);
        } else {
            state.write(ret.to_string());
        }
    }
    state.end_span(f.sig_span);
    match &*f.body {
        (_, ExpX::Block(..)) => {
            emit_exp(state, &f.body);
        }
        _ => {
            panic!("function body should be a block");
        }
    }
}

fn emit_fields(state: &mut EmitState, fields: &Fields, suffix: &str) {
    match fields {
        Fields::Pos(fields) => {
            state.write("(");
            state.push_indent();
            for ty in fields.iter() {
                state.newline();
                state.write(ty.to_string());
                state.write(",");
            }
            state.newline_unindent();
            state.write(")");
            state.write(suffix);
        }
        Fields::Named(fields) => {
            state.write(" {");
            state.push_indent();
            for field in fields {
                state.newline();
                state.write(&field.name.to_string());
                state.write(": ");
                state.write(field.typ.to_string());
                state.write(",");
            }
            state.newline_unindent();
            state.write("}");
        }
    }
}

pub(crate) fn emit_datatype_decl(state: &mut EmitState, d: &DatatypeDecl) {
    state.newline();
    if d.implements_copy {
        state.newline();
        state.write("#[derive(Clone, Copy)]");
    }
    let d_keyword = match &*d.datatype {
        Datatype::Struct(..) => "struct ",
        Datatype::Enum(..) => "enum ",
    };
    state.newline();
    state.write_spanned(d_keyword, d.span);
    state.write(&d.name.to_string());
    if d.generics.len() > 0 {
        state.write("<");
        for gparam in d.generics.iter() {
            state.write(emit_generic_param(gparam));
            state.write(", ");
        }
        state.write(">");
    }
    match &*d.datatype {
        Datatype::Struct(fields) => {
            emit_fields(state, fields, ";");
        }
        Datatype::Enum(variants) => {
            state.write(" {");
            state.push_indent();
            for (x, fields) in variants {
                state.newline();
                state.write(&x.to_string());
                emit_fields(state, fields, "");
                state.write(",");
            }
            state.newline_unindent();
            state.write("}");
        }
    }
}
