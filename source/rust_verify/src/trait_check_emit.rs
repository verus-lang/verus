use crate::trait_check_ast::*;
use rustc_span::{BytePos, Span};

pub(crate) fn encode_id(kind: IdKind, rename_count: usize, raw_id: &String) -> String {
    match kind {
        IdKind::Trait => format!("T{}_{}", rename_count, raw_id),
        IdKind::Datatype => format!("D{}_{}", rename_count, raw_id),
        IdKind::TypParam => format!("A{}_{}", rename_count, raw_id),
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
    pub(crate) start_of_decl: bool,
    // For each line in buffer, map column in buffer to position in original code
    pub(crate) positions: Vec<(usize, BytePos)>,
}

pub(crate) const INDENT_SIZE: usize = 4;

impl Line {
    pub(crate) fn new(indent: usize, start_of_decl: bool) -> Self {
        Line { text: " ".repeat(indent * INDENT_SIZE), start_of_decl, positions: Vec::new() }
    }
}

fn typ_args_to_string(
    path: Option<&Id>,
    lifetimes: &Vec<Id>,
    args: &Vec<Typ>,
    equality: &Option<(Id, Vec<Id>, Typ)>,
) -> String {
    let mut buf = String::new();
    if let Some(path) = path {
        buf += &path.to_string();
    }
    if (lifetimes.len() + args.len()) > 0 || equality.is_some() {
        buf.push('<');
        for lifetime in lifetimes {
            buf += &lifetime.to_string();
            buf += ", ";
        }
        for arg in args {
            buf += &arg.to_string();
            buf += ", ";
        }
        if let Some((x, x_args, t)) = equality {
            buf += &x.to_string();
            buf += &typ_args_to_string(None, x_args, &vec![], &None);
            buf += " = ";
            buf += &t.to_string();
        }
        buf.push('>');
    }
    buf
}

impl ToString for TypX {
    fn to_string(&self) -> String {
        match self {
            TypX::Primitive(s) => s.clone(),
            TypX::TypParam(id) => id.to_string(),
            TypX::TraitSelf => "Self".to_string(),
            TypX::Tuple(typs) => {
                let mut buf = "(".to_string();
                for typ in typs {
                    buf += &typ.to_string();
                    buf += ", ";
                }
                buf.push(')');
                buf
            }
            TypX::Datatype(path, lifetimes, args) => {
                typ_args_to_string(Some(path), lifetimes, args, &None)
            }
            TypX::Dyn(path, args) => {
                format!("dyn {}", typ_args_to_string(Some(path), &vec![], args, &None))
            }
            TypX::Slice(elem) => {
                format!("[{}]", elem.to_string())
            }
            TypX::StrSlice => "str".to_string(),
            TypX::Projection { self_typ, trait_as_datatype: tr, name, assoc_typ_args } => {
                format!(
                    "<{} as {}>::{}",
                    self_typ.to_string(),
                    tr.to_string(),
                    typ_args_to_string(Some(name), assoc_typ_args, &vec![], &None)
                )
            }
            TypX::PointeeMetadata(t) => {
                format!("<{} as std::ptr::Pointee>::Metadata", t.to_string())
            }
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
        EmitState { indent: 0, lines: vec![Line::new(0, true)] }
    }

    pub(crate) fn get_pos(&self, line: usize, column: usize) -> Option<BytePos> {
        let mut offset: usize = 0;
        let lines = &self.lines;
        let mut neg_ok = true;
        let mut pos_ok = true;
        let found_line = loop {
            // Try to find nearest line with position information
            if offset <= line && neg_ok {
                if lines[line - offset].positions.len() > 0 {
                    break line - offset;
                }
                if lines[line - offset].start_of_decl {
                    // reached boundary of current declaration
                    neg_ok = false;
                }
            } else if line + offset < lines.len() && pos_ok {
                if lines[line + offset].positions.len() > 0 {
                    break line + offset;
                }
                if lines[line + offset].start_of_decl {
                    // reached boundary of current declaration
                    pos_ok = false;
                }
            } else {
                // give up
                return None;
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
            if p < 0 { None } else { Some(BytePos(p as u32)) }
        } else if found_line < line {
            // last pos on found_line is closest
            Some(positions.last().expect("found_line").1)
        } else {
            assert!(found_line > line);
            // first pos on found_line is closest
            Some(positions.first().expect("found_line").1)
        }
    }

    pub(crate) fn get_span(
        &self,
        line1: usize,
        column1: usize,
        line2: usize,
        column2: usize,
    ) -> Option<Span> {
        let pos1 = self.get_pos(line1, column1)?;
        let pos2 = self.get_pos(line2, column2)?;
        Some(Span::with_root_ctxt(pos1, pos2))
    }

    pub(crate) fn newdecl(&mut self) {
        self.lines.push(Line::new(self.indent, true));
    }

    pub(crate) fn newline(&mut self) {
        self.lines.push(Line::new(self.indent, false));
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

    pub(crate) fn begin_span_opt(&mut self, span: Option<Span>) {
        if let Some(span) = span {
            self.begin_span(span);
        }
    }

    pub(crate) fn end_span(&mut self, span: Span) {
        let line = self.lines.last_mut().expect("write buffer");
        let column = line.text.len();
        if !span.is_dummy() {
            line.positions.push((column, span.hi()));
        }
    }

    pub(crate) fn end_span_opt(&mut self, span: Option<Span>) {
        if let Some(span) = span {
            self.end_span(span);
        }
    }
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
    }
    buf
}

fn emit_generic_params(state: &mut EmitState, generics: &Vec<GenericParam>) {
    if generics.len() > 0 {
        state.write("<");
        for gparam in generics.iter() {
            state.write(emit_generic_param(gparam));
            state.write(", ");
        }
        state.write(">");
    }
}

fn emit_generic_bound(bound: &GenericBound, bare: bool) -> Option<String> {
    let mut buf = String::new();
    if !bound.bound_vars.is_empty() {
        buf += "for<";
        for b in bound.bound_vars.iter() {
            buf += &b.to_string();
            buf += ","
        }
        buf += "> ";
    }
    let mut clause = String::new();
    if !bare {
        clause += &bound.typ.to_string();
        clause += ": ";
    }
    match &bound.bound {
        Bound::Sized => {
            if *bound.typ == TypX::TraitSelf {
                buf += &clause;
                buf += "Sized";
            }
        }
        Bound::Trait { trait_path, args, equality } => {
            buf += &clause;
            buf += &typ_args_to_string(Some(trait_path), &vec![], args, equality);
        }
    }
    // We need to ensure that we don't emit empty bounds to avoid triggering
    // https://github.com/rust-lang/rust/issues/148349
    if buf.is_empty() { None } else { Some(buf) }
}

// Return (bare bounds ": U", where bounds "where ...")
pub(crate) fn simplify_assoc_typ_bounds(
    trait_name: &Id,
    assoc_name: &Id,
    bounds: Vec<GenericBound>,
) -> (Vec<GenericBound>, Vec<GenericBound>) {
    // When rustc sees "trait T { type X: U; }",
    // it converts it into "trait T { type X where <Self as T>::X: U; }".
    // However, if we emit "where <Self as T>::X: U" directly,
    // rustc seems to lose track of the bound, as described in this issue:
    // https://github.com/rust-lang/rust/issues/113195
    // Therefore, we need to convert the bound back to the simpler bare "X: U" syntax.
    // (Also note that "type X: for<'a> U<'a>" becomes "type X where for<'a> <Self as T>::X: U<'a>")
    let mut bares: Vec<GenericBound> = Vec::new();
    let mut wheres: Vec<GenericBound> = Vec::new();
    for bound in bounds {
        let is_bare = match &*bound.typ {
            TypX::Projection { self_typ, trait_as_datatype, name, .. } if name == assoc_name => {
                match (&**self_typ, &**trait_as_datatype) {
                    (TypX::TraitSelf, TypX::Datatype(id, _, _)) if id == trait_name => true,
                    _ => false,
                }
            }
            _ => false,
        };
        if is_bare {
            bares.push(bound);
        } else {
            wheres.push(bound);
        }
    }
    (bares, wheres)
}

fn emit_generic_bounds(
    state: &mut EmitState,
    params: &Vec<GenericParam>,
    bounds: &Vec<GenericBound>,
) {
    use std::collections::HashSet;
    let mut printed_where = false;
    let print_where = |state: &mut EmitState, printed_where: &mut bool| {
        if !*printed_where {
            *printed_where = true;
            state.write(" where ");
        }
    };
    let mut sized: HashSet<Id> = HashSet::new();
    for bound in bounds.iter() {
        print_where(state, &mut printed_where);
        emit_generic_bound(bound, false).into_iter().for_each(|b| {
            state.write(b);
            state.write(", ");
        });
        if bound.bound == Bound::Sized {
            if let TypX::TypParam(x) = &*bound.typ {
                sized.insert(x.clone());
            }
        }
    }
    for param in params {
        print_where(state, &mut printed_where);
        if param.const_typ.is_none() && param.name.is_typ_param() && !sized.contains(&param.name) {
            state.write(param.name.to_string());
            state.write(" : ?Sized, ");
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
    }
}

pub(crate) fn emit_trait_decl(state: &mut EmitState, t: &TraitDecl) {
    state.newdecl();
    state.newline();
    state.write("trait ");
    state.write(&t.name.to_string());
    emit_generic_params(state, &t.generic_params);

    // Move the assoc_typs bounds into the top-level generic_bounds,
    // because rustc seems to have overflow issues with bounds directly on associated types.
    // See, for example: https://github.com/rust-lang/rust/issues/87755
    let mut generic_bounds = t.generic_bounds.clone();
    for (a, _, bounds) in &t.assoc_typs {
        let (_bares, wheres) = simplify_assoc_typ_bounds(&t.name, a, bounds.clone());
        generic_bounds.extend(wheres.clone());
    }

    emit_generic_bounds(state, &t.generic_params, &generic_bounds);
    state.write(" {");
    state.push_indent();
    for (a, params, bounds) in &t.assoc_typs {
        let (bares, _wheres) = simplify_assoc_typ_bounds(&t.name, a, bounds.clone());
        state.newline();
        state.write("type ");
        state.write(a.to_string());
        emit_generic_params(state, &params);
        let sized = bares.iter().any(|b| b.bound == Bound::Sized);
        let unsize = if sized { vec![] } else { vec!["?Sized".to_string()] };
        // See comment above about overflow issues
        // if bounds.len() + unsize.len() > 0 {
        if bares.len() + unsize.len() > 0 {
            state.write(" : ");
            let bounds_strs: Vec<_> = bares
                .iter()
                .filter_map(|bound| emit_generic_bound(bound, true))
                .chain(unsize.into_iter())
                .collect();
            state.write(bounds_strs.join("+"));
            // See comment above about overflow issues
            //emit_generic_bounds(state, &vec![], &wheres);
        }
        state.write(";");
    }
    state.newline_unindent();
    state.write("}");
}

pub(crate) fn emit_datatype_decl(state: &mut EmitState, d: &DatatypeDecl) {
    state.newdecl();
    state.newline();
    state.begin_span_opt(d.span);
    let d_keyword = match &*d.datatype {
        Datatype::Struct(..) => "struct ",
    };
    state.write(d_keyword);
    state.write(&d.name.to_string());
    emit_generic_params(state, &d.generic_params);
    let suffix_where = match &*d.datatype {
        Datatype::Struct(Fields::Pos(..)) => true,
    };
    match &*d.datatype {
        Datatype::Struct(fields) => {
            let suffix = if suffix_where { "" } else { ";" };
            emit_fields(state, fields, suffix);
            if suffix_where {
                emit_generic_bounds(state, &d.generic_params, &d.generic_bounds);
                state.write(";");
            }
        }
    }
    state.end_span_opt(d.span);
}

pub(crate) fn emit_trait_impl(state: &mut EmitState, t: &TraitImpl) {
    let TraitImpl {
        span,
        trait_as_datatype,
        self_typ,
        generic_params,
        generic_bounds,
        assoc_typs,
        trait_polarity,
        is_clone,
    } = t;
    state.newdecl();
    state.newline();
    state.begin_span_opt(*span);
    state.write("impl");
    emit_generic_params(state, &generic_params);
    state.write(" ");
    if trait_polarity == &rustc_middle::ty::ImplPolarity::Negative {
        state.write("!");
    }
    state.write(&trait_as_datatype.to_string());
    state.write(" for ");
    state.write(&self_typ.to_string());
    emit_generic_bounds(state, &generic_params, &generic_bounds);
    state.write(" {");
    state.push_indent();
    for (name, params, typ) in assoc_typs {
        state.newline();
        state.write("type ");
        state.write(&name.to_string());
        emit_generic_params(state, params);
        state.write(" = ");
        state.write(&typ.to_string());
        state.write(";");
    }
    if *is_clone {
        state.newline();
        state.write("fn clone(&self) -> Self { panic!() }");
    }
    state.newline_unindent();
    state.write("}");
    state.end_span_opt(*span);
}
