use crate::ast::*;
use air::printer::macro_push_node;
use air::{node, nodes};
use sise::Node;

const VIR_BREAK_ON: &[&str] = &["Function"];
const VIR_BREAK_AFTER: &[&str] =
    &["Block", ":variants", ":typ_params", ":typ_bounds", ":params", ":require", ":ensure"];

pub struct NodeWriter<'a> {
    pub break_on: std::collections::HashSet<&'a str>,
    pub break_after: std::collections::HashSet<&'a str>,
}

impl<'a> NodeWriter<'a> {
    pub(crate) fn new_vir() -> Self {
        use std::iter::FromIterator;
        NodeWriter {
            break_on: std::collections::HashSet::from_iter(VIR_BREAK_ON.iter().map(|x| *x)),
            break_after: std::collections::HashSet::from_iter(VIR_BREAK_AFTER.iter().map(|x| *x)),
        }
    }

    pub fn write_node(
        &mut self,
        writer: &mut sise::SpacedStringWriter,
        node: &Node,
        break_len: usize,
        brk: bool,
        brk_next: bool,
    ) {
        use sise::Writer;
        let opts =
            sise::SpacedStringWriterNodeOptions { break_line_len: if brk { 0 } else { break_len } };
        match node {
            Node::Atom(a) => {
                writer.write_atom(a, opts).unwrap();
            }
            Node::List(l) => {
                writer.begin_list(opts).unwrap();
                let mut brk = false;
                let brk_from_next = brk_next;
                let mut brk_next = false;
                for n in l {
                    self.write_node(writer, n, break_len + 1, brk || brk_from_next, brk_next);
                    brk_next = false;
                    brk = false;
                    if let Node::Atom(a) = n {
                        if self.break_on.contains(a.as_str()) {
                            brk = true;
                        }
                        if self.break_after.contains(a.as_str()) {
                            brk_next = true;
                        }
                    }
                }
                writer.end_list(()).unwrap();
            }
        }
    }

    fn clean_up_lines(input: String, _indentation: &str) -> String {
        let lines: Vec<&str> = input.lines().collect();
        let mut result: String = "".to_string();
        let mut i = 0;
        while i < lines.len() {
            let mut line = lines[i].to_owned();
            while i + 1 < lines.len() && lines[i + 1].trim() == ")" {
                line = line + lines[i + 1].trim();
                i += 1;
            }
            result.push_str(&line);
            i += 1;
            if i < lines.len() {
                result.push_str("\n");
            }
        }
        result
    }

    pub fn node_to_string(&mut self, node: &Node) -> String {
        use sise::Writer;
        let indentation = " ";
        let style = sise::SpacedStringWriterStyle { line_break: &("\n".to_string()), indentation };
        let mut result = String::new();
        let mut string_writer = sise::SpacedStringWriter::new(style, &mut result);
        self.write_node(&mut string_writer, &node, 120, false, false);
        string_writer.finish(()).unwrap();
        // Clean up result:
        Self::clean_up_lines(result, indentation)
    }
}

#[derive(Debug)]
pub struct ToDebugSNodeOpts {
    pub no_span: bool,
    pub no_type: bool,
    pub no_fn_details: bool,
    pub no_encoding: bool,
}

pub const COMPACT_TONODEOPTS: ToDebugSNodeOpts =
    ToDebugSNodeOpts { no_span: true, no_type: true, no_fn_details: true, no_encoding: true };

impl Default for ToDebugSNodeOpts {
    fn default() -> Self {
        Self { no_span: false, no_type: false, no_fn_details: false, no_encoding: false }
    }
}

pub(crate) trait ToDebugSNode {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node;
}

impl<A: ToDebugSNode> ToDebugSNode for crate::def::Spanned<A> {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node {
        if opts.no_span {
            self.x.to_node(opts)
        } else {
            Node::List(vec![
                Node::Atom("@".to_string()),
                Node::Atom(format!("\"{}\"", self.span.as_string)),
                self.x.to_node(opts),
            ])
        }
    }
}

impl<A: ToDebugSNode> ToDebugSNode for Vec<A> {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node {
        let nodes = self.iter().map(|x| x.to_node(opts)).collect();
        Node::List(nodes)
    }
}

impl<A: ToDebugSNode> ToDebugSNode for std::sync::Arc<A> {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node {
        (**self).to_node(opts)
    }
}

impl ToDebugSNode for String {
    fn to_node(&self, _opts: &ToDebugSNodeOpts) -> Node {
        Node::Atom(match self.is_ascii() {
            true => format!("\"{}\"", self.replace("\n", "\\n")),
            false => "non_ascii_string".to_string(),
        })
    }
}

impl<A: ToDebugSNode> ToDebugSNode for Option<A> {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node {
        match self {
            Some(v) => v.to_node(opts),
            None => Node::Atom("None".to_string()),
        }
    }
}

impl<A: ToDebugSNode, B: ToDebugSNode> ToDebugSNode for (A, B) {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node {
        let (a, b) = self;
        Node::List(vec![Node::Atom("tuple".to_string()), a.to_node(opts), b.to_node(opts)])
    }
}

impl<A: ToDebugSNode, B: ToDebugSNode, C: ToDebugSNode> ToDebugSNode for (A, B, C) {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node {
        let (a, b, c) = self;
        Node::List(vec![
            Node::Atom("tuple".to_string()),
            a.to_node(opts),
            b.to_node(opts),
            c.to_node(opts),
        ])
    }
}

impl ToDebugSNode for bool {
    fn to_node(&self, _opts: &ToDebugSNodeOpts) -> Node {
        Node::Atom(format!("{:?}", self))
    }
}

impl ToDebugSNode for u32 {
    fn to_node(&self, _opts: &ToDebugSNodeOpts) -> Node {
        Node::Atom(self.to_string())
    }
}

impl ToDebugSNode for char {
    fn to_node(&self, _opts: &ToDebugSNodeOpts) -> Node {
        let a = match self.is_ascii_alphanumeric() {
            true => format!("char<{}>", self.to_string()),
            false => format!("char<{:x}>", *self as u32),
        };
        Node::Atom(a)
    }
}

impl ToDebugSNode for u64 {
    fn to_node(&self, _opts: &ToDebugSNodeOpts) -> Node {
        Node::Atom(self.to_string())
    }
}

impl ToDebugSNode for usize {
    fn to_node(&self, _opts: &ToDebugSNodeOpts) -> Node {
        Node::Atom(self.to_string())
    }
}

impl ToDebugSNode for f32 {
    fn to_node(&self, _opts: &ToDebugSNodeOpts) -> Node {
        Node::Atom(self.to_string())
    }
}

impl ToDebugSNode for num_bigint::BigInt {
    fn to_node(&self, _opts: &ToDebugSNodeOpts) -> Node {
        Node::Atom(self.to_string())
    }
}

impl ToDebugSNode for air::ast::TypX {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node {
        use air::ast::TypX;
        match self {
            TypX::Bool => Node::Atom("Bool".to_string()),
            TypX::Int => Node::Atom("Int".to_string()),
            TypX::Fun => Node::Atom("Fun".to_string()),
            TypX::Named(ident) => {
                Node::List(vec![Node::Atom("Named".to_string()), ident.to_node(opts)])
            }
            TypX::BitVec(size) => {
                Node::List(vec![Node::Atom("BitVec".to_string()), size.to_node(opts)])
            }
        }
    }
}

impl<A: ToDebugSNode> ToDebugSNode for SpannedTyped<A> {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node {
        if opts.no_span && opts.no_type {
            self.x.to_node(opts)
        } else {
            let mut v = vec![Node::Atom("@@".to_string())];
            if !opts.no_span {
                v.push(Node::Atom(format!("\"{}\"", self.span.as_string)));
            }
            v.push(self.x.to_node(opts));
            if !opts.no_type {
                v.push(self.typ.to_node(opts));
            }
            Node::List(v)
        }
    }
}

impl<A: ToDebugSNode + Clone> ToDebugSNode for Binder<A> {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node {
        Node::List(vec![
            Node::Atom("->".to_string()),
            Node::Atom((**self.name).to_string()),
            self.a.to_node(opts),
        ])
    }
}

impl<A: ToDebugSNode + Clone> ToDebugSNode for VarBinder<A> {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node {
        Node::List(vec![
            Node::Atom("->".to_string()),
            Node::Atom((&self.name).into()),
            self.a.to_node(opts),
        ])
    }
}

impl ToDebugSNode for Quant {
    fn to_node(&self, _opts: &ToDebugSNodeOpts) -> Node {
        let Quant { quant } = self;
        let nodes = vec![Node::Atom(format!("{:?}", quant))];
        Node::List(nodes)
    }
}

impl ToDebugSNode for Mode {
    fn to_node(&self, _opts: &ToDebugSNodeOpts) -> Node {
        Node::Atom(format!("{:?}", self))
    }
}

impl ToDebugSNode for FunctionX {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node {
        if opts.no_fn_details {
            nodes!(
                Function
                {self.name.to_node(opts)}
                {Node::Atom(":mode".to_string())}
                {self.mode.to_node(opts)}
                {Node::Atom(":typ_bounds".to_string())}
                {self.typ_bounds.to_node(opts)}
                {Node::Atom(":params".to_string())}
                {self.params.to_node(opts)}
                {Node::Atom(":ret".to_string())}
                {self.ret.to_node(opts)}
                {Node::Atom(":require".to_string())}
                {self.require.to_node(opts)}
                {Node::Atom(":ensure".to_string())}
                {self.ensure.to_node(opts)}
                {Node::Atom(":body".to_string())}
                {self.body.to_node(opts)}
            )
        } else {
            self.to_node_inner(opts)
        }
    }
}

impl ToDebugSNode for ExprX {
    fn to_node(&self, opts: &ToDebugSNodeOpts) -> Node {
        if opts.no_encoding {
            match self {
                ExprX::Unary(UnaryOp::Clip { .. }, inner) => inner.to_node(opts),
                ExprX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner) => {
                    inner.to_node(opts)
                }
                _ => self.to_node_inner(opts),
            }
        } else {
            self.to_node_inner(opts)
        }
    }
}

fn path_to_node(path: &Path) -> Node {
    Node::Atom(format!(
        "\"{}\"",
        crate::def::path_to_string(path).replace("{", "_$LBRACE_").replace("}", "_$RBRACE_")
    ))
}

impl ToDebugSNode for Path {
    fn to_node(&self, _opts: &ToDebugSNodeOpts) -> Node {
        path_to_node(self)
    }
}

pub fn write_krate(mut write: impl std::io::Write, vir_crate: &Krate, opts: &ToDebugSNodeOpts) {
    let mut nw = NodeWriter::new_vir();

    let KrateX {
        datatypes,
        functions,
        reveal_groups,
        traits,
        trait_impls,
        assoc_type_impls,
        modules,
        external_fns,
        external_types,
        path_as_rust_names: _,
        arch,
    } = &**vir_crate;
    for datatype in datatypes.iter() {
        if opts.no_span {
            writeln!(&mut write, ";; {}", &datatype.span.as_string)
                .expect("cannot write to vir write");
        }
        writeln!(&mut write, "{}\n", nw.node_to_string(&datatype.to_node(opts)))
            .expect("cannot write to vir write");
    }
    for function in functions.iter() {
        if opts.no_span {
            writeln!(&mut write, ";; {}", &function.span.as_string)
                .expect("cannot write to vir write");
        }
        writeln!(&mut write, "{}\n", nw.node_to_string(&function.to_node(opts)))
            .expect("cannot write to vir write");
    }
    for group in reveal_groups.iter() {
        let group_id_node = nodes!(group_id {path_to_node(&group.x.name.path)});
        writeln!(&mut write, "{}\n", nw.node_to_string(&group_id_node))
            .expect("cannot write to vir write");
    }
    for t in traits.iter() {
        let t = nodes!(trait {path_to_node(&t.x.name)});
        writeln!(&mut write, "{}\n", nw.node_to_string(&t)).expect("cannot write to vir write");
    }
    for t in trait_impls.iter() {
        let t = nodes!(trait_impl {path_to_node(&t.x.impl_path)} {path_to_node(&t.x.trait_path)});
        writeln!(&mut write, "{}\n", nw.node_to_string(&t)).expect("cannot write to vir write");
    }
    for assoc in assoc_type_impls.iter() {
        if opts.no_span {
            writeln!(&mut write, ";; {}", &assoc.span.as_string)
                .expect("cannot write to vir write");
        }
        writeln!(&mut write, "{}\n", nw.node_to_string(&assoc.to_node(opts)))
            .expect("cannot write to vir write");
    }
    for module in modules.iter() {
        let module_id_node = nodes!(module_id {path_to_node(&module.x.path)});
        writeln!(&mut write, "{}\n", nw.node_to_string(&module_id_node))
            .expect("cannot write to vir write");
    }
    for external_fn in external_fns.iter() {
        let external_fn_node = nodes!(external_fn {external_fn.to_node(opts)});
        writeln!(&mut write, "{}\n", nw.node_to_string(&external_fn_node))
            .expect("cannot write to vir write");
    }
    for external_type in external_types.iter() {
        let external_type_node = nodes!(external_type {path_to_node(external_type)});
        writeln!(&mut write, "{}\n", nw.node_to_string(&external_type_node))
            .expect("cannot write to vir write");
    }
    let arch_nodes = nodes!(arch_word_bits {arch.word_bits.to_node(opts)});
    writeln!(&mut write, "{}\n", nw.node_to_string(&arch_nodes))
        .expect("cannot write to vir write");
}
