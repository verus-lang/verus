use crate::ast::*;
use air::ast::Span;
use air::printer::macro_push_node;
use air::printer::str_to_node;
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

pub(crate) trait ToNode {
    fn to_node(&self) -> Node;
}

impl<A: ToNode> ToNode for crate::def::Spanned<A> {
    fn to_node(&self) -> Node {
        Node::List(vec![
            Node::Atom("@".to_string()),
            Node::Atom(format!("\"{}\"", self.span.as_string)),
            self.x.to_node(),
        ])
    }
}

impl<A: ToNode> ToNode for Vec<A> {
    fn to_node(&self) -> Node {
        let nodes = self.iter().map(|x| x.to_node()).collect();
        Node::List(nodes)
    }
}

impl<A: ToNode> ToNode for std::sync::Arc<A> {
    fn to_node(&self) -> Node {
        (**self).to_node()
    }
}

impl ToNode for String {
    fn to_node(&self) -> Node {
        Node::Atom(format!("\"{}\"", self))
    }
}

impl<A: ToNode> ToNode for Option<A> {
    fn to_node(&self) -> Node {
        match self {
            Some(v) => v.to_node(),
            None => Node::Atom("None".to_string()),
        }
    }
}

impl<A: ToNode, B: ToNode> ToNode for (A, B) {
    fn to_node(&self) -> Node {
        let (a, b) = self;
        Node::List(vec![Node::Atom("tuple".to_string()), a.to_node(), b.to_node()])
    }
}

impl<A: ToNode, B: ToNode, C: ToNode> ToNode for (A, B, C) {
    fn to_node(&self) -> Node {
        let (a, b, c) = self;
        Node::List(vec![Node::Atom("tuple".to_string()), a.to_node(), b.to_node(), c.to_node()])
    }
}

impl ToNode for bool {
    fn to_node(&self) -> Node {
        Node::Atom(format!("{:?}", self))
    }
}

impl ToNode for u32 {
    fn to_node(&self) -> Node {
        Node::Atom(self.to_string())
    }
}

impl ToNode for char {
    fn to_node(&self) -> Node {
        let a = match self.is_ascii() {
            true => format!("'{}'", self.to_string()),
            false => format!("char<{:x}>", *self as u32),
        };
        Node::Atom(a)
    }
}

impl ToNode for u64 {
    fn to_node(&self) -> Node {
        Node::Atom(self.to_string())
    }
}

impl ToNode for usize {
    fn to_node(&self) -> Node {
        Node::Atom(self.to_string())
    }
}

impl ToNode for num_bigint::BigInt {
    fn to_node(&self) -> Node {
        Node::Atom(self.to_string())
    }
}

impl ToNode for air::ast::TypX {
    fn to_node(&self) -> Node {
        use air::ast::TypX::*;
        match self {
            Bool => Node::Atom("Bool".to_string()),
            Int => Node::Atom("Int".to_string()),
            Lambda => Node::Atom("Lambda".to_string()),
            Named(ident) => Node::List(vec![Node::Atom("Named".to_string()), ident.to_node()]),
            BitVec(size) => Node::List(vec![Node::Atom("BitVec".to_string()), size.to_node()]),
        }
    }
}

impl<A: ToNode> ToNode for SpannedTyped<A> {
    fn to_node(&self) -> Node {
        Node::List(vec![
            Node::Atom("@@".to_string()),
            Node::Atom(format!("\"{}\"", self.span.as_string)),
            self.x.to_node(),
            self.typ.to_node(),
        ])
    }
}

impl<A: ToNode + Clone> ToNode for Binder<A> {
    fn to_node(&self) -> Node {
        Node::List(vec![
            Node::Atom("->".to_string()),
            Node::Atom((**self.name).to_string()),
            self.a.to_node(),
        ])
    }
}

impl ToNode for Quant {
    fn to_node(&self) -> Node {
        let Quant { quant, boxed_params } = self;
        let nodes = vec![Node::Atom(format!("{:?}", quant)), boxed_params.to_node()];
        Node::List(nodes)
    }
}

fn str_node(s: &str) -> Node {
    Node::Atom(format!("\"{}\"", s))
}

fn spanned_node(node: Node, span: &Span) -> Node {
    Node::List(vec![str_to_node("span"), str_node(&span.as_string), node])
}

fn path_to_node(path: &Path) -> Node {
    Node::Atom(crate::def::path_to_string(path).replace("{", "_$LBRACE_").replace("}", "_$RBRACE_"))
}

pub fn write_krate(mut write: impl std::io::Write, vir_crate: &Krate) {
    let mut nw = NodeWriter::new_vir();

    let KrateX { datatypes, functions, traits, module_ids } = &**vir_crate;
    for datatype in datatypes.iter() {
        writeln!(
            &mut write,
            "{}\n",
            nw.node_to_string(&spanned_node(datatype.x.to_node(), &datatype.span))
        )
        .expect("cannot write to vir write");
    }
    for function in functions.iter() {
        writeln!(
            &mut write,
            "{}\n",
            nw.node_to_string(&spanned_node(function.x.to_node(), &function.span))
        )
        .expect("cannot write to vir write");
    }
    for t in traits.iter() {
        let t = nodes!(trait {path_to_node(&t.x.name)});
        writeln!(&mut write, "{}\n", nw.node_to_string(&t)).expect("cannot write to vir write");
    }
    for module_id in module_ids.iter() {
        let module_id_node = nodes!(module_id {path_to_node(module_id)});
        writeln!(&mut write, "{}\n", nw.node_to_string(&module_id_node))
            .expect("cannot write to vir write");
    }
}
