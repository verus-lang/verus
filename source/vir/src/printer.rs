use crate::ast::*;
use air::ast::Span;
use air::printer::macro_push_node;
use air::printer::{str_to_node, NodeWriter};
use air::{node, nodes, nodes_vec};
use sise::Node;

fn str_node(s: &str) -> Node {
    Node::Atom(format!("\"{}\"", s))
}

pub struct Printer {
    no_span: bool,
    no_type: bool,
    no_function_attribute: bool,
    no_encoding: bool, // omit `box`, `unbox`, `clip`s
    pretty_format: bool,
}

impl Printer {
    pub fn new(
        no_span: bool,
        no_type: bool,
        no_function_attribute: bool,
        no_encoding: bool,
        pretty_format: bool,
    ) -> Printer {
        Printer { no_span, no_type, no_function_attribute, no_encoding, pretty_format }
    }

    fn path_to_node(&self, path: &Path) -> Node {
        Node::Atom(crate::def::path_to_string(path))
    }

    fn spanned_node(&self, node: Node, span: &Span) -> Node {
        if !self.no_span {
            Node::List(vec![str_to_node("span"), str_node(&span.as_string), node])
        } else {
            node
        }
    }

    fn visibility_to_node(&self, visibility: &Visibility) -> Node {
        let Visibility { owning_module, is_private } = visibility;
        let mut nodes = vec![str_to_node("visiblity")];
        if let Some(om) = owning_module {
            nodes.push(str_to_node(":owning_module"));
            nodes.push(self.path_to_node(&om));
        }
        if *is_private {
            nodes.push(str_to_node("+is_private"));
        }
        Node::List(nodes)
    }

    fn bound_to_node(&self, bound: &GenericBound) -> Node {
        match &**bound {
            GenericBoundX::Traits(ts) => {
                Node::List(ts.iter().map(|x| self.path_to_node(x)).collect())
            }
            GenericBoundX::FnSpec(typs, ret) => {
                nodes!(fnspec {self.typs_to_node(typs)} {self.typ_to_node(ret)})
            }
        }
    }

    fn binder_node<A: Clone>(&self, binder: &Binder<A>, f: &impl Fn(&A) -> Node) -> Node {
        Node::List(vec![str_to_node(&binder.name), f(&binder.a)])
    }

    fn binders_node<A: Clone>(&self, binders: &Binders<A>, f: &impl Fn(&A) -> Node) -> Node {
        Node::List(binders.iter().map(|binder| self.binder_node(binder, &f)).collect())
    }

    fn typs_to_node(&self, typs: &Typs) -> Node {
        Node::List(typs.iter().map(|x| self.typ_to_node(x)).collect())
    }

    fn int_range_to_node(&self, int_range: &IntRange) -> Node {
        match int_range {
            IntRange::Int => node!(Int),
            IntRange::Nat => node!(Nat),
            IntRange::U(bits) => nodes!(U {str_to_node(&format!("{}", bits))}),
            IntRange::I(bits) => nodes!(I {str_to_node(&format!("{}", bits))}),
            IntRange::USize => node!(USize),
            IntRange::ISize => node!(ISize),
        }
    }

    fn typ_to_node(&self, typ: &Typ) -> Node {
        if self.no_type {
            return Node::List(vec![]);
        }
        match &**typ {
            TypX::Bool => node!(Bool),
            TypX::Int(range) => nodes!(Int {self.int_range_to_node(range)}),
            TypX::Tuple(typs) => nodes!(Tuple {self.typs_to_node(typs)}),
            TypX::Lambda(typs, ret) => {
                nodes!(Lambda {self.typs_to_node(typs)} {self.typ_to_node(ret)})
            }
            TypX::Datatype(path, typs) => {
                nodes!(Datatype {self.path_to_node(path)} {self.typs_to_node(typs)})
            }
            TypX::Boxed(btyp) => nodes!(Boxed {self.typ_to_node(btyp)}),
            TypX::TypParam(ident) => nodes!(TypParam {str_to_node(ident)}),
            TypX::TypeId => nodes!(TypeId),
            TypX::Air(_air_typ) => nodes!({ str_to_node("AirTyp") }),
        }
    }

    fn atomicity_to_node(&self, atomicity: InvAtomicity) -> Node {
        match atomicity {
            InvAtomicity::Atomic => node!(Atomic),
            InvAtomicity::NonAtomic => node!(NonAtomic),
        }
    }

    fn datatype_to_node(&self, datatype: &DatatypeX) -> Node {
        let DatatypeX { path, visibility, transparency, typ_params, variants, mode, unforgeable } =
            datatype;
        let typ_params_node = Node::List(
            typ_params
                .iter()
                .map(|(ident, bound, positive)| {
                    let mut nodes = vec![str_to_node(ident), self.bound_to_node(bound)];
                    if *positive {
                        nodes.push(str_to_node("+strictly_positive"));
                    }
                    Node::List(nodes)
                })
                .collect(),
        );
        let variants_node = self.binders_node(variants, &|fields| {
            self.binders_node(fields, &|(typ, mode, visibility)| {
                Node::List(vec![
                    self.typ_to_node(typ),
                    Node::Atom(format!("{:?}", mode)),
                    self.visibility_to_node(visibility),
                ])
            })
        });
        let mut nodes = vec![
            str_to_node("datatype"),
            self.path_to_node(path),
            self.visibility_to_node(visibility),
            str_to_node(":transparency"),
            Node::Atom(format!("{:?}", transparency)),
            str_to_node(":typ_params"),
            typ_params_node,
            str_to_node(":variants"),
            variants_node,
            str_to_node(":mode"),
            Node::Atom(format!("{:?}", mode)),
        ];
        if *unforgeable {
            nodes.push(str_to_node("+unforgeable"));
        }
        Node::List(nodes)
    }

    fn fun_to_node(&self, fun: &FunX) -> Node {
        let FunX { path, trait_path } = fun;
        let mut nodes = vec![str_to_node("fun"), self.path_to_node(path)];
        if let Some(tp) = trait_path {
            nodes.push(str_to_node(":trait_path"));
            nodes.push(self.path_to_node(tp));
        }
        Node::List(nodes)
    }

    fn header_expr_to_node(&self, header_expr: &HeaderExprX) -> Node {
        match header_expr {
            HeaderExprX::NoMethodBody => nodes!(no_method_body),
            HeaderExprX::Requires(exprs) => nodes!(requires {self.exprs_to_node(exprs)}),
            HeaderExprX::Ensures(retval, exprs) => {
                let mut nodes = nodes_vec!(ensures);
                if let Some((ident, typ)) = retval {
                    nodes.push(nodes!({str_to_node(ident)} {self.typ_to_node(typ)}));
                }
                nodes.push(self.exprs_to_node(exprs));
                Node::List(nodes)
            }
            HeaderExprX::Recommends(exprs) => nodes!(recommends {self.exprs_to_node(exprs)}),
            HeaderExprX::Invariant(exprs) => nodes!(invariant {self.exprs_to_node(exprs)}),
            HeaderExprX::Decreases(exprs) => nodes!(decreases {self.exprs_to_node(exprs)}),
            HeaderExprX::DecreasesWhen(expr) => nodes!(decreases_when {self.expr_to_node(expr)}),
            HeaderExprX::DecreasesBy(path) => nodes!(decreases_by {self.fun_to_node(path)}),
            HeaderExprX::InvariantOpens(exprs) => {
                nodes!(invariantOpens {self.exprs_to_node(exprs)})
            }
            HeaderExprX::InvariantOpensExcept(exprs) => {
                nodes!(invariantOpensExcept {self.exprs_to_node(exprs)})
            }
            HeaderExprX::Hide(fun) => nodes!(hide {self.fun_to_node(fun)}),
            HeaderExprX::ExtraDependency(fun) => nodes!(extra_dependency {self.fun_to_node(fun)}),
        }
    }

    fn pattern_to_node(&self, pattern: &Pattern) -> Node {
        let node = match &pattern.x {
            PatternX::Wildcard => node!(wildcard),
            PatternX::Var { name, mutable } => {
                let mut nodes = nodes_vec!(var {str_to_node(name)});
                if *mutable {
                    nodes.push(str_to_node("+mutable"));
                }
                Node::List(nodes)
            }
            PatternX::Tuple(patterns) => {
                let mut nodes = nodes_vec!(patterns);
                nodes.extend(patterns.iter().map(|x| self.pattern_to_node(x)));
                Node::List(nodes)
            }
            PatternX::Constructor(path, ident, binders) => {
                nodes!(constructor {self.path_to_node(path)} {str_to_node(ident)} {self.binders_node(binders, &|x| self.pattern_to_node(x))})
            }
        };
        self.spanned_node(node, &pattern.span)
    }

    fn exprs_to_node(&self, exprs: &Exprs) -> Node {
        Node::List(exprs.iter().map(|x| self.expr_to_node(x)).collect())
    }

    fn expr_to_node(&self, expr: &Expr) -> Node {
        let node = match &expr.x {
            ExprX::Const(cnst) if !self.pretty_format => nodes!(
                const {
                    match cnst {
                        Constant::Bool(val) => str_to_node(&format!("{}", val)),
                        Constant::Nat(val) => str_to_node(&format!("{}", val)),
                    }
                }
            ),
            ExprX::Const(cnst) if self.pretty_format => match cnst {
                Constant::Bool(val) => str_to_node(&format!("{}", val)),
                Constant::Nat(val) => str_to_node(&format!("{}", val)),
            },
            ExprX::Var(ident) if !self.pretty_format => nodes!(var {str_to_node(ident)}),
            ExprX::Var(ident) if self.pretty_format => str_to_node(ident),
            ExprX::VarLoc(ident) => nodes!(varloc {str_to_node(ident)}),
            ExprX::VarAt(ident, var_at) => {
                nodes!(varat {str_to_node(ident)} {str_to_node(&format!("{:?}", var_at))})
            }
            ExprX::ConstVar(fun) => nodes!(constvar {self.fun_to_node(fun)}),
            ExprX::Loc(expr) => nodes!(loc {self.expr_to_node(expr)}),
            ExprX::Call(call_target, exprs) => nodes!(call {match call_target {
                CallTarget::Static(fun, typs) => nodes!(static {self.fun_to_node(fun)} {self.typs_to_node(typs)}),
                CallTarget::FnSpec(e) => nodes!(fnspec {self.expr_to_node(e)}),
            }} {self.exprs_to_node(exprs)}),
            ExprX::Tuple(exprs) => nodes!(tuple {self.exprs_to_node(exprs)}),
            ExprX::Ctor(path, ident, binders, expr) => {
                let mut nodes = nodes_vec!(ctor {self.path_to_node(path)} {str_to_node(ident)} {self.binders_node(binders, &|x| self.expr_to_node(x))});
                if let Some(e) = expr {
                    nodes.push(str_to_node(":update"));
                    nodes.push(self.expr_to_node(e));
                }
                Node::List(nodes)
            }
            ExprX::Unary(unary_op, expr) => Node::List({
                let mut nodes = match unary_op {
                    UnaryOp::Not => nodes_vec!(not),
                    UnaryOp::BitNot => nodes_vec!(bitnot),
                    UnaryOp::Trigger(group) => {
                        let mut nodes = nodes_vec!(trigger);
                        if let crate::ast::TriggerAnnotation::Trigger(Some(group)) = group {
                            nodes.push(str_to_node(":group"));
                            nodes.push(str_to_node(&format!("{}", group)));
                        }
                        nodes
                    }
                    UnaryOp::Clip(range) => {
                        if self.no_encoding {
                            vec![]
                        } else {
                            nodes_vec!(clip {self.int_range_to_node(range)})
                        }
                    }
                    UnaryOp::MustBeFinalized => nodes_vec!(MustBeFinalized),
                };
                nodes.push(self.expr_to_node(expr));
                nodes
            }),
            ExprX::UnaryOpr(unary_opr, expr) => Node::List({
                let mut nodes = match unary_opr {
                    UnaryOpr::Box(typ) => {
                        if self.no_encoding {
                            vec![]
                        } else {
                            nodes_vec!(box { self.typ_to_node(typ) })
                        }
                    }
                    UnaryOpr::Unbox(typ) => {
                        if self.no_encoding {
                            vec![]
                        } else {
                            nodes_vec!(unbox {self.typ_to_node(typ)})
                        }
                    }
                    UnaryOpr::HasType(typ) => nodes_vec!(hastype {self.typ_to_node(typ)}),
                    UnaryOpr::IsVariant { datatype, variant } => {
                        nodes_vec!(isvariant {self.path_to_node(datatype)} {str_to_node(variant)})
                    }
                    UnaryOpr::TupleField { tuple_arity, field } => {
                        nodes_vec!(tuplefield {str_to_node(":arity")} {str_to_node(&format!("{}", tuple_arity))} {str_to_node(&format!("{}", field))})
                    }
                    UnaryOpr::Field(FieldOpr { datatype, variant, field }) => {
                        nodes_vec!(field {self.path_to_node(datatype)} {str_to_node(variant)} {str_to_node(field)})
                    }
                };
                nodes.push(self.expr_to_node(expr));
                nodes
            }),
            ExprX::Binary(binary_op, e1, e2) => match binary_op {
                BinaryOp::Eq(mode) if !self.pretty_format => {
                    nodes!(eq {str_to_node(":mode")} {str_to_node(&format!("{:?}", mode))} {self.expr_to_node(e1)} {self.expr_to_node(e2)})
                }
                BinaryOp::Eq(_) if self.pretty_format => {
                    nodes!({self.expr_to_node(e1)} {str_to_node("==")} {self.expr_to_node(e2)})
                }
                BinaryOp::Arith(op, _) if !self.pretty_format => {
                    nodes!({str_to_node(&format!("{:?}", op))} {self.expr_to_node(e1)} {self.expr_to_node(e2)})
                }
                BinaryOp::Arith(op, _) if self.pretty_format => {
                    let aop = match op {
                        ArithOp::Add => "+",
                        ArithOp::Sub => "-",
                        ArithOp::Mul => "*",
                        ArithOp::EuclideanDiv => "/",
                        ArithOp::EuclideanMod => "%",
                    };
                    nodes!({self.expr_to_node(e1)} {str_to_node(aop)} {self.expr_to_node(e2)})
                }
                BinaryOp::Inequality(op) if !self.pretty_format => {
                    nodes!({str_to_node(&format!("{:?}", op))} {self.expr_to_node(e1)} {self.expr_to_node(e2)})
                }
                BinaryOp::Inequality(op) if self.pretty_format => {
                    let aop = match op {
                        InequalityOp::Le => "<=",
                        InequalityOp::Ge => ">=",
                        InequalityOp::Lt => "<",
                        InequalityOp::Gt => ">",
                    };
                    nodes!({self.expr_to_node(e1)} {str_to_node(aop)} {self.expr_to_node(e2)})
                }
                BinaryOp::Bitwise(op) if !self.pretty_format => {
                    nodes!({str_to_node(&format!("{:?}", op))} {self.expr_to_node(e1)} {self.expr_to_node(e2)})
                }
                BinaryOp::Bitwise(op) if self.pretty_format => {
                    let aop = match op {
                        BitwiseOp::BitXor => "bitxor",
                        BitwiseOp::BitAnd => "&",
                        BitwiseOp::BitOr => "bitor",
                        BitwiseOp::Shr => ">>",
                        BitwiseOp::Shl => "<<",
                    };
                    nodes!({self.expr_to_node(e1)} {str_to_node(aop)} {self.expr_to_node(e2)})
                }
                _ if !self.pretty_format => {
                    nodes!({str_to_node(&format!("{:?}", binary_op).to_lowercase())} {self.expr_to_node(e1)} {self.expr_to_node(e2)})
                }
                _ if self.pretty_format => {
                    let aop = match binary_op {
                        BinaryOp::And => "&&",
                        BinaryOp::Or => "or",
                        BinaryOp::Xor => "xor",
                        BinaryOp::Implies => "==>",
                        BinaryOp::Ne => "!=",
                        _ => unreachable!(),
                    };
                    nodes!({self.expr_to_node(e1)} {str_to_node(aop)} {self.expr_to_node(e2)})
                }
                _ => unreachable!(),
            },
            ExprX::Multi(MultiOp::Chained(ops), es) => {
                let ops: Vec<Node> =
                    ops.iter().map(|op| str_to_node(&format!("{:?}", op))).collect();
                let es: Vec<Node> = es.iter().map(|x| self.expr_to_node(x)).collect();
                nodes!(multi {Node::List(ops)} {Node::List(es)})
            }
            ExprX::Quant(quant, binders, expr) => {
                nodes!({str_to_node(&format!("{:?}", quant.quant).to_lowercase())} {self.binders_node(binders, &|x| self.typ_to_node(x))} {self.expr_to_node(expr)})
            }
            ExprX::Closure(binders, expr) => {
                nodes!(closure {self.binders_node(binders, &|x| self.typ_to_node(x))} {self.expr_to_node(expr)})
            }
            ExprX::Choose { params, cond, body } => {
                nodes!(choose {self.binders_node(params, &|x| self.typ_to_node(x))} {self.expr_to_node(cond)} {self.expr_to_node(body)})
            }
            ExprX::WithTriggers { triggers, body } => {
                let ts = Node::List(triggers.iter().map(|x| self.exprs_to_node(x)).collect());
                nodes!(with_triggers {ts} {self.expr_to_node(body)})
            }
            ExprX::Assign { init_not_mut, lhs: e0, rhs: e1 } => {
                let mut nodes = nodes_vec!(assign);
                if *init_not_mut {
                    nodes.push(str_to_node(":init_not_mut"));
                }
                nodes.push(self.expr_to_node(e0));
                nodes.push(self.expr_to_node(e1));
                Node::List(nodes)
            }
            ExprX::Fuel(fun, fuel) => {
                nodes!(fuel {self.fun_to_node(fun)} {str_to_node(&format!("{}", fuel))})
            }
            ExprX::Header(header_expr) => nodes!(header {self.header_expr_to_node(header_expr)}),
            ExprX::Admit => node!(admit),
            ExprX::Forall { vars, require, ensure, proof } => {
                nodes!(forall {self.binders_node(vars, &|x| self.typ_to_node(x))} {str_to_node(":require")} {self.expr_to_node(require)} {str_to_node(":ensure")} {self.expr_to_node(ensure)} {str_to_node(":proof")} {self.expr_to_node(proof)})
            }
            ExprX::AssertQuery { requires, ensures, proof, mode } => {
                nodes!(assertQuery {str_to_node(":requires")} {self.exprs_to_node(requires)} {str_to_node(":ensures")} {self.exprs_to_node(ensures)} {str_to_node(":proof")} {self.expr_to_node(proof)} {str_to_node(":mode")} {str_to_node(&format!("{:?}", mode))})
            }
            ExprX::AssertBV(expr) => nodes!(assertbv {self.expr_to_node(expr)}),
            ExprX::If(e0, e1, e2) => {
                let mut nodes = nodes_vec!(if { self.expr_to_node(e0) } {
                    self.expr_to_node(e1)
                });
                if let Some(els) = e2 {
                    nodes.push(self.expr_to_node(els));
                }
                Node::List(nodes)
            }
            ExprX::Match(expr, arms) => {
                nodes!(match {self.expr_to_node(expr)} {Node::List(arms.iter().map(|arm| {
                let ArmX { pattern, guard, body } = &arm.x;
                let node = nodes!(arm {self.pattern_to_node(pattern)} {self.expr_to_node(guard)} {self.expr_to_node(body)});
                self.spanned_node(node, &arm.span)
            }).collect())})
            }
            ExprX::While { cond, body, invs } => {
                nodes!(while {self.expr_to_node(cond)} {self.expr_to_node(body)} {str_to_node(":invs")} {self.exprs_to_node(invs)})
            }
            ExprX::OpenInvariant(e1, binder, e2, atomicity) => {
                nodes!(openinvariant {self.expr_to_node(e1)} {self.binder_node(binder, &|x| self.typ_to_node(x))} {self.expr_to_node(e2)} {self.atomicity_to_node(*atomicity)})
            }
            ExprX::Return(expr) => {
                let mut nodes = nodes_vec!(return);
                if let Some(e) = expr {
                    nodes.push(self.expr_to_node(e));
                }
                Node::List(nodes)
            }
            ExprX::Ghost { alloc_wrapper, tracked, expr } => {
                let ghost = match (alloc_wrapper, tracked) {
                    (None, false) => "proof",
                    (None, true) => "tracked",
                    (Some(_), false) => "Ghost",
                    (Some(_), true) => "Tracked",
                };
                Node::List(nodes_vec!({str_to_node(ghost)} {self.expr_to_node(expr)}))
            }
            ExprX::Block(stmts, expr) => {
                let mut nodes = nodes_vec!(block {
                Node::List(stmts.iter().map(|stmt| {
                    let node = match &stmt.x {
                        StmtX::Expr(expr) => self.expr_to_node(expr),
                        StmtX::Decl { pattern, mode, init } => {
                            let mut nodes = nodes_vec!(decl {self.pattern_to_node(pattern)} {str_to_node(":mode")} {str_to_node(&format!("{:?}", mode))});
                            if let Some(inite) = init {
                                nodes.push(self.expr_to_node(inite));
                            }
                            Node::List(nodes)
                        }
                    };
                    self.spanned_node(node, &stmt.span)
                }).collect())});
                if let Some(e) = expr {
                    nodes.push(self.expr_to_node(e));
                }
                Node::List(nodes)
            }
            _ => unreachable!(),
        };
        self.spanned_node(node, &expr.span)
    }

    fn function_to_node(&self, function: &FunctionX) -> Node {
        let FunctionX {
            name,
            kind,
            visibility,
            mode,
            fuel,
            typ_bounds,
            params,
            ret,
            require,
            ensure,
            decrease,
            decrease_when,
            decrease_by,
            broadcast_forall: _,
            mask_spec,
            is_const,
            publish,
            attrs,
            body,
            extra_dependencies,
        } = function;
        let typ_bounds_node = Node::List(
            typ_bounds
                .iter()
                .map(|(ident, bound)| {
                    Node::List(vec![str_to_node(ident), self.bound_to_node(bound)])
                })
                .collect(),
        );
        let param_to_node = |param: &Param| {
            let ParamX { name, typ, mode, is_mut } = &param.x;
            let mut nodes = vec![
                str_to_node(name),
                self.typ_to_node(typ),
                str_to_node(":mode"),
                Node::Atom(format!("{:?}", mode)),
            ];
            if *is_mut {
                nodes.push(str_to_node("+is_mut"));
            }
            self.spanned_node(Node::List(nodes), &param.span)
        };
        let params_node = Node::List(params.iter().map(param_to_node).collect());
        let mask_spec_node = nodes!(mask_spec {match mask_spec {
            MaskSpec::InvariantOpens(exprs) => nodes!(InvariantOpens {self.exprs_to_node(exprs)}),
            MaskSpec::InvariantOpensExcept(exprs) => nodes!(InvariantsOpensExcept {self.exprs_to_node(exprs)}),
            MaskSpec::NoSpec => node!(NoSpec),
        }});

        let function_attrs_node = if self.no_function_attribute {
            Node::List(vec![])
        } else {
            let FunctionAttrsX {
                uses_ghost_blocks,
                inline,
                hidden,
                broadcast_forall,
                no_auto_trigger,
                custom_req_err,
                autoview,
                autospec,
                bit_vector,
                atomic,
                integer_ring,
                is_decrease_by,
                check_recommends,
                nonlinear,
                spinoff_prover,
            } = &**attrs;

            let mut nodes = vec![
                str_to_node("attrs"),
                str_to_node(":hidden"),
                Node::List(hidden.iter().map(|f| self.fun_to_node(&**f)).collect()),
            ];
            if *uses_ghost_blocks {
                nodes.push(str_to_node("+uses_ghost_blocks"));
            }
            if *inline {
                nodes.push(str_to_node("+inline"));
            }
            if *broadcast_forall {
                nodes.push(str_to_node("+broadcast_forall"));
            }
            if *no_auto_trigger {
                nodes.push(str_to_node("+no_auto_trigger"));
            }
            if let Some(re) = custom_req_err {
                nodes.push(str_to_node(":custom_req_err"));
                nodes.push(str_node(re));
            }
            if *autoview {
                nodes.push(str_to_node("+autoview"));
            }
            if let Some(f) = autospec {
                nodes.push(str_to_node(":autospec"));
                nodes.push(self.fun_to_node(f));
            }
            if *bit_vector {
                nodes.push(str_to_node("+bit_vector"));
            }
            if *atomic {
                nodes.push(str_to_node("+atomic"));
            }
            if *integer_ring {
                nodes.push(str_to_node("+integer_ring"));
            }
            if *is_decrease_by {
                nodes.push(str_to_node("+is_decrease_by"));
            }
            if *check_recommends {
                nodes.push(str_to_node("+check_recommends"));
            }
            if *nonlinear {
                nodes.push(str_to_node("+nonlinear"));
            }
            if *spinoff_prover {
                nodes.push(str_to_node("+spinoff_prover"));
            }
            Node::List(nodes)
        };
        let extra_dependencies_node = {
            let mut nodes: Vec<Node> = vec![str_to_node("extra_dependencies")];
            nodes.extend(extra_dependencies.iter().map(|ed| self.fun_to_node(ed)));
            Node::List(nodes)
        };
        let mut nodes = vec![
            str_to_node("function"),
            self.fun_to_node(name),
            str_to_node(":kind"),
            (match kind {
                FunctionKind::Static => node!(static),
                FunctionKind::TraitMethodDecl { trait_path } => {
                    node!((decl {self.path_to_node(trait_path)}))
                }
                FunctionKind::TraitMethodImpl {
                    method,
                    trait_path,
                    trait_typ_args,
                    datatype,
                    datatype_typ_args,
                } => {
                    node!((
                        impl
                        {self.fun_to_node(method)}
                        {self.path_to_node(trait_path)}
                        {self.typs_to_node(trait_typ_args)}
                        {self.path_to_node(datatype)}
                        {self.typs_to_node(datatype_typ_args)}
                    ))
                }
            }),
            self.visibility_to_node(visibility),
            str_to_node(":mode"),
            Node::Atom(format!("{:?}", mode)),
            str_to_node(":fuel"),
            Node::Atom(format!("{}", fuel)),
            str_to_node(":typ_bounds"),
            typ_bounds_node,
            str_to_node(":params"),
            params_node,
            str_to_node(":ret"),
            param_to_node(ret),
            str_to_node(":require"),
            self.exprs_to_node(require),
            str_to_node(":ensure"),
            self.exprs_to_node(ensure),
            str_to_node(":decrease"),
            self.exprs_to_node(decrease),
        ];
        if let Some(decrease_when) = &decrease_when {
            nodes.push(str_to_node(":decrease_when"));
            nodes.push(self.expr_to_node(decrease_when));
        }
        if let Some(decrease_by) = &decrease_by {
            nodes.push(str_to_node(":decrease_by"));
            nodes.push(self.fun_to_node(decrease_by));
        }
        nodes.push(mask_spec_node);
        nodes.push(extra_dependencies_node);
        if *is_const {
            nodes.push(str_to_node("+is_const"));
        }
        if let Some(publish) = publish {
            nodes.push(nodes!(publish {Node::Atom(format!("{}", publish))}));
        }
        nodes.push(function_attrs_node);
        if let Some(body) = body {
            nodes.push(str_to_node(":body"));
            nodes.push(self.expr_to_node(body));
        }
        Node::List(nodes)
    }

    pub fn write_krate(&self, mut write: impl std::io::Write, vir_crate: &Krate) {
        let KrateX { datatypes, functions, traits, module_ids } = &**vir_crate;
        let mut nw = NodeWriter::new();
        for datatype in datatypes.iter() {
            writeln!(
                &mut write,
                "{}\n",
                nw.node_to_string_indent(
                    &" ".to_string(),
                    &self.spanned_node(self.datatype_to_node(&datatype.x), &datatype.span)
                )
            )
            .expect("cannot write to vir write");
        }
        for function in functions.iter() {
            writeln!(
                &mut write,
                "{}\n",
                nw.node_to_string_indent(
                    &" ".to_string(),
                    &self.spanned_node(self.function_to_node(&function.x), &function.span)
                )
            )
            .expect("cannot write to vir write");
        }
        for t in traits.iter() {
            let t = nodes!(trait {self.path_to_node(&t.x.name)});
            writeln!(&mut write, "{}\n", nw.node_to_string_indent(&" ".to_string(), &t))
                .expect("cannot write to vir write");
        }
        for module_id in module_ids.iter() {
            let module_id_node = nodes!(module_id {self.path_to_node(module_id)});
            writeln!(
                &mut write,
                "{}\n",
                nw.node_to_string_indent(&" ".to_string(), &module_id_node)
            )
            .expect("cannot write to vir write");
        }
    }
}
