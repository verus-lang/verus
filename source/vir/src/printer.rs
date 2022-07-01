use crate::ast::*;
use air::ast::Span;
use air::printer::macro_push_node;
use air::printer::{str_to_node, NodeWriter};
use air::{node, nodes, nodes_vec};
use sise::Node;

fn str_node(s: &str) -> Node {
    Node::Atom(format!("\"{}\"", s))
}

fn spanned_node(node: Node, span: &Span) -> Node {
    Node::List(vec![str_to_node("span"), str_node(&span.as_string), node])
}

fn path_to_node(path: &Path) -> Node {
    Node::Atom(crate::def::path_to_string(path))
}

fn visibility_to_node(visibility: &Visibility) -> Node {
    let Visibility { owning_module, is_private } = visibility;
    let mut nodes = vec![str_to_node("visiblity")];
    if let Some(om) = owning_module {
        nodes.push(str_to_node(":owning_module"));
        nodes.push(path_to_node(&om));
    }
    if *is_private {
        nodes.push(str_to_node("+is_private"));
    }
    Node::List(nodes)
}

fn bound_to_node(bound: &GenericBound) -> Node {
    match &**bound {
        GenericBoundX::Traits(ts) => Node::List(ts.iter().map(path_to_node).collect()),
        GenericBoundX::FnSpec(typs, ret) => {
            nodes!(fnspec {typs_to_node(typs)} {typ_to_node(ret)})
        }
    }
}

fn binder_node<A: Clone>(binder: &Binder<A>, f: &impl Fn(&A) -> Node) -> Node {
    Node::List(vec![str_to_node(&binder.name), f(&binder.a)])
}

fn binders_node<A: Clone>(binders: &Binders<A>, f: &impl Fn(&A) -> Node) -> Node {
    Node::List(binders.iter().map(|binder| binder_node(binder, &f)).collect())
}

fn typs_to_node(typs: &Typs) -> Node {
    Node::List(typs.iter().map(typ_to_node).collect())
}

fn int_range_to_node(int_range: &IntRange) -> Node {
    match int_range {
        IntRange::Int => node!(Int),
        IntRange::Nat => node!(Nat),
        IntRange::U(bits) => nodes!(U {str_to_node(&format!("{}", bits))}),
        IntRange::I(bits) => nodes!(I {str_to_node(&format!("{}", bits))}),
        IntRange::USize => node!(USize),
        IntRange::ISize => node!(ISize),
    }
}

fn typ_to_node(typ: &Typ) -> Node {
    match &**typ {
        TypX::Bool => node!(Bool),
        TypX::Int(range) => nodes!(Int {int_range_to_node(range)}),
        TypX::Tuple(typs) => nodes!(Tuple {typs_to_node(typs)}),
        TypX::Lambda(typs, ret) => nodes!(Lambda {typs_to_node(typs)} {typ_to_node(ret)}),
        TypX::Datatype(path, typs) => nodes!(Datatype {path_to_node(path)} {typs_to_node(typs)}),
        TypX::Boxed(btyp) => nodes!(Boxed {typ_to_node(btyp)}),
        TypX::TypParam(ident) => nodes!(TypParam {str_to_node(ident)}),
        TypX::TypeId => nodes!(TypeId),
        TypX::Air(_air_typ) => nodes!({ str_to_node("AirTyp") }),
    }
}

fn atomicity_to_node(atomicity: InvAtomicity) -> Node {
    match atomicity {
        InvAtomicity::Atomic => node!(Atomic),
        InvAtomicity::NonAtomic => node!(NonAtomic),
    }
}

fn datatype_to_node(datatype: &DatatypeX) -> Node {
    let DatatypeX { path, visibility, transparency, typ_params, variants, mode, unforgeable } =
        datatype;
    let typ_params_node = Node::List(
        typ_params
            .iter()
            .map(|(ident, bound, positive)| {
                let mut nodes = vec![str_to_node(ident), bound_to_node(bound)];
                if *positive {
                    nodes.push(str_to_node("+strictly_positive"));
                }
                Node::List(nodes)
            })
            .collect(),
    );
    let variants_node = binders_node(variants, &|fields| {
        binders_node(fields, &|(typ, mode, visibility)| {
            Node::List(vec![
                typ_to_node(typ),
                Node::Atom(format!("{:?}", mode)),
                visibility_to_node(visibility),
            ])
        })
    });
    let mut nodes = vec![
        str_to_node("datatype"),
        path_to_node(path),
        visibility_to_node(visibility),
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

fn fun_to_node(fun: &FunX) -> Node {
    let FunX { path, trait_path } = fun;
    let mut nodes = vec![str_to_node("fun"), path_to_node(path)];
    if let Some(tp) = trait_path {
        nodes.push(str_to_node(":trait_path"));
        nodes.push(path_to_node(tp));
    }
    Node::List(nodes)
}

fn header_expr_to_node(header_expr: &HeaderExprX) -> Node {
    match header_expr {
        HeaderExprX::NoMethodBody => nodes!(no_method_body),
        HeaderExprX::Requires(exprs) => nodes!(requires {exprs_to_node(exprs)}),
        HeaderExprX::Ensures(retval, exprs) => {
            let mut nodes = nodes_vec!(ensures);
            if let Some((ident, typ)) = retval {
                nodes.push(nodes!({str_to_node(ident)} {typ_to_node(typ)}));
            }
            nodes.push(exprs_to_node(exprs));
            Node::List(nodes)
        }
        HeaderExprX::Recommends(exprs) => nodes!(recommends {exprs_to_node(exprs)}),
        HeaderExprX::Invariant(exprs) => nodes!(invariant {exprs_to_node(exprs)}),
        HeaderExprX::Decreases(exprs) => nodes!(decreases {exprs_to_node(exprs)}),
        HeaderExprX::DecreasesWhen(expr) => nodes!(decreases_when {expr_to_node(expr)}),
        HeaderExprX::DecreasesBy(path) => nodes!(decreases_by {fun_to_node(path)}),
        HeaderExprX::InvariantOpens(exprs) => nodes!(invariantOpens {exprs_to_node(exprs)}),
        HeaderExprX::InvariantOpensExcept(exprs) => {
            nodes!(invariantOpensExcept {exprs_to_node(exprs)})
        }
        HeaderExprX::Hide(fun) => nodes!(hide {fun_to_node(fun)}),
        HeaderExprX::ExtraDependency(fun) => nodes!(extra_dependency {fun_to_node(fun)}),
    }
}

fn pattern_to_node(pattern: &Pattern) -> Node {
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
            nodes.extend(patterns.iter().map(pattern_to_node));
            Node::List(nodes)
        }
        PatternX::Constructor(path, ident, binders) => {
            nodes!(constructor {path_to_node(path)} {str_to_node(ident)} {binders_node(binders, &pattern_to_node)})
        }
    };
    spanned_node(node, &pattern.span)
}

fn exprs_to_node(exprs: &Exprs) -> Node {
    Node::List(exprs.iter().map(expr_to_node).collect())
}

fn expr_to_node(expr: &Expr) -> Node {
    let node = match &expr.x {
        ExprX::Const(cnst) => nodes!(
            const {
                match cnst {
                    Constant::Bool(val) => str_to_node(&format!("{}", val)),
                    Constant::Nat(val) => str_to_node(&format!("{}", val)),
                }
            }
        ),
        ExprX::Var(ident) => nodes!(var {str_to_node(ident)}),
        ExprX::VarLoc(ident) => nodes!(varloc {str_to_node(ident)}),
        ExprX::VarAt(ident, var_at) => {
            nodes!(varat {str_to_node(ident)} {str_to_node(&format!("{:?}", var_at))})
        }
        ExprX::ConstVar(fun) => nodes!(constvar {fun_to_node(fun)}),
        ExprX::Loc(expr) => nodes!(loc {expr_to_node(expr)}),
        ExprX::Call(call_target, exprs) => nodes!(call {match call_target {
            CallTarget::Static(fun, typs) => nodes!(static {fun_to_node(fun)} {typs_to_node(typs)}),
            CallTarget::FnSpec(e) => nodes!(fnspec {expr_to_node(e)}),
        }} {exprs_to_node(exprs)}),
        ExprX::Tuple(exprs) => nodes!(tuple {exprs_to_node(exprs)}),
        ExprX::Ctor(path, ident, binders, expr) => {
            let mut nodes = nodes_vec!(ctor {path_to_node(path)} {str_to_node(ident)} {binders_node(binders, &expr_to_node)});
            if let Some(e) = expr {
                nodes.push(str_to_node(":update"));
                nodes.push(expr_to_node(e));
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
                UnaryOp::Clip(range) => nodes_vec!(clip {int_range_to_node(range)}),
            };
            nodes.push(expr_to_node(expr));
            nodes
        }),
        ExprX::UnaryOpr(unary_opr, expr) => Node::List({
            let mut nodes = match unary_opr {
                UnaryOpr::Box(typ) => nodes_vec!(box { typ_to_node(typ) }),
                UnaryOpr::Unbox(typ) => nodes_vec!(unbox {typ_to_node(typ)}),
                UnaryOpr::HasType(typ) => nodes_vec!(hastype {typ_to_node(typ)}),
                UnaryOpr::IsVariant { datatype, variant } => {
                    nodes_vec!(isvariant {path_to_node(datatype)} {str_to_node(variant)})
                }
                UnaryOpr::TupleField { tuple_arity, field } => {
                    nodes_vec!(tuplefield {str_to_node(":arity")} {str_to_node(&format!("{}", tuple_arity))} {str_to_node(&format!("{}", field))})
                }
                UnaryOpr::Field(FieldOpr { datatype, variant, field }) => {
                    nodes_vec!(field {path_to_node(datatype)} {str_to_node(variant)} {str_to_node(field)})
                }
            };
            nodes.push(expr_to_node(expr));
            nodes
        }),
        ExprX::Binary(binary_op, e1, e2) => match binary_op {
            BinaryOp::Eq(mode) => {
                nodes!(eq {str_to_node(":mode")} {str_to_node(&format!("{:?}", mode))} {expr_to_node(e1)} {expr_to_node(e2)})
            }
            BinaryOp::Arith(op, _) => {
                nodes!({str_to_node(&format!("{:?}", op))} {expr_to_node(e1)} {expr_to_node(e2)})
            }
            BinaryOp::Inequality(op) => {
                nodes!({str_to_node(&format!("{:?}", op))} {expr_to_node(e1)} {expr_to_node(e2)})
            }
            BinaryOp::Bitwise(op) => {
                nodes!({str_to_node(&format!("{:?}", op))} {expr_to_node(e1)} {expr_to_node(e2)})
            }
            _ => {
                nodes!({str_to_node(&format!("{:?}", binary_op).to_lowercase())} {expr_to_node(e1)} {expr_to_node(e2)})
            }
        },
        ExprX::Multi(MultiOp::Chained(ops), es) => {
            let ops: Vec<Node> = ops.iter().map(|op| str_to_node(&format!("{:?}", op))).collect();
            let es: Vec<Node> = es.iter().map(expr_to_node).collect();
            nodes!(multi {Node::List(ops)} {Node::List(es)})
        }
        ExprX::Quant(quant, binders, expr) => {
            nodes!({str_to_node(&format!("{:?}", quant.quant).to_lowercase())} {binders_node(binders, &typ_to_node)} {expr_to_node(expr)})
        }
        ExprX::Closure(binders, expr) => {
            nodes!(closure {binders_node(binders, &typ_to_node)} {expr_to_node(expr)})
        }
        ExprX::Choose { params, cond, body } => {
            nodes!(choose {binders_node(params, &typ_to_node)} {expr_to_node(cond)} {expr_to_node(body)})
        }
        ExprX::WithTriggers { triggers, body } => {
            let ts = Node::List(triggers.iter().map(exprs_to_node).collect());
            nodes!(with_triggers {ts} {expr_to_node(body)})
        }
        ExprX::Assign { init_not_mut, lhs: e0, rhs: e1 } => {
            let mut nodes = nodes_vec!(assign);
            if *init_not_mut {
                nodes.push(str_to_node(":init_not_mut"));
            }
            nodes.push(expr_to_node(e0));
            nodes.push(expr_to_node(e1));
            Node::List(nodes)
        }
        ExprX::Fuel(fun, fuel) => {
            nodes!(fuel {fun_to_node(fun)} {str_to_node(&format!("{}", fuel))})
        }
        ExprX::Header(header_expr) => nodes!(header {header_expr_to_node(header_expr)}),
        ExprX::Admit => node!(admit),
        ExprX::Forall { vars, require, ensure, proof } => {
            nodes!(forall {binders_node(vars, &typ_to_node)} {str_to_node(":require")} {expr_to_node(require)} {str_to_node(":ensure")} {expr_to_node(ensure)} {str_to_node(":proof")} {expr_to_node(proof)})
        }
        ExprX::AssertQuery { requires, ensures, proof, mode } => {
            nodes!(assertQuery {str_to_node(":requires")} {exprs_to_node(requires)} {str_to_node(":ensures")} {exprs_to_node(ensures)} {str_to_node(":proof")} {expr_to_node(proof)} {str_to_node(":mode")} {str_to_node(&format!("{:?}", mode))})
        }
        ExprX::AssertBV(expr) => nodes!(assertbv {expr_to_node(expr)}),
        ExprX::If(e0, e1, e2) => {
            let mut nodes = nodes_vec!(if { expr_to_node(e0) } {
                expr_to_node(e1)
            });
            if let Some(els) = e2 {
                nodes.push(expr_to_node(els));
            }
            Node::List(nodes)
        }
        ExprX::Match(expr, arms) => {
            nodes!(match {expr_to_node(expr)} {Node::List(arms.iter().map(|arm| {
            let ArmX { pattern, guard, body } = &arm.x;
            let node = nodes!(arm {pattern_to_node(pattern)} {expr_to_node(guard)} {expr_to_node(body)});
            spanned_node(node, &arm.span)
        }).collect())})
        }
        ExprX::While { cond, body, invs } => {
            nodes!(while {expr_to_node(cond)} {expr_to_node(body)} {str_to_node(":invs")} {exprs_to_node(invs)})
        }
        ExprX::OpenInvariant(e1, binder, e2, atomicity) => {
            nodes!(openinvariant {expr_to_node(e1)} {binder_node(binder, &typ_to_node)} {expr_to_node(e2)} {atomicity_to_node(*atomicity)})
        }
        ExprX::Return(expr) => {
            let mut nodes = nodes_vec!(return);
            if let Some(e) = expr {
                nodes.push(expr_to_node(e));
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
            Node::List(nodes_vec!({str_to_node(ghost)} {expr_to_node(expr)}))
        }
        ExprX::Block(stmts, expr) => {
            let mut nodes = nodes_vec!(block {
            Node::List(stmts.iter().map(|stmt| {
                let node = match &stmt.x {
                    StmtX::Expr(expr) => expr_to_node(expr),
                    StmtX::Decl { pattern, mode, init } => {
                        let mut nodes = nodes_vec!(decl {pattern_to_node(pattern)} {str_to_node(":mode")} {str_to_node(&format!("{:?}", mode))});
                        if let Some(inite) = init {
                            nodes.push(expr_to_node(inite));
                        }
                        Node::List(nodes)
                    }
                };
                spanned_node(node, &stmt.span)
            }).collect())});
            if let Some(e) = expr {
                nodes.push(expr_to_node(e));
            }
            Node::List(nodes)
        }
    };
    spanned_node(node, &expr.span)
}

fn function_to_node(function: &FunctionX) -> Node {
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
            .map(|(ident, bound)| Node::List(vec![str_to_node(ident), bound_to_node(bound)]))
            .collect(),
    );
    let param_to_node = |param: &Param| {
        let ParamX { name, typ, mode, is_mut } = &param.x;
        let mut nodes = vec![
            str_to_node(name),
            typ_to_node(typ),
            str_to_node(":mode"),
            Node::Atom(format!("{:?}", mode)),
        ];
        if *is_mut {
            nodes.push(str_to_node("+is_mut"));
        }
        spanned_node(Node::List(nodes), &param.span)
    };
    let params_node = Node::List(params.iter().map(param_to_node).collect());
    let mask_spec_node = nodes!(mask_spec {match mask_spec {
        MaskSpec::InvariantOpens(exprs) => nodes!(InvariantOpens {exprs_to_node(exprs)}),
        MaskSpec::InvariantOpensExcept(exprs) => nodes!(InvariantsOpensExcept {exprs_to_node(exprs)}),
        MaskSpec::NoSpec => node!(NoSpec),
    }});
    let function_attrs_node = {
        let FunctionAttrsX {
            uses_ghost_blocks,
            hidden,
            broadcast_forall,
            no_auto_trigger,
            custom_req_err,
            autoview,
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
            Node::List(hidden.iter().map(|f| fun_to_node(&**f)).collect()),
        ];
        if *uses_ghost_blocks {
            nodes.push(str_to_node("+uses_ghost_blocks"));
        }
        if *broadcast_forall {
            nodes.push(str_to_node("+broadcast_forall"));
        }
        if *no_auto_trigger {
            nodes.push(str_to_node("+no_auto_trigger"));
        }
        // TODO
        /*if let Some(re) = custom_req_err {
            nodes.push(str_to_node(":custom_req_err"));
            nodes.push(str_node(re));
        }*/
        if *autoview {
            nodes.push(str_to_node("+autoview"));
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
        nodes.extend(extra_dependencies.iter().map(|ed| fun_to_node(ed)));
        Node::List(nodes)
    };
    let mut nodes = vec![
        str_to_node("function"),
        fun_to_node(name),
        str_to_node(":kind"),
        (match kind {
            FunctionKind::Static => node!(static),
            FunctionKind::TraitMethodDecl { trait_path } => {
                node!((decl {path_to_node(trait_path)}))
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
                    {fun_to_node(method)}
                    {path_to_node(trait_path)}
                    {typs_to_node(trait_typ_args)}
                    {path_to_node(datatype)}
                    {typs_to_node(datatype_typ_args)}
                ))
            }
        }),
        visibility_to_node(visibility),
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
        exprs_to_node(require),
        str_to_node(":ensure"),
        exprs_to_node(ensure),
        str_to_node(":decrease"),
        exprs_to_node(decrease),
    ];
    if let Some(decrease_when) = &decrease_when {
        nodes.push(str_to_node(":decrease_when"));
        nodes.push(expr_to_node(decrease_when));
    }
    if let Some(decrease_by) = &decrease_by {
        nodes.push(str_to_node(":decrease_by"));
        nodes.push(fun_to_node(decrease_by));
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
        nodes.push(expr_to_node(body));
    }
    Node::List(nodes)
}

pub fn write_krate(mut write: impl std::io::Write, vir_crate: &Krate) {
    let KrateX { datatypes, functions, traits, module_ids } = &**vir_crate;
    let mut nw = NodeWriter::new();
    for datatype in datatypes.iter() {
        writeln!(
            &mut write,
            "{}\n",
            nw.node_to_string_indent(
                &" ".to_string(),
                &spanned_node(datatype_to_node(&datatype.x), &datatype.span)
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
                &spanned_node(function_to_node(&function.x), &function.span)
            )
        )
        .expect("cannot write to vir write");
    }
    for t in traits.iter() {
        let t = nodes!(trait {path_to_node(&t.x.name)});
        writeln!(&mut write, "{}\n", nw.node_to_string_indent(&" ".to_string(), &t))
            .expect("cannot write to vir write");
    }
    for module_id in module_ids.iter() {
        let module_id_node = nodes!(module_id {path_to_node(module_id)});
        writeln!(&mut write, "{}\n", nw.node_to_string_indent(&" ".to_string(), &module_id_node))
            .expect("cannot write to vir write");
    }
}
