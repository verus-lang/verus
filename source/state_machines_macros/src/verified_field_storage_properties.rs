//! Readonly native properties backed by real, possibly overlapping observations.
//! This module emits no allocation, mutation, or owned empty capabilities.
use crate::ast::*;
use crate::field_access_visitor::visit_field_accesses;
use crate::verified_field_storage_roles as roles;
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote, ToTokens};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

#[derive(Default)]
struct Body {
    requires: Vec<Expr>,
    asserts: Vec<Expr>,
    have: Vec<(Ident, SpecialOp, Option<Ident>)>,
    guard: Option<(Ident, SpecialOp)>,
}

fn collect(stmt: &TransitionStmt, out: &mut Body) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, xs) => {
            for x in xs {
                collect(x, out)?;
            }
        }
        TransitionStmt::Require(_, e) => out.requires.push(e.clone()),
        TransitionStmt::Assert(_, e, _) => out.asserts.push(e.clone()),
        TransitionStmt::Split(span, split, xs) => {
            match &**split {
                SplitKind::Special(n, op, _, binding)
                    if matches!(op.stmt, MonoidStmtType::Have) =>
                {
                    let binding = match binding {
                        None => None,
                        Some(p) => match &**p {
                            verus_syn::Pat::Ident(p) => Some(p.ident.clone()),
                            _ => {
                                return Err(Error::new(
                                    *span,
                                    "readonly bound Have requires one identifier",
                                ))
                            }
                        },
                    };
                    out.have.push((n.clone(), op.clone(), binding));
                }
                SplitKind::Special(n, op, _, None) if matches!(op.stmt, MonoidStmtType::Guard) => {
                    if out.guard.replace((n.clone(), op.clone())).is_some() {
                        return Err(Error::new(
                            *span,
                            "readonly native property supports one physical guard",
                        ));
                    }
                }
                _ => {
                    return Err(Error::new(
                        *span,
                        "readonly native property requires straight-line Have/Guard/Require/Assert",
                    ))
                }
            }
            for x in xs {
                collect(x, out)?;
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "unsupported readonly native property statement",
            ))
        }
    }
    Ok(())
}

fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
    for token in tokens {
        match token {
            TokenTree::Ident(n) => {
                names.insert(n.to_string().trim_start_matches("r#").to_string());
            }
            TokenTree::Group(g) => reserve(g.stream(), names),
            _ => {}
        }
    }
}
fn operand(elt: &MonoidElt) -> TokenStream {
    match elt {
        MonoidElt::General(e) | MonoidElt::SingletonMultiset(e) | MonoidElt::SingletonSet(e) => {
            quote! {#e}
        }
        MonoidElt::OptionSome(Some(e)) => quote! {#e},
        MonoidElt::OptionSome(None) => quote! {},
        MonoidElt::SingletonKV(k, v) => quote! {#k #v},
        MonoidElt::True => quote! {true},
    }
}
fn footprint(
    e: &Expr,
    fields: &HashMap<String, Field>,
    used: &mut HashSet<String>,
) -> Result<(), Error> {
    let mut e = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut e,
        |_, f, _| {
            used.insert(f.name.to_string());
        },
        &mut errors,
        fields,
    );
    if let Some(e) = errors.into_iter().next() {
        return Err(e);
    }
    Ok(())
}
fn lower(
    e: &Expr,
    fields: &HashMap<String, Field>,
    values: &HashMap<String, TokenStream>,
) -> Result<TokenStream, Error> {
    let mut e = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut e,
        |errors, f, node| {
            if let Some(value) = values.get(&f.name.to_string()) {
                *node = Expr::Verbatim(value.clone());
            } else {
                errors.push(Error::new(
                    f.name.span(),
                    "readonly native expression needs an exact Variable/Constant observation",
                ));
            }
        },
        &mut errors,
        fields,
    );
    if let Some(e) = errors.into_iter().next() {
        return Err(e);
    }
    Ok(quote! {#e})
}
/// Substitute the values bound by an actual Have owner. Lexical closure, match
/// and block bindings may shadow a model binding and retain their original use.
fn lower_bound(
    e: &Expr,
    fields: &HashMap<String, Field>,
    values: &HashMap<String, TokenStream>,
    bindings: &HashMap<String, TokenStream>,
) -> Result<TokenStream, Error> {
    use verus_syn::visit_mut::{self, VisitMut};
    fn bind_pattern(p: &verus_syn::Pat, names: &mut HashSet<String>) {
        use verus_syn::visit::{self, Visit};
        struct Bind<'a>(&'a mut HashSet<String>);
        impl<'ast> Visit<'ast> for Bind<'_> {
            fn visit_pat_ident(&mut self, p: &'ast verus_syn::PatIdent) {
                self.0.insert(p.ident.to_string());
                visit::visit_pat_ident(self, p);
            }
        }
        Bind(names).visit_pat(p);
    }
    struct Lower<'a> {
        bindings: &'a HashMap<String, TokenStream>,
        shadow: HashSet<String>,
    }
    impl Lower<'_> {
        fn visit_condition(&mut self, e: &mut Expr) {
            match e {
                Expr::Let(local) => {
                    self.visit_expr_mut(&mut local.expr);
                    bind_pattern(&local.pat, &mut self.shadow);
                }
                Expr::Binary(binary) if matches!(binary.op, verus_syn::BinOp::And(_)) => {
                    self.visit_condition(&mut binary.left);
                    self.visit_condition(&mut binary.right);
                }
                Expr::Paren(paren) => self.visit_condition(&mut paren.expr),
                _ => self.visit_expr_mut(e),
            }
        }
    }
    impl VisitMut for Lower<'_> {
        fn visit_block_mut(&mut self, block: &mut verus_syn::Block) {
            let before = self.shadow.clone();
            for stmt in &mut block.stmts {
                if let verus_syn::Stmt::Local(local) = stmt {
                    if let Some(init) = &mut local.init {
                        self.visit_expr_mut(&mut init.expr);
                        if let Some((_, diverge)) = &mut init.diverge {
                            self.visit_expr_mut(diverge);
                        }
                    }
                    bind_pattern(&local.pat, &mut self.shadow);
                } else {
                    visit_mut::visit_stmt_mut(self, stmt);
                }
            }
            self.shadow = before;
        }
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            if let Expr::Path(p) = e {
                if p.qself.is_none() && p.path.segments.len() == 1 {
                    let name = p.path.segments[0].ident.to_string();
                    if !self.shadow.contains(&name) {
                        if let Some(value) = self.bindings.get(&name) {
                            *e = verus_syn::parse2(value.clone())
                                .expect("generated native bound-value expression");
                            return;
                        }
                    }
                }
            }
            match e {
                Expr::Closure(c) => {
                    let before = self.shadow.clone();
                    for arg in &c.inputs {
                        bind_pattern(&arg.pat, &mut self.shadow);
                    }
                    self.visit_expr_mut(&mut c.body);
                    self.shadow = before;
                }
                Expr::Match(m) => {
                    self.visit_expr_mut(&mut m.expr);
                    for arm in &mut m.arms {
                        let before = self.shadow.clone();
                        bind_pattern(&arm.pat, &mut self.shadow);
                        if let Some((_, guard)) = &mut arm.guard {
                            self.visit_expr_mut(guard);
                        }
                        self.visit_expr_mut(&mut arm.body);
                        self.shadow = before;
                    }
                }
                Expr::Block(b) => {
                    self.visit_block_mut(&mut b.block);
                }
                Expr::If(branch) => {
                    let before = self.shadow.clone();
                    self.visit_condition(&mut branch.cond);
                    self.visit_block_mut(&mut branch.then_branch);
                    self.shadow = before.clone();
                    if let Some((_, other)) = &mut branch.else_branch {
                        self.visit_expr_mut(other);
                    }
                    self.shadow = before;
                }
                _ => visit_mut::visit_expr_mut(self, e),
            }
        }
    }
    let mut e = e.clone();
    Lower {
        bindings,
        shadow: HashSet::new(),
    }
    .visit_expr_mut(&mut e);
    lower(&e, fields, values)
}
fn some_argument(e: &Expr) -> Option<&Expr> {
    let e = match e {
        Expr::Paren(p) => return some_argument(&p.expr),
        _ => e,
    };
    match e {
        Expr::Call(call)
            if call.args.len() == 1
                && matches!(&*call.func, Expr::Path(p) if p.qself.is_none() && p.path.segments.last().is_some_and(|s| s.ident=="Some")) =>
        {
            call.args.first()
        }
        _ => None,
    }
}

/// Checked algebra helpers, shared by readonly and owned-exchange adapters.
pub struct Helpers {
    pub declarations: TokenStream,
    pub reflexive: Ident,
    pub transitive: Ident,
    pub lift: Ident,
}
pub fn helpers(sm: &SM) -> Helpers {
    let mut reserved: HashSet<String> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string().trim_start_matches("r#").to_string())
        .chain(
            sm.transitions
                .iter()
                .map(|tr| tr.name.to_string().trim_start_matches("r#").to_string()),
        )
        .collect();
    let generics = &sm.generics;
    reserve(quote! {#generics}, &mut reserved);
    let mut helper_name = |label: &str| {
        let mut s = format!("__tsm_readonly_{label}");
        while reserved.contains(&s) {
            s.push('_');
        }
        reserved.insert(s.clone());
        Ident::new(&s, Span::mixed_site())
    };
    let machine = helper_name("machine");
    let reflexive = helper_name("reflexive");
    let transitive = helper_name("transitive");
    let lift = helper_name("lift");
    // Keep the algebraic proofs polymorphic. Their contracts carry the exact
    // equations into the concrete machine, without a borrowed ownership sum.
    let declarations = quote! {
        proof fn #reflexive<#machine: ::vstd::resource::tsm::Machine>(source:#machine::Fragment)
            ensures ::vstd::resource::tsm::fragment_included::<#machine>(source,source),
        {
            <#machine::Fragment as ::vstd::resource::pcm::PCM>::op_unit(source);
            assert(<#machine::Fragment as ::vstd::resource::algebra::ResourceAlgebra>::op(
                source,<#machine::Fragment as ::vstd::resource::pcm::PCM>::unit())==source);
        }
        proof fn #transitive<#machine: ::vstd::resource::tsm::Machine>(
            source:#machine::Fragment,middle:#machine::Fragment,upper:#machine::Fragment)
            requires ::vstd::resource::tsm::fragment_included::<#machine>(source,middle),
                ::vstd::resource::tsm::fragment_included::<#machine>(middle,upper),
            ensures ::vstd::resource::tsm::fragment_included::<#machine>(source,upper),
        {
            let left=choose|left:#machine::Fragment|
                <#machine::Fragment as ::vstd::resource::algebra::ResourceAlgebra>::op(source,left)==middle;
            let right=choose|right:#machine::Fragment|
                <#machine::Fragment as ::vstd::resource::algebra::ResourceAlgebra>::op(middle,right)==upper;
            <#machine::Fragment as ::vstd::resource::algebra::ResourceAlgebra>::associative(source,left,right);
            assert(<#machine::Fragment as ::vstd::resource::algebra::ResourceAlgebra>::op(source,
                <#machine::Fragment as ::vstd::resource::algebra::ResourceAlgebra>::op(left,right))==upper);
        }
        proof fn #lift<#machine: ::vstd::resource::tsm::Machine>(
            source:#machine::Fragment,upper:#machine::Fragment,frame:#machine::Fragment,state:#machine::State)
            ->(out:#machine::Fragment)
            requires ::vstd::resource::tsm::fragment_included::<#machine>(source,upper),
                <#machine::Fragment as ::vstd::resource::algebra::ResourceAlgebra>::op(upper,frame)==#machine::embed(state),
            ensures <#machine::Fragment as ::vstd::resource::algebra::ResourceAlgebra>::op(source,out)==#machine::embed(state),
        {
            let remainder=choose|remainder:#machine::Fragment|
                <#machine::Fragment as ::vstd::resource::algebra::ResourceAlgebra>::op(source,remainder)==upper;
            <#machine::Fragment as ::vstd::resource::algebra::ResourceAlgebra>::associative(source,remainder,frame);
            <#machine::Fragment as ::vstd::resource::algebra::ResourceAlgebra>::op(remainder,frame)
        }
    };
    Helpers {
        declarations,
        reflexive,
        transitive,
        lift,
    }
}

/// Produce native Instance methods. Every reference is an actual owned role;
/// repeated references may alias and are never combined by additive ownership.
pub fn methods(sm: &SM, cx: &roles::Context<'_>) -> Result<TokenStream, Error> {
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let types = cx.types;
    let expr = cx.expr;
    let Helpers {
        declarations,
        reflexive,
        transitive,
        lift,
    } = helpers(sm);
    let mut methods = vec![declarations];
    for tr in sm
        .transitions
        .iter()
        .filter(|tr| tr.kind == TransitionKind::Property)
    {
        if ["id", "info", "clone", "invariant", "__initial_constants"]
            .contains(&tr.name.to_string().as_str())
            || cx.constants.iter().any(|f| f.name == tr.name)
        {
            return Err(Error::new(
                tr.name.span(),
                "property collides with a generated readonly Instance method",
            ));
        }
        let mut body = Body::default();
        collect(&tr.body, &mut body)?;
        let mut names: HashSet<String> = sm
            .fields
            .iter()
            .map(|f| f.name.to_string().trim_start_matches("r#").to_string())
            .chain(
                sm.transitions
                    .iter()
                    .map(|tr| tr.name.to_string().trim_start_matches("r#").to_string()),
            )
            .chain(
                tr.params
                    .iter()
                    .map(|p| p.name.to_string().trim_start_matches("r#").to_string()),
            )
            .collect();
        let generics = &sm.generics;
        reserve(quote! {#generics}, &mut names);
        for field in &sm.fields {
            let ty = field.get_type();
            reserve(quote! {#ty}, &mut names);
        }
        for p in &tr.params {
            let ty = &p.ty;
            reserve(quote! {#ty}, &mut names);
        }
        for e in body.requires.iter().chain(body.asserts.iter()) {
            reserve(quote! {#e}, &mut names);
        }
        for (_, op, binding) in &body.have {
            reserve(operand(&op.elt), &mut names);
            if let Some(binding) = binding {
                names.insert(binding.to_string().trim_start_matches("r#").to_string());
            }
        }
        if let Some((_, op)) = &body.guard {
            reserve(operand(&op.elt), &mut names);
        }
        let mut fresh = |label: &str| {
            let mut name = format!("__tsm_property_{label}");
            while names.contains(&name) {
                name.push('_');
            }
            names.insert(name.clone());
            Ident::new(&name, Span::mixed_site())
        };
        let pre = fresh("state");
        let completion = fresh("completion");
        let output = fresh("output");
        let native_pre = fresh("native_pre");
        let native_completion = fresh("native_completion");
        let field_frame = fresh("field_frame");
        let piece = fresh("piece");
        let outer = fresh("outer");
        let joined_frame = fresh("joined_frame");
        let lifetime_ident = fresh("borrow");
        let lifetime = verus_syn::Lifetime::new(&format!("'{lifetime_ident}"), Span::mixed_site());
        let mut used = HashSet::new();
        for e in body.requires.iter().chain(body.asserts.iter()) {
            footprint(e, &fields, &mut used)?;
        }
        for (_, op, _) in &body.have {
            let tokens = operand(&op.elt);
            // The real source expressions, rather than a reparsed token string,
            // retain field access information and proc-macro spacing independence.
            match &op.elt {
                MonoidElt::General(e)
                | MonoidElt::SingletonMultiset(e)
                | MonoidElt::SingletonSet(e) => footprint(e, &fields, &mut used)?,
                MonoidElt::OptionSome(Some(e)) => footprint(e, &fields, &mut used)?,
                MonoidElt::SingletonKV(k, v) => {
                    footprint(k, &fields, &mut used)?;
                    if let Some(v) = v {
                        footprint(v, &fields, &mut used)?;
                    }
                }
                _ => {
                    let _ = tokens;
                }
            }
        }
        // Exact native pre expressions come only from variables and immutable
        // constants. Counts, bags and persistent knowledge are local fragments.
        let mut values = HashMap::new();
        for f in cx.constants {
            let n = &f.name;
            values.insert(n.to_string(), quote! {self.#n()});
        }
        let mut inputs: Vec<(&Field, Ident, Option<usize>)> = vec![];
        for field in &sm.fields {
            if matches!(field.stype, ShardableType::Variable(_))
                && used.contains(&field.name.to_string())
            {
                let input = fresh(&format!("{}_owner", field.name));
                values.insert(field.name.to_string(), quote! {#input.value()});
                inputs.push((field, input, None));
            }
            for (i, (n, _, _)) in body.have.iter().enumerate() {
                if n == &field.name {
                    inputs.push((field, fresh(&format!("{}_owner_{i}", field.name)), Some(i)));
                }
            }
        }
        let name = &tr.name;
        let params: Vec<_> = tr
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let ty = &p.ty;
                quote! {#n:#ty}
            })
            .collect();
        let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
        let mut boundvalues = HashMap::new();
        for (field, input, have) in &inputs {
            if let Some(i) = have {
                if let Some(binding) = &body.have[*i].2 {
                    if !matches!(
                        field.stype,
                        ShardableType::PersistentMap(..)
                            | ShardableType::Option(_)
                            | ShardableType::PersistentOption(_)
                    ) {
                        return Err(Error::new(
                            binding.span(),
                            "unsupported readonly bound Have payload",
                        ));
                    }
                    if boundvalues
                        .insert(binding.to_string(), quote! {#input.value()})
                        .is_some()
                    {
                        return Err(Error::new(
                            binding.span(),
                            "readonly native property has a repeated bound Have name",
                        ));
                    }
                }
            }
        }
        let requires: Vec<_> = body
            .requires
            .iter()
            .map(|e| lower_bound(e, &fields, &values, &boundvalues))
            .collect::<Result<_, _>>()?;
        let asserts: Vec<_> = body
            .asserts
            .iter()
            .map(|e| lower_bound(e, &fields, &values, &boundvalues))
            .collect::<Result<_, _>>()?;
        let enabled = format_ident!("{name}_enabled");
        let safety = format_ident!("{name}_safety");
        if inputs.is_empty() {
            if body.guard.is_some() || !body.have.is_empty() {
                return Err(Error::new(
                    name.span(),
                    "readonly native property needs an actual observation",
                ));
            }
            methods.push(quote! {
                pub proof fn #name(tracked &self,#(#params),*)
                    requires #(#requires,)*
                    ensures #(#asserts,)*
                { ::vstd::prelude::use_type_invariant(self);assert(self.__initial_constants()); }
            });
            continue;
        }
        let mut capacities = vec![];
        let mut state_facts = vec![];
        let mut state_lower = HashMap::new();
        for f in &sm.fields {
            let n = &f.name;
            state_lower.insert(n.to_string(), quote! {#pre.#n});
        }
        let mut bindings = vec![];
        let mut input_bodies = vec![];
        let mut observe_bodies = vec![];
        let mut included: Vec<Ident> = vec![];
        let mut upper: Option<Ident> = None;
        for (field, input, have) in &inputs {
            let n = &field.name;
            let frame = fresh(&format!("{n}_frame"));
            input_bodies.push(quote! {
                ::vstd::prelude::use_type_invariant(#input);
                self.metadata.agrees(&#input.metadata);
            });
            let observation = fresh(&format!("{n}_observation"));
            observe_bodies.push(quote! {let tracked #observation=#input.borrow_token().observe();});
            if let Some(previous) = &upper {
                let next = fresh("upper");
                let old_fragment = quote! {#previous.fragment()};
                let next_fragment = quote! {#next.fragment()};
                let transitivity:Vec<_> = included.iter().map(|prior| quote! {
                    Self::#transitive::<Protocol #types>(#prior.raw_fragment(),#old_fragment,#next_fragment);
                }).collect();
                observe_bodies.push(
                    quote! {let tracked #next=#previous.join(&#observation);#(#transitivity)*},
                );
                upper = Some(next);
            } else {
                observe_bodies.push(quote! {
                    Self::#reflexive::<Protocol #types>(#input.raw_fragment());
                });
                upper = Some(observation);
            }
            included.push(input.clone());
            let native_exact = if have.is_none() {
                quote! {assert(#pre.#n==#input.value());}
            } else {
                quote! {}
            };
            let monoid_fact = match &field.stype {
                ShardableType::Constant(_) => unreachable!(),
                ShardableType::Variable(_) => quote! {},
                ShardableType::Option(_) => quote! {
                    ::vstd::resource::tsm_collections::option_owned_frame(#input.raw_fragment().#n,#frame.#n,#pre.#n,#input.value());
                },
                ShardableType::PersistentOption(_) => quote! {
                    ::vstd::resource::tsm_collections::persistent_option_owned_frame(#input.raw_fragment().#n,#frame.#n,#pre.#n,#input.value());
                },
                ShardableType::Set(_) => quote! {
                    ::vstd::resource::tsm_collections::set_owned_frame(#input.raw_fragment().#n,#frame.#n,#pre.#n.to_iset(),#input.element());
                },
                ShardableType::PersistentSet(_) => quote! {
                    ::vstd::resource::tsm_collections::persistent_set_owned_frame(#input.raw_fragment().#n,#frame.#n,#pre.#n.to_iset(),#input.element());
                },
                ShardableType::Multiset(element) => {
                    if have.is_some_and(|i| matches!(body.have[i].1.elt, MonoidElt::General(_))) {
                        let member = fresh(&format!("{n}_bulk_member"));
                        quote! {
                            assert forall|#member:#element|#[trigger]#pre.#n.count(#member)>=#input.multiset().count(#member) by {
                                ::vstd::resource::tsm_finite_multiset::finite_multiset_owned_frame(#input.raw_fragment().#n,#frame.#n,#pre.#n,#member);
                            }
                            assert(#input.multiset().subset_of(#pre.#n));
                        }
                    } else {
                        quote! {
                            ::vstd::resource::tsm_finite_multiset::finite_multiset_owned_frame(#input.raw_fragment().#n,#frame.#n,#pre.#n,#input.element());
                        }
                    }
                }
                ShardableType::PersistentMap(..) => quote! {
                    ::vstd::resource::tsm_collections::persistent_map_owned_frame(#input.raw_fragment().#n,#frame.#n,#pre.#n.to_imap(),#input.key(),#input.value());
                },
                ShardableType::Count | ShardableType::Bool | ShardableType::PersistentBool => {
                    quote! {}
                }
                _ => {
                    return Err(Error::new(
                        n.span(),
                        "unsupported readonly nominal field strategy",
                    ))
                }
            };
            state_facts.push((
                input.clone(),
                frame.clone(),
                quote! {#monoid_fact #native_exact},
            ));
            if let Some(i) = have {
                let (_, op, binding) = &body.have[*i];
                let capacity =
                    match (&field.stype, &op.elt) {
                        (ShardableType::Count, MonoidElt::General(e)) => {
                            let e = lower_bound(e, &fields, &values, &boundvalues)?;
                            quote! {#input.count()>=#e}
                        }
                        (ShardableType::Bool | ShardableType::PersistentBool, MonoidElt::True) => {
                            quote! {true}
                        }
                        (
                            ShardableType::Bool | ShardableType::PersistentBool,
                            MonoidElt::General(e),
                        ) => {
                            let e = lower_bound(e, &fields, &values, &boundvalues)?;
                            quote! {#e}
                        }
                        (
                            ShardableType::Option(_) | ShardableType::PersistentOption(_),
                            MonoidElt::OptionSome(Some(e)),
                        ) => {
                            let e = lower_bound(e, &fields, &values, &boundvalues)?;
                            quote! {#input.value()==#e}
                        }
                        (
                            ShardableType::Option(_) | ShardableType::PersistentOption(_),
                            MonoidElt::General(e),
                        ) => {
                            let e = lower_bound(e, &fields, &values, &boundvalues)?;
                            quote! {Some(#input.value())==#e}
                        }
                        (
                            ShardableType::Option(_) | ShardableType::PersistentOption(_),
                            MonoidElt::OptionSome(None),
                        ) if binding.is_some() => quote! {true},
                        (
                            ShardableType::Set(_)
                            | ShardableType::PersistentSet(_)
                            | ShardableType::Multiset(_),
                            MonoidElt::SingletonSet(e) | MonoidElt::SingletonMultiset(e),
                        ) => {
                            let e = lower_bound(e, &fields, &values, &boundvalues)?;
                            quote! {#input.element()==#e}
                        }
                        (ShardableType::Multiset(_), MonoidElt::General(e)) => {
                            let e = lower_bound(e, &fields, &values, &boundvalues)?;
                            quote! {(#e).subset_of(#input.multiset())}
                        }
                        (ShardableType::PersistentMap(..), MonoidElt::SingletonKV(k, v)) => {
                            let k = lower_bound(k, &fields, &values, &boundvalues)?;
                            let value = v
                                .as_ref()
                                .map(|v| lower_bound(v, &fields, &values, &boundvalues))
                                .transpose()?
                                .map(|v| quote! {&&#input.value()==#v});
                            quote! {#input.key()==#k #value}
                        }
                        _ => return Err(Error::new(
                            n.span(),
                            "readonly native Have requires a scalar/count or singleton observation",
                        )),
                    };
                capacities.push(capacity);
                if let Some(binding) = binding {
                    let value = match field.stype {
                        ShardableType::PersistentMap(..)
                        | ShardableType::Option(_)
                        | ShardableType::PersistentOption(_) => quote! {#input.value()},
                        _ => {
                            return Err(Error::new(
                                binding.span(),
                                "unsupported readonly bound Have payload",
                            ))
                        }
                    };
                    bindings.push(quote! {let #binding=#value;});
                }
            }
        }
        let upper = upper.unwrap();
        let state_frames:Vec<_>=state_facts.iter().map(|(input,frame,facts)|quote! {
            let #frame=Self::#lift::<Protocol #types>(#input.raw_fragment(),#upper.fragment(),#completion,#pre);
            #facts
        }).collect();
        let native_inputs: Vec<_> = inputs
            .iter()
            .map(|(f, n, have)| {
                let field = if matches!(f.stype, ShardableType::Multiset(_))
                    && have.is_some_and(|i| matches!(body.have[i].1.elt, MonoidElt::General(_)))
                {
                    format_ident!("{}_collection", f.name)
                } else {
                    f.name.clone()
                };
                quote! {tracked #n:&#lifetime #field #types}
            })
            .collect();
        let identity: Vec<_> = inputs
            .iter()
            .map(|(_, n, _)| quote! {#n.instance_id()==self.id()})
            .collect();
        let first = &inputs[0].1;
        let const_facts: Vec<_> = cx
            .constants
            .iter()
            .map(|f| {
                let n = &f.name;
                quote! {assert(#pre.#n==self.#n());}
            })
            .collect();
        let prove = quote! {
            #(#state_frames)* #(#const_facts)* #(#bindings)*
            assert(State #expr::#enabled(#pre,#(#pn),*));
            State #expr::#safety(#pre,#(#pn),*);
        };
        let completion_proof = quote! {
            #upper.validate();
            let (#completion,#pre)=choose|#completion:Fragment #types,#pre:State #types|
                #pre.invariant()&&Fragment #expr::op(#upper.fragment(),#completion)==Protocol #expr::embed(#pre);
            #prove
        };
        let (returns, extra_ensures, finish) = if let Some((storage, op)) = &body.guard {
            let field = &fields[&storage.to_string()];
            let ShardableType::StorageOption(element) = &field.stype else {
                return Err(Error::new(
                    storage.span(),
                    "readonly native guard currently supports StorageOption",
                ));
            };
            let guardvalue = match &op.elt {
                MonoidElt::OptionSome(Some(e)) => lower_bound(e, &fields, &values, &boundvalues)?,
                MonoidElt::General(e) => lower_bound(
                    some_argument(e).ok_or_else(|| {
                        Error::new(
                            storage.span(),
                            "readonly native guard requires explicit Some payload",
                        )
                    })?,
                    &fields,
                    &values,
                    &boundvalues,
                )?,
                _ => {
                    return Err(Error::new(
                        storage.span(),
                        "readonly native guard requires explicit Some payload",
                    ))
                }
            };
            let guarded = format_ident!("{name}_guarded");
            let frame_method = format_ident!("{name}_frame");
            let owner_enabled = format_ident!("{name}_owners_enabled");
            let projection = format_ident!("__borrow_{storage}");
            let map = fresh("guarded_map");
            let tagged = fresh("tagged_map");
            // Prove the unchanged universal Protocol guard premise for EVERY
            // compatible completion of the actual joined observation.
            let generic_prove = prove.clone();
            (
                quote! {->(tracked #output:&#lifetime #element)},
                quote! {*#output==#guardvalue,},
                quote! {
                    assert forall|#completion:Fragment #types,#pre:State #types|
                        #pre.invariant()&&Fragment #expr::op(#upper.fragment(),#completion)==Protocol #expr::embed(#pre)
                        implies State #expr::#enabled(#pre,#(#pn),*)
                            &&State #expr::#owner_enabled(#pre,#upper.fragment(),Fragment #expr::empty(),#(#pn),*) by {
                        #generic_prove
                    }
                    Protocol #expr::#frame_method(#upper.fragment(),#(#pn),*);
                    let #map=Protocol #expr::#guarded(#upper.fragment(),#(#pn),*);
                    let tracked #tagged=#upper.guard(#map);
                    let tracked #output=<Protocol #types as ::vstd::resource::tsm_storage::StorageMachine>::Key::#projection(#tagged);
                    #output.tracked_unwrap()
                },
            )
        } else {
            (quote! {}, quote! {}, quote! {})
        };
        methods.push(quote! {
            pub proof fn #name<#lifetime>(tracked &self,#(#params,)*#(#native_inputs),*) #returns
                requires #(#identity,)*#(#capacities,)*#(#requires,)*
                ensures #extra_ensures #(#asserts,)*
            {
                ::vstd::prelude::use_type_invariant(self);
                #(#input_bodies)*#(#observe_bodies)*
                // Metadata equality connects constants and the protocol location
                // of actual inputs; it supplies no completion or owned resource.
                assert(#first.resource_location()==self.metadata.value().protocol_location);
                #completion_proof
                #finish
            }
        });
        let _ = (native_pre, native_completion, joined_frame);
    }
    Ok(quote! {#(#methods)*})
}
