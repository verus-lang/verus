//! A complete physical IMap under actual exclusive fragment ownership.
//! Opaque keys use the original full State. No completion is inferred from a
//! descriptor, and no weak transition supplies a strong exchange premise.
use crate::ast::*;
use crate::parse_token_stream::SMBundle;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::HashSet;
use verus_syn::visit::{self, Visit};
use verus_syn::{Error, Expr, Ident};

pub fn needed(sm: &SM) -> bool {
    sm.fields.len() == 1 && matches!(sm.fields[0].stype, ShardableType::StorageIMap(..))
}

fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
    for token in tokens {
        match token {
            TokenTree::Ident(id) => {
                names.insert(id.to_string().trim_start_matches("r#").to_string());
            }
            TokenTree::Group(group) => reserve(group.stream(), names),
            _ => {}
        }
    }
}

// These new module-level names must not silently reinterpret an original outer
// type or constructor. Explicitly qualified paths keep their original meaning.
struct Namespace {
    error: Option<Error>,
}
impl Namespace {
    fn path(&mut self, path: &verus_syn::Path) {
        let reserved = [
            "Protocol",
            "Fragment",
            "Token",
            "Instance",
            "ResourceAlgebra",
            "Machine",
            "StorageMachine",
        ];
        if path.leading_colon.is_none() {
            if let Some(first) = path.segments.first() {
                if reserved.contains(&first.ident.to_string().trim_start_matches("r#")) {
                    self.error.get_or_insert_with(|| Error::new(first.ident.span(),
                        "owned storage source references a reserved generated namespace; qualify the original path"));
                }
            }
        }
    }
}
impl<'a> Visit<'a> for Namespace {
    fn visit_type_path(&mut self, path: &'a verus_syn::TypePath) {
        self.path(&path.path);
        visit::visit_type_path(self, path);
    }
    fn visit_expr_path(&mut self, path: &'a verus_syn::ExprPath) {
        self.path(&path.path);
        visit::visit_expr_path(self, path);
    }
}
fn namespace_stmt(stmt: &TransitionStmt, visitor: &mut Namespace) {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                namespace_stmt(child, visitor);
            }
        }
        TransitionStmt::Require(_, expression)
        | TransitionStmt::Update(_, _, expression)
        | TransitionStmt::Initialize(_, _, expression)
        | TransitionStmt::PostCondition(_, expression) => {
            visitor.visit_expr(expression);
        }
        TransitionStmt::Assert(_, expression, _) => visitor.visit_expr(expression),
        TransitionStmt::SubUpdate(_, _, indices, expression) => {
            visitor.visit_expr(expression);
            for index in indices {
                if let SubIdx::Idx(expression) = index {
                    visitor.visit_expr(expression);
                }
            }
        }
        TransitionStmt::Split(_, kind, children) => {
            match &**kind {
                SplitKind::If(expression) => visitor.visit_expr(expression),
                SplitKind::Match(expression, arms) => {
                    visitor.visit_expr(expression);
                    for arm in arms {
                        visitor.visit_pat(&arm.pat);
                        if let Some((_, expression)) = &arm.guard {
                            visitor.visit_expr(expression);
                        }
                    }
                }
                SplitKind::Let(pattern, ty, _, expression) => {
                    visitor.visit_pat(pattern);
                    if let Some(ty) = ty {
                        visitor.visit_type(ty);
                    }
                    visitor.visit_expr(expression);
                }
                SplitKind::Special(_, op, _, pattern) => {
                    if let Some(pattern) = pattern {
                        visitor.visit_pat(pattern);
                    }
                    match &op.elt {
                        MonoidElt::SingletonKV(key, value) => {
                            visitor.visit_expr(key);
                            if let Some(value) = value {
                                visitor.visit_expr(value);
                            }
                        }
                        MonoidElt::General(expression)
                        | MonoidElt::SingletonMultiset(expression)
                        | MonoidElt::SingletonSet(expression) => visitor.visit_expr(expression),
                        MonoidElt::OptionSome(value) => {
                            if let Some(value) = value {
                                visitor.visit_expr(value);
                            }
                        }
                        MonoidElt::True => {}
                    }
                }
            }
            for child in children {
                namespace_stmt(child, visitor);
            }
        }
    }
}

#[derive(Default)]
struct Body {
    initial: Option<Expr>,
    withdrawal: Option<(Expr, Expr)>,
}

fn collect(stmt: &TransitionStmt, field: &Ident, body: &mut Body) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                collect(child, field, body)?;
            }
        }
        TransitionStmt::Initialize(_, name, expression) if name == field => {
            if body.initial.replace(expression.clone()).is_some() {
                return Err(Error::new(
                    name.span(),
                    "owned storage initializer repeats its field",
                ));
            }
        }
        TransitionStmt::Require(..) | TransitionStmt::Assert(..) => {}
        TransitionStmt::Split(span, kind, children) => {
            if let SplitKind::Special(name, operation, _, None) = &**kind {
                if name == field && matches!(operation.stmt, MonoidStmtType::Withdraw) {
                    if let MonoidElt::SingletonKV(key, Some(value)) = &operation.elt {
                        if body
                            .withdrawal
                            .replace((key.clone(), (**value).clone()))
                            .is_some()
                        {
                            return Err(Error::new(
                                *span,
                                "owned storage permits one singleton withdrawal",
                            ));
                        }
                        for child in children {
                            collect(child, field, body)?;
                        }
                        return Ok(());
                    }
                }
            }
            return Err(Error::new(
                *span,
                "owned storage requires an explicit singleton withdrawal without a bound pattern",
            ));
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "unsupported owned storage statement",
            ))
        }
    }
    Ok(())
}

pub fn output(bundle: &SMBundle) -> Result<TokenStream, Error> {
    let sm = &bundle.sm;
    let field = &sm.fields[0].name;
    // The inherited mathematical simplifier derives update_tmp_FIELD names.
    // Reject raw fields before that lowering can construct an invalid identifier.
    if field.to_string().starts_with("r#") {
        return Err(Error::new(
            field.span(),
            "owned storage raw field identifiers are not supported",
        ));
    }
    let ShardableType::StorageIMap(key_type, value_type) = &sm.fields[0].stype else {
        unreachable!()
    };
    let mut namespace = Namespace { error: None };
    namespace.visit_type(key_type);
    namespace.visit_type(value_type);
    for tr in &sm.transitions {
        for parameter in &tr.params {
            namespace.visit_type(&parameter.ty);
        }
        namespace_stmt(&tr.body, &mut namespace);
    }
    for function in &bundle.normal_fns {
        namespace.visit_impl_item_fn(function);
    }
    for invariant in &bundle.extras.invariants {
        namespace.visit_impl_item_fn(&invariant.func);
    }
    for lemma in &bundle.extras.lemmas {
        namespace.visit_impl_item_fn(&lemma.func);
    }
    if let Some(error) = namespace.error {
        return Err(error);
    }
    if sm.transition_label.is_some() || sm.init_label.is_some() {
        return Err(Error::new(
            sm.name.span(),
            "owned storage labels are not supported",
        ));
    }
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let field_ast = &sm.fields_named_ast;
    let mut names = HashSet::new();
    reserve(quote! {#generics #field_ast}, &mut names);
    for tr in &sm.transitions {
        let name = &tr.name;
        reserve(quote! {#name}, &mut names);
        crate::verified_field_storage_map_pair::reserve_stmt(&tr.body, &mut names);
        for param in &tr.params {
            let name = &param.name;
            let ty = &param.ty;
            reserve(quote! {#name #ty}, &mut names);
        }
    }
    for function in &bundle.normal_fns {
        reserve(quote! {#function}, &mut names);
    }
    for invariant in &bundle.extras.invariants {
        let function = &invariant.func;
        reserve(quote! {#function}, &mut names);
    }
    for lemma in &bundle.extras.lemmas {
        let function = &lemma.func;
        reserve(quote! {#function}, &mut names);
    }
    let reserved = [
        "Protocol",
        "Fragment",
        "Token",
        "Instance",
        "State",
        "Ghost",
        "Tracked",
        "IMap",
        "ResourceAlgebra",
        "Machine",
        "StorageMachine",
    ];
    if reserved.contains(&field.to_string().trim_start_matches("r#")) {
        return Err(Error::new(
            field.span(),
            "owned storage field conflicts with a generated type",
        ));
    }
    if let Some(g) = &sm.generics {
        for param in &g.params {
            if let verus_syn::GenericParam::Type(t) = param {
                if reserved.contains(&t.ident.to_string().trim_start_matches("r#")) {
                    return Err(Error::new(
                        t.ident.span(),
                        "owned storage generic conflicts with a generated type",
                    ));
                }
            }
        }
    }
    let mut fresh = |label: &str| {
        let mut name = format!("__tsm_owned_imap_{label}");
        while names.contains(&name) {
            name.push('_');
        }
        names.insert(name.clone());
        Ident::new(&name, Span::mixed_site())
    };
    let raw = fresh("raw");
    let map = fresh("map");
    let before = fresh("before");
    let after = fresh("after");
    let state = fresh("state");
    let frame = fresh("frame");
    let pin = fresh("pin");
    let result = fresh("result");
    let actual = fresh("actual");
    let current = fresh("current");
    let next = fresh("next");
    let withdrawn = fresh("withdrawn");
    let wd = fresh("withdrawal");
    let index = fresh("index");
    let value = fresh("value");
    let slot = fresh("slot");
    let mut methods =
        HashSet::from(["id", "value", "invariant", "borrow_at", "borrow_token"].map(str::to_owned));
    let mut state_helpers = Vec::new();
    let mut instance_methods = Vec::new();
    for tr in &sm.transitions {
        let name = &tr.name;
        if !methods.insert(name.to_string().trim_start_matches("r#").to_string()) {
            return Err(Error::new(
                name.span(),
                "owned storage transition conflicts with an Instance method",
            ));
        }
        let mut body = Body::default();
        collect(&tr.body, field, &mut body)?;
        let params: Vec<_> = tr
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let t = &p.ty;
                quote! {#n: #t}
            })
            .collect();
        let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
        let enabled = format_ident!("{name}_enabled_strong");
        let strong = format_ident!("{name}_strong");
        if tr.kind == TransitionKind::Init {
            let Some(initial) = body.initial else {
                return Err(Error::new(
                    name.span(),
                    "owned storage initializer must initialize its map",
                ));
            };
            if body.withdrawal.is_some() {
                return Err(Error::new(
                    name.span(),
                    "owned storage initializer cannot withdraw",
                ));
            }
            let initial_fn = fresh(&format!("{name}_initial"));
            state_helpers.push(quote! {
                pub open spec fn #initial_fn(#(#params),*) -> IMap<#key_type,#value_type> { #initial }
            });
            instance_methods.push(quote! {
                pub proof fn #name(#(#params,)* tracked #actual: IMap<#key_type,#value_type>)
                    -> (tracked #result: Self)
                    requires State #expr::#enabled(#(#pn),*),
                        #actual == State #expr::#initial_fn(#(#pn),*),
                    ensures #result.value() == State #expr::#initial_fn(#(#pn),*),
                {
                    let #state = take_step::#name #expr(#(#pn),*);
                    assert(#state.#field == State #expr::#initial_fn(#(#pn),*));
                    let tracked #raw = Token #expr::alloc_state(#state, #actual);
                    Self { #raw: Tracked(Some(#raw)) }
                }
            });
        } else if tr.kind == TransitionKind::Transition {
            if body.initial.is_some() {
                return Err(Error::new(
                    name.span(),
                    "owned storage transition cannot initialize",
                ));
            }
            let Some((key, payload)) = body.withdrawal else {
                return Err(Error::new(
                    name.span(),
                    "owned storage transition must withdraw one explicit singleton",
                ));
            };
            let key_fn = fresh(&format!("{name}_key"));
            let payload_fn = fresh(&format!("{name}_payload"));
            let transfer = fresh(&format!("{name}_transfer"));
            state_helpers.push(quote! {
                pub open spec fn #key_fn(pre: Self, #(#params),*) -> #key_type { #key }
                pub open spec fn #payload_fn(pre: Self, #(#params),*) -> #value_type { #payload }
            });
            instance_methods.push(quote! {
                pub proof fn #name(tracked &mut self, #(#params),*) -> (tracked #result: #value_type)
                    requires State #expr::#enabled(State {#field: old(self).value()}, #(#pn),*),
                    ensures final(self).id() == old(self).id(),
                        #result == State #expr::#payload_fn(State {#field: old(self).value()}, #(#pn),*),
                        State #expr::#strong(State {#field: old(self).value()}, State {#field: final(self).value()}, #(#pn),*),
                {
                    ::vstd::prelude::use_type_invariant(&*self);
                    let #before = State {#field: self.value()};
                    Self::#transfer(&mut self.#raw, #before, #(#pn),*)
                }
                proof fn #transfer(tracked #slot: &mut Tracked<Option<Token #types>>,
                    #before: State #types, #(#params),*) -> (tracked #result: #value_type)
                    requires old(#slot)@ is Some,
                        old(#slot)@->Some_0.fragment()
                            == Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(#before.#field)),
                        State #expr::#enabled(#before, #(#pn),*),
                    ensures final(#slot)@ is Some,
                        final(#slot)@->Some_0.loc() == old(#slot)@->Some_0.loc(),
                        final(#slot)@->Some_0.fragment() is Some,
                        final(#slot)@->Some_0.fragment()->Some_0 is Exclusive,
                        #result == State #expr::#payload_fn(#before, #(#pn),*),
                        State #expr::#strong(#before,
                            State {#field: final(#slot)@->Some_0.fragment()->Some_0->Exclusive_0}, #(#pn),*),
                {
                    broadcast use {::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas};
                    let tracked #current = #slot.borrow_mut().tracked_take();
                    #current.validate();
                    let (#frame, #state) = choose |#frame: Fragment #types, #state: State #types|
                        <Protocol #types as ::vstd::resource::tsm::Machine>::invariant(#state)
                        && Fragment #expr::op(#current.fragment(), #frame)
                            == <Protocol #types as ::vstd::resource::tsm::Machine>::embed(#state);
                    Self::#pin(#before.#field, #frame, #state);
                    assert(#before == #state);
                    let #after = take_step::#name #expr(#before, #(#pn),*);
                    let #index = State #expr::#key_fn(#before, #(#pn),*);
                    let #value = State #expr::#payload_fn(#before, #(#pn),*);
                    let #wd = IMap::<#key_type,#value_type>::empty().insert(#index, #value);
                    assert(#wd.submap_of(#before.#field));
                    assert(#after.#field == #before.#field.remove_keys(#wd.dom())) by {
                        assert(::vstd::prelude::ext_equal(#after.#field, #before.#field.remove_keys(#wd.dom())));
                    }
                    let #next = Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(#after.#field));
                    assert forall |#frame: Fragment #types, #state: State #types|
                        <Protocol #types as ::vstd::resource::tsm::Machine>::invariant(#state)
                        && Fragment #expr::op(#current.fragment(), #frame)
                            == <Protocol #types as ::vstd::resource::tsm::Machine>::embed(#state)
                        implies {
                            #state.#field.dom().disjoint(IMap::<#key_type,#value_type>::empty().dom())
                            && #wd.submap_of(#state.#field.union_prefer_right(IMap::empty()))
                            && exists |#state: State #types| #state.invariant()
                                && Fragment #expr::op(#next, #frame)
                                    == <Protocol #types as ::vstd::resource::tsm::Machine>::embed(#state)
                                && #state.#field == #before.#field.union_prefer_right(IMap::empty()).remove_keys(#wd.dom())
                        } by {
                            Self::#pin(#before.#field, #frame, #state);
                            assert(#after.invariant());
                            assert(Fragment #expr::op(#next, #frame)
                                == <Protocol #types as ::vstd::resource::tsm::Machine>::embed(#after));
                        }
                    assert(::vstd::resource::tsm_storage::frame_exchange::<Protocol #types>(
                        #current.fragment(), IMap::empty(), #next, #wd));
                    let tracked (#current, mut #withdrawn) = #current.exchange(IMap::tracked_empty(), #next, #wd);
                    *#slot = Tracked(Some(#current));
                    #withdrawn.tracked_remove(#index)
                }
            });
        } else {
            return Err(Error::new(
                name.span(),
                "owned storage properties and readonly transitions are not supported",
            ));
        }
    }
    Ok(quote! {
        use ::vstd::resource::algebra::ResourceAlgebra;
        use ::vstd::resource::tsm::Machine;
        use ::vstd::resource::tsm_storage::StorageMachine;
        pub type Fragment #decl #wc = Option<::vstd::resource::exclusive::ExclusiveRA<IMap<#key_type,#value_type>>>;
        #(#attrs)* pub struct Protocol #decl #wc { ghost #map: IMap<#key_type,#value_type> }
        impl #decl Machine for Protocol #types #wc {
            type Fragment = Fragment #types;
            type State = State #types;
            open spec fn invariant(#state: State #types) -> bool { #state.invariant() }
            open spec fn embed(#state: State #types) -> Fragment #types {
                Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(#state.#field))
            }
        }
        impl #decl StorageMachine for Protocol #types #wc {
            type Key = #key_type;
            type Value = #value_type;
            open spec fn storage(#state: State #types) -> IMap<#key_type,#value_type> { #state.#field }
        }
        pub type Token #decl #wc = ::vstd::resource::tsm_storage::StorageToken<Protocol #types>;
        impl #decl State #types #wc { #(#state_helpers)* }
        #(#attrs)* pub tracked struct Instance #decl #wc { #raw: Tracked<Option<Token #types>> }
        impl #decl Instance #types #wc {
            #[verifier::type_invariant]
            spec fn invariant(self) -> bool {
                self.#raw@ is Some && self.#raw@->Some_0.fragment() is Some
                    && self.#raw@->Some_0.fragment()->Some_0 is Exclusive
            }
            pub closed spec fn id(&self) -> ::vstd::resource::Loc { self.#raw@->Some_0.loc() }
            pub closed spec fn value(&self) -> IMap<#key_type,#value_type> {
                self.#raw@->Some_0.fragment()->Some_0->Exclusive_0
            }
            proof fn #pin(#map: IMap<#key_type,#value_type>, #frame: Fragment #types, #state: State #types)
                requires Fragment #expr::op(Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(#map)), #frame)
                    == <Protocol #types as Machine>::embed(#state),
                ensures #frame is None, #state.#field == #map,
            { match #frame { None => {}, Some(_) => {} } }
            pub proof fn borrow_token<'a>(tracked &'a self) -> (tracked #result: &'a Token #types)
                ensures #result.loc() == self.id(),
                    #result.fragment() == Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(self.value())),
            {
                ::vstd::prelude::use_type_invariant(self);
                self.#raw.borrow().tracked_borrow()
            }
            pub proof fn borrow_at<'a>(tracked &'a self, #index: #key_type) -> (tracked #result: &'a #value_type)
                requires self.value().contains_key(#index),
                ensures *#result == self.value()[#index],
            {
                broadcast use {::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas};
                let tracked #raw = self.borrow_token();
                let #map = self.value();
                let #wd = IMap::<#key_type,#value_type>::empty().insert(#index,#map[#index]);
                assert forall |#frame: Fragment #types, #state: State #types|
                    #state.invariant() && Fragment #expr::op(#raw.fragment(), #frame)
                        == <Protocol #types as Machine>::embed(#state)
                    implies #wd.submap_of(#state.#field) by {
                        Self::#pin(#map,#frame,#state);
                    }
                let tracked #actual = #raw.guard(#wd);
                #actual.tracked_borrow(#index)
            }
            #(#instance_methods)*
        }
    })
}
