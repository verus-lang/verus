//! Nominal physical owners. Descriptor resources carry identity and immutable
//! metadata only; every operation consumes a genuine checked storage owner.
use crate::ast::*;
use crate::field_access_visitor::visit_field_accesses;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

struct Generics {
    decl: TokenStream,
    wc: TokenStream,
    attrs: Vec<verus_syn::Attribute>,
    types: TokenStream,
    expr: TokenStream,
}

fn generics(sm: &SM) -> Generics {
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    Generics {
        decl,
        wc,
        attrs,
        types: args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default(),
        expr: args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default(),
    }
}

fn fresh(sm: &SM, tr: &Transition, label: &str) -> Ident {
    let mut unavailable: HashSet<_> = sm.fields.iter().map(|f| f.name.to_string()).collect();
    unavailable.extend(tr.params.iter().map(|p| p.name.to_string()));
    fn bindings(stmt: &TransitionStmt, out: &mut HashSet<String>) {
        struct Names<'a>(&'a mut HashSet<String>);
        impl<'ast> verus_syn::visit::Visit<'ast> for Names<'_> {
            fn visit_ident(&mut self, ident: &'ast Ident) {
                self.0.insert(ident.to_string());
            }
        }
        use verus_syn::visit::Visit;
        match stmt {
            TransitionStmt::Block(_, children) => {
                for child in children {
                    bindings(child, out);
                }
            }
            TransitionStmt::Split(_, split, children) => {
                match &**split {
                    SplitKind::Let(pat, ..) => Names(out).visit_pat(pat),
                    SplitKind::Special(_, _, _, Some(pat)) => Names(out).visit_pat(pat),
                    SplitKind::Match(_, arms) => {
                        for arm in arms {
                            Names(out).visit_pat(&arm.pat);
                        }
                    }
                    _ => {}
                }
                for child in children {
                    bindings(child, out);
                }
            }
            _ => {}
        }
    }
    bindings(&tr.body, &mut unavailable);
    let mut candidate = format!("__tsm_storage_{label}");
    while unavailable.contains(&candidate) {
        candidate.push('_');
    }
    Ident::new(&candidate, Span::mixed_site())
}

fn initial(
    stmt: &TransitionStmt,
    values: &mut HashMap<String, Expr>,
    requirements: &mut Vec<Expr>,
) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                initial(child, values, requirements)?;
            }
        }
        TransitionStmt::Initialize(_, name, value) => {
            values.insert(name.to_string(), value.clone());
        }
        TransitionStmt::Require(_, value) => requirements.push(value.clone()),
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "physical field initializer requires straight-line initialization",
            ))
        }
    }
    Ok(())
}

#[derive(Default)]
struct Operation {
    updates: HashMap<String, Expr>,
    requirements: Vec<Expr>,
    assertions: Vec<Expr>,
    physical: Option<(SpecialOp, Option<Box<verus_syn::Pat>>)>,
}

fn operation(stmt: &TransitionStmt, out: &mut Operation) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                operation(child, out)?;
            }
        }
        TransitionStmt::Update(_, name, value) => {
            if out
                .updates
                .insert(name.to_string(), value.clone())
                .is_some()
            {
                return Err(Error::new(
                    name.span(),
                    "physical field facade requires one write per field",
                ));
            }
        }
        TransitionStmt::Require(_, value) => out.requirements.push(value.clone()),
        TransitionStmt::Assert(_, value, _) => out.assertions.push(value.clone()),
        TransitionStmt::Split(_, split, children) => {
            let SplitKind::Special(_, op, _, pattern) = &**split else {
                return Err(Error::new(
                    *stmt.get_span(),
                    "physical field facade currently requires straight-line operations",
                ));
            };
            if !matches!(op.stmt, MonoidStmtType::Deposit | MonoidStmtType::Withdraw)
                || out
                    .physical
                    .replace((op.clone(), pattern.clone()))
                    .is_some()
            {
                return Err(Error::new(
                    *stmt.get_span(),
                    "physical field facade currently supports one deposit or withdrawal",
                ));
            }
            for child in children {
                operation(child, out)?;
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "unsupported physical field operation",
            ))
        }
    }
    Ok(())
}

fn native(
    input: &Expr,
    fields: &HashMap<String, Field>,
    variable: &Field,
    field_arg: &Ident,
    before: Option<&TokenStream>,
    old: bool,
) -> Result<TokenStream, Error> {
    let mut expression = input.clone();
    let mut errors = Vec::new();
    visit_field_accesses(
        &mut expression,
        |errors, field, node| {
            let getter = format_ident!("value_{}", field.name);
            *node = Expr::Verbatim(if let Some(before) = before {
                quote! {#before.#getter()}
            } else if matches!(field.stype, ShardableType::Constant(_)) {
                let n = &field.name;
                quote! {self.#n()}
            } else if field.name == variable.name {
                if old {
                    quote! {old(#field_arg).value()}
                } else {
                    quote! {#field_arg.value()}
                }
            } else {
                errors.push(Error::new(
                    field.name.span(),
                    "physical field expressions require an actually owned ordinary field",
                ));
                quote! {false}
            });
        },
        &mut errors,
        fields,
    );
    if let Some(error) = errors.into_iter().next() {
        return Err(error);
    }
    Ok(quote! {#expression})
}

pub fn output(sm: &SM, selected: &HashSet<String>) -> Result<TokenStream, Error> {
    let mut ordinary = Vec::new();
    let mut constants = Vec::new();
    let mut physical = None;
    for field in &sm.fields {
        match &field.stype {
            ShardableType::Variable(_) => ordinary.push(field),
            ShardableType::Constant(_) => constants.push(field),
            ShardableType::StorageOption(ty) => {
                if physical.replace((field, ty)).is_some() {
                    return Err(Error::new(
                        field.name.span(),
                        "physical field facade requires one physical field",
                    ));
                }
            }
            _ => return Err(Error::new(
                field.name.span(),
                "physical nominal facade currently supports ordinary fields and optional storage",
            )),
        }
    }
    let Some((storage, permission_ty)) = physical else {
        return Err(Error::new(
            sm.name.span(),
            "physical field facade requires storage",
        ));
    };
    if ordinary.len() != 1 {
        return Err(Error::new(
            sm.name.span(),
            "physical transition facade currently requires one ordinary variable",
        ));
    }
    let variable = ordinary[0];
    let name = &variable.name;
    let value_ty = variable.get_type();
    let factory = format_ident!("field_{name}");
    let getter = format_ident!("value_{name}");
    let owns = format_ident!("owns_{name}");
    let storage_name = &storage.name;
    let identity_field = fresh(sm, &sm.transitions[0], "protocol_loc");
    let payload_marker = fresh(sm, &sm.transitions[0], "storage_type");
    let Generics {
        decl,
        wc,
        attrs,
        types,
        expr,
    } = generics(sm);
    let token = quote! {Token #types};
    let metadata = quote! {__StorageMetadata #types};
    let descriptor = quote! {::vstd::resource::tsm_context::Descriptor<#metadata>};
    let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
    let ct: Vec<_> = constants.iter().map(|f| f.get_type()).collect();
    let setters: Vec<_> = cn.iter().map(|n| format_ident!("with_{n}")).collect();
    let rawgetters: Vec<_> = cn.iter().map(|n| format_ident!("value_{n}")).collect();
    let shape =
        quote! {Fragment #expr::#factory(self.value()) #(.#setters(self.metadata.value().#cn))*};
    let context_shape = quote! {Fragment #expr::empty() #(.#setters(self.metadata.value().#cn))*};
    let rawshape = quote! {Fragment #expr::#factory(raw.fragment().#getter()) #(.#setters(metadata.value().#cn))*};
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let mut reserved: HashSet<_> = [
        "Instance",
        "Protocol",
        "State",
        "Fragment",
        "Token",
        "TransitionObservation",
        "__StorageMetadata",
    ]
    .iter()
    .map(|name| name.to_string())
    .collect();
    for field in &sm.fields {
        if !reserved.insert(field.name.to_string()) {
            return Err(Error::new(
                field.name.span(),
                "physical nominal type conflicts with a generated type",
            ));
        }
    }
    let mut methods = HashSet::from([
        "clone".to_string(),
        "id".to_string(),
        "invariant".to_string(),
    ]);
    for c in &constants {
        if !methods.insert(c.name.to_string()) {
            return Err(Error::new(
                c.name.span(),
                "constant getter conflicts with a physical instance method",
            ));
        }
    }
    for tr in &sm.transitions {
        if !methods.insert(tr.name.to_string()) {
            return Err(Error::new(
                tr.name.span(),
                "transition conflicts with a physical instance method",
            ));
        }
        if tr.kind != TransitionKind::Init && !methods.insert(format!("__physical_raw_{}", tr.name))
        {
            return Err(Error::new(
                tr.name.span(),
                "transition conflicts with a physical instance helper",
            ));
        }
    }
    let wrappers = quote! {
        #(#attrs)* struct __StorageMetadata #decl #wc {
            ghost #identity_field: ::vstd::resource::Loc,
            #(ghost #cn:#ct,)*
            ghost #payload_marker:Option<#permission_ty>,
        }
        #(#attrs)* #[allow(non_camel_case_types)]
        pub tracked struct #name #decl #wc {
            raw:Tracked<Option<#token>>, metadata:#descriptor,
        }
        impl #decl #name #types #wc {
            #[verifier::type_invariant]
            spec fn invariant(self)->bool {
                self.raw@ is Some
                && self.raw@->Some_0.loc()==self.metadata.value().#identity_field
                && self.raw@->Some_0.fragment().#owns()
                && self.raw@->Some_0.fragment()==#shape
            }
            pub closed spec fn instance_id(&self)->::vstd::resource::Loc {self.metadata.id()}
            pub closed spec fn value(&self)->#value_ty {self.raw@->Some_0.fragment().#getter()}
            pub closed spec fn resource_location(&self)->::vstd::resource::Loc {
                self.raw@->Some_0.loc()
            }
            pub closed spec fn raw_fragment(&self)->Fragment #types {
                self.raw@->Some_0.fragment()
            }
            /// Borrow actual authority; the metadata identity alone grants none.
            pub proof fn borrow_token(tracked &self)->(tracked out:&#token)
                ensures out.loc()==self.resource_location(),
                    out.fragment()==self.raw_fragment(),
                    out.fragment().#owns(),out.fragment().#getter()==self.value(),
            {::vstd::prelude::use_type_invariant(self);self.raw.borrow().tracked_borrow()}
            proof fn __from_token(tracked raw:#token,tracked metadata:#descriptor)->(tracked out:Self)
                requires raw.loc()==metadata.value().#identity_field,raw.fragment().#owns(),
                    raw.fragment()==#rawshape,
                ensures out.instance_id()==metadata.id(),out.value()==raw.fragment().#getter(),
            {Self{raw:Tracked(Some(raw)),metadata}}
        }
    };
    let mut api = Vec::new();
    for tr in &sm.transitions {
        let trname = &tr.name;
        let params: Vec<_> = tr
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let ty = &p.ty;
                quote! {#n:#ty}
            })
            .collect();
        let args: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
        if tr.kind == TransitionKind::Init {
            let mut values = HashMap::new();
            let mut requirements = Vec::new();
            initial(&tr.body, &mut values, &mut requirements)?;
            let initial_value = &values[&name.to_string()];
            let storage_value = &values[&storage_name.to_string()];
            let constant_values: Vec<_> = cn.iter().map(|c| &values[&c.to_string()]).collect();
            let input = fresh(sm, tr, "initial_permission");
            let deposited = fresh(sm, tr, "initial_deposit");
            let full = fresh(sm, tr, "full");
            let md = fresh(sm, tr, "metadata");
            let constant = quote! {Fragment #expr::empty() #(.#setters(#constant_values))*};
            let owner =
                quote! {Fragment #expr::#factory(#initial_value) #(.#setters(#constant_values))*};
            api.push(quote! {
                pub proof fn #trname(#(#params,)*tracked #input:Option<#permission_ty>)
                    ->(tracked out:(Tracked<Self>,Tracked<#name #types>))
                    requires #(#requirements,)*#input==#storage_value,
                    ensures out.1@.instance_id()==out.0@.id(),out.1@.value()==#initial_value,
                        #(out.0@.#cn()==#constant_values,)*
                {
                    let tracked #deposited=match #input {
                        Some(permission)=>::vstd::resource::tsm_helpers::singleton_map(0int,permission),
                        None=>IMap::<int,#permission_ty>::tracked_empty(),
                    };
                    let tracked #full=Protocol #expr::#trname(#deposited,#(#args),*);
                    let tracked #md=::vstd::resource::tsm_context::Descriptor::alloc(__StorageMetadata #expr {
                        #identity_field:#full.loc(),#(#cn:#constant_values,)*#payload_marker:None,
                    });
                    assert(Fragment #expr::op(#owner,#constant)==#full.fragment());
                    let tracked (owner,context)=#full.split(#owner,#constant);
                    let tracked owner=<#name #types>::__from_token(owner,#md.clone());
                    (Tracked(Self{metadata:#md,context:Tracked(Some(context))}),Tracked(owner))
                }
            });
            continue;
        }
        if tr.kind != TransitionKind::Transition || !selected.contains(&tr.name.to_string()) {
            return Err(Error::new(
                tr.name.span(),
                "physical nominal transitions require selected checked local readiness",
            ));
        }
        let mut op = Operation::default();
        operation(&tr.body, &mut op)?;
        let Some((physical, binding)) = &op.physical else {
            return Err(Error::new(
                tr.name.span(),
                "physical nominal transition requires a physical transfer",
            ));
        };
        let Some(update) = op.updates.get(&name.to_string()) else {
            return Err(Error::new(
                tr.name.span(),
                "physical nominal transition must update its ordinary variable",
            ));
        };
        let field_arg = fresh(sm, tr, "field");
        let slot = fresh(sm, tr, "slot");
        let actual = fresh(sm, tr, "permission");
        let owned = fresh(sm, tr, "owned");
        let initial = fresh(sm, tr, "initial");
        let next = fresh(sm, tr, "next");
        let withdrawn = fresh(sm, tr, "withdrawn");
        let before = fresh(sm, tr, "before");
        let after = fresh(sm, tr, "after");
        let deposit = fresh(sm, tr, "deposit");
        let result = fresh(sm, tr, "result");
        let raw = format_ident!("__physical_raw_{trname}");
        let observed = format_ident!("{trname}_observed");
        let local = format_ident!("{trname}_local_requires");
        let initial_expr = quote! {#initial};
        let oldslot = quote! {old(#slot)@->Some_0.fragment()};
        let raw_update = native(update, &fields, variable, &field_arg, Some(&oldslot), false)?;
        let public_update = native(update, &fields, variable, &field_arg, None, true)?;
        let requirements: Vec<_> = op
            .requirements
            .iter()
            .map(|r| native(r, &fields, variable, &field_arg, None, false))
            .collect::<Result<_, _>>()?;
        let setter = format_ident!("with_{name}");
        let mut assertions = Vec::new();
        let mut raw_assertions = Vec::new();
        for assertion in &op.assertions {
            let mut public = native(assertion, &fields, variable, &field_arg, None, true)?;
            let mut rawassert = native(
                assertion,
                &fields,
                variable,
                &field_arg,
                Some(&oldslot),
                false,
            )?;
            if let Some(pattern) = binding {
                public = quote! {{let #pattern=#result;#public}};
                rawassert = quote! {{let #pattern=#result;#rawassert}};
            }
            assertions.push(public);
            raw_assertions.push(rawassert);
        }
        match (&physical.stmt, &physical.elt) {
            (MonoidStmtType::Deposit, MonoidElt::OptionSome(Some(value))) => {
                let native_value = native(value, &fields, variable, &field_arg, None, false)?;
                let raw_value =
                    native(value, &fields, variable, &field_arg, Some(&oldslot), false)?;
                let call_value = native(
                    value,
                    &fields,
                    variable,
                    &field_arg,
                    Some(&initial_expr),
                    false,
                )?;
                api.push(quote! {
                    proof fn #raw(tracked #slot:&mut Tracked<Option<#token>>,#(#params,)*tracked #actual:#permission_ty)
                        requires old(#slot)@ is Some,
                            Protocol #expr::#local(old(#slot)@->Some_0.fragment(),Fragment #expr::empty(),
                                IMap::empty().insert(0int,#actual),#(#args),*),
                            #actual==#raw_value,
                        ensures final(#slot)@ is Some,
                            final(#slot)@->Some_0.loc()==old(#slot)@->Some_0.loc(),
                            final(#slot)@->Some_0.fragment()==old(#slot)@->Some_0.fragment().#setter(#raw_update),
                            #(#raw_assertions,)*
                    {
                        let tracked #owned=#slot.borrow_mut().tracked_take();
                        let #initial=#owned.fragment();
                        let tracked #deposit=::vstd::resource::tsm_helpers::singleton_map(0int,#actual);
                        let tracked TransitionObservation #expr {token:#next,..}
                            =Protocol #expr::#observed(#owned,#deposit,#(#args),*);
                        assert(#call_value==#actual);
                        *#slot=Tracked(Some(#next));
                    }
                    pub proof fn #trname(tracked &self,#(#params,)*tracked #field_arg:&mut #name #types,tracked #actual:#permission_ty)
                        requires #field_arg.instance_id()==self.id(),#(#requirements,)*#actual==#native_value,
                        ensures final(#field_arg).instance_id()==self.id(),
                            final(#field_arg).value()==#public_update,#(#assertions,)*
                    {
                        ::vstd::prelude::use_type_invariant(&*#field_arg);
                        self.metadata.agrees(&#field_arg.metadata);
                        Self::#raw(&mut #field_arg.raw,#(#args,)*#actual);
                    }
                });
            }
            (MonoidStmtType::Withdraw, MonoidElt::OptionSome(None)) if binding.is_some() => {
                api.push(quote! {
                    proof fn #raw(tracked #slot:&mut Tracked<Option<#token>>,#(#params),*)->(tracked #result:#permission_ty)
                        requires old(#slot)@ is Some,
                            Protocol #expr::#local(old(#slot)@->Some_0.fragment(),Fragment #expr::empty(),
                                IMap::empty(),#(#args),*),
                        ensures final(#slot)@ is Some,
                            final(#slot)@->Some_0.loc()==old(#slot)@->Some_0.loc(),
                            final(#slot)@->Some_0.fragment()==old(#slot)@->Some_0.fragment().#setter(#raw_update),
                            #(#raw_assertions,)*
                    {
                        let tracked #owned=#slot.borrow_mut().tracked_take();
                        let #initial=#owned.fragment();
                        let tracked TransitionObservation #expr {
                            token:#next,withdrawn:#withdrawn,before:#before,after:#after,..
                        }=Protocol #expr::#observed(#owned,#(#args),*);
                        #(assert(#before.#cn==#initial.#rawgetters());)*
                        assert(#before.#storage_name is Some);
                        assert(#after.#storage_name is None);
                        assert(#withdrawn==IMap::empty().insert(0int,#before.#storage_name->Some_0));
                        let tracked #result=::vstd::resource::tsm_helpers::take_singleton(#withdrawn,0int);
                        *#slot=Tracked(Some(#next));
                        #result
                    }
                    pub proof fn #trname(tracked &self,#(#params,)*tracked #field_arg:&mut #name #types)->(tracked #result:#permission_ty)
                        requires #field_arg.instance_id()==self.id(),#(#requirements,)*
                        ensures final(#field_arg).instance_id()==self.id(),
                            final(#field_arg).value()==#public_update,#(#assertions,)*
                    {
                        ::vstd::prelude::use_type_invariant(&*#field_arg);
                        self.metadata.agrees(&#field_arg.metadata);
                        Self::#raw(&mut #field_arg.raw,#(#args),*)
                    }
                });
            }
            _ => {
                return Err(Error::new(
                    tr.name.span(),
                    "physical nominal facade currently requires singleton optional transfers",
                ))
            }
        }
    }
    Ok(quote! {
        #wrappers
        #(#attrs)* pub tracked struct Instance #decl #wc {
            metadata:#descriptor,context:Tracked<Option<#token>>,
        }
        impl #decl Instance #types #wc {
            #[verifier::type_invariant]
            spec fn invariant(self)->bool {
                ::vstd::prelude::imply(self.context@ is Some, {
                    self.context@->Some_0.loc()==self.metadata.value().#identity_field
                    && self.context@->Some_0.fragment()==#context_shape
                })
            }
            pub closed spec fn id(&self)->::vstd::resource::Loc {self.metadata.id()}
            #(pub closed spec fn #cn(&self)->#ct {self.metadata.value().#cn})*
            /// Cloning metadata conveys identity, never a new storage owner.
            pub proof fn clone(tracked &self)->(tracked out:Self)
                ensures out.id()==self.id(),#(out.#cn()==self.#cn(),)*
            {Self{metadata:self.metadata.clone(),context:Tracked(None)}}
            #(#api)*
        }
    })
}
