//! Field-specific checked ownership over the existing low-level resources.
use crate::ast::*;
use crate::field_access_visitor::visit_field_accesses;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

/// Append the facade inside the existing checked machine module.
pub fn append(output: TokenStream, api: TokenStream) -> Result<TokenStream, Error> {
    let mut module: verus_syn::ItemMod = verus_syn::parse2(output)?;
    let (_, items) = module.content.as_mut().unwrap();
    for item in items {
        if let verus_syn::Item::Macro(item) = item {
            if item
                .mac
                .path
                .segments
                .last()
                .is_some_and(|s| s.ident == "verus")
            {
                // Token observers are trait methods (`vstd::resource::tsm::TokenValue`).
                item.mac.tokens.extend(quote! {
                    #[allow(unused_imports)]
                    use ::vstd::resource::tsm::{TokenValue as _, TokenCount as _};
                });
                item.mac.tokens.extend(api);
                return Ok(quote! {#module});
            }
        }
    }
    Err(Error::new(
        module.ident.span(),
        "checked field facade module not found",
    ))
}

#[derive(Default)]
struct Straight {
    writes: HashMap<String, Expr>,
    requirements: Vec<Expr>,
    assertions: Vec<Expr>,
}
fn straight(stmt: &TransitionStmt, out: &mut Straight) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                straight(child, out)?;
            }
        }
        TransitionStmt::Update(_, name, e) | TransitionStmt::Initialize(_, name, e) => {
            if out.writes.insert(name.to_string(), e.clone()).is_some() {
                return Err(Error::new(
                    name.span(),
                    "field facade requires at most one write per field",
                ));
            }
        }
        TransitionStmt::Require(_, e) => out.requirements.push(e.clone()),
        TransitionStmt::Assert(_, e, _) => out.assertions.push(e.clone()),
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "field facade currently supports straight-line ordinary fields",
            ))
        }
    }
    Ok(())
}
fn local(
    e: &Expr,
    fields: &HashMap<String, Field>,
    old: bool,
    used: &mut HashSet<String>,
) -> Result<TokenStream, Error> {
    let mut e = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut e,
        |_, field, node| {
            let n = &field.name;
            used.insert(n.to_string());
            *node = Expr::Verbatim(if old {
                quote! {old(#n).value()}
            } else {
                quote! {#n.value()}
            });
        },
        &mut errors,
        fields,
    );
    if let Some(e) = errors.into_iter().next() {
        return Err(e);
    }
    Ok(quote! {#e})
}

fn fresh(sm: &SM, tr: &Transition, label: &str) -> Ident {
    let mut unavailable: HashSet<_> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .collect();
    // A substituted pre-field access can occur under a user closure/quantifier.
    // Reserve every expression identifier so its binders cannot capture a slot.
    fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
        for token in tokens {
            match token {
                proc_macro2::TokenTree::Ident(name) => { names.insert(name.to_string()); }
                proc_macro2::TokenTree::Group(group) => reserve(group.stream(), names),
                _ => {}
            }
        }
    }
    let mut flat = CountStraight::default();
    if count_straight(&tr.body, &mut flat).is_ok() {
        for expression in flat.ordinary.writes.values()
            .chain(flat.ordinary.requirements.iter())
            .chain(flat.ordinary.assertions.iter())
            .chain(flat.ops.values().map(|(_, expression)| expression))
        {
            reserve(quote! {#expression}, &mut unavailable);
        }
    }
    for suffix in 0.. {
        let name = format!("__tsm_field_{}_{}", label, suffix);
        if !unavailable.contains(&name) {
            return Ident::new(&name, Span::mixed_site());
        }
    }
    unreachable!()
}
fn validate(sm: &SM) -> Result<(), Error> {
    let mut methods = HashSet::from([
        "clone".to_string(),
        "id".to_string(),
        "invariant".to_string(),
    ]);
    for f in &sm.fields {
        if matches!(f.stype, ShardableType::Constant(_)) && !methods.insert(f.name.to_string()) {
            return Err(Error::new(
                f.name.span(),
                "constant getter conflicts with a generated field facade method",
            ));
        }
    }
    for tr in &sm.transitions {
        if !methods.insert(tr.name.to_string()) {
            return Err(Error::new(
                tr.name.span(),
                "transition name conflicts with a generated field facade method",
            ));
        }
    }
    for tr in &sm.transitions {
        if tr.kind == TransitionKind::Transition
            && !methods.insert(format!("__field_update_{}", tr.name))
        {
            return Err(Error::new(
                tr.name.span(),
                "transition name conflicts with a generated field facade method",
            ));
        }
        for p in &tr.params {
            if tr.kind != TransitionKind::Init
                && !(crate::verified_general::needed(sm)
                    && sm.fields.iter().all(|f| matches!(f.stype, ShardableType::Variable(_) | ShardableType::Constant(_))))
                && !(tr.kind == TransitionKind::Transition
                    && sm.fields.iter().any(|f| matches!(f.stype, ShardableType::Variable(_)))
                    && sm.fields.iter().all(|f| matches!(f.stype, ShardableType::Variable(_) | ShardableType::Constant(_)))
                    && sm.fields.iter().any(|f| matches!(f.stype, ShardableType::Constant(_)))
                    && !crate::verified_general::needed(sm))
                && sm.fields.iter().any(|f| f.name == p.name)
            {
                return Err(Error::new(
                    p.name.span(),
                    "transition parameter conflicts with a field-token argument",
                ));
            }
        }
    }
    Ok(())
}

pub fn output(sm: &SM) -> Result<TokenStream, Error> {
    if crate::verified_field_logical::needed(sm) {
        return crate::verified_field_logical::output(sm);
    }
    validate(sm)?;
    if crate::verified_general::needed(sm)
        && sm.fields.iter().all(|f| matches!(f.stype, ShardableType::Variable(_) | ShardableType::Constant(_)))
    {
        return crate::verified_field_control::output(sm);
    }
    if sm.fields.iter().any(|f| {
        !matches!(
            f.stype,
            ShardableType::Variable(_) | ShardableType::Constant(_) | ShardableType::Count
        )
    }) {
        return Err(Error::new(
            sm.name.span(),
            "field facade currently supports variable, constant and count fields",
        ));
    }
    let reserved = ["Instance", "Protocol", "State", "Fragment", "Token"];
    for f in &sm.fields {
        if reserved.contains(&f.name.to_string().as_str()) {
            return Err(Error::new(
                f.name.span(),
                "field token name conflicts with a generated machine type",
            ));
        }
    }
    if sm
        .fields
        .iter()
        .any(|f| !matches!(f.stype, ShardableType::Variable(_)))
        && sm.fields.iter().all(|f| {
            matches!(
                f.stype,
                ShardableType::Variable(_) | ShardableType::Constant(_) | ShardableType::Count
            )
        })
    {
        return count_output(sm);
    }
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let mut wrappers = vec![];
    let mut methods = vec![];
    for f in &sm.fields {
        let n = &f.name;
        let ty = f.get_type();
        let factory = format_ident!("field_{}", n);
        let value = format_ident!("value_{}", n);
        let owns = format_ident!("owns_{}", n);
        wrappers.push(quote!{
            #(#attrs)*
            #[allow(non_camel_case_types)]
            pub tracked struct #n #decl #wc { raw:Token #types }
            impl #decl #n #types #wc {
                #[verifier::type_invariant]
                spec fn invariant(self)->bool {
                    self.raw.fragment().#owns()
                    && self.raw.fragment()==Fragment #expr::#factory(self.raw.fragment().#value())
                }
                pub closed spec fn instance_id(&self)->::vstd::resource::Loc {self.raw.loc()}
                /// Borrow the actual current resource for low-level checked observation.
                pub proof fn borrow_token(tracked &self)->(tracked out:&Token #types)
                    ensures out.loc()==self.instance_id(),
                        out.fragment()==Fragment #expr::#factory(self.value())
                {::vstd::prelude::use_type_invariant(self);&self.raw}
                proof fn __from_token(tracked raw:Token #types)->(tracked out:Self)
                    requires raw.fragment().#owns(),raw.fragment()==Fragment #expr::#factory(raw.fragment().#value())
                    ensures out.instance_id()==raw.loc(),out.value()==raw.fragment().#value()
                {Self{raw}}
            }
            // A trait method, not an inherent one: see `vstd::resource::tsm::TokenValue`.
            impl #decl ::vstd::resource::tsm::TokenValue<#ty> for #n #types #wc {
                closed spec fn value(&self)->#ty {self.raw.fragment().#value()}
            }
        });
    }
    // An operation-free variable model exports nominal types only. Keeping a
    // Protocol token in Instance would create a type/associated-State cycle when
    // an original Variable payload is Instance itself. Metadata contains no
    // operational rights and has no public constructor or initializer here.
    if sm.transitions.is_empty()
        && !sm.fields.is_empty()
        && sm.fields.iter().all(|f| matches!(f.stype, ShardableType::Variable(_)))
    {
        return Ok(quote! {
            #(#wrappers)*
            #(#attrs)*
            pub tracked struct Instance #decl #wc {
                context: ::vstd::resource::tsm_context::Descriptor<::vstd::resource::Loc>,
                // Retain the original model type/variance link without using
                // a Protocol-associated token in the nominal identity type.
                ghost marker: core::marker::PhantomData<State #types>,
            }
            impl #decl Instance #types #wc {
                pub closed spec fn id(&self) -> ::vstd::resource::Loc {self.context.value()}
                pub proof fn clone(tracked &self) -> (tracked out: Self)
                    ensures out.id() == self.id(),
                {Self {context: self.context.clone(), marker: self.marker}}
            }
        });
    }
    for tr in &sm.transitions {
        let n = &tr.name;
        let mut flat = Straight::default();
        straight(&tr.body, &mut flat)?;
        let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
        let params: Vec<_> = tr
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let t = &p.ty;
                quote! {#n:#t}
            })
            .collect();
        if tr.kind == TransitionKind::Init {
            let names: Vec<_> = sm.fields.iter().map(|f| &f.name).collect();
            let init_values: Vec<_> = sm
                .fields
                .iter()
                .map(|f| {
                    flat.writes.get(&f.name.to_string()).ok_or_else(|| {
                        Error::new(f.name.span(), "missing facade initializer field")
                    })
                })
                .collect::<Result<_, _>>()?;
            let all = fresh(sm, tr, "initial");
            let context = fresh(sm, tr, "context");
            let remaining = fresh(sm, tr, "remaining");
            let takes: Vec<_> = names
                .iter()
                .map(|n| {
                    let take = format_ident!("take_{}", n);
                    quote! {let tracked (#n,#remaining)=Protocol #expr::#take(#remaining);}
                })
                .collect();
            let initial_requirements = &flat.requirements;
            let indices: Vec<_> = (1..=names.len()).map(verus_syn::Index::from).collect();
            methods.push(quote!{
                pub proof fn #n(#(#params),*)->(tracked out:(Tracked<Self>,#(Tracked<#names #types>),*))
                    requires #(#initial_requirements,)*
                    ensures #(out.#indices@.instance_id()==out.0@.id(),out.#indices@.value()==#init_values,)*
                {
                    let tracked #all=Protocol #expr::#n(#(#pn),*);
                    let tracked #context=#all.empty();
                    let tracked #remaining=#all;
                    #(#takes)*
                    (Tracked(Self{context:#context}),#(Tracked(#names #expr::__from_token(#names))),*)
                }
            });
            continue;
        }
        let mut used = HashSet::new();
        let requirements: Vec<_> = flat
            .requirements
            .iter()
            .map(|e| local(e, &fields, false, &mut used))
            .collect::<Result<_, _>>()?;
        let assertions: Vec<_> = flat
            .assertions
            .iter()
            .map(|e| local(e, &fields, tr.kind == TransitionKind::Transition, &mut used))
            .collect::<Result<_, _>>()?;
        let write_values: HashMap<_, _> = flat
            .writes
            .iter()
            .map(|(n, e)| Ok((n.clone(), local(e, &fields, true, &mut used)?)))
            .collect::<Result<_, Error>>()?;
        used.extend(flat.writes.keys().cloned());
        let selected: Vec<_> = sm
            .fields
            .iter()
            .filter(|f| used.contains(&f.name.to_string()))
            .collect();
        let names: Vec<_> = selected.iter().map(|f| &f.name).collect();
        if tr.kind == TransitionKind::Transition {
            if selected
                .iter()
                .any(|f| !flat.writes.contains_key(&f.name.to_string()))
            {
                return Err(Error::new(
                    n.span(),
                    "ordinary field facade currently requires every observed field to be updated",
                ));
            }
            // Keep references under fresh names while extracting the owned tokens.
            let refs: Vec<_> = names
                .iter()
                .map(|f| fresh(sm, tr, &format!("reference_{}", f)))
                .collect();
            let owned = fresh(sm, tr, "owned");
            let remaining = fresh(sm, tr, "remaining");
            let extraction: Vec<_> = names
                .iter()
                .zip(&refs)
                .map(|(f, r)| {
                    quote! {
                        let tracked #r=#f;
                        let tracked mut #f=#r.empty();
                        ::vstd::modes::tracked_swap(#r,&mut #f);
                    }
                })
                .collect();
            let mut combined = quote! {#owned};
            let mut joins = vec![];
            if let Some(first) = names.first() {
                joins.push(quote! {let tracked #owned=#first;});
                for field in names.iter().skip(1) {
                    joins.push(quote! {let tracked #owned=#owned.join(#field);});
                }
            } else {
                combined = quote! {self.context.empty()};
            }
            let split: Vec<_> = names
                .iter()
                .zip(&refs)
                .map(|(f, r)| {
                    let take = format_ident!("take_{}", f);
                    quote! {
                        let tracked (#f,#remaining)=Protocol #expr::#take(#remaining);
                        let tracked mut #f=#f;
                        ::vstd::modes::tracked_swap(#r,&mut #f);
                    }
                })
                .collect();
            let values: Vec<_> = names
                .iter()
                .map(|f| &write_values[&f.to_string()])
                .collect();
            let helper = format_ident!("__field_update_{}", n);
            let req = format_ident!("{}_requires", n);
            let post = format_ident!("{}_fragment", n);
            let mut current = quote! {Fragment #expr::empty()};
            let mut old_fragment = quote! {Fragment #expr::empty()};
            for field in &names {
                current = quote! {Fragment #expr::op(#current,#field.fragment())};
                old_fragment = quote! {Fragment #expr::op(#old_fragment,old(#field).fragment())};
            }
            let selects: Vec<_> = names
                .iter()
                .map(|f| format_ident!("select_{}", f))
                .collect();
            let opens: Vec<_> = names
                .iter()
                .map(|f| quote! {::vstd::prelude::use_type_invariant(&*#f);})
                .collect();
            let post_expr = quote! {Protocol #expr::#post(#old_fragment,#(#pn),*)};
            let first = names.first().ok_or_else(|| {
                Error::new(n.span(), "ordinary mutating facade needs an updated field")
            })?;
            methods.push(quote!{
                proof fn #helper(#(#params,)*#(tracked #names:&mut Token #types),*)
                    requires #(old(#names).loc()==old(#first).loc(),)* Protocol #expr::#req(#current,#(#pn),*)
                    ensures #(final(#names).loc()==old(#names).loc(),final(#names).fragment()==#post_expr.#selects(),)*
                {
                    #(#extraction)* #(#joins)*
                    let tracked #remaining=Protocol #expr::#n(#combined,#(#pn),*);
                    #(#split)*
                }
                pub proof fn #n(tracked &self,#(#params,)*#(tracked #names:&mut #names #types),*)
                    requires #(#names.instance_id()==self.id(),)* #(#requirements,)*
                    ensures #(final(#names).instance_id()==self.id(),final(#names).value()==#values,)*
                {
                    ::vstd::prelude::use_type_invariant(self);
                    #(#opens)*
                    Self::#helper(#(#pn,)*#(&mut #names.raw),*);
                }
            });
        } else {
            if names.len() > 3 {
                return Err(Error::new(
                    n.span(),
                    "ordinary property facade supports at most three observations",
                ));
            }
            let safety = format_ident!("{}_safety", n);
            let state = fresh(sm, tr, "state");
            let frame = fresh(sm, tr, "frame");
            let left = fresh(sm, tr, "left_frame");
            let right = fresh(sm, tr, "right_frame");
            let third = fresh(sm, tr, "third_frame");
            let completion = match names.as_slice() {
                [] => {
                    quote! {self.context.validate();let (#frame,#state)=choose|#frame:Fragment #types,#state:State #types|#state.invariant() && Fragment #expr::op(self.context.fragment(),#frame)==Protocol #expr::embed(#state);}
                }
                [a] => {
                    quote! {#a.raw.validate();let (#frame,#state)=choose|#frame:Fragment #types,#state:State #types|#state.invariant() && Fragment #expr::op(#a.raw.fragment(),#frame)==Protocol #expr::embed(#state);}
                }
                [a, b] => quote! {let (#state,#left,#right)=#a.raw.compatible_with(&#b.raw);},
                [a, b, c] => {
                    quote! {let (#state,#left,#right,#third)=#a.raw.compatible_3(&#b.raw,&#c.raw);}
                }
                _ => unreachable!(),
            };
            let opens:Vec<_>=names.iter().map(|f|quote!{::vstd::prelude::use_type_invariant(#f);assert(#state.#f==#f.value());}).collect();
            methods.push(quote! {
                pub proof fn #n(tracked &self,#(#params,)*#(tracked #names:&#names #types),*)
                    requires #(#names.instance_id()==self.id(),)* #(#requirements,)*
                    ensures #(#assertions,)*
                {#completion #(#opens)* State #expr::#safety(#state,#(#pn),*);}
            });
        }
    }
    Ok(quote! {
        #(#wrappers)*
        #(#attrs)*
        pub tracked struct Instance #decl #wc {context:Token #types}
        impl #decl Instance #types #wc {
            #[verifier::type_invariant]
            spec fn invariant(self)->bool {self.context.fragment()==Fragment #expr::empty()}
            pub closed spec fn id(&self)->::vstd::resource::Loc {self.context.loc()}
            pub proof fn clone(tracked &self)->(tracked out:Self)
                ensures out.id()==self.id()
            {::vstd::prelude::use_type_invariant(self);Fragment #expr::op_unit(self.context.fragment());let tracked context=self.context.duplicate();Self{context}}
            #(#methods)*
        }
    })
}

// Private staged Count/Constant facade emission, sharing the checked low-level API.
fn count_output(sm: &SM) -> Result<TokenStream, Error> {
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let frag = quote! {Fragment #types};
    let token = quote! {Token #types};
    let protocol = quote! {Protocol #expr};
    let constants: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(_)))
        .collect();
    let owners: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| !matches!(f.stype, ShardableType::Constant(_)))
        .collect();
    let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
    let getters: Vec<_> = cn.iter().map(|n| format_ident!("value_{}", n)).collect();
    let cty: Vec<_> = constants.iter().map(|f| f.get_type()).collect();
    let context_shape = constants
        .iter()
        .fold(quote! {Fragment #expr::empty()}, |out, f| {
            let setter = format_ident!("with_{}", f.name);
            let getter = format_ident!("value_{}", f.name);
            quote! {#out.#setter(self.context.fragment().#getter())}
        });
    let mut wrappers = vec![];
    let mut methods = vec![];
    for f in &sm.fields {
        let n = &f.name;
        let factory = format_ident!("field_{}", n);
        let getter = format_ident!("value_{}", n);
        let ty = f.get_type();
        let name = if matches!(f.stype, ShardableType::Count) {
            format_ident!("count")
        } else {
            format_ident!("value")
        };
        let observer = if matches!(f.stype, ShardableType::Count) {
            quote! {::vstd::resource::tsm::TokenCount}
        } else {
            quote! {::vstd::resource::tsm::TokenValue<#ty>}
        };
        let tag = if matches!(f.stype, ShardableType::Count) {
            quote! {true}
        } else {
            let owns = format_ident!("owns_{}", n);
            quote! {self.raw.fragment().#owns()}
        };
        let rawtag = if matches!(f.stype, ShardableType::Count) {
            quote! {true}
        } else {
            let owns = format_ident!("owns_{}", n);
            quote! {raw.fragment().#owns()}
        };
        let mono = if crate::verified_field_monoids::supported(&f.stype) {
            crate::verified_field_monoids::methods(f, &frag, &token, &protocol)?
        } else {
            quote! {}
        };
        wrappers.push(quote!{
            #(#attrs)* #[allow(non_camel_case_types)] pub tracked struct #n #decl #wc {raw:Token #types}
            impl #decl #n #types #wc {
                #[verifier::type_invariant] spec fn invariant(self)->bool {#tag && self.raw.fragment()==Fragment #expr::#factory(self.raw.fragment().#getter())}
                pub closed spec fn instance_id(&self)->::vstd::resource::Loc {self.raw.loc()}
                pub proof fn borrow_token(tracked &self)->(tracked out:&Token #types)
                    ensures out.loc()==self.instance_id(),out.fragment()==Fragment #expr::#factory(self.#name())
                {::vstd::prelude::use_type_invariant(self);&self.raw}
                proof fn __from_token(tracked raw:Token #types)->(tracked out:Self)
                    requires #rawtag,raw.fragment()==Fragment #expr::#factory(raw.fragment().#getter())
                    ensures out.instance_id()==raw.loc(),out.#name()==raw.fragment().#getter()
                {Self{raw}}
                #mono
            }
            // A trait method, not an inherent one: see `vstd::resource::tsm::TokenValue`.
            impl #decl #observer for #n #types #wc {
                closed spec fn #name(&self)->#ty {self.raw.fragment().#getter()}
            }
        });
    }
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    for tr in &sm.transitions {
        let n = &tr.name;
        let mut flat = CountStraight::default();
        count_straight(&tr.body, &mut flat)?;
        let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
        let params: Vec<_> = tr
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let ty = &p.ty;
                quote! {#n:#ty}
            })
            .collect();
        if tr.kind == TransitionKind::Init {
            let names: Vec<_> = owners.iter().map(|f| &f.name).collect();
            let accessor: Vec<_> = owners
                .iter()
                .map(|f| {
                    if matches!(f.stype, ShardableType::Count) {
                        format_ident!("count")
                    } else {
                        format_ident!("value")
                    }
                })
                .collect();
            let values: Vec<_> = owners
                .iter()
                .map(|f| &flat.ordinary.writes[&f.name.to_string()])
                .collect();
            let constvalues: Vec<_> = constants
                .iter()
                .map(|f| &flat.ordinary.writes[&f.name.to_string()])
                .collect();
            let remaining = fresh(sm, tr, "remaining");
            let initial = fresh(sm, tr, "initial");
            let takes: Vec<_> = names
                .iter()
                .map(|f| {
                    let take = format_ident!("take_{}", f);
                    quote! {let tracked (#f,#remaining)=Protocol #expr::#take(#remaining);}
                })
                .collect();
            let initial_requirements = &flat.ordinary.requirements;
            let indices: Vec<_> = (1..=names.len()).map(verus_syn::Index::from).collect();
            methods.push(quote!{
                pub proof fn #n(#(#params),*)->(tracked out:(Tracked<Self>,#(Tracked<#names #types>),*))
                    requires #(#initial_requirements,)*
                    ensures #(out.#indices@.instance_id()==out.0@.id(),out.#indices@.#accessor()==#values,)* #(out.0@.#cn()==#constvalues,)*
                {let tracked #initial=Protocol #expr::#n(#(#pn),*);let tracked #remaining=#initial;#(#takes)*
                    (Tracked(Self{context:#remaining}),#(Tracked(#names #expr::__from_token(#names))),*)}
            });
            continue;
        }
        let mut used = HashSet::new();
        let requirements: Vec<_> = flat
            .ordinary
            .requirements
            .iter()
            .map(|e| count_local(e, &fields, false, &mut used))
            .collect::<Result<_, _>>()?;
        let assertions: Vec<_> = flat
            .ordinary
            .assertions
            .iter()
            .map(|e| count_local(e, &fields, tr.kind == TransitionKind::Transition, &mut used))
            .collect::<Result<_, _>>()?;
        let writes: HashMap<_, _> = flat
            .ordinary
            .writes
            .iter()
            .map(|(n, e)| Ok((n.clone(), count_local(e, &fields, true, &mut used)?)))
            .collect::<Result<_, Error>>()?;
        for (_, (_, e)) in &flat.ops {
            count_local(e, &fields, false, &mut used)?;
        }
        if tr.kind == TransitionKind::Transition {
            for (field, (op, _)) in &flat.ops {
                if !matches!(fields[field].stype, ShardableType::Count)
                    || !matches!(op, MonoidStmtType::Remove | MonoidStmtType::Add(false))
                {
                    return Err(Error::new(
                        n.span(),
                        "Count facade currently supports consuming and producing count owners",
                    ));
                }
            }
            for field in flat.ordinary.writes.keys() {
                if !matches!(fields[field].stype, ShardableType::Variable(_)) {
                    return Err(Error::new(
                        n.span(),
                        "Count facade ordinary updates require variable fields",
                    ));
                }
            }
            for field in &used {
                if !matches!(fields[field].stype, ShardableType::Constant(_))
                    && !flat.ordinary.writes.contains_key(field)
                    && !flat.ops.contains_key(field)
                {
                    return Err(Error::new(
                        n.span(),
                        "Count facade requires every ordinary observation to be updated",
                    ));
                }
            }
            let vars: Vec<_> = sm
                .fields
                .iter()
                .filter(|f| flat.ordinary.writes.contains_key(&f.name.to_string()))
                .collect();
            let vn: Vec<_> = vars.iter().map(|f| &f.name).collect();
            let removed: Vec<_> = sm
                .fields
                .iter()
                .filter(|f| {
                    flat.ops
                        .get(&f.name.to_string())
                        .is_some_and(|(op, _)| matches!(op, MonoidStmtType::Remove))
                })
                .collect();
            let added: Vec<_> = sm
                .fields
                .iter()
                .filter(|f| {
                    flat.ops
                        .get(&f.name.to_string())
                        .is_some_and(|(op, _)| matches!(op, MonoidStmtType::Add(_)))
                })
                .collect();
            // Constant/Variable updates use a borrowed agreement context and restore
            // every actual variable owner; the context is not consumed or recreated.
            if added.is_empty() && flat.ops.is_empty() && !vars.is_empty() {
                // Keep field/type labels and user parameters unchanged. Only
                // generated tracked bindings get fresh names, including in pre accesses.
                let bindings: HashMap<_, _> = vars.iter().map(|f| (f.name.to_string(), fresh(sm, tr, &format!("argument_{}", f.name)))).collect();
                let slots: Vec<_> = vn.iter().map(|f| &bindings[&f.to_string()]).collect();
                let requirements: Vec<_> = flat.ordinary.requirements.iter().map(|e| count_local_with_names(e, &fields, false, &mut used, &bindings)).collect::<Result<_, _>>()?;
                let assertions: Vec<_> = flat.ordinary.assertions.iter().map(|e| count_local_with_names(e, &fields, true, &mut used, &bindings)).collect::<Result<_, _>>()?;
                let values: Vec<_> = vn.iter().map(|f| count_local_with_names(&flat.ordinary.writes[&f.to_string()], &fields, true, &mut used, &bindings)).collect::<Result<_, _>>()?;
                let helper = format_ident!("__field_update_{}", n);
                let shared = format_ident!("{}_with_shared", n);
                let req = format_ident!("{}_shared_requires", n);
                let effect = format_ident!("{}_owned_fragment", n);
                let facts = format_ident!("{}_facts", n);
                let refs: Vec<_> = vn.iter().map(|f| fresh(sm, tr, &format!("reference_{}", f))).collect();
                let owned = fresh(sm, tr, "owned");
                let remaining = fresh(sm, tr, "remaining");
                let context = fresh(sm, tr, "context");
                let extraction: Vec<_> = slots.iter().zip(&refs).map(|(f,r)| quote! {
                    let tracked #r=#f;let tracked mut #f=#r.empty();
                    ::vstd::modes::tracked_swap(#r,&mut #f);
                }).collect();
                let first=slots[0];
                let joins:Vec<_>=slots.iter().skip(1).map(|f|quote!{let tracked #owned=#owned.join(#f);}).collect();
                let takes:Vec<_>=vn.iter().zip(&slots).zip(&refs).map(|((f,slot),r)|{
                    let take=format_ident!("take_{}",f);quote!{
                        let tracked (#slot,#remaining)=Protocol #expr::#take(#remaining);
                        let tracked mut #slot=#slot;::vstd::modes::tracked_swap(#r,&mut #slot);
                    }
                }).collect();
                let mut combined=quote!{Fragment #expr::empty()};
                let mut before=combined.clone();
                for slot in &slots {
                    combined=quote!{Fragment #expr::op(#combined,#slot.fragment())};
                    before=quote!{Fragment #expr::op(#before,old(#slot).fragment())};
                }
                let selects:Vec<_>=vn.iter().map(|f|format_ident!("select_{}",f)).collect();
                let opens:Vec<_>=slots.iter().map(|f|quote!{::vstd::prelude::use_type_invariant(&*#f);}).collect();
                let post_expr=quote!{Protocol #expr::#effect(#before,#context.fragment(),#(#pn),*)};
                methods.push(quote!{
                    proof fn #helper(tracked #context:&Token #types,#(#params,)*#(tracked #slots:&mut Token #types),*)
                        requires #(old(#slots).loc()==#context.loc(),)*Protocol #expr::#req(#combined,#context.fragment(),#(#pn),*)
                        ensures #(final(#slots).loc()==#context.loc(),final(#slots).fragment()==#post_expr.#selects(),)*Protocol #expr::#facts(Fragment #expr::op(#before,#context.fragment()),#(#pn),*)
                    {#(#extraction)*let tracked #owned=#first;#(#joins)*let tracked #remaining=Protocol #expr::#shared(#owned,#context,#(#pn),*);#(#takes)*}
                    pub proof fn #n(tracked &self,#(#params,)*#(tracked #slots:&mut #vn #types),*)
                        requires #(#slots.instance_id()==self.id(),)*#(#requirements,)*
                        ensures #(final(#slots).instance_id()==self.id(),final(#slots).value()==#values,)*#(#assertions,)*
                    {::vstd::prelude::use_type_invariant(self);#(#opens)*Self::#helper(&self.context,#(#pn,)*#(&mut #slots.raw),*);}
                });
                continue;
            }
            if added.len() != 1 || vars.is_empty() {
                return Err(Error::new(
                    n.span(),
                    "Count facade requires an ordinary update and one produced count field",
                ));
            }
            let rn: Vec<_> = removed.iter().map(|f| &f.name).collect();
            let an = &added[0].name;
            let remvalues: Vec<_> = removed
                .iter()
                .map(|f| count_local(&flat.ops[&f.name.to_string()].1, &fields, false, &mut used))
                .collect::<Result<_, _>>()?;
            let addvalue = count_local(&flat.ops[&an.to_string()].1, &fields, true, &mut used)?;
            let values: Vec<_> = vn.iter().map(|n| &writes[&n.to_string()]).collect();
            let helper = format_ident!("__field_update_{}", n);
            let shared = format_ident!("{}_with_shared", n);
            let req = format_ident!("{}_shared_requires", n);
            let effect = format_ident!("{}_owned_fragment", n);
            let facts = format_ident!("{}_facts", n);
            let refs: Vec<_> = vn
                .iter()
                .map(|f| fresh(sm, tr, &format!("reference_{}", f)))
                .collect();
            let owned = fresh(sm, tr, "owned");
            let remainder = fresh(sm, tr, "remaining");
            let returned = fresh(sm, tr, "returned");
            let context = fresh(sm, tr, "context");
            let extraction:Vec<_>=vn.iter().zip(&refs).map(|(f,r)|quote!{let tracked #r=#f;let tracked mut #f=#r.empty();::vstd::modes::tracked_swap(#r,&mut #f);}).collect();
            let input: Vec<_> = vn.iter().chain(rn.iter()).collect();
            let first = input[0];
            let joins: Vec<_> = input
                .iter()
                .skip(1)
                .map(|f| quote! {let tracked #owned=#owned.join(#f);})
                .collect();
            let takes:Vec<_>=vn.iter().zip(&refs).map(|(f,r)|{let take=format_ident!("take_{}",f);quote!{let tracked (#f,#remainder)=Protocol #expr::#take(#remainder);let tracked mut #f=#f;::vstd::modes::tracked_swap(#r,&mut #f);}}).collect();
            let takeadd = format_ident!("take_{}", an);
            let mut combined = quote! {Fragment #expr::empty()};
            let mut before = combined.clone();
            for f in &vn {
                combined = quote! {Fragment #expr::op(#combined,#f.fragment())};
                before = quote! {Fragment #expr::op(#before,old(#f).fragment())};
            }
            for f in &rn {
                combined = quote! {Fragment #expr::op(#combined,#f.fragment())};
                before = quote! {Fragment #expr::op(#before,#f.fragment())};
            }
            let selects: Vec<_> = vn.iter().map(|f| format_ident!("select_{}", f)).collect();
            let selectadd = format_ident!("select_{}", an);
            let mut opens: Vec<_> = vn
                .iter()
                .map(|f| quote! {::vstd::prelude::use_type_invariant(&*#f);})
                .collect();
            opens.extend(
                rn.iter()
                    .map(|f| quote! {::vstd::prelude::use_type_invariant(&#f);}),
            );
            let post_expr = quote! {Protocol #expr::#effect(#before,#context.fragment(),#(#pn),*)};
            methods.push(quote!{
                proof fn #helper(tracked #context:&Token #types,#(#params,)*#(tracked #vn:&mut Token #types,)*#(tracked #rn:Token #types),*)->(tracked #returned:Token #types)
                    requires #(#rn.loc()==#context.loc(),)*#(old(#vn).loc()==#context.loc(),)*Protocol #expr::#req(#combined,#context.fragment(),#(#pn),*)
                    ensures #(final(#vn).loc()==#context.loc(),final(#vn).fragment()==#post_expr.#selects(),)* #returned.loc()==#context.loc(),#returned.fragment()==#post_expr.#selectadd(),Protocol #expr::#facts(Fragment #expr::op(#before,#context.fragment()),#(#pn),*)
                {#(#extraction)*let tracked #owned=#first;#(#joins)*let tracked #remainder=Protocol #expr::#shared(#owned,#context,#(#pn),*);#(#takes)*let tracked (#returned,#remainder)=Protocol #expr::#takeadd(#remainder);#returned}
                pub proof fn #n(tracked &self,#(#params,)*#(tracked #vn:&mut #vn #types,)*#(tracked #rn:#rn #types),*)->(tracked out:#an #types)
                    requires #(#vn.instance_id()==self.id(),)*#(#rn.instance_id()==self.id(),#rn.count()==#remvalues,)*#(#requirements,)*
                    ensures #(final(#vn).instance_id()==self.id(),final(#vn).value()==#values,)*out.instance_id()==self.id(),out.count()==#addvalue,#(#assertions,)*
                {::vstd::prelude::use_type_invariant(self);#(#opens)*let tracked #returned=Self::#helper(&self.context,#(#pn,)*#(&mut #vn.raw,)*#(#rn.raw),*);#an #expr::__from_token(#returned)}
            });
        } else {
            // Properties use a single common completion with independent frames.
            let selected: Vec<_> = owners
                .iter()
                .filter(|f| {
                    used.contains(&f.name.to_string()) || flat.ops.contains_key(&f.name.to_string())
                })
                .collect();
            if selected.is_empty() || selected.len() > 2 {
                return Err(Error::new(n.span(),"Count property facade currently needs one or two owner observations plus constant context"));
            }
            let names: Vec<_> = selected.iter().map(|f| &f.name).collect();
            let a = names[0];

            let state = fresh(sm, tr, "state");
            let frame = fresh(sm, tr, "frame");
            let left = fresh(sm, tr, "left");
            let right = fresh(sm, tr, "right");
            let completion = if names.len() == 1 {
                quote!{let (#state,#frame,#left)=self.context.compatible_with(&#a.raw);}
            } else {
                let b=names[1];
                quote!{let (#state,#frame,#left,#right)=self.context.compatible_3(&#a.raw,&#b.raw);}
            };
            let observes: Vec<_> = selected
                .iter()
                .map(|f| {
                    let n = &f.name;
                    if matches!(f.stype, ShardableType::Count) {
                        quote! {assert(#n.count()<=#state.#n);}
                    } else {
                        quote! {assert(#state.#n==#n.value());}
                    }
                })
                .collect();
            let have: Vec<_> = flat
                .ops
                .iter()
                .map(|(key, (op, e))| {
                    let n = &fields[key].name;
                    if !matches!(op, MonoidStmtType::Have) {
                        return Err(Error::new(
                            n.span(),
                            "Count property requires Have operations",
                        ));
                    }
                    let e = count_local(e, &fields, false, &mut used)?;
                    Ok(quote! {#n.count()>=#e})
                })
                .collect::<Result<_, Error>>()?;
            let safety = format_ident!("{}_safety", n);
            methods.push(quote!{
                pub proof fn #n(tracked &self,#(#params,)*#(tracked #names:&#names #types),*)
                    requires #(#names.instance_id()==self.id(),)*#(#requirements,)*#(#have,)*ensures #(#assertions,)*
                {::vstd::prelude::use_type_invariant(self);#(::vstd::prelude::use_type_invariant(#names);)*#completion #(assert(#state.#cn==self.#cn());)*#(#observes)*State #expr::#safety(#state,#(#pn),*);}
            });
        }
    }
    Ok(
        quote! {#(#wrappers)*#(#attrs)*pub tracked struct Instance #decl #wc {context:Token #types}
            impl #decl Instance #types #wc {
                #[verifier::type_invariant] spec fn invariant(self)->bool {self.context.fragment()==#context_shape #(&& self.context.fragment().#getters()==self.#cn())*}
                pub closed spec fn id(&self)->::vstd::resource::Loc {self.context.loc()}
                #(pub closed spec fn #cn(&self)->#cty {self.context.fragment().#getters()})*
                pub proof fn clone(tracked &self)->(tracked out:Self) ensures out.id()==self.id(),#(out.#cn()==self.#cn(),)*
                {::vstd::prelude::use_type_invariant(self);let tracked context=self.context.duplicate();Self{context}}
                #(#methods)*
            }
        },
    )
}
#[derive(Default)]
struct CountStraight {
    ordinary: Straight,
    ops: HashMap<String, (MonoidStmtType, Expr)>,
}
fn count_straight(stmt: &TransitionStmt, out: &mut CountStraight) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for c in children {
                count_straight(c, out)?;
            }
        }
        TransitionStmt::Split(_, kind, children) => {
            if let SplitKind::Special(n, op, _, None) = &**kind {
                if let MonoidElt::General(e) = &op.elt {
                    if out
                        .ops
                        .insert(n.to_string(), (op.stmt, e.clone()))
                        .is_some()
                    {
                        return Err(Error::new(
                            n.span(),
                            "Count facade requires one operation per field",
                        ));
                    }
                    for c in children {
                        count_straight(c, out)?;
                    }
                    return Ok(());
                }
            }
            return Err(Error::new(
                *stmt.get_span(),
                "Count facade currently supports straight-line count operands",
            ));
        }
        _ => straight(stmt, &mut out.ordinary)?,
    }
    Ok(())
}
fn count_local(
    e: &Expr,
    fields: &HashMap<String, Field>,
    old: bool,
    used: &mut HashSet<String>,
) -> Result<TokenStream, Error> {
    count_local_with_names(e, fields, old, used, &HashMap::new())
}
fn count_local_with_names(
    e: &Expr,
    fields: &HashMap<String, Field>,
    old: bool,
    used: &mut HashSet<String>,
    bindings: &HashMap<String, Ident>,
) -> Result<TokenStream, Error> {
    let mut e = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut e,
        |_, field, node| {
            let n = &field.name;
            used.insert(n.to_string());
            let slot = bindings.get(&n.to_string()).unwrap_or(n);
            *node = Expr::Verbatim(match field.stype {
                ShardableType::Constant(_) => quote! {self.#n()},
                ShardableType::Count => quote! {#slot.count()},
                _ => {
                    if old {
                        quote! {old(#slot).value()}
                    } else {
                        quote! {#slot.value()}
                    }
                }
            });
        },
        &mut errors,
        fields,
    );
    if let Some(e) = errors.into_iter().next() {
        return Err(e);
    }
    Ok(quote! {#e})
}
