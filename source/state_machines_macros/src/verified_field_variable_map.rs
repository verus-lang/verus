//! Checked nominal authority and singleton-map ownership over logical resources.
use crate::ast::*;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote, ToTokens};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident, Pat};

fn profile(sm: &SM) -> Option<(&Field, &Field)> {
    if sm.fields.len() != 2 {
        return None;
    }
    let authority = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::Variable(..)))?;
    let entries = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::Map(..)))?;
    let ShardableType::Variable(verus_syn::Type::Path(path)) = &authority.stype else {
        return None;
    };
    let ShardableType::Map(k, v) = &entries.stype else {
        return None;
    };
    let segment = path.path.segments.last()?;
    if segment.ident != "Map" {
        return None;
    }
    let verus_syn::PathArguments::AngleBracketed(args) = &segment.arguments else {
        return None;
    };
    let actual = args.args.to_token_stream().to_string();
    (actual == quote! {#k,#v}.to_string()).then_some((authority, entries))
}
pub fn supports(sm: &SM) -> bool {
    profile(sm).is_some()
}
pub fn aliases(sm: &SM) -> Result<TokenStream, Error> {
    let (g, _) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&g);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let mut aliases = TokenStream::new();
    for entries in sm.fields.iter().filter(|field|
        matches!(field.stype, ShardableType::Map(..) | ShardableType::IMap(..)))
    {
        let alias = format_ident!("{}_map", entries.name);
        let collection = format_ident!("{}_collection", entries.name);
        let normalized = alias.to_string().trim_start_matches("r#").to_string();
        if sm.fields.iter().any(|field| field.name.to_string().trim_start_matches("r#") == normalized)
            || sm.generics.as_ref().is_some_and(|generics| generics.params.iter().any(|parameter|
                matches!(parameter, verus_syn::GenericParam::Type(parameter)
                    if parameter.ident.to_string().trim_start_matches("r#") == normalized)))
        {
            let message = if profile(sm).is_some() {
                "authority-map collection alias conflicts with a field or generic type"
            } else {
                "map collection alias conflicts with a field or generic type"
            };
            return Err(Error::new(entries.name.span(), message));
        }
        aliases.extend(quote! {#[allow(non_camel_case_types)] pub type #alias #decl #wc = #collection #types;});
    }
    Ok(aliases)
}
#[derive(Default)]
struct Operations {
    update: Option<(Ident, Expr)>,
    special: Vec<(Ident, SpecialOp, Option<Box<Pat>>)>,
    assertions: Vec<Expr>,
}
fn collect(stmt: &TransitionStmt, out: &mut Operations) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                collect(child, out)?;
            }
        }
        TransitionStmt::Update(_, name, e) if out.update.is_none() => {
            out.update = Some((name.clone(), e.clone()))
        }
        TransitionStmt::Assert(_, e, _) => out.assertions.push(e.clone()),
        TransitionStmt::Split(_, split, children) => {
            let SplitKind::Special(name, op, _, binding) = &**split else {
                return Err(Error::new(
                    *stmt.get_span(),
                    "authority-map adapter requires straight-line singleton operations",
                ));
            };
            out.special
                .push((name.clone(), op.clone(), binding.clone()));
            for child in children {
                collect(child, out)?;
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "unsupported authority-map native operation",
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
fn lower(sm: &SM, authority: &Field, expression: &Expr, value: TokenStream) -> Result<Expr, Error> {
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let mut e = expression.clone();
    let mut errors = vec![];
    crate::field_access_visitor::visit_field_accesses(
        &mut e,
        |errors, field, node| {
            if field.name == authority.name {
                *node = verus_syn::parse2(value.clone()).unwrap();
            } else {
                errors.push(Error::new(
                    field.name.span(),
                    "authority-map native facts cannot expose an unowned full map",
                ));
            }
        },
        &mut errors,
        &fields,
    );
    match errors.into_iter().next() {
        Some(e) => Err(e),
        None => Ok(e),
    }
}
pub fn method(sm: &SM, tr: &Transition) -> Result<TokenStream, Error> {
    let (authority, entries) = profile(sm).unwrap();
    let mut ops = Operations::default();
    collect(&tr.body, &mut ops)?;
    let (g, _) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&g);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let mut occupied = HashSet::new();
    let original_fields = &sm.fields_named_ast;
    let original_generics = &sm.generics;
    reserve(quote! {#original_fields #original_generics}, &mut occupied);
    for transition in &sm.transitions {
        occupied.insert(transition.name.to_string());
        for p in &transition.params {
            let n = &p.name;
            let t = &p.ty;
            reserve(quote! {#n #t}, &mut occupied);
        }
        crate::verified_field_storage_map_pair::reserve_stmt(&transition.body, &mut occupied);
    }
    let mut fresh = |label: &str| {
        let mut name = format!("__tsm_authority_map_{label}");
        while occupied.contains(&name) {
            name.push('_');
        }
        occupied.insert(name.clone());
        Ident::new(&name, Span::mixed_site())
    };
    let owner = fresh("authority");
    let entry = fresh("entry");
    let slot = fresh("slot");
    let raw_entry = fresh("raw_entry");
    let current = fresh("current");
    let before = fresh("before");
    let pre = fresh("pre");
    let post = fresh("post");
    let frame = fresh("frame");
    let result = fresh("result");
    let a = &authority.name;
    let e = &entries.name;
    let ShardableType::Map(key_type, value_type) = &entries.stype else {
        unreachable!()
    };
    let af = format_ident!("field_{a}");
    let ef = format_ident!("field_{e}");
    let av = format_ident!("value_{a}");
    let ev = format_ident!("value_{e}_at");
    let eo = format_ident!("owns_{e}_at");
    let take = format_ident!("take_{a}");
    let name = &tr.name;
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
    if tr.kind == TransitionKind::Property {
        if ops.update.is_some() || ops.special.len() != 1 {
            return Err(Error::new(
                name.span(),
                "authority-map property requires one singleton Have",
            ));
        }
        let (field, op, binding) = &ops.special[0];
        let MonoidElt::SingletonKV(key, None) = &op.elt else {
            return Err(Error::new(
                name.span(),
                "authority-map Have requires a bound singleton value",
            ));
        };
        let Some(binding) = binding else {
            return Err(Error::new(
                name.span(),
                "authority-map Have requires a binding",
            ));
        };
        if field != e || !op.is_have() {
            return Err(Error::new(
                name.span(),
                "authority-map property borrows its map entry",
            ));
        }
        let facts: Vec<_> = ops
            .assertions
            .iter()
            .map(|x| lower(sm, authority, x, quote! {#owner.value()}))
            .collect::<Result<_, _>>()?;
        let safety = format_ident!("{name}_safety");
        return Ok(quote! {
            pub proof fn #name(tracked &self,#(#params,)*tracked #owner:&#a #types,tracked #entry:&#e #types)
                requires #owner.instance_id()==self.id(),#entry.instance_id()==self.id(),#entry.key()==#key,
                ensures {let #binding=#entry.value();true #(&& #facts)*},
            {
                ::vstd::prelude::use_type_invariant(#owner);
                ::vstd::prelude::use_type_invariant(#entry);
                let (#pre,#frame,#post)=#owner.raw.compatible_with(&#entry.raw);
                assert(#pre.#a==#owner.value());
                ::vstd::resource::tsm_collections::map_owned_frame(
                    #entry.raw.fragment().#e,#post.#e,#pre.#e.to_imap(),#key,#entry.value());
                State #expr::#safety(#pre,#(#pn),*);
                let #binding=#entry.value();
                #(assert(#facts);)*
            }
        });
    }
    if tr.kind != TransitionKind::Transition || ops.special.len() != 2 || !ops.assertions.is_empty()
    {
        return Err(Error::new(
            name.span(),
            "authority-map exchange requires one update and singleton replacement",
        ));
    }
    let Some((updated, update)) = &ops.update else {
        return Err(Error::new(
            name.span(),
            "authority-map exchange needs its variable update",
        ));
    };
    let (removed, remove, binding) = &ops.special[0];
    let (added, add, add_binding) = &ops.special[1];
    let (MonoidElt::SingletonKV(key, None), MonoidElt::SingletonKV(add_key, Some(value))) =
        (&remove.elt, &add.elt)
    else {
        return Err(Error::new(
            name.span(),
            "authority-map exchange needs bound singleton removal and addition",
        ));
    };
    if updated != a
        || removed != e
        || added != e
        || !remove.is_remove()
        || !add.is_add()
        || key.to_token_stream().to_string() != add_key.to_token_stream().to_string()
        || add_binding.is_some()
        || !binding
            .as_ref()
            .is_some_and(|p| matches!(&**p, Pat::Wild(_)))
    {
        return Err(Error::new(
            name.span(),
            "authority-map exchange keeps its singleton key and discards the old binding",
        ));
    }
    let updated_value = lower(sm, authority, update, quote! {old(#owner).value()})?;
    let raw_value = lower(sm, authority, update, quote! {#before.#av()})?;
    let req = format_ident!("{name}_requires");
    let enabled = format_ident!("{name}_enabled");
    let owners = format_ident!("{name}_owners_enabled");
    let strong = format_ident!("{name}_strong");
    let owned_post = format_ident!("{name}_owned_post");
    let helper = fresh("replace");
    let point = fresh("point");
    Ok(quote! {
        proof fn #helper(#(#params,)*tracked #slot:&mut Token #types,tracked #raw_entry:Token #types)->(tracked #result:Token #types)
            requires old(#slot).loc()==#raw_entry.loc(),
                old(#slot).fragment()==Fragment #expr::#af(old(#slot).fragment().#av()),
                #raw_entry.fragment().#eo(#key),
                #raw_entry.fragment()==Fragment #expr::#ef(Map::<#key_type,#value_type>::empty().insert(#key,#raw_entry.fragment().#ev(#key))),
            ensures final(#slot).loc()==old(#slot).loc(),
                final(#slot).fragment()==Fragment #expr::#af({let #before=old(#slot).fragment();#raw_value}),
                #result.loc()==old(#slot).loc(),
                #result.fragment()==Fragment #expr::#ef(Map::<#key_type,#value_type>::empty().insert(#key,#value)),
        {
            let tracked mut #current=#slot.empty();
            ::vstd::modes::tracked_swap(#slot,&mut #current);
            let tracked #current=#current.join(#raw_entry);
            let #before=#current.fragment();
            #before.op_unit();
            assert(Protocol #expr::#req(#before,Fragment #expr::unit(),#(#pn),*)) by {
                assert forall|#frame:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,Fragment #expr::unit()),#frame)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#pn),*)&&State #expr::#owners(#pre,#before,Fragment #expr::unit(),#(#pn),*) by {
                        assert(#pre.#a==#before.#av());
                        ::vstd::resource::tsm_collections::map_owned_frame(#before.#e,#frame.#e,#pre.#e.to_imap(),#key,#before.#ev(#key));
                    }
            }
            let tracked #current=Protocol #expr::#name(#current,#(#pn),*);
            let (#frame,#pre,#post)=choose|#frame:Fragment #types,#pre:State #types,#post:State #types|
                #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,Fragment #expr::unit()),#frame)==Protocol #expr::embed(#pre)
                &&State #expr::#strong(#pre,#post,#(#pn),*)&&#post.invariant()
                &&#current.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#pn),*)
                &&Fragment #expr::op(Fragment #expr::op(#current.fragment(),Fragment #expr::unit()),#frame)==Protocol #expr::embed(#post);
            assert(#pre.#a==#before.#av());
            assert forall|#point:#key_type| #[trigger] #current.fragment().#e.at(#point)==
                ::vstd::resource::tsm_collections::map_frag(Map::<#key_type,#value_type>::empty().insert(#key,#value).to_imap()).at(#point) by {};
            ::vstd::resource::tsm_collections::Pointwise::extensionality(#current.fragment().#e,
                ::vstd::resource::tsm_collections::map_frag(Map::<#key_type,#value_type>::empty().insert(#key,#value).to_imap()));
            let tracked (#result,#current)=Protocol #expr::#take(#current);
            *#slot=#result;
            #current
        }
        pub proof fn #name(tracked &self,#(#params,)*tracked #owner:&mut #a #types,tracked #entry:#e #types)->(tracked #result:#e #types)
            requires old(#owner).instance_id()==self.id(),#entry.instance_id()==self.id(),#entry.key()==#key,
            ensures final(#owner).instance_id()==self.id(),final(#owner).value()==#updated_value,
                #result.instance_id()==self.id(),#result.key()==#key,#result.value()==#value,
        {
            ::vstd::prelude::use_type_invariant(&*#owner);
            ::vstd::prelude::use_type_invariant(&#entry);
            let tracked #current=Self::#helper(#(#pn,)*&mut #owner.raw,#entry.raw);
            <#e #types>::__from_token(#current,#key,#value)
        }
    })
}
