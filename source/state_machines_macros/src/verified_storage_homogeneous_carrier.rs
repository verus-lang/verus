//! Checked key-only tagging when every physical field has the same payload.
//! Changing keys transfers actual values even for an arbitrary tracked IMap.
use crate::ast::{Field, ShardableType, SM};
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote, ToTokens};
use std::collections::HashSet;
use verus_syn::{Error, Ident, Type};

pub fn payload(fields: &[Field]) -> Option<Type> {
    let get = |f: &Field| match &f.stype {
        ShardableType::StorageOption(v)
        | ShardableType::StorageMap(_, v)
        | ShardableType::StorageIMap(_, v) => Some(v.clone()),
        _ => None,
    };
    let first = get(fields.first()?)?;
    fields.iter().all(|f| get(f).is_some_and(|v|
        v.to_token_stream().to_string() == first.to_token_stream().to_string()
    )).then_some(first)
}

pub struct Output {
    pub key: Type,
    pub key_expr: TokenStream,
    pub declarations: TokenStream,
    pub projection: TokenStream,
}

pub fn build(
    sm: &SM,
    fields: &[Field],
    value: &Type,
    reservation: TokenStream,
) -> Result<Output, Error> {
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
    let mut names = HashSet::new();
    let fields_ast = &sm.fields_named_ast;
    let generic_ast = &sm.generics;
    reserve(quote! {#fields_ast #generic_ast #reservation}, &mut names);
    // Reserve expressions, binders and proof blocks from every operation.
    fn walk(stmt: &crate::ast::TransitionStmt, names: &mut HashSet<String>) {
        use crate::ast::{MonoidElt, SplitKind, SubIdx, TransitionStmt};
        match stmt {
            TransitionStmt::Block(_, children) => {
                for child in children { walk(child, names); }
            }
            TransitionStmt::Require(_, e) | TransitionStmt::Update(_, _, e)
            | TransitionStmt::Initialize(_, _, e) | TransitionStmt::PostCondition(_, e) => reserve(quote!{#e}, names),
            TransitionStmt::Assert(_, e, proof) => {
                let block = proof.proof.as_ref().map(|b| &**b);
                reserve(quote!{#e #block}, names);
            }
            TransitionStmt::SubUpdate(_, _, indices, e) => {
                reserve(quote!{#e}, names);
                for index in indices {
                    if let SubIdx::Idx(e) = index { reserve(quote!{#e}, names); }
                }
            }
            TransitionStmt::Split(_, kind, children) => {
                match &**kind {
                    SplitKind::If(e) => reserve(quote!{#e}, names),
                    SplitKind::Match(e, arms) => {
                        reserve(quote!{#e}, names);
                        for arm in arms {
                            let pat = &arm.pat;
                            let guard = arm.guard.as_ref().map(|(_, e)| e);
                            reserve(quote!{#pat #guard}, names);
                        }
                    }
                    SplitKind::Let(pat, ty, _, e) => reserve(quote!{#pat #ty #e}, names),
                    SplitKind::Special(_, op, proof, pat) => {
                        let block = proof.proof.as_ref().map(|b| &**b);
                        reserve(quote!{#pat #block}, names);
                        match &op.elt {
                            MonoidElt::General(e) | MonoidElt::SingletonMultiset(e)
                            | MonoidElt::SingletonSet(e) => reserve(quote!{#e}, names),
                            MonoidElt::OptionSome(e) => reserve(quote!{#e}, names),
                            MonoidElt::SingletonKV(k, v) => reserve(quote!{#k #v}, names),
                            MonoidElt::True => {}
                        }
                    }
                }
                for child in children { walk(child, names); }
            }
        }
    }
    for tr in &sm.transitions {
        names.insert(tr.name.to_string().trim_start_matches("r#").to_string());
        for param in &tr.params {
            let n = &param.name;
            let ty = &param.ty;
            reserve(quote!{#n #ty}, &mut names);
        }
        walk(&tr.body, &mut names);
    }
    let mut fresh = |stem: &str| {
        let mut n = stem.to_owned();
        while names.contains(&n) { n.push('_'); }
        names.insert(n.clone());
        Ident::new(&n, Span::mixed_site())
    };
    let key_name = fresh("__StorageKey");
    let marker = fresh("__Phantom");
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote!{<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote!{::<#a>}).unwrap_or_default();
    let key_expr = quote!{#key_name #expr};
    let phantom = args.as_ref().map(|a| quote!{#marker(core::marker::PhantomData<(#a,)>),});
    let mut variants = vec![];
    let mut methods = vec![];
    let mut protocol = vec![];
    let mut domains = vec![];
    let mut values = vec![];
    let mut projection=quote!{IMap::empty()};
    for field in fields {
        let n = &field.name;
        let tag = format_ident!("__tag_{n}");
        let untag = format_ident!("__untag_{n}");
        let pack = format_ident!("__pack_{n}");
        let unpack = format_ident!("__unpack_{n}");
        let borrow = format_ident!("__borrow_{n}");
        if let ShardableType::StorageOption(_) = &field.stype {
            projection=quote!{(#projection).union_prefer_right(#key_expr::#tag(s.#n))};
            variants.push(quote!{#n,});
            domains.push(quote!{#key_expr::#n => s.#n is Some,});
            values.push(quote!{#key_expr::#n => s.#n->Some_0,});
            methods.push(quote! {
                pub open spec fn #tag(input:Option<#value>)->IMap<#key_name #types,#value> {
                    match input {Some(value)=>IMap::empty().insert(#key_expr::#n,value),None=>IMap::empty()}
                }
                pub open spec fn #untag(input:IMap<#key_name #types,#value>)->Option<#value> {
                    if input.contains_key(#key_expr::#n) {Some(input[#key_expr::#n])} else {None}
                }
                pub proof fn #pack(tracked input:Option<#value>)->(tracked output:IMap<#key_name #types,#value>)
                    ensures output==Self::#tag(input),
                {
                    match input {
                        Some(value)=>{let tracked mut output=IMap::tracked_empty();output.tracked_insert(#key_expr::#n,value);output},
                        None=>IMap::tracked_empty(),
                    }
                }
                pub proof fn #unpack(tracked input:IMap<#key_name #types,#value>)->(tracked output:Option<#value>)
                    requires input==Self::#tag(Self::#untag(input)),
                    ensures output==Self::#untag(input),
                {
                    if input.contains_key(#key_expr::#n) {
                        let tracked mut input=input;Some(input.tracked_remove(#key_expr::#n))
                    } else {None}
                }
                pub proof fn #borrow<'a>(tracked input:&'a IMap<#key_name #types,#value>)->(tracked output:Option<&'a #value>)
                    requires input.contains_key(#key_expr::#n),
                    ensures output is Some,*output->Some_0==input[#key_expr::#n],
                {Some(input.tracked_borrow(#key_expr::#n))}
            });
            continue;
        }
        let (k, finite) = match &field.stype {
            ShardableType::StorageMap(k, _) => (k, true),
            ShardableType::StorageIMap(k, _) => (k, false),
            _ => return Err(Error::new(field.type_span, "unsupported homogeneous storage role")),
        };
        variants.push(quote!{#n(#k),});
        let native = if finite {quote!{s.#n.to_imap()}} else {quote!{s.#n}};
        projection=quote!{(#projection).union_prefer_right(#key_expr::#tag(#native))};
        domains.push(quote!{#key_expr::#n(key)=>(#native).contains_key(key),});
        values.push(quote!{#key_expr::#n(key)=>(#native)[key],});
        let pack_imap = format_ident!("__pack_imap_{n}");
        let unpack_imap = format_ident!("__unpack_imap_{n}");
        methods.push(quote! {
            #[verifier::inline] pub open spec fn #tag(input:IMap<#k,#value>)->IMap<#key_name #types,#value> {
                IMap::new(|key:#key_name #types|match key {#key_expr::#n(local)=>input.contains_key(local),_=>false},
                    |key:#key_name #types|match key {#key_expr::#n(local)=>input[local],_=>arbitrary()})
            }
            #[verifier::inline] pub open spec fn #untag(input:IMap<#key_name #types,#value>)->IMap<#k,#value> {
                IMap::new(|key:#k|input.contains_key(#key_expr::#n(key)),|key:#k|input[#key_expr::#n(key)])
            }
            pub proof fn #pack_imap(tracked input:IMap<#k,#value>)->(tracked output:IMap<#key_name #types,#value>)
                ensures output==Self::#tag(input),
            {
                let key_map=IMap::new(|key:#key_name #types|match key {#key_expr::#n(local)=>input.contains_key(local),_=>false},
                    |key:#key_name #types|match key {#key_expr::#n(local)=>local,_=>arbitrary()});
                let tracked output=IMap::tracked_map_keys(input,key_map);
                assert(::vstd::prelude::ext_equal(output,Self::#tag(input)));
                output
            }
            pub proof fn #unpack_imap(tracked input:IMap<#key_name #types,#value>)->(tracked output:IMap<#k,#value>)
                requires input==Self::#tag(Self::#untag(input)),
                ensures output==Self::#untag(input),
            {
                let key_map=IMap::new(|key:#k|input.contains_key(#key_expr::#n(key)),|key:#k|#key_expr::#n(key));
                let tracked output=IMap::tracked_map_keys(input,key_map);
                assert(::vstd::prelude::ext_equal(output,Self::#untag(input)));
                output
            }
        });
        let ptag = format_ident!("__carrier_tag_{n}");
        let puntag = format_ident!("__carrier_untag_{n}");
        let ppack = format_ident!("__carrier_pack_imap_{n}");
        let punpack = format_ident!("__carrier_unpack_imap_{n}");
        let roundtrip = format_ident!("__carrier_roundtrip_{n}");
        for helper in [&ptag, &puntag, &ppack, &punpack, &roundtrip] {
            if sm.transitions.iter().any(|tr| tr.name.to_string().trim_start_matches("r#")==helper.to_string()) {
                return Err(Error::new(helper.span(), "transition conflicts with a physical transfer helper"));
            }
        }
        protocol.push(quote! {
            #[verifier::inline] pub open spec fn #ptag(input:IMap<#k,#value>)->IMap<#key_name #types,#value>{#key_expr::#tag(input)}
            #[verifier::inline] pub open spec fn #puntag(input:IMap<#key_name #types,#value>)->IMap<#k,#value>{#key_expr::#untag(input)}
            pub proof fn #roundtrip(input:IMap<#k,#value>)
                ensures Self::#puntag(Self::#ptag(input))==input,
                    Self::#ptag(Self::#puntag(Self::#ptag(input)))==Self::#ptag(input),
            {
                broadcast use {::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas};
                assert(::vstd::prelude::ext_equal(Self::#puntag(Self::#ptag(input)),input));
            }
            pub proof fn #ppack(tracked input:IMap<#k,#value>)->(tracked output:IMap<#key_name #types,#value>)
                ensures output==Self::#ptag(input),
            {#key_expr::#pack_imap(input)}
            pub proof fn #punpack(tracked input:IMap<#key_name #types,#value>)->(tracked output:IMap<#k,#value>)
                requires input==Self::#ptag(Self::#puntag(input)),
                ensures output==Self::#puntag(input),
            {#key_expr::#unpack_imap(input)}
        });
    }
    Ok(Output {
        key: verus_syn::parse2(quote!{#key_name #types})?,
        key_expr,
        declarations: quote! {
            #(#attrs)* pub enum #key_name #decl #wc {#(#variants)* #phantom}
            impl #decl #key_name #types #wc {#(#methods)*}
            impl #decl Protocol #types #wc {#(#protocol)*}
        },
        projection,
    })
}
