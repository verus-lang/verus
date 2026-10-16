//! Field-tagged physical storage projection. This module does not change State fields.
use crate::ast::{Field, MonoidElt, SM, ShardableType, SplitKind, SubIdx, TransitionStmt};
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use std::collections::HashSet;
use verus_syn::{Error, Ident, Type};

pub struct Carrier {
    pub fields: Vec<Field>,
    pub key: Type,
    pub value: Type,
    pub declarations: TokenStream,
    pub projection: TokenStream,
    key_expr: TokenStream,
    value_expr: TokenStream,
    homogeneous: bool,
}

impl Carrier {
    /// Case split on the storage tag, for any carrier layout.
    pub fn tagged_cases(&self, index: TokenStream, goal: TokenStream) -> TokenStream {
        let key = &self.key_expr;
        let arms:Vec<_> = self.fields.iter().map(|field| {
            let n=&field.name;
            if matches!(field.stype,ShardableType::StorageOption(_)) {
                quote!{#key::#n=>{assert(#goal);},}
            } else {
                quote!{#key::#n(..)=>{assert(#goal);},}
            }
        }).collect();
        quote!{match #index {#(#arms)*_=>{assert(#goal);}}}
    }

    pub fn pointwise(&self, index: TokenStream, goal: TokenStream) -> TokenStream {
        if !self.homogeneous { return quote!{}; }
        let key = &self.key_expr;
        let arms:Vec<_> = self.fields.iter().map(|field| {
            let n=&field.name;
            if matches!(field.stype,ShardableType::StorageOption(_)) {
                quote!{#key::#n=>{assert(#goal);},}
            } else {
                quote!{#key::#n(..)=>{assert(#goal);},}
            }
        }).collect();
        quote!{match #index {#(#arms)*_=>{assert(#goal);}}}
    }

    pub fn build(sm: &SM, caller_items: TokenStream) -> Result<Option<Self>, Error> {
        let fields: Vec<_> = sm
            .fields
            .iter()
            .filter(|f| f.stype.is_storage())
            .cloned()
            .collect();
        // Keep the homogeneous-Option carrier unchanged. Field-tagged carriers
        // also cover multiple map namespaces; State keeps each original field.
        let has_option = fields.iter().any(|f| matches!(f.stype, ShardableType::StorageOption(_)));
        let map_count = fields.iter().filter(|f| matches!(f.stype,
            ShardableType::StorageMap(..) | ShardableType::StorageIMap(..))).count();
        if fields.len() < 2 || !(has_option && map_count > 0 || map_count > 1) {
            return Ok(None);
        }
        // Preserve existing carrier layouts outside the four-role mixed
        // logical/physical profile. Its arbitrary-domain initializer needs
        // key-only transfers, since its original payloads are homogeneous.
        if sm.fields.len() == 4
            && sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::Option(_))).count() == 1
            && sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::Map(..) | ShardableType::IMap(..))).count() == 1
            && fields.iter().filter(|f| matches!(f.stype, ShardableType::StorageOption(_))).count() == 1
            && fields.iter().filter(|f| matches!(f.stype, ShardableType::StorageMap(..) | ShardableType::StorageIMap(..))).count() == 1
        {
            if let Some(value) = crate::verified_storage_homogeneous_carrier::payload(&fields) {
                let output = crate::verified_storage_homogeneous_carrier::build(sm, &fields, &value, caller_items)?;
                return Ok(Some(Self {
                    fields, key: output.key, value: value.clone(),
                    declarations: output.declarations, projection: output.projection,
                    key_expr: output.key_expr, value_expr: quote!{#value},
                    homogeneous: true,
                }));
            }
        }
        fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
            for token in tokens {
                match token {
                    proc_macro2::TokenTree::Ident(id) => {
                        names.insert(id.to_string());
                    }
                    proc_macro2::TokenTree::Group(group) => reserve(group.stream(), names),
                    _ => {}
                }
            }
        }
        fn fresh(names: &mut HashSet<String>, stem: &str) -> Ident {
            let mut name = stem.to_string();
            while names.contains(&name) {
                name.push('_');
            }
            names.insert(name.clone());
            Ident::new(&name, Span::mixed_site())
        }
        fn walk(stmt: &TransitionStmt, names: &mut HashSet<String>) {
            match stmt {
                TransitionStmt::Block(_, children) => {
                    for child in children {
                        walk(child, names);
                    }
                }
                TransitionStmt::Require(_, expr)
                | TransitionStmt::Update(_, _, expr)
                | TransitionStmt::Initialize(_, _, expr)
                | TransitionStmt::PostCondition(_, expr) => reserve(quote! {#expr}, names),
                TransitionStmt::Assert(_, expr, proof) => {
                    let block = proof.proof.as_ref().map(|block| &**block);
                    reserve(quote! {#expr #block}, names);
                }
                TransitionStmt::SubUpdate(_, _, indices, expr) => {
                    reserve(quote! {#expr}, names);
                    for index in indices {
                        if let SubIdx::Idx(expr) = index {
                            reserve(quote! {#expr}, names);
                        }
                    }
                }
                TransitionStmt::Split(_, kind, children) => {
                    match &**kind {
                        SplitKind::If(expr) => reserve(quote! {#expr}, names),
                        SplitKind::Match(expr, arms) => {
                            reserve(quote! {#expr}, names);
                            for arm in arms {
                                let pat = &arm.pat;
                                let guard = arm.guard.as_ref().map(|(_, expr)| expr);
                                reserve(quote! {#pat #guard}, names);
                            }
                        }
                        SplitKind::Let(pat, ty, _, expr) => reserve(quote! {#pat #ty #expr}, names),
                        SplitKind::Special(_, op, proof, pat) => {
                            let block = proof.proof.as_ref().map(|block| &**block);
                            reserve(quote! {#pat #block}, names);
                            match &op.elt {
                                MonoidElt::General(expr)
                                | MonoidElt::SingletonMultiset(expr)
                                | MonoidElt::SingletonSet(expr) => reserve(quote! {#expr}, names),
                                MonoidElt::OptionSome(expr) => reserve(quote! {#expr}, names),
                                MonoidElt::SingletonKV(key, value) => {
                                    reserve(quote! {#key #value}, names)
                                }
                                MonoidElt::True => {}
                            }
                        }
                    }
                    for child in children {
                        walk(child, names);
                    }
                }
            }
        }
        let field_ast = &sm.fields_named_ast;
        let generics_ast = &sm.generics;
        let mut names = HashSet::new();
        reserve(caller_items, &mut names);
        reserve(quote! {#field_ast #generics_ast}, &mut names);
        for tr in &sm.transitions {
            names.insert(tr.name.to_string());
            walk(&tr.body, &mut names);
            for param in &tr.params {
                let ty = &param.ty;
                reserve(quote! {#ty}, &mut names);
            }
        }
        for field in &fields {
            for prefix in ["__tag_", "__tag_finite_", "__untag_", "__pack_", "__unpack_", "__borrow_"] {
                let helper = format!("{prefix}{}", field.name);
                if fields.iter().any(|other| other.name == helper) {
                    return Err(Error::new(
                        field.type_span,
                        "physical field conflicts with a generated carrier helper",
                    ));
                }
            }
        }
        let key_name = fresh(&mut names, "__StorageKey");
        let value_name = fresh(&mut names, "__StorageValue");
        let marker_name = fresh(&mut names, "__Phantom");
        let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
        let (decl, wc) = generics_for_decl(&generics);
        let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
        let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
        let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
        let key_expr = quote! {#key_name #expr};
        let value_expr = quote! {#value_name #expr};
        let phantom = args
            .as_ref()
            .map(|a| quote! {#marker_name(core::marker::PhantomData<(#a,)>),});
        let mut key_variants = Vec::new();
        let mut value_variants = Vec::new();
        let mut domains = Vec::new();
        let mut values = Vec::new();
        let mut specs = Vec::new();
        let mut protocol_helpers = Vec::new();
        for field in &fields {
            let n = &field.name;
            let (key_type, value_type) = match &field.stype {
                ShardableType::StorageOption(v) => {
                    key_variants.push(quote! {#n,});
                    (None, v)
                }
                ShardableType::StorageMap(k, v) | ShardableType::StorageIMap(k, v) => {
                    key_variants.push(quote! {#n(#k),});
                    (Some(k), v)
                }
                _ => {
                    return Err(Error::new(
                        field.type_span,
                        "unsupported tagged physical storage strategy",
                    ));
                }
            };
            value_variants.push(quote! {#n(#value_type),});
            if let Some(k) = key_type {
                let local = if matches!(field.stype, ShardableType::StorageMap(..)) {
                    quote! {s.#n.to_imap()}
                } else {
                    quote! {s.#n}
                };
                domains.push(quote! {#key_expr::#n(key)=> (#local).contains_key(key),});
                values.push(quote! {#key_expr::#n(key)=>#value_expr::#n((#local)[key]),});
                let tag = format_ident!("__tag_{}", n);
                let untag = format_ident!("__untag_{}", n);
                let accessor = format_ident!("{}_0", n);
                specs.push(quote!{
                    pub open spec fn #tag(input:IMap<#k,#value_type>)->IMap<#key_name #types,#value_name #types>{
                        IMap::new(|key:#key_name #types|match key{
                            #key_expr::#n(local)=>input.contains_key(local),_=>false,
                        },|key:#key_name #types|match key{
                            #key_expr::#n(local)=>#value_expr::#n(input[local]),_=>arbitrary(),
                        })
                    }
                    pub open spec fn #untag(input:IMap<#key_name #types,#value_name #types>)->IMap<#k,#value_type>{
                        IMap::new(|key:#k|input.contains_key(#key_expr::#n(key))&&input[#key_expr::#n(key)] is #n,
                            |key:#k|input[#key_expr::#n(key)]->#accessor)
                    }
                });
                let pack = format_ident!("__pack_{}", n);
                let tag_finite = format_ident!("__tag_finite_{}", n);
                let unpack = format_ident!("__unpack_{}", n);
                let borrow = format_ident!("__borrow_{}", n);
                let public_tag = format_ident!("__carrier_tag_{}", n);
                let public_untag = format_ident!("__carrier_untag_{}", n);
                let public_pack = format_ident!("__carrier_pack_{}", n);
                let public_unpack = format_ident!("__carrier_unpack_{}", n);
                let public_borrow = format_ident!("__carrier_borrow_{}", n);
                let public_shape = format_ident!("__carrier_shape_{}", n);
                for helper in [&public_tag,&public_untag,&public_pack,&public_unpack,&public_borrow,&public_shape] {
                    if sm.transitions.iter().any(|tr| tr.name==*helper) {
                        return Err(Error::new(helper.span(),"transition conflicts with a generated physical transfer helper"));
                    }
                }
                protocol_helpers.push(quote! {
                    pub open spec fn #public_tag(input:IMap<#k,#value_type>)->IMap<#key_name #types,#value_name #types> {
                        #key_expr::#tag(input)
                    }
                    pub open spec fn #public_untag(input:IMap<#key_name #types,#value_name #types>)->IMap<#k,#value_type> {
                        #key_expr::#untag(input)
                    }
                    pub proof fn #public_shape(input:IMap<#k,#value_type>)
                        requires input.dom().finite(),
                        ensures Self::#public_tag(input).dom().finite(),
                            Self::#public_untag(Self::#public_tag(input))==input,
                    {
                        let inject=|key:#k|#key_expr::#n(key);
                        input.dom().lemma_map_finite(inject);
                        assert(::vstd::prelude::ext_equal(Self::#public_tag(input).dom(),input.dom().map(inject)));
                        assert(::vstd::prelude::ext_equal(Self::#public_untag(Self::#public_tag(input)),input));
                    }
                    pub proof fn #public_pack(tracked input:Map<#k,#value_type>)->(tracked output:IMap<#key_name #types,#value_name #types>)
                        ensures output==Self::#public_tag(input.to_imap()),output.dom().finite(),output.dom().len()==input.len(),
                    {#key_expr::#pack(input)}
                    pub proof fn #public_unpack(tracked input:IMap<#key_name #types,#value_name #types>)->(tracked output:Map<#k,#value_type>)
                        requires input.dom().finite(),input==Self::#public_tag(Self::#public_untag(input)),
                        ensures output.to_imap()==Self::#public_untag(input),
                    {#key_expr::#unpack(input)}
                    pub proof fn #public_borrow<'a>(tracked input:&'a IMap<#key_name #types,#value_name #types>,key:#k)->(tracked output:Option<&'a #value_type>)
                        requires input.contains_key(#key_expr::#n(key)),input[#key_expr::#n(key)] is #n,
                        ensures output is Some,*output->Some_0==input[#key_expr::#n(key)]->#accessor,
                    {#key_expr::#borrow(input,key)}
                });
                specs.push(quote!{
                    pub proof fn #tag_finite(input:Map<#k,#value_type>)
                        ensures Self::#tag(input.to_imap()).dom().finite(),
                        decreases input.len(),
                    {
                        broadcast use {::vstd::map::group_map_lemmas,::vstd::imap::group_imap_lemmas,
                            ::vstd::set::group_set_lemmas,::vstd::iset::group_iset_lemmas};
                        ::vstd::set_lib::lemma_set_empty_equivalency_len(input.dom());
                        if input.len()==0 {
                            assert(::vstd::prelude::ext_equal(Self::#tag(input.to_imap()).dom(),ISet::<#key_expr>::empty()));
                        } else {
                            let key=choose|key:#k|input.dom().contains(key);
                            ::vstd::set::lemma_set_remove_len(input.dom(),key);
                            Self::#tag_finite(input.remove(key));
                            assert(::vstd::prelude::ext_equal(Self::#tag(input.to_imap()).dom(),
                                Self::#tag(input.remove(key).to_imap()).dom().insert(#key_expr::#n(key))));
                        }
                    }
                    pub proof fn #pack(tracked input:Map<#k,#value_type>)->(tracked output:IMap<#key_expr,#value_expr>)
                        ensures output==Self::#tag(input.to_imap()),output.dom().finite(),output.dom().len()==input.len(), decreases input.len(),
                    {
                        broadcast use {::vstd::map::group_map_lemmas,::vstd::imap::group_imap_lemmas,
                            ::vstd::set::group_set_lemmas,::vstd::iset::group_iset_lemmas};
                        let ghost original=input;
                        ::vstd::set_lib::lemma_set_empty_equivalency_len(input.dom());
                        if input.len()==0 {
                            let tracked output=IMap::tracked_empty();
                            assert(::vstd::prelude::ext_equal(output,Self::#tag(original.to_imap())));
                            output
                        } else {
                            let key=choose|key:#k|input.dom().contains(key);
                            ::vstd::set::lemma_set_remove_len(input.dom(),key);
                            let tracked mut input=input;
                            let tracked value=input.tracked_remove(key);
                            let tracked mut output=Self::#pack(input);
                            output.tracked_insert(#key_expr::#n(key),#value_expr::#n(value));
                            assert(::vstd::prelude::ext_equal(output,Self::#tag(original.to_imap())));
                            output
                        }
                    }
                    pub proof fn #unpack(tracked input:IMap<#key_expr,#value_expr>)->(tracked output:Map<#k,#value_type>)
                        requires input.dom().finite(),input==Self::#tag(Self::#untag(input)),
                        ensures output.to_imap()==Self::#untag(input), decreases input.dom().len(),
                    {
                        broadcast use {::vstd::map::group_map_lemmas,::vstd::imap::group_imap_lemmas,
                            ::vstd::set::group_set_lemmas,::vstd::iset::group_iset_lemmas};
                        let ghost original=input;
                        if input.dom().len()==0 {
                            let tracked output=Map::tracked_empty();
                            assert(::vstd::prelude::ext_equal(output.to_imap(),Self::#untag(original)));
                            output
                        } else {
                            let key=input.dom().choose();
                            ::vstd::iset::lemma_iset_choose_len(input.dom());
                            let native_key=match key {#key_expr::#n(key)=>key,_=>arbitrary()};
                            assert(key==#key_expr::#n(native_key));
                            ::vstd::iset::lemma_iset_remove_len(input.dom(),key);
                            let tracked mut input=input;
                            let tracked value=input.tracked_remove(key);
                            let tracked value=match value {#value_expr::#n(value)=>Some(value),_=>None};
                            assert(value is Some);
                            let tracked value=::vstd::std_specs::option::OptionAdditionalFns::tracked_unwrap(value);
                            assert(::vstd::prelude::ext_equal(input,Self::#tag(Self::#untag(input))));
                            let tracked mut output=Self::#unpack(input);
                            output.tracked_insert(native_key,value);
                            assert(::vstd::prelude::ext_equal(output.to_imap(),Self::#untag(original)));
                            output
                        }
                    }
                    pub proof fn #borrow<'a>(tracked input:&'a IMap<#key_expr,#value_expr>,key:#k)->(tracked output:Option<&'a #value_type>)
                        requires input.contains_key(#key_expr::#n(key)),input[#key_expr::#n(key)] is #n,
                        ensures output is Some,*output->Some_0==input[#key_expr::#n(key)]->#accessor,
                    {
                        let tracked value=input.tracked_borrow(#key_expr::#n(key));
                        match value {#value_expr::#n(value)=>Some(value),_=>None}
                    }
                });
            } else {
                domains.push(quote! {#key_expr::#n=>s.#n is Some,});
                values.push(quote! {#key_expr::#n=>#value_expr::#n(s.#n->Some_0),});
                let tag = format_ident!("__tag_{}", n);
                let untag = format_ident!("__untag_{}", n);
                let accessor = format_ident!("{}_0", n);
                specs.push(quote!{
                    pub open spec fn #tag(input:Option<#value_type>)->IMap<#key_name #types,#value_name #types>{
                        match input{Some(value)=>IMap::empty().insert(#key_expr::#n,#value_expr::#n(value)),None=>IMap::empty()}
                    }
                    pub open spec fn #untag(input:IMap<#key_name #types,#value_name #types>)->Option<#value_type>{
                        if input.contains_key(#key_expr::#n)&&input[#key_expr::#n] is #n {
                            Some(input[#key_expr::#n]->#accessor)
                        } else {None}
                    }
                });
                let pack = format_ident!("__pack_{}", n);
                let unpack = format_ident!("__unpack_{}", n);
                let borrow = format_ident!("__borrow_{}", n);
                specs.push(quote!{
                    pub proof fn #pack(tracked input:Option<#value_type>)->(tracked output:IMap<#key_expr,#value_expr>)
                        ensures output==Self::#tag(input),
                    {
                        match input {
                            Some(value)=>{let tracked mut output=IMap::tracked_empty();
                                output.tracked_insert(#key_expr::#n,#value_expr::#n(value));output},
                            None=>IMap::tracked_empty(),
                        }
                    }
                    pub proof fn #unpack(tracked input:IMap<#key_expr,#value_expr>)->(tracked output:Option<#value_type>)
                        requires input==Self::#tag(Self::#untag(input)),
                        ensures output==Self::#untag(input),
                    {
                        if input.contains_key(#key_expr::#n) {
                            let tracked mut input=input;
                            let tracked value=input.tracked_remove(#key_expr::#n);
                            match value {#value_expr::#n(value)=>Some(value),_=>None}
                        } else {None}
                    }
                    pub proof fn #borrow<'a>(tracked input:&'a IMap<#key_expr,#value_expr>)->(tracked output:Option<&'a #value_type>)
                        requires input.contains_key(#key_expr::#n),input[#key_expr::#n] is #n,
                        ensures output is Some,*output->Some_0==input[#key_expr::#n]->#accessor,
                    {
                        let tracked value=input.tracked_borrow(#key_expr::#n);
                        match value {#value_expr::#n(value)=>Some(value),_=>None}
                    }
                });
            }
        }
        let declarations = quote! {
            #(#attrs)* pub enum #key_name #decl #wc {#(#key_variants)* #phantom}
            #(#attrs)* pub tracked enum #value_name #decl #wc {#(#value_variants)* #phantom}
            impl #decl #key_name #types #wc {
                #(#specs)*
            }
            impl #decl Protocol #types #wc {
                #(#protocol_helpers)*
            }
        };
        let projection = quote! {IMap::new(|key:#key_name #types|match key{#(#domains)*_=>false,},
        |key:#key_name #types|match key{#(#values)*_=>arbitrary(),})};
        Ok(Some(Self {
            fields,
            key: verus_syn::parse2(quote! {#key_name #types})?,
            value: verus_syn::parse2(quote! {#value_name #types})?,
            declarations,
            projection,
            key_expr,
            value_expr,
            homogeneous: false,
        }))
    }

    pub fn singleton(&self, field: &Ident, elt: &MonoidElt) -> Result<TokenStream, Error> {
        let key = &self.key_expr;
        let value = &self.value_expr;
        match elt {
            MonoidElt::OptionSome(Some(v)) => {
                Ok(if self.homogeneous {
                    quote! {IMap::empty().insert(#key::#field,#v)}
                } else {
                    quote! {IMap::empty().insert(#key::#field,#value::#field(#v))}
                })
            }
            MonoidElt::SingletonKV(k, Some(v)) => {
                Ok(if self.homogeneous {
                    quote! {IMap::empty().insert(#key::#field(#k),#v)}
                } else {
                    quote! {IMap::empty().insert(#key::#field(#k),#value::#field(#v))}
                })
            }
            MonoidElt::General(v) => {
                let f = self
                    .fields
                    .iter()
                    .find(|f| f.name == *field)
                    .ok_or_else(|| Error::new(field.span(), "unknown tagged physical field"))?;
                let tag = format_ident!("__tag_{}", field);
                let native = if matches!(f.stype, ShardableType::StorageMap(..)) {
                    quote! {(#v).to_imap()}
                } else {
                    quote! {#v}
                };
                Ok(quote! {#key::#tag(#native)})
            }
            _ => Err(Error::new(
                field.span(),
                "tagged transfer requires an explicit optional or map operand",
            )),
        }
    }
}
