//! Bound logical Option/Map owners govern an actual matching physical map.
//! Native clients never supply a second physical owner: all compatible frames
//! must justify the original withdrawal/guard through the original invariants.
use crate::ast::*;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident, Pat};

fn profile(sm: &SM) -> Option<(&Field, &Field, &Field, bool)> {
    if sm.fields.len() != 3 {
        return None;
    }
    let optional = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::Option(_)))?;
    let map = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::Map(..) | ShardableType::IMap(..)))?;
    let physical = sm.fields.iter().find(|f| f.stype.is_storage())?;
    match (&map.stype, &physical.stype) {
        (ShardableType::Map(k, v), ShardableType::StorageMap(sk, sv)) if k == sk && v == sv => {
            Some((optional, map, physical, true))
        }
        (ShardableType::IMap(k, v), ShardableType::StorageIMap(sk, sv)) if k == sk && v == sv => {
            Some((optional, map, physical, false))
        }
        _ => None,
    }
}
pub fn needed(sm: &SM) -> bool {
    profile(sm).is_some()
}
#[derive(Default)]
struct Flat {
    initial: HashMap<String, Expr>,
    operations: Vec<(Ident, SpecialOp, Option<Box<Pat>>)>,
    requirements: Vec<Expr>,
    assertions: Vec<Expr>,
}
fn collect(stmt: &TransitionStmt, f: &mut Flat) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                collect(child, f)?;
            }
        }
        TransitionStmt::Initialize(_, name, e) => {
            if f.initial.insert(name.to_string(), e.clone()).is_some() {
                return Err(Error::new(
                    name.span(),
                    "binding initializer repeats a field",
                ));
            }
        }
        TransitionStmt::Require(_, e) => {
            if f.operations.iter().any(|(_, op, _)| op.stmt.is_withdraw()) {
                return Err(Error::new(
                    *stmt.get_span(),
                    "binding native preconditions cannot depend on withdrawn payloads",
                ));
            }
            f.requirements.push(e.clone());
        }
        TransitionStmt::Assert(_, e, _) => f.assertions.push(e.clone()),
        TransitionStmt::Split(_, kind, children) => {
            let SplitKind::Special(field, op, binding_proof, pat) = &**kind else {
                return Err(Error::new(
                    *stmt.get_span(),
                    "binding facade requires straight-line special operations",
                ));
            };
            let _ = binding_proof;
            if let Some(p) = pat {
                if !matches!(&**p,Pat::Ident(p) if p.by_ref.is_none()&&p.mutability.is_none()&&p.subpat.is_none())
                {
                    return Err(Error::new(
                        *stmt.get_span(),
                        "binding facade requires a plain bound value identifier",
                    ));
                }
            }
            f.operations.push((field.clone(), op.clone(), pat.clone()));
            for child in children {
                collect(child, f)?;
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "unsupported bound storage native operation",
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
fn local(e: &Expr, sm: &SM) -> Result<TokenStream, Error> {
    let mut e = e.clone();
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let mut errors = vec![];
    crate::field_access_visitor::visit_field_accesses(
        &mut e,
        |errors, f, _| {
            errors.push(Error::new(
                f.name.span(),
                "binding native clause cannot expose an unowned complete field",
            ));
        },
        &mut errors,
        &fields,
    );
    if let Some(e) = errors.into_iter().next() {
        Err(e)
    } else {
        Ok(quote! {#e})
    }
}

pub fn output(sm: &SM) -> Result<TokenStream, Error> {
    let Some((optional, map, physical, finite)) = profile(sm) else {
        return Err(Error::new(
            sm.name.span(),
            "binding facade requires Option, logical Map/IMap and matching physical map",
        ));
    };
    let (keyty, valty) = match &map.stype {
        ShardableType::Map(k, v) | ShardableType::IMap(k, v) => (k, v),
        _ => unreachable!(),
    };
    for field in &sm.fields {
        if field.name.to_string().starts_with("r#") {
            return Err(Error::new(
                field.name.span(),
                "binding facade does not yet support raw field identifiers",
            ));
        }
    }
    for transition in &sm.transitions {
        if transition.name.to_string().starts_with("r#") {
            return Err(Error::new(
                transition.name.span(),
                "binding facade does not yet support raw transition identifiers",
            ));
        }
    }
    let opt = &optional.name;
    let field = &map.name;
    let store = &physical.name;
    let optty = match &optional.stype {
        ShardableType::Option(t) => t,
        _ => unreachable!(),
    };
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let native_map = if finite {
        quote! {::vstd::map::Map::<#keyty,#valty>}
    } else {
        quote! {::vstd::imap::IMap::<#keyty,#valty>}
    };
    let native_type = if finite {
        quote! {::vstd::map::Map<#keyty,#valty>}
    } else {
        quote! {::vstd::imap::IMap<#keyty,#valty>}
    };
    let native_store = physical.get_type();
    let fields_ast = &sm.fields_named_ast;
    let generic_ast = &sm.generics;
    let mut names = HashSet::new();
    reserve(quote! {#fields_ast #generic_ast}, &mut names);
    for tr in &sm.transitions {
        let n = &tr.name;
        reserve(quote! {#n}, &mut names);
        for p in &tr.params {
            let n = &p.name;
            let t = &p.ty;
            reserve(quote! {#n #t}, &mut names);
        }
        crate::verified_field_storage_map_pair::reserve_stmt(&tr.body, &mut names);
    }
    let mut fresh = |label: &str| {
        let mut name = format!("__tsm_binding_{label}");
        while names.contains(&name) || names.contains(&format!("r#{name}")) {
            name.push('_');
        }
        names.insert(name.clone());
        Ident::new(&name, Span::mixed_site())
    };
    let location = fresh("protocol_location");
    let marker_name = fresh("types");
    let init_opt = fresh("initial_option_value");
    let owner = fresh("owner");
    let raw = fresh("raw");
    let before = fresh("before");
    let after = fresh("after");
    let frame = fresh("frame");
    let pre = fresh("pre");
    let post = fresh("post");
    let out = fresh("result");
    let md = fresh("metadata");
    let base = fresh("base");
    let initial = fresh("initial");
    let mapraw = fresh("map_raw");
    let optraw = fresh("option_raw");
    let rest = fresh("rest");
    let withdrawn = fresh("withdrawn");
    let value = fresh("value");
    let point = fresh("point");
    let convert = fresh("map_into_imap");
    let lifetime = fresh("guard_lifetime");
    let lifetime = verus_syn::Lifetime::new(&format!("'{}", lifetime), Span::mixed_site());
    let marker = args
        .as_ref()
        .map(|a| quote! {#marker_name:core::marker::PhantomData<(#a,)>,});
    let marker_value = args
        .as_ref()
        .map(|_| quote! {#marker_name:core::marker::PhantomData,});
    let metadata = quote! {__StorageMetadata #types};
    let descriptor = quote! {::vstd::resource::tsm_context::Descriptor<#metadata>};
    let token = quote! {Token #types};
    let cx = crate::verified_field_storage_roles::Context {
        decl: &decl,
        types: &types,
        expr: &expr,
        where_clause: &wc,
        attrs: &attrs,
        token: &token,
        descriptor: &descriptor,
        protocol_location: &location,
        constants: &[],
    };
    let opt_wrapper = crate::verified_field_storage_roles::wrapper(optional, &cx)?;
    let map_wrapper = crate::verified_field_storage_binding_maps::wrapper(
        map,
        &cx,
        &quote! {#fields_ast #generic_ast},
    )?;
    let collection = format_ident!("{}_collection", field);
    let map_alias = format_ident!("{}_map", field);
    let occupied_types: HashSet<_> = sm.fields.iter().map(|f| f.name.to_string()).collect();
    for generated in [
        "Instance".to_string(),
        "Protocol".to_string(),
        "State".to_string(),
        "Fragment".to_string(),
        "Token".to_string(),
        "__StorageMetadata".to_string(),
        collection.to_string(),
        map_alias.to_string(),
    ] {
        if occupied_types.contains(&generated)
            || sm.generics.as_ref().is_some_and(|g| {
                g.params
                    .iter()
                    .any(|p| matches!(p,verus_syn::GenericParam::Type(t) if t.ident==generated))
            })
        {
            return Err(Error::new(
                sm.name.span(),
                "binding nominal type/collection alias conflicts with a field or generic",
            ));
        }
    }
    let mut methods = HashSet::from([
        "id".to_string(),
        "clone".to_string(),
        "invariant".to_string(),
    ]);
    for tr in &sm.transitions {
        if !methods.insert(tr.name.to_string()) {
            return Err(Error::new(
                tr.name.span(),
                "binding transition conflicts with a generated Instance method",
            ));
        }
    }
    let factory_opt = format_ident!("field_{}", opt);
    let factory_map = format_ident!("field_{}", field);
    let take_opt = format_ident!("take_{}", opt);
    let getter_opt = format_ident!("value_{}", opt);
    let getter_map = format_ident!("value_{}_at", field);
    let mut emitted = vec![];
    for tr in &sm.transitions {
        let n = &tr.name;
        let mut flat = Flat::default();
        collect(&tr.body, &mut flat)?;
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
        let enabled = format_ident!("{}_enabled", n);
        let strong = format_ident!("{}_strong", n);
        let owners = format_ident!("{}_owners_enabled", n);
        let req = format_ident!("{}_requires", n);
        let witness = format_ident!("{}_witness", n);
        if tr.kind == TransitionKind::Init {
            if flat.initial.len() != 3 || !flat.operations.is_empty() || !flat.assertions.is_empty()
            {
                return Err(Error::new(
                    n.span(),
                    "binding initializer must initialize every field without physical operations",
                ));
            }
            let io = &flat.initial[&opt.to_string()];
            let im = &flat.initial[&field.to_string()];
            let is = &flat.initial[&store.to_string()];
            let requirements = &flat.requirements;
            let actual_base = if finite {
                quote! {#base.to_imap()}
            } else {
                quote! {#base}
            };
            let stored_value = if finite {
                quote! {#is.to_imap()}
            } else {
                quote! {#is}
            };
            let converted = if finite {
                quote! {let tracked #base=Self::#convert(#base);}
            } else {
                quote! {}
            };
            emitted.push(quote!{
                pub proof fn #n(tracked #base:#native_store,#(#params),*)->(tracked #out:(Tracked<Self>,Tracked<Option<#opt #types>>,Tracked<#collection #types>))
                    requires #(#requirements,)* #actual_base==#stored_value,
                    ensures ::vstd::prelude::imply(#out.1@ is Some,#out.1@->Some_0.instance_id()==#out.0@.id()),
                        {let #init_opt:Option<#optty>=#io;(#out.1@ is Some&&#init_opt is Some&&#out.1@->Some_0.value()==#init_opt->Some_0)||(#out.1@ is None&&#init_opt is None)},
                        #out.2@.instance_id()==#out.0@.id(),#out.2@.map()==#im,
                {
                    broadcast use {::vstd::map::group_map_lemmas,::vstd::set::group_set_lemmas,::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas};
                    let #init_opt:Option<#optty>=#io;
                    #converted
                    let tracked #raw=Protocol #expr::#n(#base,#(#pn),*);
                    let #initial=choose|#initial:State #types|State #expr::#n(#initial,#(#pn),*)&&#initial.invariant()&&#raw.fragment()==Protocol #expr::embed(#initial);
                    let tracked #md=::vstd::resource::tsm_context::Descriptor::alloc(__StorageMetadata #expr{#location:#raw.loc(),#marker_value});
                    let tracked(#optraw,#mapraw)=Protocol #expr::#take_opt(#raw);
                    assert(#optraw.fragment()==Fragment #expr::#factory_opt(#init_opt));
                    ::vstd::resource::tsm_collections::map_join(IMap::<#keyty,#valty>::empty(),IMap::<#keyty,#valty>::empty());
                    assert(#mapraw.fragment()==Fragment #expr::#factory_map(#im));
                    let tracked #rest=if #init_opt is Some{Some(<#opt #types>::__from_token(#optraw,#md.clone(),#init_opt->Some_0))}else{None};
                    let tracked #mapraw=<#collection #types>::__from_token(#mapraw,#md.clone(),#im);
                    (Tracked(Self{metadata:#md}),Tracked(#rest),Tracked(#mapraw))
                }
            });
            continue;
        }
        if flat.operations.len() == 1 {
            let (f, op, binding) = &flat.operations[0];
            let Some(binding) = binding else {
                return Err(Error::new(
                    n.span(),
                    "binding Option removal requires its original payload binding",
                ));
            };
            if f != opt
                || !op.is_remove()
                || !matches!(op.elt, MonoidElt::OptionSome(None))
                || tr.kind != TransitionKind::Transition
                || !flat.assertions.is_empty()
            {
                return Err(Error::new(
                    n.span(),
                    "binding single operation must consume its Option owner",
                ));
            }
            let requirements: Vec<_> = flat
                .requirements
                .iter()
                .map(|e| local(e, sm))
                .collect::<Result<_, _>>()?;
            emitted.push(quote!{
                pub proof fn #n(tracked &self,#(#params,)*tracked #owner:#opt #types)
                    requires #owner.instance_id()==self.id(),{let #binding=#owner.value();true #(&& #requirements)*},
                {
                    ::vstd::prelude::use_type_invariant(&#owner);self.metadata.agrees(&#owner.metadata);
                    let #value=#owner.value();let #binding=#value;
                    let tracked #raw=#owner.raw.get().tracked_unwrap();
                    assert(Protocol #expr::#req(#raw.fragment(),Fragment #expr::unit(),IMap::<#keyty,#valty>::empty(),#(#pn),*)) by {
                        assert forall|#frame:Fragment #types,#pre:State #types|
                            #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#raw.fragment(),Fragment #expr::unit()),#frame)==Protocol #expr::embed(#pre)
                            implies State #expr::#enabled(#pre,#(#pn),*)&&State #expr::#owners(#pre,#raw.fragment(),Fragment #expr::unit(),#(#pn),*) by {
                                Fragment #expr::op_unit(#raw.fragment());assert(#pre.#opt==Some(#value));
                            }
                    }
                    let tracked #rest=Protocol #expr::#n(#raw,#(#pn),*);
                }
            });
            continue;
        }
        if flat.operations.len() != 2 {
            return Err(Error::new(
                n.span(),
                "binding exchange/guard requires logical singleton then physical singleton",
            ));
        }
        let (logical, logical_op, binding) = &flat.operations[0];
        let (ph, physical_op, physical_binding) = &flat.operations[1];
        if logical != field || ph != store {
            return Err(Error::new(
                n.span(),
                "binding operations must address logical then matching physical map",
            ));
        }
        let MonoidElt::SingletonKV(key, None) = &logical_op.elt else {
            return Err(Error::new(
                n.span(),
                "binding logical singleton requires its payload binding",
            ));
        };
        let Some(binding) = binding else {
            return Err(Error::new(
                n.span(),
                "binding logical operation needs its original binding",
            ));
        };
        let key = local(key, sm)?;
        let requirements: Vec<_> = flat
            .requirements
            .iter()
            .map(|e| local(e, sm))
            .collect::<Result<_, _>>()?;
        let assertions: Vec<_> = flat
            .assertions
            .iter()
            .map(|e| local(e, sm))
            .collect::<Result<_, _>>()?;
        let native_pre_map = if finite {
            quote! {#pre.#field.to_imap()}
        } else {
            quote! {#pre.#field}
        };
        let actual_pre_storage = if finite {
            quote! {#pre.#store.to_imap()}
        } else {
            quote! {#pre.#store}
        };
        if logical_op.is_have() && physical_op.is_guard() {
            let MonoidElt::SingletonKV(pk, Some(pv)) = &physical_op.elt else {
                return Err(Error::new(
                    n.span(),
                    "binding guard requires explicit physical key/value",
                ));
            };
            if quote! {#pk}.to_string() != key.to_string()
                || physical_binding.is_some()
                || !matches!(
                    tr.kind,
                    TransitionKind::Property | TransitionKind::ReadonlyTransition
                )
                || !assertions.is_empty()
            {
                return Err(Error::new(
                    n.span(),
                    "binding guard keeps the logical key and is readonly/property",
                ));
            }
            let guarded_value = local(pv, sm)?;
            emitted.push(quote!{
                pub proof fn #n<#lifetime>(tracked &self,#(#params,)*tracked #owner:&#lifetime #field #types)->(tracked #out:&#lifetime #valty)
                    requires #owner.instance_id()==self.id(),#owner.key()==#key,{let #binding=#owner.value();true #(&& #requirements)*},
                    ensures *#out==#guarded_value,
                {
                    ::vstd::prelude::use_type_invariant(#owner);self.metadata.agrees(&#owner.metadata);
                    let #value=#owner.value();let #binding=#value;let tracked #raw=#owner.borrow_token();
                    assert(::vstd::resource::tsm_storage::frame_guard::<Protocol #types>(#raw.fragment(),IMap::<#keyty,#valty>::empty().insert(#key,#guarded_value))) by {
                        assert forall|#frame:Fragment #types,#pre:State #types|
                            #pre.invariant()&&Fragment #expr::op(#raw.fragment(),#frame)==Protocol #expr::embed(#pre)
                            implies IMap::<#keyty,#valty>::empty().insert(#key,#guarded_value).submap_of(#pre.__storage()) by {
                                ::vstd::resource::tsm_collections::map_owned_frame(#raw.fragment().#field,#frame.#field,#native_pre_map,#key,#value);
                                assert(State #expr::#enabled(#pre,#(#pn),*));
                                assert(#pre.#store.contains_key(#key));assert(#pre.#store[#key]==#guarded_value);
                            }
                    }
                    ::vstd::resource::tsm_helpers::guard_value(#raw,#key,#guarded_value)
                }
            });
            continue;
        }
        let MonoidElt::SingletonKV(pk, None) = &physical_op.elt else {
            return Err(Error::new(
                n.span(),
                "binding withdrawal requires its actual payload binding",
            ));
        };
        let Some(physical_binding) = physical_binding else {
            return Err(Error::new(
                n.span(),
                "binding withdrawal needs original physical binding",
            ));
        };
        if !logical_op.is_remove()
            || !physical_op.stmt.is_withdraw()
            || quote! {#pk}.to_string() != key.to_string()
            || tr.kind != TransitionKind::Transition
        {
            return Err(Error::new(
                n.span(),
                "binding mutation consumes logical singleton and withdraws matching physical key",
            ));
        }
        emitted.push(quote!{
            pub proof fn #n(tracked &self,#(#params,)*tracked #owner:#field #types)->(tracked #out:#valty)
                requires #owner.instance_id()==self.id(),#owner.key()==#key,{let #binding=#owner.value();true #(&& #requirements)*},
                ensures {let #binding=#owner.value();let #physical_binding=#out;true #(&& #assertions)*},
            {
                broadcast use {::vstd::map::group_map_lemmas,::vstd::set::group_set_lemmas,::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas};
                ::vstd::prelude::use_type_invariant(&#owner);self.metadata.agrees(&#owner.metadata);
                let #value=#owner.value();let #binding=#value;let tracked #raw=#owner.raw.get().tracked_unwrap();let #before=#raw.fragment();
                assert(Protocol #expr::#req(#before,Fragment #expr::unit(),IMap::<#keyty,#valty>::empty(),#(#pn),*)) by {
                    assert forall|#frame:Fragment #types,#pre:State #types|
                        #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,Fragment #expr::unit()),#frame)==Protocol #expr::embed(#pre)
                        implies State #expr::#enabled(#pre,#(#pn),*)&&State #expr::#owners(#pre,#before,Fragment #expr::unit(),#(#pn),*) by {
                            Fragment #expr::op_unit(#before);
                            ::vstd::resource::tsm_collections::map_owned_frame(#before.#field,#frame.#field,#native_pre_map,#key,#value);
                        }
                }
                let tracked (#rest,#withdrawn)=Protocol #expr::#n(#raw,#(#pn),*);
                let (#pre,#post,#frame)=Protocol #expr::#witness(#before,Fragment #expr::unit(),#rest.fragment(),IMap::<#keyty,#valty>::empty(),#withdrawn,#(#pn),*);
                assert(#pre.#store.contains_key(#key));
                assert(#withdrawn==IMap::<#keyty,#valty>::empty().insert(#key,#pre.#store[#key])) by {
                    assert forall|#point:#keyty|#[trigger] #withdrawn.contains_key(#point) == (#point==#key) by {};
                }
                let tracked #out=::vstd::resource::tsm_helpers::take_singleton(#withdrawn,#key);
                let #physical_binding=#out;#(assert(#assertions);)*
                #out
            }
        });
    }
    let conversion = if finite {
        quote! {
            proof fn #convert(tracked input: #native_type)->(tracked output:IMap<#keyty,#valty>)
                ensures output==input.to_imap(), decreases input.len(),
            {
                broadcast use {::vstd::map::group_map_lemmas,::vstd::imap::group_imap_lemmas,::vstd::set::group_set_lemmas,::vstd::iset::group_iset_lemmas};
                let ghost original=input;
                ::vstd::set_lib::lemma_set_empty_equivalency_len(input.dom());
                if input.len()==0 {
                    let tracked output=IMap::tracked_empty();
                    assert(::vstd::prelude::ext_equal(output,original.to_imap()));
                    output
                } else {
                    let key=choose|key:#keyty|input.dom().contains(key);
                    ::vstd::set::lemma_set_remove_len(input.dom(),key);
                    let tracked mut input=input;
                    let tracked value=input.tracked_remove(key);
                    let tracked mut output=Self::#convert(input);
                    output.tracked_insert(key,value);
                    assert(::vstd::prelude::ext_equal(output,original.to_imap()));
                    output
                }
            }
        }
    } else {
        quote! {}
    };
    Ok(quote! {
        #(#attrs)*tracked struct __StorageMetadata #decl #wc{#location: ::vstd::resource::Loc,#marker}
        #opt_wrapper #map_wrapper
        #(#attrs)*pub tracked struct Instance #decl #wc{metadata:#descriptor}
        impl #decl Instance #types #wc{
            pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}
            pub proof fn clone(tracked &self)->(tracked #out:Self)ensures #out.id()==self.id(),{Self{metadata:self.metadata.clone()}}
            #conversion
            #(#emitted)*
        }
    })
}
