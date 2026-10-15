//! Strict physical-backed logical IMap roles sharing the actual StorageIMap base.
use crate::ast::*;
use crate::field_access_visitor::visit_field_accesses;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};
#[derive(Default)]
struct Flat {
    init: HashMap<String, Expr>,
    update: HashMap<String, Expr>,
    req: Vec<Expr>,
    assertions: Vec<Expr>,
    ops: Vec<(Ident, SpecialOp)>,
}
fn collect(s: &TransitionStmt, f: &mut Flat) -> Result<(), Error> {
    match s {
        TransitionStmt::Block(_, children) => {
            for c in children {
                collect(c, f)?;
            }
        }
        TransitionStmt::Initialize(_, n, e) => {
            if f.init.insert(n.to_string(), e.clone()).is_some() {
                return Err(Error::new(
                    n.span(),
                    "physical logical-map initialization repeats a field",
                ));
            }
        }
        TransitionStmt::Update(_, n, e) => {
            if f.update.insert(n.to_string(), e.clone()).is_some() {
                return Err(Error::new(
                    n.span(),
                    "physical logical-map mutation repeats a field",
                ));
            }
        }
        TransitionStmt::Require(_, e) => f.req.push(e.clone()),
        TransitionStmt::Assert(_, e, _) => f.assertions.push(e.clone()),
        TransitionStmt::Split(_, kind, children) => {
            let SplitKind::Special(n, op, _, None) = &**kind else {
                return Err(Error::new(
                    *s.get_span(),
                    "physical logical-map facade requires explicit unbound operations",
                ));
            };
            f.ops.push((n.clone(), op.clone()));
            for c in children {
                collect(c, f)?;
            }
        }
        _ => {
            return Err(Error::new(
                *s.get_span(),
                "physical logical-map facade requires straight-line operations",
            ))
        }
    }
    Ok(())
}
pub fn needed(sm: &SM) -> bool {
    sm.fields.len() == 3
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::Variable(_)))
            .count()
            == 1
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::IMap(..)))
            .count()
            == 1
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::StorageIMap(..)))
            .count()
            == 1
}
fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
    for token in tokens {
        match token {
            TokenTree::Ident(n) => {
                names.insert(n.to_string());
            }
            TokenTree::Group(g) => reserve(g.stream(), names),
            _ => {}
        }
    }
}
fn fresh(sm: &SM, tr: &Transition, f: &Flat, label: &str) -> Ident {
    let mut names: HashSet<_> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(sm.transitions.iter().map(|t| t.name.to_string()))
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .collect();
    if let Some(g) = &sm.generics {
        reserve(quote! {#g}, &mut names);
    }
    for e in f
        .init
        .values()
        .chain(f.update.values())
        .chain(&f.req)
        .chain(&f.assertions)
    {
        reserve(quote! {#e}, &mut names);
    }
    for (_, op) in &f.ops {
        if let MonoidElt::SingletonKV(k, v) = &op.elt {
            reserve(quote! {#k #v}, &mut names);
        }
    }
    let mut name = format!("__tsm_physical_map_{label}");
    while names.contains(&name) {
        name.push('_');
    }
    Ident::new(&name, Span::mixed_site())
}
fn native(
    e: &Expr,
    fields: &HashMap<String, Field>,
    var: &Ident,
    value: TokenStream,
) -> Result<TokenStream, Error> {
    let mut e = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut e,
        |errors, f, node| {
            if f.name == *var {
                *node = Expr::Verbatim(value.clone());
            } else {
                errors.push(Error::new(
                    f.name.span(),
                    "physical logical-map operands may read only the supplied variable",
                ));
            }
        },
        &mut errors,
        fields,
    );
    if let Some(e) = errors.into_iter().next() {
        Err(e)
    } else {
        Ok(quote! {#e})
    }
}
fn property_expr(e: &Expr, fields: &HashMap<String, Field>) -> Result<TokenStream, Error> {
    let mut e = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut e,
        |errors, field, _| {
            errors.push(Error::new(
                field.name.span(),
                "physical logical-map property requires explicit supplied singleton operands",
            ));
        },
        &mut errors,
        fields,
    );
    if let Some(error) = errors.into_iter().next() {
        Err(error)
    } else {
        Ok(quote! {#e})
    }
}
fn pair(op: &SpecialOp) -> Result<(&Expr, &Expr), Error> {
    if let MonoidElt::SingletonKV(k, Some(v)) = &op.elt {
        Ok((k, v))
    } else {
        Err(Error::new(
            Span::call_site(),
            "physical logical-map facade requires explicit singleton key/value operands",
        ))
    }
}

pub fn output(sm: &SM, selected: &HashSet<String>) -> Result<TokenStream, Error> {
    if !needed(sm) {
        return Err(Error::new(
            sm.name.span(),
            "physical logical-map facade requires one Variable, IMap and StorageIMap",
        ));
    }
    let variable = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::Variable(_)))
        .unwrap();
    let var = &variable.name;
    let varty = variable.get_type();
    let logical = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::IMap(..)))
        .unwrap();
    let map = &logical.name;
    let ShardableType::IMap(keyty, valty) = &logical.stype else {
        unreachable!()
    };
    let store = sm.fields.iter().find(|f| f.stype.is_storage()).unwrap();
    let storage = &store.name;
    let ShardableType::StorageIMap(sk, sv) = &store.stype else {
        unreachable!()
    };
    if keyty != sk || valty != sv {
        return Err(Error::new(
            map.span(),
            "physical logical-map and store key/value types must match",
        ));
    }
    let mut names: HashSet<String> = [
        "Instance",
        "Protocol",
        "Token",
        "State",
        "Fragment",
        "TransitionObservation",
        "__StorageMetadata",
        "Ghost",
        "Tracked",
        "Option",
        "IMap",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    for f in &sm.fields {
        if !names.insert(f.name.to_string()) {
            return Err(Error::new(
                f.name.span(),
                "physical logical-map type collides with a generated type",
            ));
        }
    }
    let collection = format_ident!("{}_collection", map);
    if !names.insert(collection.to_string()) {
        return Err(Error::new(
            map.span(),
            "physical logical-map collection name collision",
        ));
    }
    if let Some(generics) = &sm.generics {
        for parameter in &generics.params {
            let name = match parameter {
                verus_syn::GenericParam::Type(p) => Some(&p.ident),
                verus_syn::GenericParam::Const(p) => Some(&p.ident),
                _ => None,
            };
            if let Some(name) = name {
                if names.contains(&name.to_string()) {
                    return Err(Error::new(
                        name.span(),
                        "generic parameter conflicts with a generated physical logical-map type",
                    ));
                }
            }
        }
    }
    let mut methods: HashSet<String> = ["id", "clone", "invariant", "observe"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    for t in &sm.transitions {
        if !methods.insert(t.name.to_string())
            || !methods.insert(format!("__physical_raw_{}", t.name))
        {
            return Err(Error::new(
                t.name.span(),
                "transition collides with a physical logical-map method",
            ));
        }
    }
    let (generic, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generic);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let first = sm.transitions.first().ok_or_else(|| {
        Error::new(
            sm.name.span(),
            "physical logical-map facade needs initialization",
        )
    })?;
    let empty = Flat::default();
    let location = fresh(sm, first, &empty, "protocol_loc");
    let marker_name = fresh(sm, first, &empty, "types");
    let marker = args
        .as_ref()
        .map(|a| quote! {#marker_name:core::marker::PhantomData<(#a,)>,});
    let marker_value = args
        .as_ref()
        .map(|_| quote! {#marker_name:core::marker::PhantomData,});
    let token = quote! {Token #types};
    let metadata = quote! {__StorageMetadata #types};
    let descriptor = quote! {::vstd::resource::tsm_context::Descriptor<#metadata>};
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let factory_var = format_ident!("field_{}", var);
    let getter_var = format_ident!("value_{}", var);
    let owns_var = format_ident!("owns_{}", var);
    let factory_map = format_ident!("field_{}", map);
    let take_var = format_ident!("take_{}", var);
    let take_map = format_ident!("take_{}", map);
    let col_out = fresh(sm, first, &empty, "collection_out");
    let col_raw = fresh(sm, first, &empty, "collection_raw");
    let col_native = fresh(sm, first, &empty, "collection_native");
    let col_loc = fresh(sm, first, &empty, "collection_loc");
    let col_key = fresh(sm, first, &empty, "collection_key");
    let col_original = fresh(sm, first, &empty, "collection_original");
    let col_value = fresh(sm, first, &empty, "collection_value");
    let col_single = fresh(sm, first, &empty, "collection_single");
    let col_remainder = fresh(sm, first, &empty, "collection_remainder");
    let col_owned = fresh(sm, first, &empty, "collection_owned");
    let col_rest = fresh(sm, first, &empty, "collection_rest");
    let col_md = fresh(sm, first, &empty, "collection_md");
    let col_metadata = fresh(sm, first, &empty, "collection_metadata");
    let col_id = fresh(sm, first, &empty, "collection_id");
    let col_item = fresh(sm, first, &empty, "collection_item");
    let col_updated = fresh(sm, first, &empty, "collection_updated");
    let col_entry_raw = fresh(sm, first, &empty, "collection_entry_raw");
    let collection_items = quote! {
        #[verifier::inline]
        spec fn __slots(raw:Option<#token>,native:IMap<#keyty,#valty>,metadata:Option<#descriptor>,id: ::vstd::resource::Loc)->bool {
            match raw {
                None => native==IMap::<#keyty,#valty>::empty(),
                Some(raw) => metadata is Some && metadata->Some_0.id()==id && raw.loc()==metadata->Some_0.value().#location && raw.fragment()==Fragment #expr::#factory_map(native),
            }
        }
        pub proof fn borrow_token(tracked &self)->(tracked #col_out:&#token)
            requires self.has_resource(),
            ensures #col_out.fragment()==Fragment #expr::#factory_map(self.map()),#col_out.loc()==self.__protocol_loc(),
        {::vstd::prelude::use_type_invariant(self);self.raw.borrow().tracked_borrow()}
        proof fn __remove_raw(tracked #col_raw:&mut Tracked<Option<#token>>,tracked #col_native:&mut Ghost<IMap<#keyty,#valty>>,#col_loc: ::vstd::resource::Loc,#col_key:#keyty)->(tracked #col_out:#token)
            requires old(#col_raw)@ is Some,old(#col_raw)@->Some_0.loc()==#col_loc,old(#col_raw)@->Some_0.fragment()==Fragment #expr::#factory_map(old(#col_native)@),old(#col_native)@.contains_key(#col_key),
            ensures final(#col_raw)@ is Some,final(#col_raw)@->Some_0.loc()==#col_loc,final(#col_raw)@->Some_0.fragment()==Fragment #expr::#factory_map(final(#col_native)@),final(#col_native)@==old(#col_native)@.remove(#col_key),#col_out.loc()==#col_loc,#col_out.fragment()==Fragment #expr::#factory_map(IMap::empty().insert(#col_key,old(#col_native)@[#col_key])),
        {
            broadcast use {::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas};
            let #col_original=#col_native@;
            let #col_value=#col_original[#col_key];
            let #col_single=IMap::empty().insert(#col_key,#col_value);
            let #col_remainder=#col_original.remove(#col_key);
            ::vstd::resource::tsm_collections::map_join(#col_single,#col_remainder);
            assert(::vstd::prelude::ext_equal(#col_single.union_prefer_right(#col_remainder),#col_original));
            Fragment #expr::op_unit(Fragment #expr::unit());
            assert(Fragment #expr::op(Fragment #expr::#factory_map(#col_single),Fragment #expr::#factory_map(#col_remainder))==Fragment #expr::#factory_map(#col_original));
            let tracked #col_owned=#col_raw.borrow_mut().tracked_take();
            let tracked(#col_out,#col_rest)=#col_owned.split(Fragment #expr::#factory_map(#col_single),Fragment #expr::#factory_map(#col_remainder));
            *#col_raw=Tracked(Some(#col_rest));*#col_native=Ghost(#col_remainder);#col_out
        }
        pub proof fn remove(tracked &mut self,#col_key:#keyty)->(tracked #col_out:#map #types)
            requires old(self).map().contains_key(#col_key),
            ensures final(self).instance_id()==old(self).instance_id(),final(self).map()==old(self).map().remove(#col_key),#col_out.instance_id()==old(self).instance_id(),#col_out.key()==#col_key,#col_out.value()==old(self).map()[#col_key],
        {
            ::vstd::prelude::use_type_invariant(&*self);
            assert(self.raw@ is Some);
            let #col_value=self.map()[#col_key];
            let tracked #col_md=self.metadata.borrow().tracked_borrow().clone();
            let tracked #col_out=Self::__remove_raw(&mut self.raw,&mut self.native,#col_md.value().#location,#col_key);
            <#map #types>::__from_token(#col_out,#col_md,#col_key,#col_value)
        }
        proof fn __insert_raw(tracked #col_raw:&mut Tracked<Option<#token>>,tracked #col_native:&mut Ghost<IMap<#keyty,#valty>>,tracked #col_metadata:&mut Tracked<Option<#descriptor>>,#col_id: ::vstd::resource::Loc,tracked #col_item:#map #types)
            requires Self::__slots(old(#col_raw)@,old(#col_native)@,old(#col_metadata)@,#col_id),#col_item.instance_id()==#col_id,!old(#col_native)@.contains_key(#col_item.key()),
            ensures Self::__slots(final(#col_raw)@,final(#col_native)@,final(#col_metadata)@,#col_id),final(#col_native)@==old(#col_native)@.insert(#col_item.key(),#col_item.value()),final(#col_raw)@ is Some,
        {
            ::vstd::prelude::use_type_invariant(&#col_item);
            broadcast use {::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas};
            let #col_original=#col_native@;
            let #col_key=#col_item.key();let #col_value=#col_item.value();
            let #col_single=IMap::empty().insert(#col_key,#col_value);
            let #col_updated=#col_original.insert(#col_key,#col_value);
            if #col_raw@ is Some {
                #col_metadata.borrow().tracked_borrow().agrees(&#col_item.metadata);
                ::vstd::resource::tsm_collections::map_join(#col_original,#col_single);
                assert(::vstd::prelude::ext_equal(#col_original.union_prefer_right(#col_single),#col_updated));
                Fragment #expr::op_unit(Fragment #expr::unit());
                assert(Fragment #expr::op(Fragment #expr::#factory_map(#col_original),Fragment #expr::#factory_map(#col_single))==Fragment #expr::#factory_map(#col_updated));
                let tracked #col_owned=#col_raw.borrow_mut().tracked_take();
                let tracked #col_entry_raw=#col_item.raw.get().tracked_unwrap();
                *#col_raw=Tracked(Some(#col_owned.join(#col_entry_raw)));
            }else{
                assert(#col_original==IMap::<#keyty,#valty>::empty());
                assert(#col_updated==#col_single);
                *#col_raw=Tracked(Some(#col_item.raw.get().tracked_unwrap()));
                *#col_metadata=Tracked(Some(#col_item.metadata));
            }
            *#col_native=Ghost(#col_updated);
        }
        pub proof fn insert(tracked &mut self,tracked #col_item:#map #types)
            requires old(self).instance_id()==#col_item.instance_id(),!old(self).map().contains_key(#col_item.key()),
            ensures final(self).instance_id()==old(self).instance_id(),final(self).map()==old(self).map().insert(#col_item.key(),#col_item.value()),final(self).has_resource(),
        {
            ::vstd::prelude::use_type_invariant(&*self);
            Self::__insert_raw(&mut self.raw,&mut self.native,&mut self.metadata,self.id@,#col_item);
        }

    };
    let wrappers = quote! {
    #(#attrs)*struct __StorageMetadata #decl #wc{ghost #location: ::vstd::resource::Loc,#marker}
    #(#attrs)*#[allow(non_camel_case_types)]pub tracked struct #var #decl #wc{raw:Tracked<Option<#token>>,metadata:#descriptor}
    impl #decl #var #types #wc{
    #[verifier::type_invariant]spec fn invariant(self)->bool{self.raw@ is Some&&self.raw@->Some_0.loc()==self.metadata.value().#location&&self.raw@->Some_0.fragment().#owns_var()&&self.raw@->Some_0.fragment()==Fragment #expr::#factory_var(self.value())}
    pub closed spec fn instance_id(&self)->::vstd::resource::Loc{self.metadata.id()}
    pub closed spec fn __protocol_loc(&self)->::vstd::resource::Loc{self.metadata.value().#location}
    pub closed spec fn value(&self)->#varty{self.raw@->Some_0.fragment().#getter_var()}
    pub proof fn borrow_token(tracked &self)->(tracked out:&#token)ensures out.loc()==self.__protocol_loc(),out.fragment()==Fragment #expr::#factory_var(self.value()),{::vstd::prelude::use_type_invariant(self);self.raw.borrow().tracked_borrow()}
    proof fn __from_token(tracked raw:#token,tracked metadata:#descriptor)->(tracked out:Self)requires raw.loc()==metadata.value().#location,raw.fragment().#owns_var(),raw.fragment()==Fragment #expr::#factory_var(raw.fragment().#getter_var()),ensures out.instance_id()==metadata.id(),out.value()==raw.fragment().#getter_var(),{Self{raw:Tracked(Some(raw)),metadata}}
    }
    #(#attrs)*#[allow(non_camel_case_types)]pub tracked struct #map #decl #wc{raw:Tracked<Option<#token>>,metadata:#descriptor,key:Ghost<#keyty>,value:Ghost<#valty>}
    impl #decl #map #types #wc{
    #[verifier::type_invariant]spec fn invariant(self)->bool{self.raw@ is Some&&self.raw@->Some_0.loc()==self.metadata.value().#location&&self.raw@->Some_0.fragment()==Fragment #expr::#factory_map(IMap::<#keyty,#valty>::empty().insert(self.key@,self.value@))}
    pub closed spec fn instance_id(&self)->::vstd::resource::Loc{self.metadata.id()}
    pub closed spec fn __protocol_loc(&self)->::vstd::resource::Loc{self.metadata.value().#location}
    pub closed spec fn key(&self)->#keyty{self.key@}pub closed spec fn value(&self)->#valty{self.value@}
    pub proof fn borrow_token(tracked &self)->(tracked out:&#token)ensures out.loc()==self.__protocol_loc(),out.fragment()==Fragment #expr::#factory_map(IMap::<#keyty,#valty>::empty().insert(self.key(),self.value())),{::vstd::prelude::use_type_invariant(self);self.raw.borrow().tracked_borrow()}
    proof fn __from_token(tracked raw:#token,tracked metadata:#descriptor,key:#keyty,value:#valty)->(tracked out:Self)requires raw.loc()==metadata.value().#location,raw.fragment()==Fragment #expr::#factory_map(IMap::<#keyty,#valty>::empty().insert(key,value)),ensures out.instance_id()==metadata.id(),out.key()==key,out.value()==value,{Self{raw:Tracked(Some(raw)),metadata,key:Ghost(key),value:Ghost(value)}}
    }
    #(#attrs)*#[allow(non_camel_case_types)]pub tracked struct #collection #decl #wc{raw:Tracked<Option<#token>>,metadata:Tracked<Option<#descriptor>>,native:Ghost<IMap<#keyty,#valty>>,id:Ghost<::vstd::resource::Loc>}
    impl #decl #collection #types #wc{
    #[verifier::type_invariant]spec fn invariant(self)->bool{Self::__slots(self.raw@,self.native@,self.metadata@,self.id@)}
    #collection_items
    pub closed spec fn instance_id(&self)->::vstd::resource::Loc{self.id@}
    pub closed spec fn __protocol_loc(&self)->::vstd::resource::Loc recommends self.has_resource(),{self.metadata@->Some_0.value().#location}pub closed spec fn map(&self)->IMap<#keyty,#valty>{self.native@}pub closed spec fn has_resource(&self)->bool{self.raw@ is Some}
    pub proof fn empty(id: ::vstd::resource::Loc)->(tracked out:Self)ensures out.instance_id()==id,out.map()==IMap::<#keyty,#valty>::empty(),!out.has_resource(),{Self{raw:Tracked(None),metadata:Tracked(None),native:Ghost(IMap::empty()),id:Ghost(id)}}
    proof fn __from_token(tracked raw:#token,tracked metadata:#descriptor,native:IMap<#keyty,#valty>)->(tracked out:Self)requires raw.loc()==metadata.value().#location,raw.fragment()==Fragment #expr::#factory_map(native),ensures out.instance_id()==metadata.id(),out.map()==native,out.has_resource(),{let id=metadata.id();Self{raw:Tracked(Some(raw)),metadata:Tracked(Some(metadata)),native:Ghost(native),id:Ghost(id)}}
    }
    };
    let obs_variable = fresh(sm, first, &empty, "observation_variable");
    let obs_collection = fresh(sm, first, &empty, "observation_collection");
    let obs_variable_raw = fresh(sm, first, &empty, "observation_variable_raw");
    let obs_collection_raw = fresh(sm, first, &empty, "observation_collection_raw");
    let obs_state = fresh(sm, first, &empty, "observation_state");
    let obs_left = fresh(sm, first, &empty, "observation_left");
    let obs_right = fresh(sm, first, &empty, "observation_right");
    let obs_key = fresh(sm, first, &empty, "observation_key");
    let observe = quote! {
        pub proof fn observe(tracked &self,tracked #obs_variable:&#var #types,tracked #obs_collection:&#collection #types)->(#obs_state:State #types)
            requires #obs_variable.instance_id()==self.id(),#obs_collection.instance_id()==self.id(),#obs_collection.has_resource(),
            ensures #obs_state.invariant(),#obs_state.#var==#obs_variable.value(),#obs_collection.map().submap_of(#obs_state.#map),
        {
            ::vstd::prelude::use_type_invariant(#obs_variable);::vstd::prelude::use_type_invariant(#obs_collection);
            self.metadata.agrees(&#obs_variable.metadata);self.metadata.agrees(#obs_collection.metadata.borrow().tracked_borrow());
            let tracked #obs_variable_raw=#obs_variable.borrow_token();let tracked #obs_collection_raw=#obs_collection.borrow_token();
            let(#obs_state,#obs_left,#obs_right)=#obs_variable_raw.compatible_with(#obs_collection_raw);
            assert(#obs_state.#var==#obs_variable.value());
            assert forall|#obs_key:#keyty|#[trigger] #obs_collection.map().contains_key(#obs_key) implies #obs_state.#map.contains_key(#obs_key)&&#obs_state.#map[#obs_key]==#obs_collection.map()[#obs_key] by {
                ::vstd::resource::tsm_collections::map_owned_frame(#obs_collection_raw.fragment().#map,#obs_right.#map,#obs_state.#map,#obs_key,#obs_collection.map()[#obs_key]);
            }
            #obs_state
        }
    };
    let mut emitted = Vec::new();
    for tr in &sm.transitions {
        let mut flat = Flat::default();
        collect(&tr.body, &mut flat)?;
        let name = &tr.name;
        let params: Vec<_> = tr
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let t = &p.ty;
                quote! {#n:#t}
            })
            .collect();
        let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
        let owned = fresh(sm, tr, &flat, "owned");
        let before = fresh(sm, tr, &flat, "before");
        let after = fresh(sm, tr, &flat, "after");
        let frame = fresh(sm, tr, &flat, "frame");
        let md = fresh(sm, tr, &flat, "metadata");
        let out = fresh(sm, tr, &flat, "output");
        let entry = fresh(sm, tr, &flat, "entry");
        let map_raw = fresh(sm, tr, &flat, "map_raw");
        let var_raw = fresh(sm, tr, &flat, "var_raw");
        let rest = fresh(sm, tr, &flat, "rest");
        let old_value = fresh(sm, tr, &flat, "old_value");
        let actual = fresh(sm, tr, &flat, "permission");
        let dep = fresh(sm, tr, &flat, "deposit");
        let certificate = fresh(sm, tr, &flat, "certificate");
        let slot = fresh(sm, tr, &flat, "slot");
        let key = fresh(sm, tr, &flat, "key");
        let value = fresh(sm, tr, &flat, "value");
        let native_var = fresh(sm, tr, &flat, "native_variable");
        if tr.kind == TransitionKind::Init {
            if flat.init.len() != 3 || flat.ops.len() > 0 || flat.update.len() > 0 {
                return Err(Error::new(
                    name.span(),
                    "physical logical-map initializer must initialize all three fields",
                ));
            }
            let iv = &flat.init[&var.to_string()];
            let im = &flat.init[&map.to_string()];
            let is = &flat.init[&storage.to_string()];
            let req = &flat.req;
            emitted.push(quote!{pub proof fn #name(#(#params),*)->(tracked #out:(Tracked<Self>,Tracked<#var #types>,Tracked<#collection #types>))requires #(#req,)*#is==IMap::<#keyty,#valty>::empty(),ensures #out.1@.instance_id()==#out.0@.id(),#out.1@.value()==#iv,#out.2@.instance_id()==#out.0@.id(),#out.2@.map()==#im,{
 broadcast use {::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas};
 let tracked #owned=Protocol #expr::#name(IMap::tracked_empty(),#(#pn),*);
 let #before=choose|#before:State #types|State #expr::#name(#before,#(#pn),*)&&#before.invariant()&&#owned.fragment()==Protocol #expr::embed(#before);
 let tracked #md=::vstd::resource::tsm_context::Descriptor::alloc(__StorageMetadata #expr{#location:#owned.loc(),#marker_value});
 let tracked(#var_raw,#map_raw)=Protocol #expr::#take_var(#owned);
 assert(#var_raw.fragment()==Fragment #expr::#factory_var(#iv));
 ::vstd::resource::tsm_collections::map_join(IMap::<#keyty,#valty>::empty(),#im);
 assert(#map_raw.fragment()==Fragment #expr::#factory_map(#im));
 let tracked #var_raw=<#var #types>::__from_token(#var_raw,#md.clone());let tracked #map_raw=<#collection #types>::__from_token(#map_raw,#md.clone(),#im);
 (Tracked(Self{metadata:#md}),Tracked(#var_raw),Tracked(#map_raw))}});
            continue;
        }
        if flat.ops.len() != 2 {
            return Err(Error::new(name.span(),"physical logical-map step requires one logical and one physical singleton operation"));
        }
        let (lo_field, lo) = &flat.ops[0];
        let (ph_field, ph) = &flat.ops[1];
        if lo_field != map || ph_field != storage {
            return Err(Error::new(
                name.span(),
                "physical logical-map operations must address the logical then storage fields",
            ));
        }
        let (lk, lv) = pair(lo)?;
        let (pk, pv) = pair(ph)?;
        if lk != pk || lv != pv {
            return Err(Error::new(
                name.span(),
                "physical logical-map logical and physical operands must match structurally",
            ));
        }
        if tr.kind == TransitionKind::Property {
            if !lo.is_have() || !ph.is_guard() || !flat.update.is_empty() {
                return Err(Error::new(
                    name.span(),
                    "physical logical-map property must Have then Guard",
                ));
            }
            let observed_key = property_expr(lk, &fields)?;
            let observed_value = property_expr(lv, &fields)?;
            let mut reads = vec![];
            for e in flat.req.iter().chain(&flat.assertions) {
                reads.push(property_expr(e, &fields)?);
            }
            let req = &reads[..flat.req.len()];
            let ensures = &reads[flat.req.len()..];
            let requires = format_ident!("{}_requires", name);
            let enabled = format_ident!("{}_enabled", name);
            let owners = format_ident!("{}_owners_enabled", name);
            let guarded = format_ident!("{}_guarded", name);
            emitted.push(quote!{pub proof fn #name<'a>(tracked &self,#(#params,)*tracked #entry:&'a #map #types)->(tracked #out:&'a #valty)requires #entry.instance_id()==self.id(),#entry.key()==#observed_key,#entry.value()==#observed_value,#(#req,)*ensures *#out==#observed_value,#(#ensures,)*{
 broadcast use {::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas};::vstd::prelude::use_type_invariant(#entry);self.metadata.agrees(&#entry.metadata);let tracked #owned=#entry.borrow_token();
 assert(Protocol #expr::#requires(#owned.fragment(),#(#pn),*))by{
 assert forall|#frame:Fragment #types,#before:State #types|#before.invariant()&&Fragment #expr::op(#owned.fragment(),#frame)==Protocol #expr::embed(#before)implies State #expr::#enabled(#before,#(#pn),*)&&State #expr::#owners(#before,#owned.fragment(),Fragment #expr::unit(),#(#pn),*)by{
 ::vstd::resource::tsm_collections::map_owned_frame(#owned.fragment().#map,#frame.#map,#before.#map,#observed_key,#observed_value);Fragment #expr::op_unit(#owned.fragment());}
 }
 let tracked #after=Protocol #expr::#name(#owned,#(#pn),*);
 assert(::vstd::prelude::ext_equal(*#after,IMap::<#keyty,#valty>::empty().insert(#observed_key,#observed_value)));#after.tracked_borrow(#observed_key)}});
            continue;
        }
        if !selected.contains(&name.to_string())
            || flat.update.len() != 1
            || !flat.update.contains_key(&var.to_string())
        {
            return Err(Error::new(
                name.span(),
                "physical logical-map mutation requires selected readiness and one variable update",
            ));
        }
        let deposit = lo.is_add() && ph.is_deposit();
        let withdraw = lo.is_remove() && ph.stmt.is_withdraw();
        if !deposit && !withdraw {
            return Err(Error::new(
                name.span(),
                "physical logical-map mutation must Add/Deposit or Remove/Withdraw",
            ));
        }
        let op_key = native(lk, &fields, var, quote! {old(#native_var).value()})?;
        let op_value = native(lv, &fields, var, quote! {old(#native_var).value()})?;
        let new_value = native(
            &flat.update[&var.to_string()],
            &fields,
            var,
            quote! {old(#native_var).value()},
        )?;
        let raw_key = native(lk, &fields, var, quote! {#old_value})?;
        let raw_value = native(lv, &fields, var, quote! {#old_value})?;
        let raw_new = native(
            &flat.update[&var.to_string()],
            &fields,
            var,
            quote! {#old_value},
        )?;
        let mut preconds = Vec::new();
        let mut postconds = Vec::new();
        for e in &flat.req {
            preconds.push(native(e, &fields, var, quote! {old(#native_var).value()})?);
        }
        for e in &flat.assertions {
            postconds.push(native(e, &fields, var, quote! {old(#native_var).value()})?);
        }
        let observed = format_ident!("{}_observed", name);
        let local_requires = format_ident!("{}_local_requires", name);
        let helper = format_ident!("__physical_raw_{}", name);
        let contract_old = quote! {old(#slot)@->Some_0.fragment().#getter_var()};
        let contract_key = native(lk, &fields, var, contract_old.clone())?;
        let contract_value = native(lv, &fields, var, contract_old.clone())?;
        let contract_new = native(
            &flat.update[&var.to_string()],
            &fields,
            var,
            contract_old.clone(),
        )?;
        let contract_req: Vec<_> = flat
            .req
            .iter()
            .map(|e| native(e, &fields, var, contract_old.clone()))
            .collect::<Result<_, _>>()?;
        let base_req = quote! {old(#slot)@ is Some,old(#slot)@->Some_0.fragment().#owns_var(),old(#slot)@->Some_0.fragment()==Fragment #expr::#factory_var(old(#slot)@->Some_0.fragment().#getter_var()),#(#contract_req,)*};
        let base_post = quote! {final(#slot)@ is Some,final(#slot)@->Some_0.loc()==old(#slot)@->Some_0.loc(),final(#slot)@->Some_0.fragment().#owns_var(),final(#slot)@->Some_0.fragment()==Fragment #expr::#factory_var(final(#slot)@->Some_0.fragment().#getter_var()),final(#slot)@->Some_0.fragment().#getter_var()==#contract_new,};
        if deposit {
            emitted.push(quote!{proof fn #helper(tracked #slot:&mut Tracked<Option<#token>>,#(#params,)*tracked #actual:#valty)->(tracked #out:#token)requires #base_req #actual==#contract_value,ensures #base_post #out.loc()==old(#slot)@->Some_0.loc(),#out.fragment()==Fragment #expr::#factory_map(IMap::empty().insert(#contract_key,#contract_value)),{
 broadcast use {::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas};
 let #old_value=#slot@->Some_0.fragment().#getter_var();let #key=#raw_key;let #value=#raw_value;let tracked #owned=#slot.borrow_mut().tracked_take();let tracked #dep=::vstd::resource::tsm_helpers::singleton_map(#key,#actual);
 assert(Protocol #expr::#local_requires(#owned.fragment(),Fragment #expr::unit(),#dep,#(#pn),*));let tracked #certificate=Protocol #expr::#observed(#owned,#dep,#(#pn),*);assert(#certificate.before.#var==#old_value);
 let tracked(#var_raw,#map_raw)=Protocol #expr::#take_var(#certificate.token);
 assert(#var_raw.fragment()==Fragment #expr::#factory_var(#raw_new));::vstd::resource::tsm_collections::MapFragment::<#keyty,#valty>::extensionality(::vstd::resource::tsm_collections::MapFragment::unit(),::vstd::resource::tsm_collections::map_frag(IMap::<#keyty,#valty>::empty()));::vstd::resource::tsm_collections::map_join(IMap::empty(),IMap::empty().insert(#key,#value));::vstd::resource::tsm_collections::MapFragment::<#keyty,#valty>::extensionality(#map_raw.fragment().#map,::vstd::resource::tsm_collections::map_frag(IMap::empty().insert(#key,#value)));assert(#map_raw.fragment()==Fragment #expr::#factory_map(IMap::empty().insert(#key,#value)));
 *#slot=Tracked(Some(#var_raw));#map_raw}});
            emitted.push(quote!{pub proof fn #name(tracked &self,#(#params,)*tracked #native_var:&mut #var #types,tracked #actual:#valty)->(tracked #out:#map #types)requires old(#native_var).instance_id()==self.id(),#actual==#op_value,#(#preconds,)*ensures final(#native_var).instance_id()==self.id(),final(#native_var).value()==#new_value,#out.instance_id()==self.id(),#out.key()==#op_key,#out.value()==#op_value,#(#postconds,)*{
 ::vstd::prelude::use_type_invariant(&*#native_var);self.metadata.agrees(&#native_var.metadata);let #key=#op_key;let #value=#op_value;let tracked #map_raw=Self::#helper(&mut #native_var.raw,#(#pn,)*#actual);<#map #types>::__from_token(#map_raw,self.metadata.clone(),#key,#value)}});
        } else {
            emitted.push(quote!{proof fn #helper(tracked #slot:&mut Tracked<Option<#token>>,#(#params,)*tracked #map_raw:#token)->(tracked #out:#valty)requires #base_req #map_raw.loc()==old(#slot)@->Some_0.loc(),#map_raw.fragment()==Fragment #expr::#factory_map(IMap::empty().insert(#contract_key,#contract_value)),ensures #base_post #out==#contract_value,{
 broadcast use {::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas};
 let #old_value=#slot@->Some_0.fragment().#getter_var();let #key=#raw_key;let #value=#raw_value;let tracked #owned=#slot.borrow_mut().tracked_take();let tracked #owned=#owned.join(#map_raw);
 assert(Protocol #expr::#local_requires(#owned.fragment(),Fragment #expr::unit(),IMap::<#keyty,#valty>::empty(),#(#pn),*));let tracked #certificate=Protocol #expr::#observed(#owned,#(#pn),*);
 let tracked(#var_raw,#rest)=Protocol #expr::#take_var(#certificate.token);assert(#var_raw.fragment()==Fragment #expr::#factory_var(#raw_new));
 assert(#certificate.withdrawn==IMap::empty().insert(#key,#value));let tracked #actual=::vstd::resource::tsm_helpers::take_singleton(#certificate.withdrawn,#key);
 *#slot=Tracked(Some(#var_raw));#actual}});
            emitted.push(quote!{pub proof fn #name(tracked &self,#(#params,)*tracked #native_var:&mut #var #types,tracked #entry:#map #types)->(tracked #out:#valty)requires old(#native_var).instance_id()==self.id(),#entry.instance_id()==self.id(),#entry.key()==#op_key,#entry.value()==#op_value,#(#preconds,)*ensures final(#native_var).instance_id()==self.id(),final(#native_var).value()==#new_value,#out==#op_value,#(#postconds,)*{
 ::vstd::prelude::use_type_invariant(&*#native_var);::vstd::prelude::use_type_invariant(&#entry);self.metadata.agrees(&#native_var.metadata);self.metadata.agrees(&#entry.metadata);let tracked #map_raw=#entry.raw.get().tracked_unwrap();Self::#helper(&mut #native_var.raw,#(#pn,)*#map_raw)}});
        }
    }
    Ok(
        quote! {#wrappers #(#attrs)*pub tracked struct Instance #decl #wc{metadata:#descriptor}impl #decl Instance #types #wc{pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}pub proof fn clone(tracked &self)->(tracked out:Self)ensures out.id()==self.id(),{Self{metadata:self.metadata.clone()}}#observe #(#emitted)*}},
    )
}
