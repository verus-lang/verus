//! Checked full-bulk logical owners around one physical storage namespace.
//! Every role owns a genuine sparse token, including empty logical collections.
use crate::ast::*;
use crate::field_access_visitor::visit_field_accesses;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

pub fn needed(sm: &SM) -> bool {
    sm.fields.len() == 5
        && sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::Variable(_))).count() == 1
        && sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::Option(_))).count() == 1
        && sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::Map(..) | ShardableType::IMap(..))).count() == 1
        && sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::Multiset(_))).count() == 1
        && sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::StorageIMap(..))).count() == 1
}

fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
    for token in tokens {
        match token {
            TokenTree::Ident(name) => { names.insert(name.to_string().trim_start_matches("r#").to_string()); }
            TokenTree::Group(group) => reserve(group.stream(), names),
            _ => {},
        }
    }
}

#[derive(Default)]
struct Initial {
    fields: HashMap<String, Expr>,
}

fn initial(stmt: &TransitionStmt, out: &mut Initial) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => for child in children { initial(child, out)?; },
        TransitionStmt::Initialize(_, field, value) => {
            if out.fields.insert(field.to_string(), value.clone()).is_some() {
                return Err(Error::new(field.span(), "general bulk initializer repeats a field"));
            }
        }
        // The existing checked initializer keeps and proves these statements;
        // its original enabled predicate remains the facade precondition.
        TransitionStmt::Require(..) | TransitionStmt::Assert(..) => {},
        _ => return Err(Error::new(*stmt.get_span(), "general bulk initializer requires direct field initializations")),
    }
    Ok(())
}

fn straight<'a>(stmt:&'a TransitionStmt, out:&mut Vec<&'a TransitionStmt>)->Result<(),Error> {
    match stmt {
        TransitionStmt::Block(_, children)=>for child in children {straight(child,out)?;},
        TransitionStmt::Split(_,split,children)=>{
            if !matches!(&**split,SplitKind::Special(_,_,_,None)) {
                return Err(Error::new(*stmt.get_span(),"general bulk facade requires unbound sequential operations"));
            }
            out.push(stmt);
            for child in children {straight(child,out)?;}
        }
        TransitionStmt::Require(..)|TransitionStmt::Assert(..)|TransitionStmt::Update(..)=>out.push(stmt),
        _=>return Err(Error::new(*stmt.get_span(),"unsupported general bulk transition statement")),
    }
    Ok(())
}

fn lower(e:&Expr,fields:&HashMap<String,Field>,values:&HashMap<String,TokenStream>)->Result<TokenStream,Error> {
    let mut e=e.clone();
    let mut errors=vec![];
    visit_field_accesses(&mut e,|errors,f,node|{
        if let Some(value)=values.get(&f.name.to_string()) {*node=Expr::Verbatim(value.clone());}
        else {errors.push(Error::new(f.name.span(),"general bulk expression requires an actual logical role observation"));}
    },&mut errors,fields);
    if let Some(e)=errors.into_iter().next(){return Err(e);}
    Ok(quote!{#e})
}

pub fn output(sm: &SM, selected: &HashSet<String>) -> Result<TokenStream, Error> {
    if !needed(sm) {
        return Err(Error::new(sm.name.span(), "general bulk facade requires Variable, Option, Map/IMap, Multiset and StorageIMap roles"));
    }
    for field in &sm.fields {
        if field.name.to_string().starts_with("r#") {
            return Err(Error::new(field.name.span(),"general bulk facade does not yet support raw field identifiers"));
        }
    }
    let variable = sm.fields.iter().find(|f| matches!(f.stype, ShardableType::Variable(_))).unwrap();
    let optional = sm.fields.iter().find(|f| matches!(f.stype, ShardableType::Option(_))).unwrap();
    let map = sm.fields.iter().find(|f| matches!(f.stype, ShardableType::Map(..) | ShardableType::IMap(..))).unwrap();
    let bag = sm.fields.iter().find(|f| matches!(f.stype, ShardableType::Multiset(_))).unwrap();
    let storage = sm.fields.iter().find(|f| matches!(f.stype, ShardableType::StorageIMap(..))).unwrap();
    let var = &variable.name;
    let opt = &optional.name;
    let map_name = &map.name;
    let bag_name = &bag.name;
    let storage_name = &storage.name;
    let ShardableType::StorageIMap(key_type, value_type) = &storage.stype else { unreachable!() };
    let physical = quote! {::vstd::imap::IMap<#key_type,#value_type>};
    let logical = [variable, optional, map, bag];
    let names: Vec<_> = logical.iter().map(|f| &f.name).collect();
    let fields: HashMap<_,_> = sm.fields.iter().map(|f| (f.name.to_string(), f.clone())).collect();
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let fields_ast = &sm.fields_named_ast;
    let generics_ast = &sm.generics;
    let mut occupied = HashSet::new();
    reserve(quote! {#fields_ast #generics_ast}, &mut occupied);
    for tr in &sm.transitions {
        let name=&tr.name;
        reserve(quote! {#name}, &mut occupied);
        crate::verified_field_storage_map_pair::reserve_stmt(&tr.body, &mut occupied);
        for param in &tr.params { let n=&param.name; let t=&param.ty; reserve(quote!{#n #t},&mut occupied); }
    }
    let reserved_idents:Vec<_>=occupied.iter().map(|n|Ident::new(n,Span::mixed_site())).collect();
    let mut fresh = |stem: &str| {
        let mut name = format!("__tsm_general_bulk_{stem}");
        while occupied.contains(&name) { name.push('_'); }
        occupied.insert(name.clone());
        Ident::new(&name, Span::mixed_site())
    };
    let location = fresh("location");
    let marker = fresh("marker");
    let result = fresh("result");
    let metadata = fresh("metadata");
    let raw = fresh("raw");
    let state = fresh("state");
    let before = fresh("before");
    let observed = fresh("observation");
    let frame = fresh("frame");
    let base = fresh("base");
    let token = quote! {Token #types};
    let metadata_type = fresh("Metadata");
    let descriptor = quote! {::vstd::resource::tsm_context::Descriptor<#metadata_type #types>};
    let marker_field = args.as_ref().map(|a| quote! {ghost #marker:core::marker::PhantomData<(#a,)>,});
    let marker_value = args.as_ref().map(|_| quote! {#marker:core::marker::PhantomData,});
    let fragment_marker = args.as_ref().map(|_| quote! {__tsm_phantom:core::marker::PhantomData,});
    let cx = crate::verified_field_storage_roles::Context {
        decl:&decl, types:&types, expr:&expr, where_clause:&wc, attrs:&attrs,
        token:&token, descriptor:&descriptor, protocol_location:&location, constants:&[],
    };
    let variable_wrapper = crate::verified_field_storage_roles::wrapper(variable, &cx)?;
    let optional_wrapper = crate::verified_field_storage_roles::wrapper(optional, &cx)?;
    let element_wrapper = crate::verified_field_storage_roles::wrapper(bag, &cx)?;
    let map_wrapper = crate::verified_field_storage_binding_maps::wrapper(map, &cx, &quote!{#fields_ast #generics_ast #(#reserved_idents)*})?;
    let opt_type = format_ident!("{opt}_collection");
    let map_type = format_ident!("{map_name}_collection");
    let bag_type = format_ident!("{bag_name}_multiset");
    let role_types = [quote!{#var #types}, quote!{#opt_type #types}, quote!{#map_type #types}, quote!{#bag_type #types}];
    let transition_type=fresh("Transition");
    let public_roles = [var.to_string(), opt.to_string(), opt_type.to_string(), map_name.to_string(),
        map_type.to_string(), format!("{map_name}_map"), bag_name.to_string(), bag_type.to_string()];
    let fixed_types = ["Instance", "Protocol", "State", "Fragment", "Token"];
    for f in &sm.fields {
        let name=f.name.to_string();
        if fixed_types.contains(&name.as_str())
            || (f.name!=*var&&f.name!=*opt&&f.name!=*map_name&&f.name!=*bag_name&&public_roles.contains(&name))
        {
            return Err(Error::new(f.name.span(),"general bulk field conflicts with a generated nominal type"));
        }
    }
    if let Some(g)=&sm.generics {
        for param in &g.params {
            if let verus_syn::GenericParam::Type(t)=param {
                let name=t.ident.to_string().trim_start_matches("r#").to_string();
                if fixed_types.contains(&name.as_str())||public_roles.contains(&name) {
                    return Err(Error::new(t.ident.span(),"general bulk nominal type conflicts with a generic"));
                }
            }
        }
    }
    let mut methods_seen: HashSet<String>=["id","resource_location","clone","invariant"]
        .iter().map(|name|(*name).to_owned()).collect();
    for tr in &sm.transitions {
        if !methods_seen.insert(tr.name.to_string().trim_start_matches("r#").to_string()) {
            return Err(Error::new(tr.name.span(),"general bulk transition conflicts with a generated Instance method"));
        }
    }
    let wrappers: Vec<_> = [(optional, &opt_type), (bag, &bag_type)].iter().map(|(field, role)| {
        let factory = format_ident!("field_{}", field.name);
        let getter = format_ident!("value_{}", field.name);
        let ty = field.get_type();
        quote! {
            #(#attrs)*#[allow(non_camel_case_types)]
            pub tracked struct #role #decl #wc {raw:Tracked<Option<#token>>,metadata:#descriptor}
            impl #decl #role #types #wc {
                #[verifier::type_invariant]
                spec fn invariant(self)->bool {
                    self.raw@ is Some
                    && self.raw@->Some_0.loc()==self.metadata.value().#location
                    && self.raw@->Some_0.fragment()==Fragment #expr::#factory(self.value())
                }
                pub closed spec fn instance_id(&self)->::vstd::resource::Loc {self.metadata.id()}
                pub closed spec fn resource_location(&self)->::vstd::resource::Loc {self.raw@->Some_0.loc()}
                pub closed spec fn raw_fragment(&self)->Fragment #types {self.raw@->Some_0.fragment()}
                pub closed spec fn value(&self)->#ty {self.raw@->Some_0.fragment().#getter()}
                pub proof fn borrow_token(tracked &self)->(tracked #result:&#token)
                    ensures #result.loc()==self.resource_location(),#result.fragment()==self.raw_fragment(),
                {use_type_invariant(self);self.raw.borrow().tracked_borrow()}
                proof fn __from_token(tracked #raw:#token,tracked #metadata:#descriptor,value:#ty)->(tracked #result:Self)
                    requires #raw.loc()==#metadata.value().#location,
                        #raw.fragment()==Fragment #expr::#factory(value),
                    ensures #result.instance_id()==#metadata.id(),#result.value()==value,
                        #result.resource_location()==#raw.loc(),#result.raw_fragment()==#raw.fragment(),
                {Self{raw:Tracked(Some(#raw)),metadata:#metadata}}
            }
        }
    }).collect();
    let mut methods = vec![];
    for tr in &sm.transitions {
        let n = &tr.name;
        let params:Vec<_>=tr.params.iter().map(|p|{let n=&p.name;let t=&p.ty;quote!{#n:#t}}).collect();
        let pn:Vec<_>=tr.params.iter().map(|p|&p.name).collect();
        if tr.kind == TransitionKind::Init {
            let mut init = Initial::default();
            initial(&tr.body, &mut init)?;
            for f in &sm.fields {
                if !init.fields.contains_key(&f.name.to_string()) {
                    return Err(Error::new(f.name.span(),"general bulk initializer must initialize every original field"));
                }
            }
            let values:Vec<_>=names.iter().map(|n| &init.fields[&n.to_string()]).collect();
            let storage_value=&init.fields[&storage_name.to_string()];
            let enabled=format_ident!("{n}_enabled");
            let init_rel=format_ident!("{n}_strong");
            let takes:Vec<_>=names.iter().map(|n|format_ident!("take_{n}")).collect();
            let new_raw:Vec<_>=names.iter().map(|n|fresh(&format!("initial_raw_{n}"))).collect();
            let saved_values:Vec<_>=names.iter().map(|n|fresh(&format!("initial_value_{n}"))).collect();
            let owner_names:Vec<_>=names.iter().map(|n|fresh(&format!("initial_owner_{n}"))).collect();
            let post = fresh("initial_post");
            // Avoid any specification-only owner: every constructor receives
            // one of the actual four checked token projections.
            let vr=&new_raw[0];let or=&new_raw[1];let mr=&new_raw[2];let br=&new_raw[3];
            let vv=&values[0];let ov=&values[1];let mv=&values[2];let bv=&values[3];
            let saved_opt=&saved_values[1];let saved_map=&saved_values[2];let saved_bag=&saved_values[3];
            let va=&owner_names[0];let oa=&owner_names[1];let ma=&owner_names[2];let ba=&owner_names[3];
            methods.push(quote! {
                pub proof fn #n(#(#params,)*tracked #base:#physical)->(tracked #result:(Self,#(#role_types),*))
                    requires State #expr::#enabled(#(#pn),*),#base==#storage_value,
                    ensures #result.1.instance_id()==#result.0.id(),
                        #result.2.instance_id()==#result.0.id(),#result.3.instance_id()==#result.0.id(),
                        #result.4.instance_id()==#result.0.id(),
                        #result.1.value()==(#vv),#result.2.value()==(#ov),
                        #result.3.map()==(#mv),#result.4.value()==(#bv),
                {
                    #(let ghost #saved_values=#values;)*
                    let tracked #raw=Protocol #expr::#n(#base,#(#pn),*);
                    let #post=choose|#state:State #types|State #expr::#init_rel(#state,#(#pn),*)
                        &&#state.invariant()&&#raw.fragment()==Protocol #expr::embed(#state);
                    let tracked #metadata=::vstd::resource::tsm_context::Descriptor::alloc(
                        #metadata_type #expr{#location:#raw.loc(),#marker_value});
                    #(let tracked (#new_raw,#raw)=Protocol #expr::#takes(#raw);)*
                    let tracked #va=#var #expr::__from_token(#vr,#metadata.clone());
                    let tracked #oa=#opt_type #expr::__from_token(#or,#metadata.clone(),#saved_opt);
                    let tracked #ma=#map_type #expr::__from_token(#mr,#metadata.clone(),#saved_map);
                    let tracked #ba=#bag_type #expr::__from_token(#br,#metadata.clone(),#saved_bag);
                    (Self{metadata:#metadata},#va,#oa,#ma,#ba)
                }
            });
        } else {
            if tr.kind != TransitionKind::Transition || !selected.contains(&n.to_string()) {
                return Err(Error::new(n.span(),"general bulk facade requires selected mutating transitions"));
            }
            let local_req=format_ident!("{n}_local_requires");
            let native_req=format_ident!("{n}_requires");
            let observed_op=format_ident!("{n}_observed");
            let strong=format_ident!("{n}_strong");
            let factory:Vec<_>=names.iter().map(|n|format_ident!("field_{n}")).collect();
            let takes:Vec<_>=names.iter().map(|n|format_ident!("take_{n}")).collect();
            let new_raw:Vec<_>=names.iter().map(|n|fresh(&format!("returned_raw_{n}"))).collect();
            let vr=&new_raw[0];let or=&new_raw[1];let mr=&new_raw[2];let br=&new_raw[3];
            let owner_names:Vec<_>=names.iter().map(|n|fresh(&format!("owner_{n}"))).collect();
            let va=&owner_names[0];let oa=&owner_names[1];let ma=&owner_names[2];let ba=&owner_names[3];
            let mut operations=vec![];
            straight(&tr.body,&mut operations)?;
            let input_values:HashMap<_,_>=HashMap::from([
                (var.to_string(),quote!{#va.value()}),
                (opt.to_string(),quote!{#oa.value()}),
                (map_name.to_string(),quote!{#ma.map()}),
                (bag_name.to_string(),quote!{#ba.value()}),
            ]);
            let mut post_values=input_values.clone();
            let mut deposits=false;
            for stmt in operations {
                match stmt {
                    TransitionStmt::Update(_,field,value)=>{
                        post_values.insert(field.to_string(),lower(value,&fields,&input_values)?);
                    }
                    TransitionStmt::Split(_,split,_)=>{
                        let SplitKind::Special(field,op,_,None)=&**split else {unreachable!()};
                        if fields[&field.to_string()].stype.is_storage() {
                            deposits|=op.stmt.is_deposit();
                            continue;
                        }
                        let operand=match &op.elt {
                            MonoidElt::General(e)=>lower(e,&fields,&input_values)?,
                            MonoidElt::OptionSome(Some(e))=>{let e=lower(e,&fields,&input_values)?;quote!{Some(#e)}},
                            MonoidElt::SingletonMultiset(e)=>{let e=lower(e,&fields,&input_values)?;quote!{::vstd::multiset::Multiset::singleton(#e)}},
                            _=>return Err(Error::new(field.span(),"general bulk facade requires native optional, map or multiset operands")),
                        };
                        if matches!(op.stmt,MonoidStmtType::Have) {continue;}
                        let current=&post_values[&field.to_string()];
                        let next=match (&fields[&field.to_string()].stype,&op.stmt) {
                            (ShardableType::Option(_),MonoidStmtType::Remove)=>quote!{::vstd::resource::tsm_collections::option_subtract(#current,#operand)},
                            (ShardableType::Option(_),MonoidStmtType::Add(false))=>quote!{::vstd::resource::tsm_collections::option_union(#current,#operand)},
                            (ShardableType::Map(..)|ShardableType::IMap(..),MonoidStmtType::Remove)=>quote!{(#current).remove_keys((#operand).dom())},
                            (ShardableType::Map(..)|ShardableType::IMap(..),MonoidStmtType::Add(false))=>quote!{(#current).union_prefer_right(#operand)},
                            (ShardableType::Multiset(_),MonoidStmtType::Remove)=>quote!{(#current).sub(#operand)},
                            (ShardableType::Multiset(_),MonoidStmtType::Add(false))=>quote!{(#current).add(#operand)},
                            _=>return Err(Error::new(field.span(),"unsupported general bulk ownership modifier")),
                        };
                        post_values.insert(field.to_string(),next);
                    }
                    _=>{},
                }
            }
            let next_values:Vec<_>=names.iter().map(|n|&post_values[&n.to_string()]).collect();
            let nv0=&next_values[0];let nv1=&next_values[1];let nv2=&next_values[2];let nv3=&next_values[3];
            let native_values:Vec<_>=names.iter().map(|n|fresh(&format!("post_value_{n}"))).collect();
            let vv=&native_values[0];let ov=&native_values[1];let mv=&native_values[2];let bv=&native_values[3];
            let factories:Vec<_>=factory.iter().zip(&native_values).map(|(f,v)|quote!{Fragment #expr::#f(#v)}).collect();
            let unit_hints:Vec<_>=logical.iter().zip(&owner_names).map(|(field,owner)|{
                let n=&field.name;
                let ty=match &field.stype {
                    ShardableType::Variable(t)=>quote!{Option<::vstd::resource::exclusive::ExclusiveRA<#t>>},
                    stype=>crate::verified_monoids::component(stype),
                };
                quote!{
                    #owner.raw_fragment().#n.op_unit();
                    <#ty>::unit().op_unit();
                    <#ty>::commutative(<#ty>::unit(),#owner.raw_fragment().#n);
                }
            }).collect();
            let map_key=map.stype.get_map_key_type();
            let map_factory=&factory[2];
            let map_point=fresh("map_point");
            let post_map_view=if matches!(map.stype,ShardableType::Map(..)) {
                quote!{#observed.after.#map_name.to_imap()}
            }else{quote!{#observed.after.#map_name}};
            let map_shape_hint=quote!{
                assert forall|#map_point:#map_key|
                    #[trigger] #mr.fragment().#map_name.at(#map_point)==
                        Fragment #expr::#map_factory(#mv).#map_name.at(#map_point) by {
                    assert(::vstd::resource::tsm_collections::MapFragment::op(
                        #mr.fragment().#map_name,#frame.#map_name).at(#map_point)
                        ==::vstd::resource::tsm_collections::map_frag(#post_map_view).at(#map_point));
                };
                ::vstd::resource::tsm_collections::Pointwise::extensionality(
                    #mr.fragment().#map_name,Fragment #expr::#map_factory(#mv).#map_name);
            };
            let shape_hints:Vec<_>=logical.iter().map(|f|{
                if f.name==*map_name{map_shape_hint.clone()}else{quote!{}}
            }).collect();
            let owner_args:Vec<_>=owner_names.iter().zip(&role_types).map(|(n,t)|quote!{tracked #n:#t}).collect();
            let owner_refs:Vec<_>=owner_names.iter().zip(&role_types).map(|(n,t)|quote!{#n:&#t}).collect();
            let ghost_fields:Vec<_>=names.iter().zip(&owner_names).map(|(n,owner)|quote!{#n:#owner.raw_fragment().#n}).collect();
            let native_fields:Vec<_>=names.iter().zip(&factory).map(|(n,f)|{
                let value=&input_values[&n.to_string()];
                quote!{#n:Fragment #expr::#f(#value).#n}
            }).collect();
            let dep=fresh("deposit");
            let dep_ghost=fresh("deposit_view");
            let dep_param=if deposits{quote!{tracked #dep:#physical,}}else{quote!{}};
            let dep_arg=if deposits{quote!{#dep,}}else{quote!{}};
            let dep_value=if deposits{quote!{#dep}}else{quote!{<#physical>::empty()}};
            let before_value=quote!{Fragment #expr{#(#ghost_fields),*,#fragment_marker}};
            let native_fragment=quote!{Fragment #expr{#(#native_fields),*,#fragment_marker}};
            let proto_op=quote!{Protocol #expr::#observed_op(#raw,#dep_arg #(#pn),*)};
            methods.push(quote!{
                pub open spec fn #native_req(&self,#(#owner_refs,)*#(#params,)*#dep:#physical)->bool {
                    true #(&& #owner_names.instance_id()==self.id())*
                    &&Protocol #expr::#local_req(#native_fragment,Fragment #expr::unit(),#dep,#(#pn),*)
                }
                pub proof fn #n(tracked &self,#(#owner_args,)*#dep_param #(#params),*)
                    ->(tracked #result:#transition_type #types)
                    requires self.#native_req(#(&#owner_names,)*#(#pn,)*#dep_value),
                    ensures #result.#var.instance_id()==self.id(),#result.#opt.instance_id()==self.id(),
                        #result.#map_name.instance_id()==self.id(),#result.#bag_name.instance_id()==self.id(),
                        #result.#var.value()==(#nv0),
                        #result.#opt.value()==(#nv1),
                        #result.#map_name.map()==(#nv2),
                        #result.#bag_name.value()==(#nv3),
                        #result.before.invariant(),#result.after.invariant(),
                        State #expr::#strong(#result.before,#result.after,#(#pn),*),
                        #result.before.#var==#va.value(),
                        #result.withdrawn==#result.before.__storage().union_prefer_right(#dep_value)
                            .remove_keys(#result.after.__storage().dom()),
                {
                    #(use_type_invariant(&#owner_names);)*
                    #(self.metadata.agrees(&#owner_names.metadata);)*
                    #(#unit_hints)*
                    let ghost #before=#before_value;
                    let ghost #dep_ghost=#dep_value;
                    #(let ghost #native_values=#next_values;)*
                    let tracked #raw=#va.raw.get().tracked_unwrap();
                    let tracked #raw=#raw.join(#oa.raw.get().tracked_unwrap());
                    let tracked #raw=#raw.join(#ma.raw.get().token.tracked_unwrap());
                    let tracked #raw=#raw.join(#ba.raw.get().tracked_unwrap());
                    assert(#raw.fragment()==#before);
                    let tracked #observed=#proto_op;
                    let #state=#observed.before;
                    let #frame=#observed.frame;
                    assert(#state.#var==#va.value());
                    let tracked #raw=#observed.token;
                    #(let tracked (#new_raw,#raw)=Protocol #expr::#takes(#raw);
                        #shape_hints
                        assert(#new_raw.fragment()==#factories);)*
                    let tracked #metadata=self.metadata.clone();
                    let tracked #var=#var #expr::__from_token(#vr,#metadata.clone());
                    let tracked #opt=#opt_type #expr::__from_token(#or,#metadata.clone(),#ov);
                    let tracked #map_name=#map_type #expr::__from_token(#mr,#metadata.clone(),#mv);
                    let tracked #bag_name=#bag_type #expr::__from_token(#br,#metadata.clone(),#bv);
                    #transition_type #expr{
                        #var,#opt,#map_name,#bag_name,withdrawn:#observed.withdrawn,
                        before:#observed.before,after:#observed.after,
                    }
                }
            });
        }
    }
    Ok(quote! {
        #(#attrs)*tracked struct #metadata_type #decl #wc {ghost #location: ::vstd::resource::Loc,#marker_field}
        #variable_wrapper #optional_wrapper #element_wrapper #map_wrapper #(#wrappers)*
        #(#attrs)*pub tracked struct #transition_type #decl #wc {
            #(pub #names:#role_types,)*
            pub withdrawn:#physical,
            pub ghost before:State #types,
            pub ghost after:State #types,
        }
        #(#attrs)*pub tracked struct Instance #decl #wc {metadata:#descriptor}
        impl #decl Instance #types #wc {
            pub closed spec fn id(&self)->::vstd::resource::Loc {self.metadata.id()}
            pub closed spec fn resource_location(&self)->::vstd::resource::Loc {self.metadata.value().#location}
            pub proof fn clone(tracked &self)->(tracked #result:Self)
                ensures #result.id()==self.id(),#result.resource_location()==self.resource_location(),
            {Self{metadata:self.metadata.clone()}}
            #(#methods)*
        }
    })
}
