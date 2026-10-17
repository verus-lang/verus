//! Original refutable singleton owners over matching physical map/Option stores.
//! Native patterns govern current owners; physical values come from exchange.
use crate::ast::*;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident, Pat};

fn profile(sm: &SM) -> Option<(&Field, &Field, &Field, &Field, bool)> {
    if sm.fields.len() != 4 { return None; }
    let opt=sm.fields.iter().find(|f|matches!(f.stype,ShardableType::Option(_)))?;
    let map=sm.fields.iter().find(|f|matches!(f.stype,ShardableType::Map(..)|ShardableType::IMap(..)))?;
    let po=sm.fields.iter().find(|f|matches!(f.stype,ShardableType::StorageOption(_)))?;
    let pm=sm.fields.iter().find(|f|matches!(f.stype,ShardableType::StorageMap(..)|ShardableType::StorageIMap(..)))?;
    let ShardableType::Option(v)=&opt.stype else {return None};
    let ShardableType::StorageOption(pv)=&po.stype else {return None};
    match (&map.stype,&pm.stype) {
        (ShardableType::Map(k,mv),ShardableType::StorageMap(pk,pmv)) if k==pk&&v==mv&&v==pv&&v==pmv=>Some((opt,map,po,pm,true)),
        (ShardableType::IMap(k,mv),ShardableType::StorageIMap(pk,pmv)) if k==pk&&v==mv&&v==pv&&v==pmv=>Some((opt,map,po,pm,false)),
        _=>None,
    }
}
pub fn needed(sm:&SM)->bool {profile(sm).is_some()}
#[derive(Default)]
struct Flat {
    initial:HashMap<String,Expr>,
    operations:Vec<(Ident,SpecialOp,Box<Pat>)>,
    requirements:Vec<Expr>,
    assertions:Vec<Expr>,
}
fn collect(stmt:&TransitionStmt,f:&mut Flat)->Result<(),Error> {
    match stmt {
        TransitionStmt::Block(_,children)=>for child in children{collect(child,f)?;},
        TransitionStmt::Initialize(_,field,e)=>{
            if f.initial.insert(field.to_string(),e.clone()).is_some(){return Err(Error::new(field.span(),"refutable initializer repeats a field"));}
        }
        TransitionStmt::Require(_,e)=>{
            if f.operations.iter().any(|(_,op,_)|op.stmt.is_withdraw()){
                return Err(Error::new(*stmt.get_span(),"refutable native requirements cannot use a withdrawn payload"));
            }
            f.requirements.push(e.clone());
        }
        TransitionStmt::Assert(_,e,_)=>f.assertions.push(e.clone()),
        TransitionStmt::Split(_,kind,children)=>{
            let SplitKind::Special(field,op,_,Some(pat))=&**kind else {
                return Err(Error::new(*stmt.get_span(),"refutable facade requires singleton pattern bindings"));
            };
            f.operations.push((field.clone(),op.clone(),pat.clone()));
            for child in children{collect(child,f)?;}
        }
        _=>return Err(Error::new(*stmt.get_span(),"unsupported refutable owner operation")),
    }
    Ok(())
}
fn reserve(tokens:TokenStream,names:&mut HashSet<String>) {
    for token in tokens {
        match token {
            TokenTree::Ident(n)=>{names.insert(n.to_string().trim_start_matches("r#").to_string());},
            TokenTree::Group(g)=>reserve(g.stream(),names),
            _=>{}
        }
    }
}
pub fn output(sm:&SM)->Result<TokenStream,Error> {
    let Some((optional,map,physical_opt,physical_map,finite))=profile(sm) else {
        return Err(Error::new(sm.name.span(),"refutable facade requires matching logical and physical Map/Option roles"));
    };
    for f in &sm.fields {
        if f.name.to_string().starts_with("r#") {
            return Err(Error::new(f.name.span(),"refutable facade does not yet support raw field identifiers"));
        }
    }
    let opt=&optional.name;let field=&map.name;let po=&physical_opt.name;let pm=&physical_map.name;
    let ShardableType::Option(value_type)=&optional.stype else {unreachable!()};
    let key_type=map.stype.get_map_key_type();
    let (generics,attrs)=crate::verified_tokens::datatype_generics(sm);
    let (decl,wc)=generics_for_decl(&generics);
    let args=sm.generics.as_ref().map(|g|get_generic_args(&g.params));
    let types=args.as_ref().map(|a|quote!{<#a>}).unwrap_or_default();
    let expr=args.as_ref().map(|a|quote!{::<#a>}).unwrap_or_default();
    let fields_ast=&sm.fields_named_ast;let generic_ast=&sm.generics;
    let mut occupied=HashSet::new();
    reserve(quote!{#fields_ast #generic_ast},&mut occupied);
    for tr in &sm.transitions {
        occupied.insert(tr.name.to_string().trim_start_matches("r#").to_string());
        crate::verified_field_storage_map_pair::reserve_stmt(&tr.body,&mut occupied);
        for param in &tr.params {let n=&param.name;let ty=&param.ty;reserve(quote!{#n #ty},&mut occupied);}
    }
    let mut fresh=|label:&str|{
        let mut name=format!("__tsm_refutable_{label}");
        while occupied.contains(&name){name.push('_');}
        occupied.insert(name.clone());Ident::new(&name,Span::mixed_site())
    };
    let location=fresh("location");let marker=fresh("marker");let out=fresh("result");
    let raw=fresh("raw");let before=fresh("before");let pre=fresh("pre");let post=fresh("post");
    let frame=fresh("frame");let remaining=fresh("remaining");let withdrawn=fresh("withdrawn");
    let value=fresh("value");let point=fresh("point");let md=fresh("metadata");
    let owner=fresh("owner");let map_owner=fresh("map_owner");let opt_owner=fresh("opt_owner");
    let actual_map=fresh("actual_map");let actual_opt=fresh("actual_opt");let initial=fresh("initial");
    let opt_raw=fresh("opt_raw");let map_raw=fresh("map_raw");let initial_opt=fresh("initial_opt");
    let convert=fresh("finite_into_imap");let reverse=fresh("finite_from_imap");
    let marker_field=args.as_ref().map(|a|quote!{ghost #marker:core::marker::PhantomData<(#a,)>,});
    let marker_value=args.as_ref().map(|_|quote!{#marker:core::marker::PhantomData,});
    let metadata=quote!{__StorageMetadata #types};
    let descriptor=quote!{::vstd::resource::tsm_context::Descriptor<#metadata>};
    let token=quote!{Token #types};
    let cx=crate::verified_field_storage_roles::Context{
        decl:&decl,types:&types,expr:&expr,where_clause:&wc,attrs:&attrs,token:&token,
        descriptor:&descriptor,protocol_location:&location,constants:&[],
    };
    let opt_wrapper=crate::verified_field_storage_roles::wrapper(optional,&cx)?;
    let map_wrapper=crate::verified_field_storage_binding_maps::wrapper(map,&cx,&quote!{#fields_ast #generic_ast})?;
    let collection=format_ident!("{field}_collection");let map_alias=format_ident!("{field}_map");
    let reserved_types=["Instance","Protocol","State","Fragment","Token","__StorageMetadata"];
    for f in &sm.fields {
        if reserved_types.contains(&f.name.to_string().as_str())
            || f.name==collection||f.name==map_alias
        {return Err(Error::new(f.name.span(),"refutable field conflicts with a generated nominal role"));}
    }
    if let Some(g)=&sm.generics {
        for p in &g.params {
            if let verus_syn::GenericParam::Type(t)=p {
                let name=t.ident.to_string().trim_start_matches("r#").to_string();
                if reserved_types.contains(&name.as_str())||name==collection.to_string()||name==map_alias.to_string()
                    || sm.fields.iter().any(|f|f.name.to_string().trim_start_matches("r#")==name)
                {return Err(Error::new(t.ident.span(),"refutable nominal role conflicts with a generic"));}
            }
        }
    }
    let mut methods=HashSet::from(["id".to_owned(),"clone".to_owned(),"invariant".to_owned()]);
    let native_map=if finite {quote!{Map::<#key_type,#value_type>}}else{quote!{IMap::<#key_type,#value_type>}};
    let native_map_type=map.get_type();
    let native_pre_map=if finite{quote!{#pre.#field.to_imap()}}else{quote!{#pre.#field}};
    let storage_key=quote!{<Protocol #types as ::vstd::resource::tsm_storage::StorageMachine>::Key};
    let storage_map=quote!{IMap<#storage_key,#value_type>};
    let tag_opt=format_ident!("__tag_{po}");let pack_opt=format_ident!("__pack_{po}");let unpack_opt=format_ident!("__unpack_{po}");
    let tag_map=format_ident!("__carrier_tag_{pm}");let untag_map=format_ident!("__carrier_untag_{pm}");
    let pack_map=format_ident!("__carrier_pack_imap_{pm}");let unpack_map=format_ident!("__carrier_unpack_imap_{pm}");
    let roundtrip_map=format_ident!("__carrier_roundtrip_{pm}");
    let factory_opt=format_ident!("field_{opt}");let factory_map=format_ident!("field_{field}");let take_opt=format_ident!("take_{opt}");
    let mut emitted=vec![];
    for tr in &sm.transitions {
        let n=&tr.name;
        if !methods.insert(n.to_string().trim_start_matches("r#").to_string()) {return Err(Error::new(n.span(),"refutable transition conflicts with a generated Instance method"));}
        let mut flat=Flat::default();collect(&tr.body,&mut flat)?;
        let pn:Vec<_>=tr.params.iter().map(|p|&p.name).collect();
        let params:Vec<_>=tr.params.iter().map(|p|{let n=&p.name;let t=&p.ty;quote!{#n:#t}}).collect();
        let enabled=format_ident!("{n}_enabled");let owners=format_ident!("{n}_owners_enabled");
        let strong=format_ident!("{n}_strong");
        let requires=format_ident!("{n}_requires");let witness=format_ident!("{n}_witness");
        if tr.kind==TransitionKind::Init {
            if flat.initial.len()!=4||!flat.operations.is_empty()||!flat.assertions.is_empty(){
                return Err(Error::new(n.span(),"refutable initializer must initialize all four fields"));
            }
            let io=&flat.initial[&opt.to_string()];let im=&flat.initial[&field.to_string()];
            let iso=&flat.initial[&po.to_string()];let ism=&flat.initial[&pm.to_string()];
            let requirements=&flat.requirements;
            let map_view=if finite{quote!{#actual_map.to_imap()}}else{quote!{#actual_map}};
            let converted=if finite{quote!{let tracked #actual_map=Self::#convert(#actual_map);}}else{quote!{}};
            emitted.push(quote! {
                pub proof fn #n(#(#params,)*tracked #actual_map:#native_map_type,tracked #actual_opt:Option<#value_type>)
                    ->(tracked #out:(Tracked<Self>,Tracked<#collection #types>,Tracked<Option<#opt #types>>))
                    requires #(#requirements,)*#actual_map==#ism,#actual_opt==#iso,
                    ensures #out.1@.instance_id()==#out.0@.id(),#out.1@.map()==#im,
                        {let #initial_opt:Option<#value_type>=#io;
                            (#out.2@ is Some&&#initial_opt is Some&&#out.2@->Some_0.instance_id()==#out.0@.id()&&#out.2@->Some_0.value()==#initial_opt->Some_0)
                            ||(#out.2@ is None&&#initial_opt is None)},
                {
                    broadcast use {::vstd::map::group_map_lemmas,::vstd::imap::group_imap_lemmas,::vstd::set::group_set_lemmas,::vstd::iset::group_iset_lemmas};
                    let #initial_opt:Option<#value_type>=#io;
                    #converted
                    let tracked mut #actual_map=Protocol #expr::#pack_map(#actual_map);
                    let tracked #actual_opt=<#storage_key>::#pack_opt(#actual_opt);
                    assert(#actual_map.dom().disjoint(#actual_opt.dom()));
                    #actual_map.tracked_union_prefer_right(#actual_opt);
                    assert forall|#initial:State #types|State #expr::#n(#initial,#(#pn),*)
                        implies #actual_map==#initial.__storage() by {
                            assert(::vstd::prelude::ext_equal(#actual_map,#initial.__storage()));
                        }
                    let tracked #raw=Protocol #expr::#n(#actual_map,#(#pn),*);
                    let #initial=choose|#initial:State #types|State #expr::#n(#initial,#(#pn),*)&&#initial.invariant()&&#raw.fragment()==Protocol #expr::embed(#initial);
                    let tracked #md=::vstd::resource::tsm_context::Descriptor::alloc(__StorageMetadata #expr{#location:#raw.loc(),#marker_value});
                    let tracked(#opt_raw,#map_raw)=Protocol #expr::#take_opt(#raw);
                    assert(#opt_raw.fragment()==Fragment #expr::#factory_opt(#initial_opt));
                    ::vstd::resource::tsm_collections::map_join(IMap::<#key_type,#value_type>::empty(),IMap::<#key_type,#value_type>::empty());
                    assert(#map_raw.fragment()==Fragment #expr::#factory_map(#im));
                    let tracked #map_owner=<#collection #types>::__from_token(#map_raw,#md.clone(),#im);
                    let tracked #opt_owner=match #initial_opt {
                        Some(#value)=>Some(<#opt #types>::__from_token(#opt_raw,#md.clone(),#value)),
                        None=>None,
                    };
                    (Tracked(Self{metadata:#md}),Tracked(#map_owner),Tracked(#opt_owner))
                }
            });
            let _=map_view;
            continue;
        }
        let [(first,first_op,first_pat),(second,second_op,second_pat)]=flat.operations.as_slice() else {
            return Err(Error::new(n.span(),"refutable transition requires two original singleton bindings"));
        };
        if first_op.is_have()&&second_op.is_have() {
            if first!=opt||second!=field||!flat.assertions.is_empty()||tr.kind!=TransitionKind::Transition {
                return Err(Error::new(n.span(),"refutable Have requires Option followed by Map"));
            }
            let MonoidElt::SingletonKV(key,None)=&second_op.elt else {return Err(Error::new(n.span(),"refutable Have needs a bound map singleton"));};
            let requirements=&flat.requirements;
            emitted.push(quote! {
                pub proof fn #n(tracked &self,#(#params,)*tracked #map_owner:&#field #types,tracked #opt_owner:&#opt #types)
                    requires #map_owner.instance_id()==self.id(),#opt_owner.instance_id()==self.id(),#map_owner.key()==#key,
                        match #opt_owner.value(){#first_pat=>match #map_owner.value(){#second_pat=>true #(&& #requirements)*,_=>false},_=>false},
                {
                    ::vstd::prelude::use_type_invariant(#map_owner);::vstd::prelude::use_type_invariant(#opt_owner);
                    self.metadata.agrees(&#map_owner.metadata);self.metadata.agrees(&#opt_owner.metadata);
                    let tracked #map_raw=#map_owner.borrow_token();let tracked #opt_raw=#opt_owner.borrow_token();
                    let (#pre,#frame,#remaining)=#map_raw.compatible_with(#opt_raw);
                    ::vstd::resource::tsm_collections::map_owned_frame(#map_raw.fragment().#field,#frame.#field,#native_pre_map,#key,#map_owner.value());
                    assert(#pre.#opt==Some(#opt_owner.value()));
                    assert(State #expr::#enabled(#pre,#(#pn),*));
                    assert(State #expr::#strong(#pre,#pre,#(#pn),*));
                }
            });
            continue;
        }
        let optional_remove=first==opt&&second==po;
        let map_remove=first==field&&second==pm;
        if !(optional_remove||map_remove)||!first_op.is_remove()||!second_op.stmt.is_withdraw()||tr.kind!=TransitionKind::Transition||!flat.requirements.is_empty(){
            return Err(Error::new(n.span(),"refutable mutation consumes one logical singleton and withdraws its matching physical singleton"));
        }
        let role=if optional_remove{opt}else{field};
        let lift=if optional_remove {
            quote!{assert(#pre.#opt==Some(#value));}
        }else {
            let MonoidElt::SingletonKV(key,None)=&first_op.elt else {return Err(Error::new(n.span(),"refutable removal requires bound map singleton"));};
            quote!{::vstd::resource::tsm_collections::map_owned_frame(#before.#field,#frame.#field,#native_pre_map,#key,#value);}
        };
        let key_requirement=if optional_remove{quote!{}}else{
            let MonoidElt::SingletonKV(key,None)=&first_op.elt else {unreachable!()};
            let MonoidElt::SingletonKV(physical_key,None)=&second_op.elt else {return Err(Error::new(n.span(),"refutable withdrawal requires bound map singleton"));};
            if quote!{#key}.to_string()!=quote!{#physical_key}.to_string(){return Err(Error::new(n.span(),"refutable physical key must match logical key"));}
            quote!{#owner.key()==#key,}
        };
        let withdrawn_spec=if optional_remove {
            quote!{<#storage_key>::#tag_opt(Some(#value))}
        }else{
            let MonoidElt::SingletonKV(key,None)=&first_op.elt else {unreachable!()};
            quote!{Protocol #expr::#tag_map(IMap::<#key_type,#value_type>::empty().insert(#key,#value))}
        };
        let extraction=if optional_remove {
            quote!{let tracked #out=<#storage_key>::#unpack_opt(#withdrawn);let tracked #out=::vstd::std_specs::option::OptionAdditionalFns::tracked_unwrap(#out);}
        }else{
            let MonoidElt::SingletonKV(key,None)=&first_op.elt else {unreachable!()};
            quote!{
                Protocol #expr::#roundtrip_map(IMap::<#key_type,#value_type>::empty().insert(#key,#value));
                let tracked mut #withdrawn=Protocol #expr::#unpack_map(#withdrawn);
                let tracked #out=#withdrawn.tracked_remove(#key);
            }
        };
        emitted.push(quote! {
            pub proof fn #n(tracked &self,#(#params,)*tracked #owner:#role #types)->(tracked #out:#value_type)
                requires #owner.instance_id()==self.id(),#key_requirement match #owner.value(){#first_pat=>true,_=>false},
                ensures #out==#owner.value(),
            {
                broadcast use {::vstd::map::group_map_lemmas,::vstd::imap::group_imap_lemmas,::vstd::set::group_set_lemmas,::vstd::iset::group_iset_lemmas};
                ::vstd::prelude::use_type_invariant(&#owner);self.metadata.agrees(&#owner.metadata);
                let #value=#owner.value();let tracked #raw=#owner.raw.get().tracked_unwrap();let #before=#raw.fragment();
                assert(Protocol #expr::#requires(#before,Fragment #expr::unit(),<#storage_map>::empty(),#(#pn),*)) by {
                    assert forall|#frame:Fragment #types,#pre:State #types|
                        #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,Fragment #expr::unit()),#frame)==Protocol #expr::embed(#pre)
                        implies State #expr::#enabled(#pre,#(#pn),*)&&State #expr::#owners(#pre,#before,Fragment #expr::unit(),#(#pn),*) by {
                            Fragment #expr::op_unit(#before);#lift
                        }
                }
                let tracked(#remaining,#withdrawn)=Protocol #expr::#n(#raw,#(#pn),*);
                let(#pre,#post,#frame)=Protocol #expr::#witness(#before,Fragment #expr::unit(),#remaining.fragment(),<#storage_map>::empty(),#withdrawn,#(#pn),*);
                Fragment #expr::op_unit(#before);
                #lift
                assert(#withdrawn==#withdrawn_spec) by {
                    assert forall|#point:#storage_key|#[trigger] #withdrawn.contains_key(#point)==(#withdrawn_spec).contains_key(#point) by {};
                }
                #extraction
                #out
            }
        });
    }
    let conversions=if finite {quote! {
        proof fn #convert(tracked input:Map<#key_type,#value_type>)->(tracked output:IMap<#key_type,#value_type>)
            ensures output==input.to_imap(),decreases input.len(),
        {
            broadcast use {::vstd::map::group_map_lemmas,::vstd::imap::group_imap_lemmas,::vstd::set::group_set_lemmas,::vstd::iset::group_iset_lemmas};
            let ghost original=input;
            ::vstd::set_lib::lemma_set_empty_equivalency_len(input.dom());
            if input.len()==0 {let tracked output=IMap::tracked_empty();assert(::vstd::prelude::ext_equal(output,original.to_imap()));output}
            else {
                let key=choose|key:#key_type|input.dom().contains(key);::vstd::set::lemma_set_remove_len(input.dom(),key);
                let tracked mut input=input;let tracked value=input.tracked_remove(key);
                let tracked mut output=Self::#convert(input);output.tracked_insert(key,value);
                assert(::vstd::prelude::ext_equal(output,original.to_imap()));output
            }
        }
    }}else{quote!{}};
    let _=(&native_map,&reverse,&untag_map,&factory_map);
    Ok(quote! {
        #(#attrs)*tracked struct __StorageMetadata #decl #wc{#location: ::vstd::resource::Loc,#marker_field}
        #opt_wrapper #map_wrapper
        #(#attrs)*pub tracked struct Instance #decl #wc{metadata:#descriptor}
        impl #decl Instance #types #wc {
            pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}
            pub proof fn clone(tracked &self)->(tracked #out:Self) ensures #out.id()==self.id(),{Self{metadata:self.metadata.clone()}}
            #conversions #(#emitted)*
        }
    })
}
