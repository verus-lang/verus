//! Native logical owners over distinct generated physical map namespaces.
//! The adapter under development keeps all original State fields.
use crate::ast::*;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use crate::verified_field_storage_roles as roles;
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

pub fn needed(sm: &SM)->bool {
    sm.fields.len()==6
        && sm.fields.iter().filter(|f|matches!(f.stype,ShardableType::Constant(_))).count()==1
        && sm.fields.iter().filter(|f|matches!(f.stype,ShardableType::Variable(_))).count()==1
        && sm.fields.iter().filter(|f|matches!(f.stype,ShardableType::IMap(..))).count()==2
        && sm.fields.iter().filter(|f|matches!(f.stype,ShardableType::StorageIMap(..))).count()==2
}
fn reserve(tokens:TokenStream,names:&mut HashSet<String>) {
    for t in tokens {match t {
        TokenTree::Ident(n)=>{names.insert(n.to_string().trim_start_matches("r#").to_string());},
        TokenTree::Group(g)=>reserve(g.stream(),names),_=>{},
    }}
}
pub(crate) fn reserve_stmt(stmt:&TransitionStmt,names:&mut HashSet<String>) {
    match stmt {
        TransitionStmt::Block(_,children)=>for child in children{reserve_stmt(child,names);},
        TransitionStmt::Require(_,e)|TransitionStmt::Update(_,_,e)
        |TransitionStmt::Initialize(_,_,e)|TransitionStmt::PostCondition(_,e)=>reserve(quote!{#e},names),
        TransitionStmt::Assert(_,e,proof)=>{
            let block=proof.proof.as_ref().map(|b|&**b);
            reserve(quote!{#e #block},names);
        }
        TransitionStmt::SubUpdate(_,_,indices,e)=>{
            reserve(quote!{#e},names);
            for index in indices{if let SubIdx::Idx(e)=index{reserve(quote!{#e},names);}}
        }
        TransitionStmt::Split(_,kind,children)=>{
            match &**kind{
                SplitKind::If(e)=>reserve(quote!{#e},names),
                SplitKind::Match(e,arms)=>{
                    reserve(quote!{#e},names);
                    for arm in arms{let pat=&arm.pat;let guard=arm.guard.as_ref().map(|(_,e)|e);reserve(quote!{#pat #guard},names);}
                }
                SplitKind::Let(pat,ty,_,e)=>reserve(quote!{#pat #ty #e},names),
                SplitKind::Special(_,op,proof,pat)=>{
                    let block=proof.proof.as_ref().map(|b|&**b);
                    reserve(quote!{#pat #block},names);
                    match &op.elt{
                        MonoidElt::General(e)|MonoidElt::SingletonMultiset(e)|MonoidElt::SingletonSet(e)=>reserve(quote!{#e},names),
                        MonoidElt::OptionSome(e)=>reserve(quote!{#e},names),
                        MonoidElt::SingletonKV(k,v)=>reserve(quote!{#k #v},names),
                        MonoidElt::True=>{},
                    }
                }
            }
            for child in children{reserve_stmt(child,names);}
        }
    }
}
fn initial(stmt:&TransitionStmt,values:&mut HashMap<String,Expr>)->Result<(),Error>{
    match stmt {
        TransitionStmt::Block(_,children)=>for c in children{initial(c,values)?;},
        TransitionStmt::Initialize(_,field,value)=>{
            if values.insert(field.to_string(),value.clone()).is_some(){
                return Err(Error::new(field.span(),"map-pair initializer repeats a field"));
            }
        }
        _=>return Err(Error::new(*stmt.get_span(),"map-pair initializer requires explicit complete fields")),
    }
    Ok(())
}
pub fn output(sm:&SM,_selected:&HashSet<String>)->Result<TokenStream,Error>{
    if !needed(sm){return Err(Error::new(sm.name.span(),"map-pair facade requires one Constant, one Variable, two IMaps and two StorageIMaps"));}
    let mut generated_types:HashSet<String>=["State","Fragment","Protocol","Token","Instance","Ghost","Tracked"]
        .iter().map(|name|(*name).to_string()).collect();
    if let Some(generics)=&sm.generics {
        for parameter in &generics.params {
            if let verus_syn::GenericParam::Type(parameter)=parameter {
                generated_types.insert(parameter.ident.to_string().trim_start_matches("r#").to_string());
            }
        }
    }
    for f in sm.fields.iter().filter(|f|matches!(f.stype,ShardableType::Variable(_)|ShardableType::IMap(..))){
        if !generated_types.insert(f.name.to_string().trim_start_matches("r#").to_string()){
            return Err(Error::new(f.name.span(),"map-pair field conflicts with a generated nominal type"));
        }
        if matches!(f.stype,ShardableType::IMap(..)) {
            for suffix in ["collection","map"].iter() {
                let derived=format!("{}_{}",f.name.to_string().trim_start_matches("r#"),suffix);
                if sm.fields.iter().any(|other|other.name.to_string().trim_start_matches("r#")==derived)
                    || !generated_types.insert(derived) {
                    return Err(Error::new(f.name.span(),"map-pair collection name conflicts with a generated nominal type"));
                }
            }
        }
    }
    if let Some(field)=sm.fields.iter().find(|field|field.name.to_string().starts_with("r#")) {
        return Err(Error::new(field.name.span(),"map-pair facade does not yet support raw field identifiers"));
    }
    let mut generated_methods:HashSet<String>=["id","clone","__protocol_location"]
        .iter().map(|name|(*name).to_string()).collect();
    for f in sm.fields.iter().filter(|f|matches!(f.stype,ShardableType::Constant(_))){
        if !generated_methods.insert(f.name.to_string().trim_start_matches("r#").to_string()){
            return Err(Error::new(f.name.span(),"map-pair Constant getter conflicts with an Instance method"));
        }
    }
    for tr in &sm.transitions{
        if tr.kind==TransitionKind::Property{
            return Err(Error::new(tr.name.span(),"map-pair facade does not yet support property declarations"));
        }
        if !generated_methods.insert(tr.name.to_string().trim_start_matches("r#").to_string()){
            return Err(Error::new(tr.name.span(),"map-pair transition conflicts with an Instance method"));
        }
    }
    let (g,attrs)=crate::verified_tokens::datatype_generics(sm);
    let(decl,wc)=generics_for_decl(&g);
    let args=sm.generics.as_ref().map(|g|get_generic_args(&g.params));
    let types=args.as_ref().map(|a|quote!{<#a>}).unwrap_or_default();
    let expr=args.as_ref().map(|a|quote!{::<#a>}).unwrap_or_default();
    let field_ast=&sm.fields_named_ast;
    let generic_ast=&sm.generics;
    let mut names=HashSet::new();
    reserve(quote!{#field_ast #generic_ast},&mut names);
    for tr in &sm.transitions {
        names.insert(tr.name.to_string());
        for p in &tr.params{let name=&p.name;let ty=&p.ty;reserve(quote!{#name #ty},&mut names);}
        reserve_stmt(&tr.body,&mut names);
    }
    let mut reservation=TokenStream::new();
    for name in &names {
        reservation.extend(name.parse::<TokenStream>().expect("reserved names are original identifier tokens"));
    }
    let mut fresh=|label:&str|{
        let mut n=format!("__tsm_map_pair_{label}");
        while names.contains(&n){n.push('_');}names.insert(n.clone());
        Ident::new(&n,Span::mixed_site())
    };
    let metadata=fresh("Metadata");let location=fresh("protocol_location");let marker=fresh("types");
    let token=quote!{Token #types};
    let descriptor=quote!{::vstd::resource::tsm_context::Descriptor<#metadata #types>};
    let constants:Vec<_>=sm.fields.iter().filter(|f|matches!(f.stype,ShardableType::Constant(_))).collect();
    let cn:Vec<_>=constants.iter().map(|f|&f.name).collect();
    let ct:Vec<_>=constants.iter().map(|f|f.get_type()).collect();
    let setters:Vec<_>=constants.iter().map(|f|format_ident!("with_{}",f.name)).collect();
    let cx=roles::Context{decl:&decl,types:&types,expr:&expr,where_clause:&wc,attrs:&attrs,
        token:&token,descriptor:&descriptor,protocol_location:&location,constants:&constants};
    let mut wrappers=Vec::new();
    for f in &sm.fields {
        match &f.stype{
            ShardableType::Variable(_)=>wrappers.push(roles::wrapper(f,&cx)?),
            ShardableType::IMap(..)=>wrappers.push(crate::verified_field_storage_imap_roles::wrapper(f,&cx,&reservation)?),
            _=>{},
        }
    }
    let owners:Vec<_>=sm.fields.iter().filter(|f|matches!(f.stype,ShardableType::Variable(_)|ShardableType::IMap(..))).collect();
    let mut methods=Vec::new();
    for tr in &sm.transitions {
        if tr.kind!=TransitionKind::Init {continue;}
        let mut values=HashMap::new();initial(&tr.body,&mut values)?;
        if values.len()!=sm.fields.len(){return Err(Error::new(tr.name.span(),"map-pair initialization must initialize every original field"));}
        let name=&tr.name;
        let params:Vec<_>=tr.params.iter().map(|p|{let n=&p.name;let t=&p.ty;quote!{#n:#t}}).collect();
        let pn:Vec<_>=tr.params.iter().map(|p|&p.name).collect();
        let cv:Vec<_>=constants.iter().map(|f|&values[&f.name.to_string()]).collect();
        let remaining=fresh("initial_remaining");let md=fresh("initial_metadata");
        let part=fresh("initial_part");let rest=fresh("initial_rest");
        let state=fresh("initial_state");
        let enabled=format_ident!("{name}_enabled");
        let strong=format_ident!("{name}_strong");
        let mut splits=Vec::new();let mut returns=Vec::new();let mut constructions=Vec::new();let mut ensures=Vec::new();
        for(index,field)in owners.iter().enumerate(){
            let n=&field.name;let value=&values[&n.to_string()];let native=field.get_type();
            let anchor=fresh(&format!("initial_value_{n}"));
            let value=quote!{((|#anchor:#native|#anchor)(#value))};
            let owner=fresh(&format!("initial_owner_{n}"));
            let select=format_ident!("select_{n}");let without=format_ident!("without_{n}");let law=format_ident!("take_{n}_law");
            splits.push(quote!{
                #remaining.fragment().#law();
                let #part=#remaining.fragment().#select()#(.#setters(#cv))*;
                let #rest=#remaining.fragment().#without();
                assert(Fragment #expr::op(#part,#rest)==#remaining.fragment());
                let tracked(#owner,#remaining)=#remaining.split(#part,#rest);
            });
            let ix=verus_syn::Index::from(index+1);
            if matches!(field.stype,ShardableType::IMap(..)){
                let collection=format_ident!("{n}_collection");
                returns.push(quote!{Tracked<#collection #types>});
                constructions.push(quote!{Tracked(<#collection #types>::__from_token(#owner,#md.clone(),#value))});
                ensures.push(quote!{out.#ix@.map()==#value});
            }else{
                returns.push(quote!{Tracked<#n #types>});
                constructions.push(quote!{Tracked(<#n #types>::__from_token(#owner,#md.clone()))});
                ensures.push(quote!{out.#ix@.value()==#value});
            }
            ensures.push(quote!{out.#ix@.instance_id()==out.0@.id()});
        }
        let empty_requirements:Vec<_>=sm.fields.iter().filter(|f|f.stype.is_storage()).map(|f|{
            let value=&values[&f.name.to_string()];let native=f.get_type();let anchor=fresh(&format!("initial_storage_{}",f.name));
            quote!{((|#anchor:#native|#anchor)(#value))==IMap::empty()}
        }).collect();
        methods.push(quote!{
            pub proof fn #name(#(#params),*)->(tracked out:(Tracked<Self>,#(#returns),*))
                requires #(#empty_requirements),*,
                ensures #(#ensures),*,#(out.0@.#cn()==#cv),*,
            {
                assert(State #expr::#enabled(#(#pn),*));
                assert forall|#state:State #types| State #expr::#strong(#state,#(#pn),*)
                    implies #state.__storage()==IMap::empty() by {
                    assert(::vstd::prelude::ext_equal(#state.__storage(),IMap::empty()));
                }
                let tracked #remaining=Protocol #expr::#name(IMap::tracked_empty(),#(#pn),*);
                let tracked #md=::vstd::resource::tsm_context::Descriptor::alloc(#metadata{#location:#remaining.loc(),#(#cn:#cv,)*#marker:core::marker::PhantomData});
                #(#splits)*
                (Tracked(Self{metadata:#md.clone()}),#(#constructions),*)
            }
        });
    }
    let marker_type=args.as_ref().map(|a|quote!{(#a,)}).unwrap_or_else(||quote!{()});
    let variable_methods=crate::verified_field_storage_map_pair_transitions::variable_methods(sm,&cx)?;
    let transfer_methods=crate::verified_field_storage_map_pair_transitions::transfer_methods(sm,&cx)?;
    Ok(quote!{
        #(#attrs)*struct #metadata #decl #wc {ghost #location: ::vstd::resource::Loc,#(ghost #cn:#ct,)*ghost #marker:core::marker::PhantomData<#marker_type>}
        #(#wrappers)*
        #(#attrs)*pub tracked struct Instance #decl #wc{metadata:#descriptor}
        impl #decl Instance #types #wc{
            pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}
            pub closed spec fn __protocol_location(&self)->::vstd::resource::Loc{self.metadata.value().#location}
            #(pub closed spec fn #cn(&self)->#ct{self.metadata.value().#cn})*
            pub proof fn clone(tracked &self)->(tracked out:Self)
                ensures out.id()==self.id(),out.__protocol_location()==self.__protocol_location(),#(out.#cn()==self.#cn()),*,
            {Self{metadata:self.metadata.clone()}}
            #(#methods)*
            #variable_methods
            #transfer_methods
        }
    })
}
