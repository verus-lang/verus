//! Actual variable updates with ghost observations of mutable, unowned state.
//! Observations are extracted from the existing checked output witness, never
//! from an initializer cache or an asserted distinguished global state.
use crate::ast::*;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Ident};

fn writes(stmt: &TransitionStmt, out: &mut HashSet<String>) {
    match stmt {
        TransitionStmt::Update(_, n, _) | TransitionStmt::SubUpdate(_, n, _, _) => {
            out.insert(n.to_string());
        }
        TransitionStmt::Block(_, children) | TransitionStmt::Split(_, _, children) => {
            for child in children { writes(child, out); }
        }
        _ => {}
    }
}

pub fn needed(sm: &SM) -> bool {
    let hidden: HashSet<_> = sm.fields.iter()
        .filter(|f| matches!(f.stype, ShardableType::NotTokenized(_)))
        .map(|f| f.name.to_string()).collect();
    sm.transitions.iter().any(|tr| {
        let mut changed = HashSet::new();
        writes(&tr.body, &mut changed);
        changed.iter().any(|n| hidden.contains(n))
    })
}

/// Exclude updates of unowned fields from the token read footprint only.
/// The original executor, State relations, safety and all-frame obligations
/// continue to process the untouched original transition.
pub fn token_footprint(stmt: &mut TransitionStmt, fields: &HashMap<String, Field>) {
    match stmt {
        TransitionStmt::Update(span, n, _) | TransitionStmt::SubUpdate(span, n, _, _)
            if matches!(fields[&n.to_string()].stype, ShardableType::NotTokenized(_)) =>
        {
            *stmt = TransitionStmt::Block(*span, vec![]);
        }
        TransitionStmt::Block(_, children) | TransitionStmt::Split(_, _, children) => {
            for child in children { token_footprint(child, fields); }
        }
        _ => {}
    }
}

fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
    for token in tokens {
        match token {
            TokenTree::Ident(n) => { names.insert(n.to_string().trim_start_matches("r#").to_owned()); }
            TokenTree::Group(g) => reserve(g.stream(), names),
            _ => {}
        }
    }
}

pub fn output(sm: &SM) -> Result<TokenStream, Error> {
    if !needed(sm) || sm.fields.iter().any(|f| !matches!(f.stype,
        ShardableType::Variable(_) | ShardableType::Constant(_) | ShardableType::NotTokenized(_))) {
        return Err(Error::new(sm.name.span(),
            "mutable unowned observation facade requires scalar variable/constant/not_tokenized fields"));
    }
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let marker = args.as_ref().map(|_| quote! {__tsm_phantom:core::marker::PhantomData,});
    let variables: Vec<_> = sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::Variable(_))).collect();
    let constants: Vec<_> = sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::Constant(_))).collect();
    let hidden: Vec<_> = sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::NotTokenized(_))).collect();
    let fields: HashMap<_,_> = sm.fields.iter().map(|f|(f.name.to_string(),f.clone())).collect();
    let mut occupied = HashSet::new();
    let ast = &sm.fields_named_ast;
    let generic_ast = &sm.generics;
    reserve(quote! {#ast #generic_ast}, &mut occupied);
    let mut methods_seen: HashSet<String> = ["id","clone","invariant"].iter().map(|s|s.to_string()).collect();
    for f in &sm.fields {
        let n=f.name.to_string();
        if n.starts_with("r#") || ["Instance","Protocol","State","Fragment","Token"].contains(&n.as_str()) {
            return Err(Error::new(f.name.span(),"unowned observation field conflicts with a generated type or raw field name"));
        }
        if matches!(f.stype, ShardableType::Constant(_)) && !methods_seen.insert(n) {
            return Err(Error::new(f.name.span(),"unowned observation constant getter conflicts with an Instance method"));
        }
    }
    for tr in &sm.transitions {
        let n=&tr.name;
        reserve(quote! {#n}, &mut occupied);
        crate::verified_field_storage_map_pair::reserve_stmt(&tr.body, &mut occupied);
        for p in &tr.params { let n=&p.name;let t=&p.ty;reserve(quote! {#n #t},&mut occupied); }
        if !methods_seen.insert(n.to_string().trim_start_matches("r#").to_owned()) {
            return Err(Error::new(n.span(),"unowned observation transition conflicts with an Instance method"));
        }
    }
    let mut fresh = |label: &str| {
        let mut n=format!("__tsm_nt_{label}");
        while occupied.contains(&n) { n.push('_'); }
        occupied.insert(n.clone());Ident::new(&n,Span::mixed_site())
    };
    let context=fresh("context");
    let result=fresh("result");
    let pre=fresh("before");
    let post=fresh("after");
    let frame=fresh("frame");
    let cn:Vec<_>=constants.iter().map(|f|&f.name).collect();
    let ct:Vec<_>=constants.iter().map(|f|f.get_type()).collect();
    let cg:Vec<_>=cn.iter().map(|n|format_ident!("value_{n}")).collect();
    let co:Vec<_>=cn.iter().map(|n|format_ident!("owns_{n}")).collect();
    let vn:Vec<_>=variables.iter().map(|f|&f.name).collect();
    let vg:Vec<_>=vn.iter().map(|n|format_ident!("value_{n}")).collect();
    let takes:Vec<_>=vn.iter().map(|n|format_ident!("take_{n}")).collect();
    let wrappers:Vec<_>=variables.iter().map(|f|crate::verified_field_scalars::scalar_wrapper(sm,f)).collect::<Result<_,_>>()?;
    let mut shape=quote! {Fragment #expr::unit()};
    for (n,g) in cn.iter().zip(&cg) {
        let setter=format_ident!("with_{n}");
        shape=quote! {#shape.#setter(self.context.fragment().#g())};
    }
    let reflexive=fresh("reflexive");
    let machine=fresh("machine");
    let mut methods=vec![quote! {
        proof fn #reflexive<#machine: ::vstd::resource::tsm::Machine>(source:#machine::Fragment)
            ensures ::vstd::resource::tsm::fragment_included::<#machine>(source,source)
        {source.op_unit();}
    }];
    for tr in &sm.transitions {
        let n=&tr.name;
        let pn:Vec<_>=tr.params.iter().map(|p|&p.name).collect();
        let params:Vec<_>=tr.params.iter().map(|p|{let n=&p.name;let t=&p.ty;quote! {#n:#t}}).collect();
        let strong=format_ident!("{n}_strong");
        let enabled=format_ident!("{n}_enabled");
        if tr.kind==TransitionKind::Init {
            let raw:Vec<_>=vn.iter().map(|n|fresh(&format!("initial_{n}"))).collect();
            let remaining=fresh("initial_remaining");
            let initial_state=fresh("initial_state");
            let indices:Vec<_>=(1..=vn.len()).map(verus_syn::Index::from).collect();
            let hn:Vec<_>=hidden.iter().map(|f|fresh(&format!("initial_hidden_{}",f.name))).collect();
            let ht:Vec<_>=hidden.iter().map(|f|f.get_type()).collect();
            let hf:Vec<_>=hidden.iter().zip(&hn).map(|(f,v)|{let n=&f.name;quote! {#n:#v}}).collect();
            let state=quote! {State #expr{#marker #(#cn:#result.0@.#cn(),)*#(#vn:#result.#indices@.value(),)*#(#hf),*}};
            let initial_hidden:Vec<_>=hidden.iter().map(|f|{let n=&f.name;quote! {#n:#initial_state.#n}}).collect();
            let restored_state=quote! {State #expr{#marker #(#cn:#result.0@.#cn(),)*#(#vn:#result.#indices@.value(),)*#(#initial_hidden),*}};
            methods.push(quote! {
                pub proof fn #n(#(#params),*)->(tracked #result:(Tracked<Self>,#(Tracked<#vn #types>),*))
                    requires State #expr::#enabled(#(#pn),*)
                    ensures #(#result.#indices@.instance_id()==#result.0@.id(),)*
                        exists|#(#hn:#ht),*|State #expr::#strong(#state,#(#pn),*)
                {
                    let tracked #remaining=Protocol #expr::#n(#(#pn),*);
                    let #initial_state=choose|#initial_state:State #types|
                        State #expr::#n(#initial_state,#(#pn),*)&&#initial_state.invariant()
                        &&#remaining.fragment()==Protocol #expr::embed(#initial_state);
                    assert(State #expr::#strong(#initial_state,#(#pn),*));
                    #(let tracked (#raw,#remaining)=Protocol #expr::#takes(#remaining);)*
                    #(assert(#raw.fragment().#vg()==#initial_state.#vn);)*
                    #(assert(#remaining.fragment().#cg()==#initial_state.#cn);)*
                    let tracked #result=(Tracked(Self{context:#remaining}),#(Tracked(#vn #expr::__from_token(#raw))),*);
                    assert(State #expr::#strong(#restored_state,#(#pn),*));
                    #result
                }
            });
            continue;
        }
        if tr.kind!=TransitionKind::Transition {
            return Err(Error::new(n.span(),"unowned observation facade requires init and mutating transitions"));
        }
        let mut changed=HashSet::new();writes(&tr.body,&mut changed);
        let mutable:Vec<_>=variables.iter().filter(|f|changed.contains(&f.name.to_string())).copied().collect();
        if mutable.len()!=1 {
            return Err(Error::new(n.span(),"unowned observation facade currently requires one changed variable owner"));
        }
        let owner=mutable[0];let name=&owner.name;
        let mut access_errors=vec![];
        let mut footprint=tr.body.clone();token_footprint(&mut footprint,&fields);
        let (reads,birds)=crate::field_access_visitor::find_all_accesses(&mut footprint,&mut access_errors,&fields);
        if let Some(e)=access_errors.into_iter().next(){return Err(e);}
        let readonly:Vec<_>=variables.iter().filter(|f|f.name!=*name&&reads.contains(&f.name.to_string())).copied().collect();
        let unknown:Vec<_>=sm.fields.iter().filter(|f|birds.contains(&f.name.to_string())
            && !matches!(f.stype,ShardableType::Constant(_))
            && f.name!=*name&&!readonly.iter().any(|r|r.name==f.name)).collect();
        let un:Vec<_>=unknown.iter().map(|f|&f.name).collect();
        let ut:Vec<_>=unknown.iter().map(|f|f.get_type()).collect();
        let rn:Vec<_>=readonly.iter().map(|f|&f.name).collect();
        let refs:Vec<_>=readonly.iter().map(|f|fresh(&format!("reference_{}",f.name))).collect();
        let rg:Vec<_>=rn.iter().map(|n|format_ident!("value_{n}")).collect();
        let rf:Vec<_>=rn.iter().map(|n|format_ident!("field_{n}")).collect();
        let ro:Vec<_>=rn.iter().map(|n|format_ident!("owns_{n}")).collect();
        let current=fresh("owner_reference");
        let raw=fresh("owner_raw");
        let before=fresh("owned_before");
        let shared=fresh("shared");
        let upper=fresh("upper");
        let selected=fresh("selected");
        let remainder=fresh("remainder");
        let output=fresh("output");
        let output_fragment=fresh("output_fragment");
        let replacement=fresh("replacement");
        let helper=fresh(&format!("helper_{n}"));
        let factory=format_ident!("field_{name}");
        let getter=format_ident!("value_{name}");
        let own=format_ident!("owns_{name}");
        let req=format_ident!("{n}_requires");
        let outputs=format_ident!("{n}_outputs");
        let frame_update=format_ident!("{n}_frame");
        let owned_post=format_ident!("{n}_owned_post");
        let return_signature=match ut.len(){
            0=>quote! {},
            // A proof method's unmarked result is a ghost result, matching the
            // original token generator. "ghost" is not a return-binder keyword.
            1=>{let t=&ut[0];quote! {->(#result:#t)}},
            _=>quote! {->(tracked #result:(#(Ghost<#ut>),*))},
        };
        let unknown_returns:Vec<_>=un.iter().enumerate().map(|(i,n)|{
            let value=if ut.len()==1{quote! {#result}}else{let i=verus_syn::Index::from(i);quote! {#result.#i@}};
            quote! {#pre.#n==#value}
        }).collect();
        let return_value=match un.len(){0=>quote! {()},1=>{let n=un[0];quote! {#pre.#n}},_=>quote! {(#(Ghost(#pre.#un)),*)}};
        let helper_post=quote! {exists|#pre:State #types,#post:State #types|#pre.invariant()&&#post.invariant()
            &&State #expr::#strong(#pre,#post,#(#pn),*)
            &&#pre.#name==old(#raw).fragment().#getter()&&#post.#name==final(#raw).fragment().#getter()
            #(&& #pre.#rn==#refs.fragment().#rg())* #(&& #pre.#cn==#context.fragment().#cg())*
            #(&& #unknown_returns)*};
        let public_post=quote! {exists|#pre:State #types,#post:State #types|#pre.invariant()&&#post.invariant()
            &&State #expr::#strong(#pre,#post,#(#pn),*)
            &&#pre.#name==old(#current).value()&&#post.#name==final(#current).value()
            #(&& #pre.#rn==#refs.value())* #(&& #pre.#cn==self.#cn())*
            #(&& #unknown_returns)*};
        let mut target=quote! {#context.fragment()};
        let mut helper_shape=quote! {Fragment #expr::unit()};
        for (n,g) in cn.iter().zip(&cg) {
            let setter=format_ident!("with_{n}");
            helper_shape=quote! {#helper_shape.#setter(#context.fragment().#g())};
        }
        let mut rest=quote! {#upper};
        let mut public_shared=quote! {Fragment #expr::unit()};
        for n in &cn {let s=format_ident!("with_{n}");public_shared=quote! {#public_shared.#s(self.#n())};}
        for ((n,r),g) in rn.iter().zip(&refs).zip(&rg){
            let setter=format_ident!("with_{n}");target=quote! {#target.#setter(#r.fragment().#g())};
            public_shared=quote! {#public_shared.#setter(#r.value())};
        }
        for n in cn.iter().chain(&rn){let without=format_ident!("without_{n}");rest=quote! {#rest.#without()};}
        let raw_shape=quote! {Fragment #expr::#factory(#raw.fragment().#getter())};
        let raw_after_shape=quote! {Fragment #expr::#factory(final(#raw).fragment().#getter())};
        methods.push(quote! {
            proof fn #helper(tracked #context:&Token #types,#(#params,)*tracked #raw:&mut Token #types,
                #(tracked #refs:&Token #types),*) #return_signature
                requires #(#context.fragment().#co(),)*
                    #context.fragment()==#helper_shape,
                    #raw.loc()==#context.loc(),#raw.fragment().#own(),#raw.fragment()==#raw_shape,
                    #(#refs.loc()==#context.loc(),#refs.fragment().#ro(),#refs.fragment()==Fragment #expr::#rf(#refs.fragment().#rg()),)*
                    Protocol #expr::#req(#raw.fragment(),#target,#(#pn),*)
                ensures final(#raw).loc()==old(#raw).loc(),final(#raw).fragment().#own(),
                    final(#raw).fragment()==#raw_after_shape,#helper_post
            {
                let ghost #before=#raw.fragment();
                let tracked #shared=#context.observe();
                Self::#reflexive::<Protocol #types>(#context.fragment());
                #(let tracked #shared=#shared.join(&#refs.observe());)*
                let #upper=#shared.fragment();#shared.validate();
                let(#frame,#pre)=choose|#frame:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(#upper,#frame)==Protocol #expr::embed(#pre);
                let #selected=#target;let #remainder=#rest;
                assert(Fragment #expr::op(#selected,#remainder)==#upper);
                assert(::vstd::resource::tsm::fragment_included::<Protocol #types>(#selected,#upper));
                let tracked #shared=#shared.weaken(#selected);
                let tracked mut #replacement=#raw.empty();::vstd::modes::tracked_swap(#raw,&mut #replacement);
                Protocol #expr::#frame_update(#before,#selected,#(#pn),*);
                let #output=::vstd::iset::ISet::new(|#output_fragment:Fragment #types|Protocol #expr::#outputs(#before,#selected,#output_fragment,#(#pn),*));
                let tracked mut #replacement=#replacement.update_nondeterministic_with_observation(&#shared,#output);
                let(#frame,#pre,#post)=choose|#frame:Fragment #types,#pre:State #types,#post:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#selected),#frame)==Protocol #expr::embed(#pre)
                    &&State #expr::#strong(#pre,#post,#(#pn),*)&&#post.invariant()
                    &&#replacement.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#pn),*)
                    &&Fragment #expr::op(Fragment #expr::op(#replacement.fragment(),#selected),#frame)==Protocol #expr::embed(#post);
                assert(#pre.#name==#before.#getter());
                assert(#replacement.fragment()==Fragment #expr::#factory(#post.#name));
                ::vstd::modes::tracked_swap(#raw,&mut #replacement);
                #return_value
            }
            pub proof fn #n(tracked &self,#(#params,)*tracked #current:&mut #name #types,
                #(tracked #refs:&#rn #types),*) #return_signature
                requires #current.instance_id()==self.id(),#(#refs.instance_id()==self.id(),)*
                    Protocol #expr::#req(Fragment #expr::#factory(#current.value()),#public_shared,#(#pn),*)
                ensures final(#current).instance_id()==old(#current).instance_id(),#public_post
            {
                use_type_invariant(self);use_type_invariant(&*#current);#(use_type_invariant(#refs);)*
                Self::#helper(&self.context,#(#pn,)*&mut #current.raw,#(&#refs.raw),*)
            }
        });
    }
    Ok(quote! {
        #(#wrappers)* #(#attrs)*pub tracked struct Instance #decl #wc {context:Token #types}
        impl #decl Instance #types #wc {
            #[verifier::type_invariant] spec fn invariant(self)->bool{self.context.fragment()==#shape #(&& self.context.fragment().#co())*}
            pub closed spec fn id(&self)->::vstd::resource::Loc{self.context.loc()}
            #(pub closed spec fn #cn(&self)->#ct{self.context.fragment().#cg()})*
            pub proof fn clone(tracked &self)->(tracked #result:Self)
                ensures #result.id()==self.id(),#(#result.#cn()==self.#cn(),)*
            {use_type_invariant(self);Fragment #expr::op_unit(self.context.fragment());Self{context:self.context.duplicate()}}
            #(#methods)*
        }
    })
}
