//! Checked nominal variable updates for the existing general control-flow backend.
use crate::ast::*;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use std::collections::HashSet;
use verus_syn::{Error, Ident};

fn fresh(sm: &SM, tr: &Transition, label: &str) -> Ident {
    fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
        for token in tokens {
            match token {
                proc_macro2::TokenTree::Ident(name) => {
                    names.insert(name.to_string().trim_start_matches("r#").to_string());
                }
                proc_macro2::TokenTree::Group(group) => reserve(group.stream(), names),
                _ => {}
            }
        }
    }
    let mut names = HashSet::new();
    let fields = &sm.fields_named_ast;
    let generics = &sm.generics;
    reserve(quote! {#fields #generics}, &mut names);
    for transition in &sm.transitions {
        let name = &transition.name;
        reserve(quote! {#name}, &mut names);
        for parameter in &transition.params {
            let name = &parameter.name;
            let ty = &parameter.ty;
            reserve(quote! {#name #ty}, &mut names);
        }
        crate::verified_field_storage_map_pair::reserve_stmt(&transition.body, &mut names);
    }
    let mut name = format!("__tsm_control_{label}");
    while names.contains(&name) || names.contains(&format!("r#{name}")) {
        name.push('_');
    }
    Ident::new(&name, Span::mixed_site())
}
fn changed(stmt: &TransitionStmt, out: &mut HashSet<String>) {
    match stmt {
        TransitionStmt::Update(_, name, _) | TransitionStmt::SubUpdate(_, name, _, _) => {
            out.insert(name.to_string());
        }
        TransitionStmt::Block(_, children) | TransitionStmt::Split(_, _, children) => {
            for child in children {
                changed(child, out)
            }
        }
        _ => {}
    }
}
pub fn output(sm: &SM) -> Result<TokenStream, Error> {
    if !sm
        .fields
        .iter()
        .any(|f| matches!(f.stype, ShardableType::Variable(_)))
        || sm.fields.iter().any(|f| {
            !matches!(
                f.stype,
                ShardableType::Variable(_) | ShardableType::Constant(_)
            )
        })
    {
        return Err(Error::new(
            sm.name.span(),
            "control-flow field facade currently requires variable fields with optional constants",
        ));
    }
    for f in &sm.fields {
        if ["Instance", "Protocol", "State", "Fragment", "Token"]
            .contains(&f.name.to_string().as_str())
        {
            return Err(Error::new(
                f.name.span(),
                "field name conflicts with a generated field-token type",
            ));
        }
        if sm.generics.as_ref().is_some_and(|g| {
            g.params
                .iter()
                .any(|p| matches!(p,verus_syn::GenericParam::Type(t) if t.ident==f.name))
        }) {
            return Err(Error::new(
                f.name.span(),
                "field-token type conflicts with a generic type parameter",
            ));
        }
    }
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let marker = args
        .as_ref()
        .map(|_| quote! {__tsm_phantom:core::marker::PhantomData,});
    let variables: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Variable(_)))
        .collect();
    let constants: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(_)))
        .collect();
    let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
    let ct: Vec<_> = constants.iter().map(|f| f.get_type()).collect();
    let cg: Vec<_> = cn.iter().map(|f| format_ident!("value_{}", f)).collect();
    let co: Vec<_> = cn.iter().map(|f| format_ident!("owns_{}", f)).collect();
    let mut shape = quote! {Fragment #expr::unit()};
    for (f, getter) in cn.iter().zip(&cg) {
        let with = format_ident!("with_{}", f);
        shape = quote! {#shape.#with(self.context.fragment().#getter())};
    }
    let wrappers: Vec<_> = variables
        .iter()
        .map(|f| crate::verified_field_scalars::scalar_wrapper(sm, f))
        .collect::<Result<_, _>>()?;
    let names: Vec<_> = variables.iter().map(|f| &f.name).collect();
    let getters: Vec<_> = names.iter().map(|n| format_ident!("value_{}", n)).collect();
    let owns: Vec<_> = names.iter().map(|n| format_ident!("owns_{}", n)).collect();
    let factories: Vec<_> = names.iter().map(|n| format_ident!("field_{}", n)).collect();
    let takes: Vec<_> = names.iter().map(|n| format_ident!("take_{}", n)).collect();
    let inclusion = quote! {::vstd::resource::tsm::fragment_included_transitive};
    let reflexive = quote! {::vstd::resource::tsm::fragment_included_reflexive};
    let mut methods = Vec::new();
    for tr in &sm.transitions {
        let n = &tr.name;
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
        let refs: Vec<_> = names
            .iter()
            .map(|f| fresh(sm, tr, &format!("reference_{}", f)))
            .collect();
        let raw: Vec<_> = names
            .iter()
            .map(|f| fresh(sm, tr, &format!("raw_{}", f)))
            .collect();
        let enabled = format_ident!("{}_enabled", n);
        let strong = format_ident!("{}_strong", n);
        let pre = fresh(sm, tr, "pre");
        let post = fresh(sm, tr, "post");
        let context = fresh(sm, tr, "context");
        let mut helper_shape = quote! {Fragment #expr::unit()};
        for (f, getter) in cn.iter().zip(&cg) {
            let with = format_ident!("with_{}", f);
            helper_shape = quote! {#helper_shape.#with(#context.fragment().#getter())};
        }
        let owned = fresh(sm, tr, "owned");
        let remaining = fresh(sm, tr, "remaining");
        if tr.kind == TransitionKind::Init {
            let all = fresh(sm, tr, "initial");
            let indices: Vec<_> = (1..=names.len()).map(verus_syn::Index::from).collect();
            let result = quote! {State #expr {#marker #(#cn:out.0@.#cn(),)* #(#names:out.#indices@.value()),*}};
            let extraction:Vec<_>=takes.iter().zip(&raw).map(|(take,r)|quote!{let tracked (#r,#remaining)=Protocol #expr::#take(#remaining);}).collect();
            methods.push(quote!{
                pub proof fn #n(#(#params),*)->(tracked out:(Tracked<Self>,#(Tracked<#names #types>),*))
                    requires State #expr::#enabled(#(#pn),*)
                    ensures #(out.#indices@.instance_id()==out.0@.id(),)*
                        State #expr::#strong(#result,#(#pn),*)
                {
                    let tracked #all=Protocol #expr::#n(#(#pn),*);
                    let tracked #remaining=#all;
                    #(#extraction)*
                    let tracked #context=#remaining;
                    (Tracked(Self{context:#context}),#(Tracked(#names #expr::__from_token(#raw))),*)
                }
            });
            continue;
        }
        if tr.kind != TransitionKind::Transition {
            return Err(Error::new(
                n.span(),
                "control-flow field facade property support is not implemented",
            ));
        }
        let helper = fresh(sm, tr, &format!("helper_{}", n));
        let req = format_ident!("{}_requires", n);
        let outputs = format_ident!("{}_outputs", n);
        let frame_update = format_ident!("{}_frame", n);
        let mut writes = HashSet::new();
        changed(&tr.body, &mut writes);
        let fields = sm.fields.iter().map(|f| (f.name.to_string(), f.clone())).collect();
        let mut access_errors = vec![];
        let (mut reads, birds_eye_reads) = crate::field_access_visitor::find_all_accesses(
            &mut tr.body.clone(), &mut access_errors, &fields,
        );
        reads.extend(birds_eye_reads);
        if let Some(error) = access_errors.into_iter().next() {
            return Err(error);
        }
        let selected_indices: Vec<_> = names.iter().enumerate()
            .filter_map(|(i, name)| {
                (writes.contains(&name.to_string()) || reads.contains(&name.to_string()))
                    .then_some(i)
            }).collect();
        let unused_names: Vec<_> = names.iter().enumerate()
            .filter_map(|(i, name)| (!selected_indices.contains(&i)).then_some(*name))
            .collect();
        // Unmentioned fields are pure placeholders in the local relation.
        // Actual update readiness still quantifies over every invariant-compatible
        // completion of the owned and observed resources.
        let marker = quote! {#marker #(#unused_names: ::vstd::prelude::arbitrary(),)*};
        let names: Vec<_> = selected_indices.iter().map(|&i| names[i]).collect();
        let getters: Vec<_> = selected_indices.iter().map(|&i| getters[i].clone()).collect();
        let owns: Vec<_> = selected_indices.iter().map(|&i| owns[i].clone()).collect();
        let factories: Vec<_> = selected_indices.iter().map(|&i| factories[i].clone()).collect();
        let takes: Vec<_> = selected_indices.iter().map(|&i| takes[i].clone()).collect();
        let refs: Vec<_> = selected_indices.iter().map(|&i| refs[i].clone()).collect();
        let raw: Vec<_> = selected_indices.iter().map(|&i| raw[i].clone()).collect();
        let mutable: Vec<_> = names
            .iter()
            .enumerate()
            .filter_map(|(i, f)| writes.contains(&f.to_string()).then_some(i))
            .collect();
        let readonly: Vec<_> = names
            .iter()
            .enumerate()
            .filter_map(|(i, f)| (!writes.contains(&f.to_string())).then_some(i))
            .collect();
        let helper_params: Vec<_> = raw
            .iter()
            .enumerate()
            .map(|(i, r)| {
                if mutable.contains(&i) {
                    quote! {tracked #r:&mut Token #types}
                } else {
                    quote! {tracked #r:&Token #types}
                }
            })
            .collect();
        let helper_before: Vec<_> = raw
            .iter()
            .enumerate()
            .map(|(i, r)| {
                if mutable.contains(&i) {
                    quote! {old(#r)}
                } else {
                    quote! {#r}
                }
            })
            .collect();
        let helper_after: Vec<_> = raw
            .iter()
            .enumerate()
            .map(|(i, r)| {
                if mutable.contains(&i) {
                    quote! {final(#r)}
                } else {
                    quote! {#r}
                }
            })
            .collect();
        let public_params: Vec<_> = refs
            .iter()
            .zip(&names)
            .enumerate()
            .map(|(i, (r, f))| {
                if mutable.contains(&i) {
                    quote! {tracked #r:&mut #f #types}
                } else {
                    quote! {tracked #r:&#f #types}
                }
            })
            .collect();
        let public_before: Vec<_> = refs
            .iter()
            .enumerate()
            .map(|(i, r)| {
                if mutable.contains(&i) {
                    quote! {old(#r)}
                } else {
                    quote! {#r}
                }
            })
            .collect();
        let public_after: Vec<_> = refs
            .iter()
            .enumerate()
            .map(|(i, r)| {
                if mutable.contains(&i) {
                    quote! {final(#r)}
                } else {
                    quote! {#r}
                }
            })
            .collect();
        let helper_call: Vec<_> = refs
            .iter()
            .enumerate()
            .map(|(i, r)| {
                if mutable.contains(&i) {
                    quote! {&mut #r.raw}
                } else {
                    quote! {&#r.raw}
                }
            })
            .collect();
        let before = quote! {State #expr{#marker #(#cn:#context.fragment().#cg(),)* #(#names:#helper_before.fragment().#getters()),*}};
        let after = quote! {State #expr{#marker #(#cn:#context.fragment().#cg(),)* #(#names:#helper_after.fragment().#getters()),*}};
        let publicbefore =
            quote! {State #expr{#marker #(#cn:self.#cn(),)* #(#names:#public_before.value()),*}};
        let publicafter =
            quote! {State #expr{#marker #(#cn:self.#cn(),)* #(#names:#public_after.value()),*}};
        let mut fragment = quote! {Fragment #expr::unit()};
        for &i in &mutable {
            let r = &raw[i];
            fragment = quote! {Fragment #expr::op(#fragment,#r.fragment())};
        }
        let observed = fresh(sm, tr, "observation");
        let upper = fresh(sm, tr, "upper");
        let selected = fresh(sm, tr, "selected_observation");
        let remainder = fresh(sm, tr, "observation_remainder");
        let outer = fresh(sm, tr, "observation_outer");
        let state = fresh(sm, tr, "observation_state");
        let projection_fields: Vec<_> = readonly
            .iter()
            .map(|&i| &names[i])
            .chain(cn.iter())
            .collect();
        let lower_tokens: Vec<_> = readonly
            .iter()
            .map(|&i| &raw[i])
            .chain(std::iter::once(&context))
            .collect();
        let mut join_observations = vec![];
        let mut previous_tokens = vec![&context];
        for &i in &readonly {
            let r = &raw[i];
            let middle = fresh(sm, tr, &format!("observation_middle_{i}"));
            join_observations.push(quote! {
                let #middle=#observed.fragment();
                let tracked #observed=#observed.join(&#r.observe());
                #(#inclusion::<Protocol #types>(#previous_tokens.fragment(),#middle,#observed.fragment());)*
            });
            previous_tokens.push(r);
        }
        let mut target = quote! {#context.fragment()};
        let mut rest = quote! {#upper};
        for &i in &readonly {
            let setter = format_ident!("with_{}", names[i]);
            let getter = &getters[i];
            let r = &raw[i];
            target = quote! {#target.#setter(#r.fragment().#getter())};
        }
        for f in &projection_fields {
            let without = format_ident!("without_{}", f);
            rest = quote! {#rest.#without()};
        }
        let restore:Vec<_>=mutable.iter().map(|&i|{let take=&takes[i];let r=&raw[i];let v=fresh(sm,tr,&format!("return_{i}"));quote!{let tracked(mut #v,#remaining)=Protocol #expr::#take(#remaining);::vstd::modes::tracked_swap(#r,&mut #v);}}).collect();
        let mut extract = vec![];
        let mut owners = vec![];
        for &i in &mutable {
            let r = &raw[i];
            let v = fresh(sm, tr, &format!("owner_{i}"));
            extract.push(
                quote! {let tracked mut #v=#r.empty();::vstd::modes::tracked_swap(#r,&mut #v);},
            );
            owners.push(v);
        }
        let joins: Vec<_> = owners
            .iter()
            .skip(1)
            .map(|v| quote! {let tracked #owned=#owned.join(#v);})
            .collect();
        let first = if let Some(v) = owners.first() {
            quote! {#v}
        } else {
            quote! {#context.duplicate()}
        };
        let new = fresh(sm, tr, "new_fragment");
        let set = fresh(sm, tr, "outputs");
        methods.push(quote!{
            proof fn #helper(tracked #context:&Token #types,#(#params,)*#(#helper_params),*)
                requires #(#context.fragment().#co(),)*#context.fragment()==#helper_shape,
                    #(#helper_before.loc()==#context.loc(),#helper_before.fragment().#owns(),#helper_before.fragment()==Fragment #expr::#factories(#helper_before.fragment().#getters()),)*
                    State #expr::#enabled(#before,#(#pn),*)
                ensures #(#helper_after.loc()==#helper_before.loc(),#helper_after.fragment().#owns(),#helper_after.fragment()==Fragment #expr::#factories(#helper_after.fragment().#getters()),)*
                    State #expr::#strong(#before,#after,#(#pn),*)
            {
                let #pre=State #expr{#marker #(#cn:#context.fragment().#cg(),)*#(#names:#raw.fragment().#getters()),*};
                let tracked #observed=#context.observe();
                #reflexive::<Protocol #types>(#context.fragment());
                Fragment #expr::op_unit(#context.fragment());
                assert(Fragment #expr::op(#context.fragment(),Fragment #expr::unit())==#observed.fragment());
                assert(::vstd::resource::tsm::fragment_included::<Protocol #types>(#context.fragment(),#observed.fragment()));
                #(#join_observations)*
                let #upper=#observed.fragment();#observed.validate();
                let(#outer,#state)=choose|#outer:Fragment #types,#state:State #types|#state.invariant()&&Fragment #expr::op(#upper,#outer)==Protocol #expr::embed(#state);
                #(assert(::vstd::resource::tsm::fragment_included::<Protocol #types>(#lower_tokens.fragment(),#upper));)*
                let #selected=#target;let #remainder=#rest;
                assert(Fragment #expr::op(#selected,#remainder)==#upper);
                assert(::vstd::resource::tsm::fragment_included::<Protocol #types>(#selected,#upper));
                let tracked #observed=#observed.weaken(#selected);
                assert(Protocol #expr::#req(#fragment,#selected,#(#pn),*));
                #(#extract)*let tracked #owned=#first;#(#joins)*
                Protocol #expr::#frame_update(#owned.fragment(),#observed.fragment(),#(#pn),*);
                let #set=::vstd::iset::ISet::new(|#new:Fragment #types|Protocol #expr::#outputs(#owned.fragment(),#observed.fragment(),#new,#(#pn),*));
                let tracked #remaining=#owned.update_nondeterministic_with_observation(&#observed,#set);
                #(#restore)*
                assert(State #expr::#strong(#pre,#after,#(#pn),*));
            }
            pub proof fn #n(tracked &self,#(#params,)*#(#public_params),*)
                requires #(#refs.instance_id()==self.id(),)*State #expr::#enabled(#publicbefore,#(#pn),*)
                ensures #(#public_after.instance_id()==self.id(),)*State #expr::#strong(#publicbefore,#publicafter,#(#pn),*)
            {
                use_type_invariant(self);#(use_type_invariant(&*#refs);)*
                Self::#helper(&self.context,#(#pn,)*#(#helper_call),*);
            }
        });
    }
    Ok(quote! {
        #(#wrappers)* #(#attrs)*
        pub tracked struct Instance #decl #wc {context:Token #types}
        impl #decl Instance #types #wc {
            #[verifier::type_invariant] spec fn invariant(self)->bool{self.context.fragment()==#shape #(&& self.context.fragment().#co())*}
            #(pub closed spec fn #cn(&self)->#ct {self.context.fragment().#cg()})*
            pub closed spec fn id(&self)->::vstd::resource::Loc{self.context.loc()}
            pub proof fn clone(tracked &self)->(tracked out:Self) ensures out.id()==self.id(),#(out.#cn()==self.#cn(),)* {
                use_type_invariant(self);Fragment #expr::op_unit(self.context.fragment());
                let tracked context=self.context.duplicate();Self{context}
            }
            #(#methods)*
        }
    })
}
