//! Checked persistent map native unions and observations of actual supplied owners.
use crate::ast::*;
use crate::verified_field_logical::{generics, Generics};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

#[derive(Default)]
struct Flat {
    operations: Vec<(Ident, SpecialOp)>,
    requirements: Vec<Expr>,
    assertions: Vec<Expr>,
}
fn collect(stmt: &TransitionStmt, out: &mut Flat) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                collect(child, out)?;
            }
        }
        TransitionStmt::Require(_, e) => out.requirements.push(e.clone()),
        TransitionStmt::Assert(_, e, _) => out.assertions.push(e.clone()),
        TransitionStmt::Split(_, kind, children) => {
            if let SplitKind::Special(field, op, _, None) = &**kind {
                out.operations.push((field.clone(), op.clone()));
                for child in children {
                    collect(child, out)?;
                }
            } else {
                return Err(Error::new(
                    *stmt.get_span(),
                    "persistent map facade requires unbound straight-line operations",
                ));
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "persistent map facade requires explicit Add/Have operations",
            ))
        }
    }
    Ok(())
}
pub fn supports(sm: &SM, _tr: &Transition) -> bool {
    sm.fields.len() == 1
        && matches!(
            sm.fields[0].stype,
            ShardableType::PersistentMap(..) | ShardableType::PersistentIMap(..)
        )
}
/// Legacy domain view reports only the collection's CURRENT local map.
/// In particular an empty None collection gains no machine completion fact.
pub fn accessors(sm: &SM) -> TokenStream {
    if sm.fields.len() != 1 {
        return quote! {};
    }
    let field = &sm.fields[0];
    let domain = match &field.stype {
        ShardableType::PersistentMap(k, _) => quote! {::vstd::set::Set<#k>},
        ShardableType::PersistentIMap(k, _) => quote! {::vstd::iset::ISet<#k>},
        _ => return quote! {},
    };
    let (generic, _) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = crate::to_token_stream::generics_for_decl(&generic);
    let Generics { types, .. } = generics(sm);
    let bulk = format_ident!("{}_collection", field.name);
    quote! {impl #decl #bulk #types #wc{pub open spec fn dom(&self)->#domain{self.map().dom()}}}
}
fn fresh(sm: &SM, tr: &Transition, flat: &Flat, label: &str) -> Ident {
    fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
        for token in tokens {
            match token {
                TokenTree::Ident(id) => {
                    names.insert(id.to_string());
                }
                TokenTree::Group(g) => reserve(g.stream(), names),
                _ => {}
            }
        }
    }
    let mut names: HashSet<_> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .chain(sm.transitions.iter().map(|t| t.name.to_string()))
        .collect();
    if let Some(generics) = &sm.generics {
        reserve(quote! {#generics}, &mut names);
    }
    for e in flat.requirements.iter().chain(&flat.assertions) {
        reserve(quote! {#e}, &mut names);
    }
    for (_, op) in &flat.operations {
        match &op.elt {
            MonoidElt::General(e) => reserve(quote! {#e}, &mut names),
            MonoidElt::SingletonKV(k, Some(v)) => {
                reserve(quote! {#k}, &mut names);
                reserve(quote! {#v}, &mut names);
            }
            _ => {}
        }
    }
    let mut name = format!("__tsm_native_pmap_{label}");
    while names.contains(&name) {
        name.push('_');
    }
    Ident::new(&name, Span::mixed_site())
}
pub fn method(sm: &SM, tr: &Transition) -> Result<TokenStream, Error> {
    let mut flat = Flat::default();
    collect(&tr.body, &mut flat)?;
    let mut have = None;
    let mut add = None;
    for (_, op) in &flat.operations {
        match op.stmt {
            MonoidStmtType::Have if have.is_none() && add.is_none() => have = Some(op),
            MonoidStmtType::Add(_) if add.is_none() => add = Some(op),
            _ => {
                return Err(Error::new(
                    tr.name.span(),
                    "persistent map facade permits one Have before at most one Add",
                ))
            }
        }
    }
    if have.is_none() && add.is_none() {
        return Err(Error::new(
            tr.name.span(),
            "persistent map facade needs a supplied operation",
        ));
    }
    let field = &sm.fields[0];
    let field_name = &field.name;
    let native = field.get_type();
    let (kt, vt, finite) = match &field.stype {
        ShardableType::PersistentMap(k, v) => (k, v, true),
        ShardableType::PersistentIMap(k, v) => (k, v, false),
        _ => unreachable!(),
    };
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let check = |expression: &Expr| -> Result<(), Error> {
        let mut e = expression.clone();
        let mut errors = vec![];
        crate::field_access_visitor::visit_field_accesses(
            &mut e,
            |errors, f, _| {
                errors.push(Error::new(
                    f.name.span(),
                    "persistent map facade requires explicit native operands and assertions",
                ))
            },
            &mut errors,
            &fields,
        );
        if let Some(e) = errors.into_iter().next() {
            Err(e)
        } else {
            Ok(())
        }
    };
    for e in flat.requirements.iter().chain(&flat.assertions) {
        check(e)?;
    }
    let operand = |op: &SpecialOp| -> Result<TokenStream, Error> {
        Ok(match &op.elt {
            MonoidElt::SingletonKV(k, Some(v)) => {
                check(k)?;
                check(v)?;
                quote! {<#native>::empty().insert(#k,#v)}
            }
            MonoidElt::General(e) => {
                check(e)?;
                quote! {#e}
            }
            _ => {
                return Err(Error::new(
                    field_name.span(),
                    "persistent map facade needs explicit entries or native maps",
                ))
            }
        })
    };
    let Generics { types, expr, .. } = generics(sm);
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
    let args: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let req = format_ident!("{}_requires", name);
    let enabled = format_ident!("{}_enabled", name);
    let owners = format_ident!("{}_owners_enabled", name);
    let strong = format_ident!("{}_strong", name);
    let owned_post = format_ident!("{}_owned_post", name);
    let adapter = format_ident!("__field_{}_with_observation", name);
    let factory = format_ident!("field_{}", field_name);
    let take = format_ident!("take_{}", field_name);
    let bulk = format_ident!("{}_collection", field_name);
    let input = fresh(sm, tr, &flat, "input");
    let observed = fresh(sm, tr, &flat, "observed");
    let owned = fresh(sm, tr, &flat, "owned");
    let before = fresh(sm, tr, &flat, "before");
    let outer = fresh(sm, tr, &flat, "outer");
    let pre = fresh(sm, tr, &flat, "pre");
    let post = fresh(sm, tr, &flat, "post");
    let next = fresh(sm, tr, &flat, "next");
    let lower = fresh(sm, tr, &flat, "lower");
    let key = fresh(sm, tr, &flat, "key");
    let needed = fresh(sm, tr, &flat, "needed");
    let added = fresh(sm, tr, &flat, "added");
    let raw = fresh(sm, tr, &flat, "raw");
    let rest = fresh(sm, tr, &flat, "rest");
    let actual_key = fresh(sm, tr, &flat, "actual_key");
    let actual_value = fresh(sm, tr, &flat, "actual_value");
    let out = fresh(sm, tr, &flat, "output");
    let view = if finite {
        quote! {.to_imap()}
    } else {
        quote! {}
    };
    let mut inputs = Vec::new();
    let mut bounds = Vec::new();
    let mut setup = Vec::new();
    let mut facts = Vec::new();
    let mut returns = Vec::new();
    let mut observation = quote! {self.context.observe()};
    let mut observation_shape = quote! {};
    if let Some(op) = have {
        let value = operand(op)?;
        setup.push(quote! {let #needed:#native=#value;});
        let singleton = matches!(op.elt, MonoidElt::SingletonKV(..));
        let source_type = if singleton {
            quote! {#field_name #types}
        } else {
            quote! {#bulk #types}
        };
        inputs.push(quote! {tracked #input:&#source_type});
        bounds.push(quote! {#input.instance_id()==self.id()});
        if let MonoidElt::SingletonKV(k, Some(v)) = &op.elt {
            bounds.push(quote! {#input.key()==#k&&#input.value()==#v});
            observation = quote! {#input.raw.observe()};
            observation_shape = quote! {assert(#observed.fragment()==Fragment #expr::#factory(<#native>::empty().insert(#input.key(),#input.value())));};
        } else {
            bounds.push(quote! {(#value).submap_of(#input.map())});
            observation = quote! {if #input.has_resource(){#input.borrow_token().observe()}else{self.context.observe()}};
            observation_shape = quote! {if #input.has_resource(){assert(#observed.fragment()==Fragment #expr::#factory(#input.map()));}else{assert(#input.map()==<#native>::empty());assert(#observed.fragment()==Fragment #expr::unit());}};
        }
        let local_membership = if singleton {
            quote! {}
        } else {
            quote! {
                assert(#input.map().dom().contains(#key));
                assert(#needed[#key]==#input.map()[#key]);
                assert((#input.map() #view).contains_key(#key));
                assert((#input.map() #view)[#key]==(#needed #view)[#key]);
            }
        };
        setup.push(quote! {::vstd::prelude::use_type_invariant(#input);});
        facts.push(quote!{
            Fragment #expr::commutative(#before,#observed.fragment());
            Fragment #expr::associative(#observed.fragment(),#before,#outer);
            let #lower=Fragment #expr::op(#before,#outer);
            assert forall|#key:#kt|#[trigger] (#needed #view).contains_key(#key) implies #observed.fragment().#field_name.at(#key)==Some(::vstd::resource::agree::AgreementRA::Agree((#needed #view)[#key])) by{
                assert(#needed.dom().contains(#key));#local_membership
            };
            ::vstd::resource::tsm_collections::persistent_map_have_many_frame(#observed.fragment().#field_name,#lower.#field_name,#pre.#field_name #view,#needed #view);
        });
        if let MonoidElt::SingletonKV(k, Some(v)) = &op.elt {
            facts.push(quote!{assert((#needed #view).contains_key(#k));
                ::vstd::resource::tsm_collections::persistent_map_owned_frame(#observed.fragment().#field_name,#lower.#field_name,#pre.#field_name #view,#k,#v);
                assert(#pre.#field_name.contains_key(#k));assert(#pre.#field_name[#k]==#v);});
        } else {
            facts.push(quote! {
                assert forall|#key:#kt|#[trigger] #needed.dom().contains(#key) implies #pre.#field_name.dom().contains(#key)&&#needed[#key]==#pre.#field_name[#key] by{
                    assert((#needed #view).contains_key(#key));
                    assert((#needed #view).dom().contains(#key));
                    assert((#pre.#field_name #view).dom().contains(#key));
                    assert((#needed #view)[#key]==(#pre.#field_name #view)[#key]);
                    assert(#needed[#key]==(#needed #view)[#key]);
                    assert(#pre.#field_name[#key]==(#pre.#field_name #view)[#key]);
                }
                assert(#needed.submap_of(#pre.#field_name));
            });
        }
    }
    let mut returned_type = quote! {()};
    let mut result = quote! {()};
    if let Some(op) = add {
        let value = operand(op)?;
        setup.push(quote! {let #added:#native=#value;});
        if let MonoidElt::SingletonKV(k, Some(v)) = &op.elt {
            setup.push(quote! {let #actual_key:#kt=#k;let #actual_value:#vt=#v;});
            returned_type = quote! {#field_name #types};
            returns.push(quote! {#out.instance_id()==self.id(),#out.key()==#k,#out.value()==#v});
            result = quote! {<#field_name #types>::__from_token(#raw,#actual_key,#actual_value)};
        } else {
            returned_type = quote! {#bulk #types};
            returns.push(quote! {#out.instance_id()==self.id(),#out.map()==#value});
            result = quote! {<#bulk #types>::__from_token(#raw,#added)};
        }
        result = quote! {
            ::vstd::resource::tsm_collections::persistent_map_join(::vstd::imap::IMap::<#kt,#vt>::empty(),#added #view);
            let tracked (#raw,#rest)=Protocol #expr::#take(#next);
            ::vstd::resource::tsm_collections::Pointwise::extensionality(#raw.fragment().#field_name,Fragment #expr::#factory(#added).#field_name);
            assert(#raw.fragment()==Fragment #expr::#factory(#added));#result
        };
    }
    let requirements = &flat.requirements;
    let assertions = &flat.assertions;
    Ok(quote! {
        pub proof fn #name(tracked &self,#(#params,)*#(#inputs),*)->(tracked #out:#returned_type)
        requires #(#bounds,)*#(#requirements,)*
        ensures #(#returns,)*#(#assertions,)*
        {
            broadcast use {::vstd::map::group_map_lemmas,::vstd::imap::group_imap_lemmas};
            ::vstd::prelude::use_type_invariant(self);#(#setup)*
            Fragment #expr::op_unit(Fragment #expr::unit());
            assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());
            let tracked #owned=self.context.duplicate();let #before=#owned.fragment();let tracked #observed=#observation;#observation_shape
            assert(Protocol #expr::#req(#before,#observed.fragment(),#(#args),*)) by{
                assert forall|#outer:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#observed.fragment(),#(#args),*) by{#(#facts)*}
            }
            let tracked #next=Protocol #expr::#adapter(#owned,&#observed,#(#args),*);
            let (#outer,#pre,#post)=choose|#outer:Fragment #types,#pre:State #types,#post:State #types|
                #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                &&State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()
                &&#next.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
                &&Fragment #expr::op(Fragment #expr::op(#next.fragment(),#observed.fragment()),#outer)==Protocol #expr::embed(#post);
            #result
        }
    })
}
