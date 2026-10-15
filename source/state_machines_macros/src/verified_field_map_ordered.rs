//! Ordered logical map replacements consume an actual present entry and observe a separate actual entry.
use crate::ast::*;
use crate::verified_field_logical::{generics, Generics};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};
#[derive(Default)]
struct Flat {
    ops: Vec<(Ident, SpecialOp)>,
    require: Vec<Expr>,
    assertions: Vec<Expr>,
}
fn collect(stmt: &TransitionStmt, out: &mut Flat) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                collect(child, out)?;
            }
        }
        TransitionStmt::Require(_, e) => out.require.push(e.clone()),
        TransitionStmt::Assert(_, e, _) => out.assertions.push(e.clone()),
        TransitionStmt::Split(_, kind, children) => {
            let SplitKind::Special(field, op, _, None) = &**kind else {
                return Err(Error::new(
                    *stmt.get_span(),
                    "ordered map facade requires unbound straight-line operations",
                ));
            };
            out.ops.push((field.clone(), op.clone()));
            for child in children {
                collect(child, out)?;
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "ordered map facade supports singleton replacement only",
            ))
        }
    }
    Ok(())
}
pub fn supports(sm: &SM, tr: &Transition) -> bool {
    if sm.fields.len() != 1
        || !matches!(
            sm.fields[0].stype,
            ShardableType::Map(..) | ShardableType::IMap(..)
        )
    {
        return false;
    }
    fn modifies(stmt: &TransitionStmt) -> bool {
        match stmt {
            TransitionStmt::Block(_, children) => children.iter().any(modifies),
            TransitionStmt::Split(_, kind, children) => {
                matches!(&**kind, SplitKind::Special(_, op, _, _) if op.is_remove() || op.is_add())
                    || children.iter().any(modifies)
            }
            _ => false,
        }
    }
    modifies(&tr.body)
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
    for e in flat.require.iter().chain(&flat.assertions) {
        reserve(quote! {#e}, &mut names);
    }
    for (_, op) in &flat.ops {
        match &op.elt {
            MonoidElt::General(e) => reserve(quote! {#e}, &mut names),
            MonoidElt::SingletonKV(k, Some(v)) => {
                reserve(quote! {#k}, &mut names);
                reserve(quote! {#v}, &mut names);
            }
            _ => {}
        }
    }
    let mut name = format!("__tsm_native_map_ordered_{label}");
    while names.contains(&name) {
        name.push('_');
    }
    Ident::new(&name, Span::mixed_site())
}
pub fn method(sm: &SM, tr: &Transition) -> Result<TokenStream, Error> {
    let mut flat = Flat::default();
    collect(&tr.body, &mut flat)?;
    if flat.ops.len() != 2 && flat.ops.len() != 3 {
        return Err(Error::new(
            tr.name.span(),
            "ordered map facade needs remove followed by add",
        ));
    }
    let (field_name, remove) = &flat.ops[0];
    let (add_name, add) = flat.ops.last().unwrap();
    if field_name != add_name || !remove.is_remove() || !add.is_add() {
        return Err(Error::new(
            tr.name.span(),
            "ordered map facade needs one current entry replaced on the same field",
        ));
    }
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let check = |e: &Expr| -> Result<(), Error> {
        let mut e = e.clone();
        let mut errors = vec![];
        crate::field_access_visitor::visit_field_accesses(
            &mut e,
            |errors, f, _| {
                errors.push(Error::new(
                    f.name.span(),
                    "ordered map facade requires explicit native operands and assertions",
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
    for e in flat.require.iter().chain(&flat.assertions) {
        check(e)?;
    }
    for (_, op) in &flat.ops {
        if let MonoidElt::SingletonKV(k, Some(v)) = &op.elt {
            check(k)?;
            check(v)?;
        }
    }
    let field = sm.fields.iter().find(|f| f.name == *field_name).unwrap();
    let (key_ty, value_ty, finite) = match &field.stype {
        ShardableType::Map(k, v) => (k, v, true),
        ShardableType::IMap(k, v) => (k, v, false),
        _ => {
            return Err(Error::new(
                field_name.span(),
                "ordered map facade supports exclusive maps",
            ))
        }
    };
    let (old_key, old_value) = match &remove.elt {
        crate::ast::MonoidElt::SingletonKV(k, Some(v)) => (k, v),
        _ => {
            return Err(Error::new(
                field_name.span(),
                "ordered map facade requires an explicit removed entry",
            ))
        }
    };
    let (new_key, new_value) = match &add.elt {
        crate::ast::MonoidElt::SingletonKV(k, Some(v)) => (k, v),
        _ => {
            return Err(Error::new(
                field_name.span(),
                "ordered map facade requires an explicit added entry",
            ))
        }
    };
    let mut have_signature = quote! {};
    let mut have_requires = quote! {};
    let mut have_setup = quote! {};
    let mut have_facts = quote! {};
    let have_input = fresh(sm, tr, &flat, "have_entry");
    let observation = if flat.ops.len() == 3 {
        let (have_field, have) = &flat.ops[1];
        if have_field != field_name || !have.is_have() {
            return Err(Error::new(
                tr.name.span(),
                "ordered map facade permits Remove, optional Have, then Add on one field",
            ));
        }
        let (hk, hv) = match &have.elt {
            MonoidElt::SingletonKV(k, Some(v)) => (k, v),
            _ => {
                return Err(Error::new(
                    tr.name.span(),
                    "ordered map facade needs an explicit singleton Have",
                ))
            }
        };
        let Generics { types, .. } = generics(sm);
        have_signature = quote! {,tracked #have_input:&#field_name #types};
        have_requires = quote! {#have_input.instance_id()==self.id(),#have_input.key()==#hk,#have_input.value()==#hv,};
        have_setup = quote! {::vstd::prelude::use_type_invariant(#have_input);};
        quote! {#have_input.raw.observe()}
    } else {
        quote! {self.context.observe()}
    };
    let Generics { types, expr, .. } = generics(sm);
    let field_ty = field.get_type();
    let input = fresh(sm, tr, &flat, "replace_entry");
    let old_k = fresh(sm, tr, &flat, "replace_old_key");
    let old_v = fresh(sm, tr, &flat, "replace_old_value");
    let new_k = fresh(sm, tr, &flat, "replace_new_key");
    let new_v = fresh(sm, tr, &flat, "replace_new_value");
    let owned = fresh(sm, tr, &flat, "replace_owned");
    let observed = fresh(sm, tr, &flat, "replace_observed");
    let before = fresh(sm, tr, &flat, "replace_before");
    let next = fresh(sm, tr, &flat, "replace_next");
    let outer = fresh(sm, tr, &flat, "replace_outer");
    let pre = fresh(sm, tr, &flat, "replace_pre");
    let post = fresh(sm, tr, &flat, "replace_post");
    let raw = fresh(sm, tr, &flat, "replace_raw");
    let rest = fresh(sm, tr, &flat, "replace_rest");
    let removed = fresh(sm, tr, &flat, "removed");
    let cleared = fresh(sm, tr, &flat, "cleared");
    let native_new = fresh(sm, tr, &flat, "native_new");
    let scan_key = fresh(sm, tr, &flat, "scan_key");
    let out = fresh(sm, tr, &flat, "output");
    let name = &tr.name;
    let req = format_ident!("{}_requires", name);
    let enabled = format_ident!("{}_enabled", name);
    let owners = format_ident!("{}_owners_enabled", name);
    let strong = format_ident!("{}_strong", name);
    let owned_post = format_ident!("{}_owned_post", name);
    let adapter = format_ident!("__field_{}_with_observation", name);
    let take = format_ident!("take_{}", field_name);
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
    let group = if finite {
        quote! {.to_imap()}
    } else {
        quote! {}
    };
    if flat.ops.len() == 3 {
        let (_, have) = &flat.ops[1];
        let MonoidElt::SingletonKV(hk, Some(hv)) = &have.elt else {
            unreachable!()
        };
        have_facts = quote! {
            assert(#before.#field_name.at(#old_k)==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(#old_v)));
            assert(Fragment #expr::op(#observed.fragment(),#outer).#field_name.at(#old_k)==None);
            assert(#observed.fragment().#field_name.at(#hk)==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(#hv)));
            assert(#old_k!=#hk);
            Fragment #expr::commutative(#before,#observed.fragment());
            Fragment #expr::associative(#observed.fragment(),#before,#outer);
            ::vstd::resource::tsm_collections::map_owned_frame(#observed.fragment().#field_name,Fragment #expr::op(#before,#outer).#field_name,#pre.#field_name #group,#hk,#hv);
            assert(#pre.#field_name.remove(#old_k).contains_key(#hk));
            assert(#pre.#field_name.remove(#old_k)[#hk]==#hv);
        };
    }
    let requirement = &flat.require;
    let assertions = &flat.assertions;
    Ok(quote! {
        pub proof fn #name(tracked &self,#(#params,)*tracked #input:#field_name #types #have_signature)->(tracked #out:#field_name #types)
            requires #input.instance_id()==self.id(),#input.key()==#old_key,#input.value()==#old_value,#have_requires #(#requirement,)*
            ensures #out.instance_id()==self.id(),#out.key()==#new_key,#out.value()==#new_value,#(#assertions,)*
        {
            broadcast use ::vstd::imap::group_imap_lemmas;
            broadcast use ::vstd::iset::group_iset_lemmas;
            broadcast use ::vstd::map::group_map_lemmas;
            broadcast use ::vstd::set::group_set_lemmas;
            Fragment #expr::op_unit(Fragment #expr::unit());
            ::vstd::prelude::use_type_invariant(self);::vstd::prelude::use_type_invariant(&#input);#have_setup
            let #old_k:#key_ty=#old_key;let #old_v:#value_ty=#old_value;let #new_k:#key_ty=#new_key;let #new_v:#value_ty=#new_value;
            assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());
            let tracked #owned=self.context.duplicate().join(#input.raw);
            let #before=#owned.fragment();let tracked #observed=#observation;
            assert(Protocol #expr::#req(#before,#observed.fragment(),#(#args),*)) by {
                assert forall|#outer:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#observed.fragment(),#(#args),*) by {
                    Fragment #expr::associative(#before,#observed.fragment(),#outer);
                    ::vstd::resource::tsm_collections::map_owned_frame(#before.#field_name,
                        Fragment #expr::op(#observed.fragment(),#outer).#field_name,#pre.#field_name #group,#old_k,#old_v);#have_facts
                }
            }
            let tracked #next=Protocol #expr::#adapter(#owned,&#observed,#(#args),*);
            let (#outer,#pre,#post)=choose|#outer:Fragment #types,#pre:State #types,#post:State #types|
                #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                &&State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()
                &&#next.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
                &&Fragment #expr::op(Fragment #expr::op(#next.fragment(),#observed.fragment()),#outer)==Protocol #expr::embed(#post);
            let #removed=<#field_ty>::empty().insert(#old_k,#old_v) #group;
            assert(::vstd::prelude::ext_equal(#removed,::vstd::imap::IMap::empty().insert(#old_k,#old_v)));
            let #cleared=::vstd::resource::tsm_collections::map_remove_many(#before.#field_name,#removed.dom());
            assert forall|#scan_key:#key_ty|#[trigger] #cleared.at(#scan_key)==::vstd::resource::tsm_collections::MapFragment::unit().at(#scan_key) by {};
            ::vstd::resource::tsm_collections::MapFragment::extensionality(#cleared,::vstd::resource::tsm_collections::MapFragment::unit());
            let #native_new=<#field_ty>::empty().insert(#new_k,#new_v);
            assert(::vstd::prelude::ext_equal(#native_new #group,::vstd::imap::IMap::empty().insert(#new_k,#new_v)));
            ::vstd::resource::tsm_collections::MapFragment::op_unit(::vstd::resource::tsm_collections::map_frag(#native_new #group));
            ::vstd::resource::tsm_collections::MapFragment::commutative(::vstd::resource::tsm_collections::MapFragment::unit(),::vstd::resource::tsm_collections::map_frag(#native_new #group));
            let tracked (#raw,#rest)=Protocol #expr::#take(#next);
            <#field_name #types>::__from_token(#raw,#new_k,#new_v)
        }
    })
}
