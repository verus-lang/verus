//! Checked native persistent set observations and actual idempotent additions.
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
                    "set facade requires unbound straight-line operations",
                ));
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "set facade currently supports one explicit Add or Have",
            ))
        }
    }
    Ok(())
}
pub fn supports(sm: &SM, _tr: &Transition) -> bool {
    sm.fields.len() == 1
        && matches!(
            sm.fields[0].stype,
            ShardableType::PersistentSet(_) | ShardableType::PersistentISet(_)
        )
}
fn fresh(sm: &SM, tr: &Transition, flat: &Flat, label: &str) -> Ident {
    let mut names: HashSet<String> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .collect();
    fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
        for token in tokens {
            match token {
                TokenTree::Ident(id) => {
                    names.insert(id.to_string());
                }
                TokenTree::Group(group) => reserve(group.stream(), names),
                _ => {}
            }
        }
    }
    for e in flat.requirements.iter().chain(&flat.assertions) {
        reserve(quote! {#e}, &mut names);
    }
    for (_, op) in &flat.operations {
        match &op.elt {
            MonoidElt::General(e) | MonoidElt::SingletonSet(e) => reserve(quote! {#e}, &mut names),
            _ => {}
        }
    }
    let mut name = format!("__tsm_native_set_{label}");
    while names.contains(&name) {
        name.push('_');
    }
    Ident::new(&name, Span::mixed_site())
}
pub fn method(sm: &SM, tr: &Transition) -> Result<TokenStream, Error> {
    let mut flat = Flat::default();
    collect(&tr.body, &mut flat)?;
    if flat.operations.len() != 1 {
        return Err(Error::new(
            tr.name.span(),
            "set facade requires one supplied set operation",
        ));
    }
    let (field_name, op) = &flat.operations[0];
    let field = sm.fields.iter().find(|f| f.name == *field_name).unwrap();
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
                    "set facade requires explicit native operands and assertions",
                ))
            },
            &mut errors,
            &fields,
        );
        if let Some(error) = errors.into_iter().next() {
            Err(error)
        } else {
            Ok(())
        }
    };
    for e in flat.requirements.iter().chain(&flat.assertions) {
        check(e)?;
    }
    let native = field.get_type();
    let (key_type, finite) = match &field.stype {
        ShardableType::PersistentSet(k) => (k, true),
        ShardableType::PersistentISet(k) => (k, false),
        _ => unreachable!(),
    };
    let (operand, singleton) = match &op.elt {
        MonoidElt::SingletonSet(e) => {
            check(e)?;
            (quote! {<#native>::empty().insert(#e)}, Some(e))
        }
        MonoidElt::General(e) => {
            check(e)?;
            (quote! {#e}, None)
        }
        _ => {
            return Err(Error::new(
                field_name.span(),
                "set facade needs a singleton or native set operand",
            ))
        }
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
    let take = format_ident!("take_{}", field_name);
    let factory = format_ident!("field_{}", field_name);
    let input = fresh(sm, tr, &flat, "input");
    let value = fresh(sm, tr, &flat, "value");
    let element = fresh(sm, tr, &flat, "element");
    let supplied = fresh(sm, tr, &flat, "supplied");
    let observed = fresh(sm, tr, &flat, "observed");
    let owned = fresh(sm, tr, &flat, "owned");
    let before = fresh(sm, tr, &flat, "before");
    let outer = fresh(sm, tr, &flat, "outer");
    let pre = fresh(sm, tr, &flat, "pre");
    let post = fresh(sm, tr, &flat, "post");
    let lower = fresh(sm, tr, &flat, "lower");
    let next = fresh(sm, tr, &flat, "next");
    let raw = fresh(sm, tr, &flat, "raw");
    let rest = fresh(sm, tr, &flat, "rest");
    let key = fresh(sm, tr, &flat, "key");
    let bulk = format_ident!("{}_collection", field_name);
    let requirement = &flat.requirements;
    let assertions = &flat.assertions;
    let view = if finite {
        quote! {.to_iset()}
    } else {
        quote! {}
    };
    let setup = if let Some(e) = singleton {
        quote! {let #element:#key_type=#e;let #value:#native=<#native>::empty().insert(#element);}
    } else {
        quote! {let #value:#native=#operand;}
    };
    let frame_result = quote! {
        let (#outer,#pre,#post)=choose|#outer:Fragment #types,#pre:State #types,#post:State #types|
          #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
          &&State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()
          &&#next.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
          &&Fragment #expr::op(Fragment #expr::op(#next.fragment(),#observed.fragment()),#outer)==Protocol #expr::embed(#post);
    };
    if op.is_add() {
        let returned = if singleton.is_some() {
            quote! {#field_name #types}
        } else {
            quote! {#bulk #types}
        };
        let out = fresh(sm, tr, &flat, "output");
        let result = if let Some(e) = singleton {
            quote! {#out.element()==#e}
        } else {
            quote! {#out.set()==#operand}
        };
        let construct = if singleton.is_some() {
            quote! {<#field_name #types>::__from_token(#raw,#element)}
        } else {
            quote! {<#bulk #types>::__from_token(#raw,#value)}
        };
        return Ok(quote! {
          pub proof fn #name(tracked &self,#(#params),*)->(tracked #out:#returned)
          requires #(#requirement,)*
          ensures #out.instance_id()==self.id(),#result,#(#assertions,)*
          {
            broadcast use {::vstd::set::group_set_lemmas,::vstd::iset::group_iset_lemmas};
            ::vstd::prelude::use_type_invariant(self);#setup
            Fragment #expr::op_unit(Fragment #expr::unit());
            assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());
            let tracked #owned=self.context.duplicate();let #before=#owned.fragment();let tracked #observed=self.context.observe();
            assert(Protocol #expr::#req(#before,#observed.fragment(),#(#args),*)) by {
              assert forall|#outer:Fragment #types,#pre:State #types|
                #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#observed.fragment(),#(#args),*) by {}
            }
            let tracked #next=Protocol #expr::#adapter(#owned,&#observed,#(#args),*);#frame_result
            ::vstd::resource::tsm_collections::persistent_set_join(::vstd::iset::ISet::<#key_type>::empty(),#value #view);
            let tracked (#raw,#rest)=Protocol #expr::#take(#next);
            ::vstd::resource::tsm_collections::Pointwise::extensionality(#raw.fragment().#field_name,Fragment #expr::#factory(#value).#field_name);
            assert(#raw.fragment()==Fragment #expr::#factory(#value));#construct
          }
        });
    }
    if !op.stmt.is_have() {
        return Err(Error::new(
            tr.name.span(),
            "persistent set facade supports Add or Have only",
        ));
    }
    let input_type = if singleton.is_some() {
        quote! {#field_name #types}
    } else {
        quote! {#bulk #types}
    };
    let capacity = if let Some(e) = singleton {
        quote! {#input.element()==#e}
    } else {
        quote! {(#operand).subset_of(#input.set())}
    };
    let supplied_value = if singleton.is_some() {
        quote! {<#native>::empty().insert(#input.element())}
    } else {
        quote! {#input.set()}
    };
    let observe = if singleton.is_some() {
        quote! {#input.raw.observe()}
    } else {
        quote! {if #input.has_resource(){#input.borrow_token().observe()}else{self.context.observe()}}
    };
    let local_shape = if singleton.is_some() {
        quote! {assert(#supplied==#input.raw.fragment());}
    } else {
        quote! {if #input.has_resource(){assert(#supplied==(#input.raw@)->Some_0.fragment());}else{assert(#input.set()==<#native>::empty());::vstd::resource::tsm_collections::Pointwise::extensionality(#supplied.#field_name,Fragment #expr::unit().#field_name);assert(#supplied==Fragment #expr::unit());}}
    };
    let observed_is_supplied = if singleton.is_some() {
        quote! {assert(#supplied==#observed.fragment());}
    } else {
        quote! {if #input.has_resource(){assert(#supplied==#observed.fragment());}else{assert(#supplied==self.context.fragment());assert(#supplied==#observed.fragment());}}
    };
    Ok(quote! {
      pub proof fn #name(tracked &self,#(#params,)*tracked #input:&#input_type)
      requires #input.instance_id()==self.id(),#capacity,#(#requirement,)*
      ensures #(#assertions,)*
      {
        broadcast use {::vstd::set::group_set_lemmas,::vstd::iset::group_iset_lemmas};
        ::vstd::prelude::use_type_invariant(self);::vstd::prelude::use_type_invariant(#input);#setup
        let #supplied=Fragment #expr::#factory(#supplied_value);#local_shape
        let tracked #observed=#observe;#observed_is_supplied
        Fragment #expr::op_unit(Fragment #expr::unit());
        assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());
        let tracked #owned=self.context.duplicate();let #before=#owned.fragment();
        assert(Protocol #expr::#req(#before,#observed.fragment(),#(#args),*)) by {
          assert forall|#outer:Fragment #types,#pre:State #types|
            #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
            implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#observed.fragment(),#(#args),*) by {
              Fragment #expr::commutative(#before,#supplied);
              Fragment #expr::associative(#supplied,#before,#outer);
              let #lower=Fragment #expr::op(#before,#outer);
              assert(Fragment #expr::op(#supplied,#lower)==Protocol #expr::embed(#pre));
              assert forall|#key:#key_type|(#value #view).contains(#key) implies #[trigger] #supplied.#field_name.at(#key)==Some(::vstd::resource::agree::AgreementRA::Agree(())) by {};
              ::vstd::resource::tsm_collections::persistent_set_have_many_frame(#supplied.#field_name,#lower.#field_name,#pre.#field_name #view,#value #view);
            }
        }
        let tracked #next=Protocol #expr::#adapter(#owned,&#observed,#(#args),*);#frame_result
      }
    })
}
