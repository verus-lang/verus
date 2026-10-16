//! Checked field-token API over the raw protocol, for any machine the raw
//! route accepts. The API (token types, `Instance` methods, their signatures
//! and specifications) is the one the trusted macro generates, taken from
//! `concurrency_tokens::exchange_parts`; every body here is a checked proof
//! that runs the corresponding raw protocol operation.
//!
//! Token values are kept as ghost data of a wrapper around a `StorageToken`
//! whose fragment is exactly that value. `arbitrary()` placeholders own a
//! private exclusive or agreement resource instead; their instance ids live
//! in a disjoint id space (`tsm_instance_id`), so they never match an
//! instance and the token traits stay provable.
use crate::ast::*;
use crate::concurrency_tokens::{exchange_parts, signature_tokens, InoutType, TokenParam};
use crate::parse_token_stream::SMBundle;
use crate::to_token_stream::get_generic_args;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use std::collections::HashMap;
use verus_syn::{Error, Expr, Ident, Type};

fn err<T>(span: Span, msg: &str) -> Result<T, Error> {
    Err(Error::new(span, msg))
}

/// Field kinds with a checked token type.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Map,
    Set,
    Bool,
    PersistentOption,
}

fn kind(f: &Field) -> Option<Kind> {
    match f.stype {
        ShardableType::Map(..) => Some(Kind::Map),
        ShardableType::Set(_) => Some(Kind::Set),
        ShardableType::Bool => Some(Kind::Bool),
        ShardableType::PersistentOption(_) => Some(Kind::PersistentOption),
        _ => None,
    }
}

fn check_fields(sm: &SM) -> Result<(), Error> {
    if sm.generics.is_some() {
        return err(sm.name.span(), "generic field tokens do not yet support machine type parameters");
    }
    if !sm.fields.iter().any(|f| f.stype.is_storage()) {
        return err(sm.name.span(), "generic field tokens currently require a storage field");
    }
    for f in &sm.fields {
        match f.stype {
            ShardableType::NotTokenized(_)
            | ShardableType::StorageMap(..) => {}
            _ if kind(f).is_some() => {}
            _ => {
                return err(
                    f.name.span(),
                    "generic field tokens support map, set, bool, persistent_option, storage_map and not_tokenized fields",
                )
            }
        }
        if ["Instance", "Protocol", "State", "Fragment", "Token", "Unit"]
            .contains(&f.name.to_string().as_str())
        {
            return err(f.name.span(), "field name conflicts with a generated type");
        }
    }
    Ok(())
}

/// Fragment holding exactly one token's value.
fn single_fragment(f: &Field, data: &[TokenStream]) -> TokenStream {
    let factory = format_ident!("field_{}", f.name);
    match kind(f).unwrap() {
        Kind::Map => {
            let (k, v) = (&data[0], &data[1]);
            quote! {Fragment::#factory(::vstd::map::Map::empty().insert(#k, #v))}
        }
        Kind::Set => {
            let e = &data[0];
            quote! {Fragment::#factory(::vstd::set::Set::empty().insert(#e))}
        }
        Kind::Bool => quote! {Fragment::#factory(true)},
        Kind::PersistentOption => {
            let v = &data[0];
            quote! {Fragment::#factory(Some(#v))}
        }
    }
}

/// The ghost data of a token: names and types.
fn token_data(f: &Field) -> Vec<(Ident, Type)> {
    let mk = |n: &str| Ident::new(n, Span::mixed_site());
    match &f.stype {
        ShardableType::Map(k, v) => vec![(mk("__k"), k.clone()), (mk("__v"), v.clone())],
        ShardableType::Set(e) => vec![(mk("__e"), e.clone())],
        ShardableType::Bool => vec![],
        ShardableType::PersistentOption(v) => vec![(mk("__v"), v.clone())],
        _ => unreachable!(),
    }
}

fn token_type(f: &Field) -> TokenStream {
    let n = &f.name;
    let data: Vec<_> = token_data(f).iter().map(|(n, t)| quote! {ghost #n: #t}).collect();
    let fake = if kind(f) == Some(Kind::PersistentOption) {
        let v = &token_data(f)[0].1;
        quote! {::vstd::resource::pcm::Resource<Option<::vstd::resource::agree::AgreementRA<#v>>>}
    } else {
        quote! {::vstd::resource::pcm::Resource<Option<::vstd::resource::exclusive::ExclusiveRA<()>>>}
    };
    let fake_value = if kind(f) == Some(Kind::PersistentOption) {
        let v = &token_data(f)[0].0;
        quote! {Some(::vstd::resource::agree::AgreementRA::Agree(self.#v))}
    } else {
        quote! {Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(()))}
    };
    let fake_new = if kind(f) == Some(Kind::PersistentOption) {
        quote! {
            let v = arbitrary();
            let tracked fake = <#fake>::alloc(Some(::vstd::resource::agree::AgreementRA::Agree(v)));
        }
    } else {
        quote! {
            let tracked fake = <#fake>::alloc(Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(())));
        }
    };
    let names: Vec<_> = token_data(f).iter().map(|(n, _)| n.clone()).collect();
    // Exclusive placeholders all carry the same data, so `agree` holds for them.
    let fake_data = if kind(f) == Some(Kind::PersistentOption) {
        quote! {}
    } else {
        let tys: Vec<_> = token_data(f).iter().map(|(_, t)| t.clone()).collect();
        quote! {#(&& self.#names == ::vstd::prelude::arbitrary::<#tys>())*}
    };
    let self_data: Vec<_> = names.iter().map(|n| quote! {self.#n}).collect();
    let frag = single_fragment(f, &self_data);
    let params: Vec<_> = token_data(f).iter().map(|(n, t)| quote! {#n: #t}).collect();
    let pdata: Vec<_> = names.iter().map(|n| quote! {#n}).collect();
    let pfrag = single_fragment(f, &pdata);
    let arbitrary_fields: Vec<_> = if kind(f) == Some(Kind::PersistentOption) {
        vec![quote! {__v: v}]
    } else {
        names.iter().map(|n| quote! {#n: arbitrary()}).collect()
    };
    let new_fields: Vec<_> = names.iter().map(|n| quote! {#n}).collect();
    let real_loc = quote! {self.raw->Some_0.loc()};
    let fake_loc = quote! {self.fake->Some_0.loc()};
    let instance_id = quote! {
        if self.raw is Some { ::vstd::resource::tsm_instance_id(#real_loc, false) }
        else { ::vstd::resource::tsm_instance_id(#fake_loc, true) }
    };
    let trait_impls = token_traits(f, &instance_id);
    quote! {
        #[allow(non_camel_case_types)]
        pub tracked struct #n {
            tracked raw: Option<Token>,
            tracked fake: Option<#fake>,
            #(#data,)*
        }
        impl #n {
            #[verifier::type_invariant]
            spec fn __wf(self) -> bool {
                (self.raw is Some && self.fake is None && self.raw->Some_0.fragment() == #frag)
                || (self.raw is None && self.fake is Some && self.fake->Some_0.value() == #fake_value #fake_data)
            }
            proof fn __from_raw(tracked raw: Token, #(#params),*) -> (tracked out: Self)
                requires raw.fragment() == #pfrag,
                ensures out.__id() == ::vstd::resource::tsm_instance_id(raw.loc(), false),
                    #(out.#names == #names,)*
            {Self {raw: Some(raw), fake: None, #(#new_fields),*}}
            spec fn __id(&self) -> ::vstd::resource::Loc {#instance_id}
            proof fn __lemma_id(tracked &self, loc: ::vstd::resource::Loc)
                requires self.__id() == ::vstd::resource::tsm_instance_id(loc, false),
                ensures self.raw is Some, self.raw->Some_0.loc() == loc, self.raw->Some_0.fragment() == #frag,
            {
                ::vstd::prelude::use_type_invariant(self);
                if self.fake is Some {
                    ::vstd::resource::tsm_instance_id_injective(#fake_loc, true, loc, false);
                } else {
                    ::vstd::resource::tsm_instance_id_injective(#real_loc, false, loc, false);
                }
            }
            proof fn __into_raw(tracked self, loc: ::vstd::resource::Loc) -> (tracked out: Token)
                requires self.__id() == ::vstd::resource::tsm_instance_id(loc, false),
                ensures out.loc() == loc, out.fragment() == #frag,
            {
                self.__lemma_id(loc);
                let tracked Self {raw, ..} = self;
                raw.tracked_unwrap()
            }
            proof fn __borrow_raw<'a>(tracked &'a self, loc: ::vstd::resource::Loc) -> (tracked out: &'a Token)
                requires self.__id() == ::vstd::resource::tsm_instance_id(loc, false),
                ensures out.loc() == loc, out.fragment() == #frag,
            {
                self.__lemma_id(loc);
                self.raw.tracked_borrow()
            }
            proof fn __arbitrary() -> (tracked s: Self) {
                #fake_new
                Self {raw: None, fake: Some(fake), #(#arbitrary_fields),*}
            }
        }
        #trait_impls
    }
}

/// The vstd token trait implementations of one field token type.
fn token_traits(f: &Field, instance_id: &TokenStream) -> TokenStream {
    let n = &f.name;
    let frag_at = |names: &[TokenStream]| single_fragment(f, names);
    let _ = frag_at;
    // Contradiction from two real tokens of the same exclusive slot.
    let field = &f.name;
    let slot = match kind(f).unwrap() {
        Kind::Map => quote! {mine.__k},
        Kind::Set => quote! {mine.__e},
        _ => quote! {()},
    };
    let real_conflict = match kind(f).unwrap() {
        Kind::Map | Kind::Set => quote! {
            let tracked mut r = raw.tracked_unwrap();
            r.validate_2(other.raw.tracked_borrow());
            let f = Fragment::op(r.fragment(), other.raw->Some_0.fragment());
            assert(f.#field.at(#slot) == Some(::vstd::resource::exclusive::ExclusiveRA::Invalid));
            let (frame, st) = choose|frame: Fragment, st: State|
                st.invariant() && Fragment::op(f, frame) == <Protocol as ::vstd::resource::tsm::Machine>::embed(st);
            assert(Fragment::op(f, frame).#field.at(#slot)
                == <Protocol as ::vstd::resource::tsm::Machine>::embed(st).#field.at(#slot));
            raw = Some(r);
        },
        Kind::Bool => quote! {
            let tracked mut r = raw.tracked_unwrap();
            r.validate_2(other.raw.tracked_borrow());
            let f = Fragment::op(r.fragment(), other.raw->Some_0.fragment());
            let (frame, st) = choose|frame: Fragment, st: State|
                st.invariant() && Fragment::op(f, frame) == <Protocol as ::vstd::resource::tsm::Machine>::embed(st);
            assert(Fragment::op(f, frame).#field == <Protocol as ::vstd::resource::tsm::Machine>::embed(st).#field);
            raw = Some(r);
        },
        Kind::PersistentOption => quote! {},
    };
    let unique_body = |same: TokenStream| {
        quote! {
            let tracked mut mine = Self::__arbitrary();
            ::vstd::modes::tracked_swap(self, &mut mine);
            ::vstd::prelude::use_type_invariant(&mine);
            ::vstd::prelude::use_type_invariant(other);
            let a = if mine.raw is Some { mine.raw->Some_0.loc() } else { mine.fake->Some_0.loc() };
            let b = if other.raw is Some { other.raw->Some_0.loc() } else { other.fake->Some_0.loc() };
            ::vstd::resource::tsm_instance_id_injective(a, mine.fake is Some, b, other.fake is Some);
            let same = mine.__id() == other.__id() && #same;
            let ghost saved = mine;
            let tracked Self {raw, fake, ..} = mine;
            let tracked mut raw = raw;
            let tracked mut fake = fake;
            if same {
                if raw is Some {
                    #real_conflict
                } else {
                    let tracked mut x = fake.tracked_unwrap();
                    x.validate_2(other.fake.tracked_borrow());
                    fake = Some(x);
                }
            }
            let tracked mut back = Self {raw, fake, ..saved};
            ::vstd::modes::tracked_swap(self, &mut back);
        }
    };
    match (&f.stype, kind(f).unwrap()) {
        (ShardableType::Map(k, v), Kind::Map) => {
            let body = unique_body(quote! {mine.__k == other.__k});
            quote! {
                impl ::vstd::tokens::KeyValueToken<#k, #v> for #n {
                    closed spec fn instance_id(&self) -> ::vstd::tokens::InstanceId {#instance_id}
                    closed spec fn key(&self) -> #k {self.__k}
                    closed spec fn value(&self) -> #v {self.__v}
                    proof fn agree(tracked &self, tracked other: &Self) {
                        // Two tokens for one exclusive key cannot both exist.
                        let tracked mut copy = Self::__arbitrary();
                        let _ = copy;
                        ::vstd::prelude::use_type_invariant(self);
                        ::vstd::prelude::use_type_invariant(other);
                        if self.__id() == other.__id() && self.__k == other.__k && self.__v != other.__v {
                            let a = if self.raw is Some { self.raw->Some_0.loc() } else { self.fake->Some_0.loc() };
                            let b = if other.raw is Some { other.raw->Some_0.loc() } else { other.fake->Some_0.loc() };
                            ::vstd::resource::tsm_instance_id_injective(a, self.fake is Some, b, other.fake is Some);
                            if self.raw is Some {
                                let (st, f1, f2) = self.raw.tracked_borrow().compatible_with(other.raw.tracked_borrow());
                                assert(Fragment::op(self.raw->Some_0.fragment(), f1).#field.at(self.__k)
                                    == <Protocol as ::vstd::resource::tsm::Machine>::embed(st).#field.at(self.__k));
                                assert(Fragment::op(other.raw->Some_0.fragment(), f2).#field.at(self.__k)
                                    == <Protocol as ::vstd::resource::tsm::Machine>::embed(st).#field.at(self.__k));
                            }
                        }
                    }
                    proof fn arbitrary() -> (tracked s: Self) {Self::__arbitrary()}
                }
                impl ::vstd::tokens::UniqueKeyValueToken<#k, #v> for #n {
                    proof fn unique(tracked &mut self, tracked other: &Self) {#body}
                }
            }
        }
        (ShardableType::Set(e), Kind::Set) => {
            let body = unique_body(quote! {mine.__e == other.__e});
            quote! {
                impl ::vstd::tokens::ElementToken<#e> for #n {
                    closed spec fn instance_id(&self) -> ::vstd::tokens::InstanceId {#instance_id}
                    closed spec fn element(&self) -> #e {self.__e}
                    proof fn arbitrary() -> (tracked s: Self) {Self::__arbitrary()}
                }
                impl ::vstd::tokens::UniqueElementToken<#e> for #n {
                    proof fn unique(tracked &mut self, tracked other: &Self) {#body}
                }
            }
        }
        (ShardableType::Bool, Kind::Bool) => {
            let body = unique_body(quote! {true});
            quote! {
                impl ::vstd::tokens::SimpleToken for #n {
                    closed spec fn instance_id(&self) -> ::vstd::tokens::InstanceId {#instance_id}
                    proof fn arbitrary() -> (tracked s: Self) {Self::__arbitrary()}
                }
                impl ::vstd::tokens::UniqueSimpleToken for #n {
                    proof fn unique(tracked &mut self, tracked other: &Self) {#body}
                }
            }
        }
        (ShardableType::PersistentOption(v), Kind::PersistentOption) => {
            quote! {
                impl ::vstd::tokens::ValueToken<#v> for #n {
                    closed spec fn instance_id(&self) -> ::vstd::tokens::InstanceId {#instance_id}
                    closed spec fn value(&self) -> #v {self.__v}
                    proof fn agree(tracked &self, tracked other: &Self) {
                        ::vstd::prelude::use_type_invariant(self);
                        ::vstd::prelude::use_type_invariant(other);
                        if self.__id() == other.__id() {
                            let a = if self.raw is Some { self.raw->Some_0.loc() } else { self.fake->Some_0.loc() };
                            let b = if other.raw is Some { other.raw->Some_0.loc() } else { other.fake->Some_0.loc() };
                            ::vstd::resource::tsm_instance_id_injective(a, self.fake is Some, b, other.fake is Some);
                            if self.raw is Some {
                                let (st, f1, f2) = self.raw.tracked_borrow().compatible_with(other.raw.tracked_borrow());
                                assert(Fragment::op(self.raw->Some_0.fragment(), f1).#field
                                    == <Protocol as ::vstd::resource::tsm::Machine>::embed(st).#field);
                                assert(Fragment::op(other.raw->Some_0.fragment(), f2).#field
                                    == <Protocol as ::vstd::resource::tsm::Machine>::embed(st).#field);
                            } else {
                                let tracked j = self.fake.tracked_borrow().join_shared(other.fake.tracked_borrow());
                                j.validate();
                            }
                        }
                    }
                    proof fn arbitrary() -> (tracked s: Self) {Self::__arbitrary()}
                }
            }
        }
        _ => unreachable!(),
    }
}

/// Output of the checked facade.
pub fn output(bundle: &SMBundle) -> Result<TokenStream, Error> {
    let sm = &bundle.sm;
    check_fields(sm)?;
    let _ = get_generic_args;
    let mut items = vec![];
    for f in &sm.fields {
        if kind(f).is_some() {
            items.push(token_type(f));
            items.push(collection_helpers(f));
        }
        // The trusted macro's collection aliases.
        let n = &f.name;
        match &f.stype {
            ShardableType::Map(k, v) => {
                let alias = format_ident!("{}_map", n);
                items.push(quote! {#[allow(non_camel_case_types)] pub type #alias = ::vstd::tokens::MapToken<#k, #v, #n>;});
            }
            ShardableType::Set(e) => {
                let alias = format_ident!("{}_set", n);
                items.push(quote! {#[allow(non_camel_case_types)] pub type #alias = ::vstd::tokens::SetToken<#e, #n>;});
            }
            _ => {}
        }
    }
    items.push(quote! {
        #[allow(non_camel_case_types)]
        pub tracked struct Instance {ghost __loc: ::vstd::resource::Loc}
        impl Instance {
            pub closed spec fn id(&self) -> ::vstd::tokens::InstanceId {
                ::vstd::resource::tsm_instance_id(self.__loc, false)
            }
            pub proof fn clone(tracked &self) -> (tracked s: Self) ensures s == *self {Instance {__loc: self.__loc}}
        }
        /// A unit token: the identity resource of an instance, for operations
        /// that consume no other token.
        pub tracked struct Unit {tracked raw: Token}
        impl Unit {
            #[verifier::type_invariant]
            spec fn __wf(self) -> bool {self.raw.fragment() == Fragment::unit()}
            pub closed spec fn instance_id(&self) -> ::vstd::tokens::InstanceId {
                ::vstd::resource::tsm_instance_id(self.raw.loc(), false)
            }
        }
    });
    let mut unit_fns = vec![];
    for f in &sm.fields {
        if kind(f).is_none() {
            continue;
        }
        let n = &f.name;
        let fname = format_ident!("unit_from_{}", n);
        let fclone = format_ident!("clone_{}", n);
        let (tr_path, observers): (TokenStream, Vec<Ident>) = match &f.stype {
            ShardableType::Map(k, v) => (quote! {::vstd::tokens::KeyValueToken<#k, #v>},
                vec![format_ident!("key"), format_ident!("value")]),
            ShardableType::Set(e) => (quote! {::vstd::tokens::ElementToken<#e>}, vec![format_ident!("element")]),
            ShardableType::PersistentOption(v) => (quote! {::vstd::tokens::ValueToken<#v>}, vec![format_ident!("value")]),
            _ => (quote! {::vstd::tokens::SimpleToken}, vec![]),
        };
        let id_of = quote! {<#n as #tr_path>::instance_id(&*old(t))};
        let same: Vec<_> = observers.iter().map(|o| quote! {
            <#n as #tr_path>::#o(&*final(t)) == <#n as #tr_path>::#o(&*old(t))
        }).collect();
        if kind(f) == Some(Kind::PersistentOption) {
            let v = &token_data(f)[0].1;
            unit_fns.push(quote! {
                /// Duplicate a persistent token, using a unit token of its instance.
                pub proof fn #fclone(tracked &self, tracked t: &#n, tracked u: Unit) -> (tracked out: #n)
                    requires <#n as ::vstd::tokens::ValueToken<#v>>::instance_id(t) == self.id(), u.instance_id() == self.id(),
                    ensures <#n as ::vstd::tokens::ValueToken<#v>>::instance_id(&out) == self.id(),
                        <#n as ::vstd::tokens::ValueToken<#v>>::value(&out) == <#n as ::vstd::tokens::ValueToken<#v>>::value(t),
                {
                    hide(State::invariant);
                    assert(t.__id() == <#n as ::vstd::tokens::ValueToken<#v>>::instance_id(t));
                    t.__lemma_id(self.__loc);
                    ::vstd::prelude::use_type_invariant(&u);
                    ::vstd::resource::tsm_instance_id_injective(u.raw.loc(), false, self.__loc, false);
                    let tracked Unit {raw: unit} = u;
                    let tracked obs = t.raw.tracked_borrow().observe();
                    let f = obs.fragment();
                    f.op_unit();
                    Fragment::unit().op_unit();
                    Fragment::commutative(Fragment::unit(), f);
                    assert(Fragment::op(f, f) == f);
                    let empty = ::vstd::imap::IMap::<__StorageKey, __StorageValue>::empty();
                    assert(::vstd::resource::tsm_storage::frame_exchange::<Protocol>(
                        Fragment::op(Fragment::unit(), f), empty, Fragment::op(f, f), empty)) by {
                        assert forall|frame: Fragment, state: State|
                            <Protocol as ::vstd::resource::tsm::Machine>::invariant(state)
                            && Fragment::op(Fragment::op(Fragment::unit(), f), frame)
                                == <Protocol as ::vstd::resource::tsm::Machine>::embed(state)
                            implies Protocol::storage(state).dom().disjoint(empty.dom())
                                && empty.submap_of(Protocol::storage(state).union_prefer_right(empty))
                                && exists|next: State| <Protocol as ::vstd::resource::tsm::Machine>::invariant(next)
                                    && Fragment::op(Fragment::op(f, f), frame) == <Protocol as ::vstd::resource::tsm::Machine>::embed(next)
                                    && Protocol::storage(next)
                                        == Protocol::storage(state).union_prefer_right(empty).remove_keys(empty.dom()) by {
                            assert(::vstd::prelude::ext_equal(
                                Protocol::storage(state).union_prefer_right(empty).remove_keys(empty.dom()),
                                Protocol::storage(state)));
                        }
                    }
                    let tracked (raw, _w) = unit.exchange_with_observation(&obs,
                        ::vstd::imap::IMap::tracked_empty(), f, ::vstd::imap::IMap::empty());
                    #n::__from_raw(raw, t.__v)
                }
            });
        }
        unit_fns.push(quote! {
            /// Split the unit resource off a token of this instance.
            pub proof fn #fname(tracked &self, tracked t: &mut #n) -> (tracked u: Unit)
                requires #id_of == self.id(),
                ensures <#n as #tr_path>::instance_id(&*final(t)) == self.id(), #(#same,)*
                    u.instance_id() == self.id(),
            {
                let tracked mut mine = #n::__arbitrary();
                ::vstd::modes::tracked_swap(t, &mut mine);
                assert(mine.__id() == <#n as #tr_path>::instance_id(&mine));
                ::vstd::prelude::use_type_invariant(&mine);
                mine.__lemma_id(self.__loc);
                let ghost saved = mine;
                let tracked #n {raw, fake, ..} = mine;
                let tracked raw = raw.tracked_unwrap();
                let f = raw.fragment();
                f.op_unit();
                Fragment::commutative(Fragment::unit(), f);
                let tracked (u, raw) = raw.split(Fragment::unit(), f);
                let tracked mut back = #n {raw: Some(raw), fake, ..saved};
                ::vstd::modes::tracked_swap(t, &mut back);
                Unit {raw: u}
            }
        });
    }
    items.push(quote! {impl Instance {#(#unit_fns)*}});
    let mut methods = vec![];
    let mut errors = vec![];
    for tr in &sm.transitions {
        if tr.kind == TransitionKind::ReadonlyTransition {
            continue;
        }
        match method(bundle, tr) {
            Ok(m) => methods.push(m),
            Err(e) => errors.push(e),
        }
    }
    if let Some(e) = errors.into_iter().reduce(|mut a, b| {
        a.combine(b);
        a
    }) {
        return Err(e);
    }
    items.push(quote! {impl Instance {#(#methods)*}});
    Ok(quote! {#(#items)*})
}

/// Split a bulk token into a tracked map of single-value tokens, and the
/// reverse join, for one map or set field.
fn collection_helpers(f: &Field) -> TokenStream {
    let n = &f.name;
    let factory = format_ident!("field_{}", n);
    let split = format_ident!("__split_{}", n);
    let join = format_ident!("__join_{}", n);
    match &f.stype {
        ShardableType::Map(k, v) => quote! {
            impl #n {
                proof fn #split(tracked raw: Token, m: ::vstd::map::Map<#k, #v>)
                    -> (tracked out: ::vstd::map::Map<#k, #n>)
                    requires raw.fragment() == Fragment::#factory(m),
                    ensures out.dom() == m.dom(),
                        forall|key: #k| ::vstd::prelude::imply(#[trigger] out.dom().contains(key),
                            ::vstd::tokens::KeyValueToken::key(&out[key]) == key
                            && ::vstd::tokens::KeyValueToken::value(&out[key]) == m[key]
                            && ::vstd::tokens::KeyValueToken::instance_id(&out[key])
                                == ::vstd::resource::tsm_instance_id(raw.loc(), false)),
                    decreases m.len(),
                {
                    broadcast use {::vstd::map::group_map_lemmas, ::vstd::set::group_set_lemmas,
                        ::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas};
                    if m.len() == 0 {
                        assert(::vstd::prelude::ext_equal(m.dom(), ::vstd::set::Set::empty()));
                        ::vstd::map::Map::tracked_empty()
                    } else {
                        let key = m.dom().choose();
                        let rest = m.remove(key);
                        let one = Fragment::#factory(::vstd::map::Map::empty().insert(key, m[key]));
                        let others = Fragment::#factory(rest);
                        assert(raw.fragment() == Fragment::op(one, others)) by {
                            Fragment::unit().op_unit();
                            assert forall|kk: #k| #[trigger] raw.fragment().#n.at(kk) == Fragment::op(one, others).#n.at(kk) by {
                                if kk == key {} else {}
                            }
                            ::vstd::resource::tsm_collections::Pointwise::extensionality(
                                raw.fragment().#n, Fragment::op(one, others).#n);
                        }
                        let tracked (a, b) = raw.split(one, others);
                        let tracked mut out = Self::#split(b, rest);
                        out.tracked_insert(key, Self::__from_raw(a, key, m[key]));
                        assert(::vstd::prelude::ext_equal(out.dom(), m.dom()));
                        out
                    }
                }
                proof fn #join(tracked acc: Token, tracked m: ::vstd::map::Map<#k, #n>, loc: ::vstd::resource::Loc)
                    -> (tracked out: Token)
                    requires acc.loc() == loc,
                        forall|key: #k| ::vstd::prelude::imply(#[trigger] m.dom().contains(key),
                            m[key].__id() == ::vstd::resource::tsm_instance_id(loc, false)
                            && ::vstd::tokens::KeyValueToken::key(&m[key]) == key),
                    ensures out.loc() == loc,
                        out.fragment() == Fragment::op(acc.fragment(), Fragment::#factory(
                            ::vstd::map::Map::new(m.dom(), |key: #k| ::vstd::tokens::KeyValueToken::value(&m[key])))),
                    decreases m.len(),
                {
                    broadcast use {::vstd::map::group_map_lemmas, ::vstd::set::group_set_lemmas,
                        ::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas};
                    let all = ::vstd::map::Map::new(m.dom(), |key: #k| ::vstd::tokens::KeyValueToken::value(&m[key]));
                    if m.len() == 0 {
                        Fragment::unit().op_unit();
                        acc.fragment().op_unit();
                        assert(Fragment::#factory(all) == Fragment::unit()) by {
                            assert(::vstd::prelude::ext_equal(all, ::vstd::map::Map::empty()));
                            ::vstd::resource::tsm_collections::Pointwise::extensionality(
                                Fragment::#factory(all).#n, Fragment::unit().#n);
                        }
                        acc
                    } else {
                        let key = m.dom().choose();
                        assert(m.dom().contains(key));
                        assert(m[key].__id() == ::vstd::resource::tsm_instance_id(loc, false));
                        let tracked mut m = m;
                        let ghost m0 = m;
                        let tracked t = m.tracked_remove(key);
                        let v = ::vstd::tokens::KeyValueToken::value(&t);
                        let tracked raw = t.__into_raw(loc);
                        let tracked acc2 = acc.join(raw);
                        let rest = ::vstd::map::Map::new(m.dom(), |key: #k| ::vstd::tokens::KeyValueToken::value(&m[key]));
                        let tracked out = Self::#join(acc2, m, loc);
                        let one = Fragment::#factory(::vstd::map::Map::empty().insert(key, v));
                        Fragment::unit().op_unit();
                        assert(Fragment::op(one, Fragment::#factory(rest)) == Fragment::#factory(all)) by {
                            assert forall|kk: #k| #[trigger] Fragment::op(one, Fragment::#factory(rest)).#n.at(kk)
                                == Fragment::#factory(all).#n.at(kk) by {
                                if kk == key {} else {}
                            }
                            ::vstd::resource::tsm_collections::Pointwise::extensionality(
                                Fragment::op(one, Fragment::#factory(rest)).#n, Fragment::#factory(all).#n);
                        }
                        Fragment::associative(acc.fragment(), one, Fragment::#factory(rest));
                        out
                    }
                }
            }
        },
        ShardableType::Set(e) => quote! {
            impl #n {
                proof fn #split(tracked raw: Token, s: ::vstd::set::Set<#e>)
                    -> (tracked out: ::vstd::map::Map<#e, #n>)
                    requires raw.fragment() == Fragment::#factory(s),
                    ensures out.dom() == s,
                        forall|x: #e| ::vstd::prelude::imply(#[trigger] out.dom().contains(x),
                            ::vstd::tokens::ElementToken::element(&out[x]) == x
                            && ::vstd::tokens::ElementToken::instance_id(&out[x])
                                == ::vstd::resource::tsm_instance_id(raw.loc(), false)),
                    decreases s.len(),
                {
                    broadcast use {::vstd::map::group_map_lemmas, ::vstd::set::group_set_lemmas,
                        ::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas};
                    if s.len() == 0 {
                        assert(::vstd::prelude::ext_equal(s, ::vstd::set::Set::empty()));
                        ::vstd::map::Map::tracked_empty()
                    } else {
                        let x = s.choose();
                        let rest = s.remove(x);
                        let one = Fragment::#factory(::vstd::set::Set::empty().insert(x));
                        let others = Fragment::#factory(rest);
                        assert(raw.fragment() == Fragment::op(one, others)) by {
                            Fragment::unit().op_unit();
                            assert forall|kk: #e| #[trigger] raw.fragment().#n.at(kk) == Fragment::op(one, others).#n.at(kk) by {
                                if kk == x {} else {}
                            }
                            ::vstd::resource::tsm_collections::Pointwise::extensionality(
                                raw.fragment().#n, Fragment::op(one, others).#n);
                        }
                        let tracked (a, b) = raw.split(one, others);
                        let tracked mut out = Self::#split(b, rest);
                        out.tracked_insert(x, Self::__from_raw(a, x));
                        assert(::vstd::prelude::ext_equal(out.dom(), s));
                        out
                    }
                }
                proof fn #join(tracked acc: Token, tracked m: ::vstd::map::Map<#e, #n>, loc: ::vstd::resource::Loc)
                    -> (tracked out: Token)
                    requires acc.loc() == loc,
                        forall|x: #e| ::vstd::prelude::imply(#[trigger] m.dom().contains(x),
                            m[x].__id() == ::vstd::resource::tsm_instance_id(loc, false)
                            && ::vstd::tokens::ElementToken::element(&m[x]) == x),
                    ensures out.loc() == loc,
                        out.fragment() == Fragment::op(acc.fragment(), Fragment::#factory(m.dom())),
                    decreases m.len(),
                {
                    broadcast use {::vstd::map::group_map_lemmas, ::vstd::set::group_set_lemmas,
                        ::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas};
                    if m.len() == 0 {
                        Fragment::unit().op_unit();
                        acc.fragment().op_unit();
                        assert(Fragment::#factory(m.dom()) == Fragment::unit()) by {
                            assert(::vstd::prelude::ext_equal(m.dom(), ::vstd::set::Set::empty()));
                            ::vstd::resource::tsm_collections::Pointwise::extensionality(
                                Fragment::#factory(m.dom()).#n, Fragment::unit().#n);
                        }
                        acc
                    } else {
                        let x = m.dom().choose();
                        assert(m.dom().contains(x));
                        assert(m[x].__id() == ::vstd::resource::tsm_instance_id(loc, false));
                        let all = m.dom();
                        let tracked mut m = m;
                        let tracked t = m.tracked_remove(x);
                        let tracked raw = t.__into_raw(loc);
                        let tracked acc2 = acc.join(raw);
                        let rest = m.dom();
                        let tracked out = Self::#join(acc2, m, loc);
                        let one = Fragment::#factory(::vstd::set::Set::empty().insert(x));
                        Fragment::unit().op_unit();
                        assert(Fragment::op(one, Fragment::#factory(rest)) == Fragment::#factory(all)) by {
                            assert forall|kk: #e| #[trigger] Fragment::op(one, Fragment::#factory(rest)).#n.at(kk)
                                == Fragment::#factory(all).#n.at(kk) by {
                                if kk == x {} else {}
                            }
                            ::vstd::resource::tsm_collections::Pointwise::extensionality(
                                Fragment::op(one, Fragment::#factory(rest)).#n, Fragment::#factory(all).#n);
                        }
                        Fragment::associative(acc.fragment(), one, Fragment::#factory(rest));
                        out
                    }
                }
            }
        },
        _ => {
            let _ = join;
            quote! {}
        }
    }
}


/// The collection frame lemma for one input token with value `vals`.
fn frame_lemma(f: &Field, vals: &[TokenStream], tok: TokenStream, full: TokenStream) -> TokenStream {
    let n = &f.name;
    let c = quote! {::vstd::resource::tsm_collections};
    match kind(f).unwrap() {
        Kind::Map => {
            let (k, v) = (&vals[0], &vals[1]);
            quote! {#c::map_owned_frame((#tok).#n, (#full).#n, pre.#n.to_imap(), #k, #v);}
        }
        Kind::Set => {
            let e = &vals[0];
            quote! {#c::set_owned_frame((#tok).#n, (#full).#n, pre.#n.to_iset(), #e);}
        }
        Kind::Bool => quote! {::vstd::resource::tsm_bool::bool_owned_frame((#tok).#n, (#full).#n, pre.#n);},
        Kind::PersistentOption => {
            let v = &vals[0];
            quote! {#c::persistent_option_owned_frame((#tok).#n, (#full).#n, pre.#n, #v);}
        }
    }
}

/// The included-owned lemma for one input token, given `op(op(tok, rest), z) == embed(pre)`.
fn included_lemma(f: &Field, vals: &[TokenStream], tok: TokenStream, coll: Option<TokenStream>) -> TokenStream {
    let n = &f.name;
    let c = quote! {::vstd::resource::tsm_collections};
    let rest = quote! {__tsm_c.#n};
    let z = quote! {__tsm_z.#n};
    if let Some(observed) = coll {
        return match kind(f).unwrap() {
            Kind::Map => quote! {
                #c::map_included_owned_many((#tok).#n, #rest, #z, pre.#n.to_imap(), (#observed).to_imap());
                assert forall|k| (#observed).dom().contains(k)
                    implies #[trigger] pre.#n.dom().contains(k) && pre.#n[k] == (#observed)[k] by {
                    assert((#observed).to_imap().dom().contains(k));
                    assert((#observed).to_imap().submap_of(pre.#n.to_imap()));
                    assert(pre.#n.to_imap().dom().contains(k));
                    assert(pre.#n.to_imap()[k] == pre.#n[k]);
                    assert((#observed).to_imap()[k] == (#observed)[k]);
                }
                assert((#observed).submap_of(pre.#n));
            },
            _ => quote! {
                #c::set_included_owned_many((#tok).#n, #rest, #z, pre.#n.to_iset(), (#observed).to_iset());
                assert forall|k| (#observed).contains(k) implies #[trigger] pre.#n.contains(k) by {
                    assert((#observed).to_iset().contains(k));
                }
                assert((#observed).subset_of(pre.#n));
            },
        };
    }
    match kind(f).unwrap() {
        Kind::Map => {
            let (k, v) = (&vals[0], &vals[1]);
            quote! {#c::map_included_owned_at((#tok).#n, #rest, #z, pre.#n.to_imap(), #k, #v);}
        }
        Kind::Set => {
            let e = &vals[0];
            quote! {#c::set_included_owned_at((#tok).#n, #rest, #z, pre.#n.to_iset(), #e);}
        }
        Kind::Bool => quote! {::vstd::resource::tsm_bool::bool_included_owned((#tok).#n, #rest, #z, pre.#n);},
        Kind::PersistentOption => {
            let v = &vals[0];
            quote! {#c::persistent_option_included_owned((#tok).#n, #rest, #z, pre.#n, #v);}
        }
    }
}

/// Proofs that every input fragment is included in `op(owned, shared)`.
fn inclusions(owned: &[TokenStream], shared: &[TokenStream], h: &TokenStream, owned_ident: &Ident) -> TokenStream {
    let t = quote! {::vstd::resource::tsm};
    let mut out = vec![];
    let accs: Vec<Ident> = (0..owned.len()).map(|i| format_ident!("__tsm_oacc_{}", i)).collect();
    for (i, o) in owned.iter().enumerate() {
        let a = &accs[i];
        if i == 0 {
            out.push(quote! {let ghost #a = #o;});
        } else {
            let prev = &accs[i - 1];
            out.push(quote! {
                let ghost #a = Fragment::op(#prev, #o);
                #t::fragment_included_op_left::<Protocol>(#prev, #o);
                #t::fragment_included_op_right::<Protocol>(#prev, #o);
            });
        }
    }
    let upper = quote! {Fragment::op(#owned_ident, #h)};
    out.push(quote! {
        #t::fragment_included_op_left::<Protocol>(#owned_ident, #h);
        #t::fragment_included_op_right::<Protocol>(#owned_ident, #h);
    });
    for (i, o) in owned.iter().enumerate() {
        out.push(if i == 0 { quote! {#t::fragment_included_reflexive::<Protocol>(#o);} } else { quote! {} });
        for j in (i + 1)..owned.len() {
            let (b, c) = (&accs[j - 1], &accs[j]);
            out.push(quote! {#t::fragment_included_transitive::<Protocol>(#o, #b, #c);});
        }
        let last = &accs[owned.len() - 1];
        out.push(quote! {#t::fragment_included_transitive::<Protocol>(#o, #last, #upper);});
    }
    let hs: Vec<Ident> = (0..shared.len()).map(|i| format_ident!("__tsm_hacc_{}", i)).collect();
    for (i, s) in shared.iter().enumerate() {
        out.push(if i == 0 { quote! {#t::fragment_included_reflexive::<Protocol>(#s);} } else { quote! {} });
        for j in (i + 1)..shared.len() {
            let (b, c) = (&hs[j - 1], &hs[j]);
            out.push(quote! {#t::fragment_included_transitive::<Protocol>(#s, #b, #c);});
        }
        let last = &hs[shared.len() - 1];
        out.push(quote! {#t::fragment_included_transitive::<Protocol>(#s, #last, #upper);});
    }
    quote! {#(#out)*}
}


/// A consumed token collection: its fragment, frame lemma, and join statement.
/// The API only requires `e <= tokens`, so only the tokens for `e` are joined.
fn collection_input(f: &Field, pname: &Ident, loc: &TokenStream, e: &Expr) -> Result<(TokenStream, TokenStream, TokenStream), Error> {
    let n = &f.name;
    let factory = format_ident!("field_{}", n);
    let join = format_ident!("__join_{}", n);
    let c = quote! {::vstd::resource::tsm_collections};
    match kind(f) {
        Some(Kind::Map) => {
            let frag = quote! {Fragment::#factory(#e)};
            let frame = quote! {#c::map_have_many_frame((#frag).#n, __tsm_full.#n, pre.#n.to_imap(), (#e).to_imap());};
            let st = quote! {
                let tracked mut __tsm_tokens = #pname.into_map();
                let tracked __tsm_sel = __tsm_tokens.tracked_remove_keys((#e).dom());
                assert(::vstd::prelude::ext_equal(::vstd::map::Map::new(__tsm_sel.dom(),
                    |k| ::vstd::tokens::KeyValueToken::value(&__tsm_sel[k])), #e));
                let tracked __tsm_acc = #n::#join(__tsm_acc, __tsm_sel, #loc);
            };
            Ok((frag, frame, st))
        }
        Some(Kind::Set) => {
            let frag = quote! {Fragment::#factory(#e)};
            let frame = quote! {#c::set_have_many_frame((#frag).#n, __tsm_full.#n, pre.#n.to_iset(), (#e).to_iset());};
            let st = quote! {
                let tracked mut __tsm_tokens = #pname.into_map();
                let tracked __tsm_sel = __tsm_tokens.tracked_remove_keys(#e);
                assert(::vstd::prelude::ext_equal(__tsm_sel.dom(), #e));
                let tracked __tsm_acc = #n::#join(__tsm_acc, __tsm_sel, #loc);
            };
            Ok((frag, frame, st))
        }
        _ => err(f.name.span(), "generic field tokens consume map and set token collections only"),
    }
}

/// A borrowed-tokens-only operation: its facts hold in any completion state.
fn read_only_method(
    sm: &SM,
    tr: &Transition,
    parts: &crate::concurrency_tokens::ExchangeParts,
    take_shared: &[(Ident, TokenStream)],
    frames: &[(TokenStream, TokenStream)],
    shared_frags: &[TokenStream],
    ret: TokenStream,
    req: TokenStream,
    ens: TokenStream,
) -> Result<TokenStream, Error> {
    let name = &parts.exch_name;
    let in_params = &parts.in_params;
    let gen = if parts.use_explicit_lifetime { quote! {<'a>} } else { quote! {} };
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let mut early = vec![];
    let mut skipped = false;
    lets(&parts.body, false, &mut early, &mut skipped);
    let mut late = vec![];
    let mut skipped2 = false;
    lets(&parts.body, true, &mut late, &mut skipped2);
    let shared_ident = format_ident!("__tsm_shared", span = Span::mixed_site());
    let mut joins = vec![];
    for (i, (obs, take)) in take_shared.iter().enumerate() {
        let hacc = format_ident!("__tsm_hacc_{}", i);
        joins.push(take.clone());
        if i == 0 {
            joins.push(quote! {let tracked #shared_ident = #obs; let ghost #hacc = #shared_ident.fragment();});
        } else {
            joins.push(quote! {let tracked #shared_ident = #shared_ident.join(&#obs); let ghost #hacc = #shared_ident.fragment();});
        }
    }
    let t = quote! {::vstd::resource::tsm};
    let hs: Vec<Ident> = (0..shared_frags.len()).map(|i| format_ident!("__tsm_hacc_{}", i)).collect();
    let mut incl = vec![];
    for (i, sf) in shared_frags.iter().enumerate() {
        if i == 0 {
            incl.push(quote! {#t::fragment_included_reflexive::<Protocol>(#sf);});
        }
        for j in (i + 1)..shared_frags.len() {
            let (b, c) = (&hs[j - 1], &hs[j]);
            incl.push(quote! {#t::fragment_included_transitive::<Protocol>(#sf, #b, #c);});
        }
    }
    let frames_at: Vec<_> = frames.iter().map(|(frag, lemma)| quote! {{
        let __tsm_full = #t::fragment_included_completion::<Protocol>(#frag, #shared_ident.fragment(), __tsm_z, pre);
        #lemma
    }}).collect();
    let safety = format_ident!("{}_safety", tr.name);
    let nondet: Vec<_> = sm.fields.iter()
        .filter(|f| parts.out_params.iter().any(|o| o.0.to_string() == format!("original_field_{}", f.name)))
        .map(|f| {
            let n = format_ident!("original_field_{}", f.name);
            let fname = &f.name;
            quote! {let #n = pre.#fname;}
        }).collect();
    let ret_vals: Vec<_> = parts.out_params.iter().map(|o| {
        let n = &o.0;
        quote! {Ghost(#n)}
    }).collect();
    let result = match parts.out_params.len() {
        0 => quote! {},
        1 => quote! {#(#ret_vals)*},
        _ => quote! {(#(#ret_vals),*)},
    };
    Ok(quote! {
        #[verifier::spinoff_prover]
        pub proof fn #name #gen (#(#in_params),*) #ret #req #ens {
            hide(State::invariant);
            broadcast use {::vstd::map::group_map_lemmas, ::vstd::set::group_set_lemmas,
                ::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas};
            #(#early)*
            #(#joins)*
            #(#incl)*
            #shared_ident.validate();
            let (__tsm_z, pre) = choose|__tsm_z: Fragment, pre: State| pre.invariant()
                && Fragment::op(#shared_ident.fragment(), __tsm_z) == <Protocol as ::vstd::resource::tsm::Machine>::embed(pre);
            #(#frames_at)*
            State::#safety(pre, #(#pn),*);
            #(#nondet)*
            #(#late)*
            #result
        }
    })
}

struct Param<'a> {
    field: &'a Field,
    p: &'a TokenParam,
}

/// Body statements binding the transition's `let`s and token patterns.
fn lets(s: &TransitionStmt, birds_eye: bool, out: &mut Vec<TokenStream>, skipped: &mut bool) {
    match s {
        TransitionStmt::Block(_, xs) => xs.iter().for_each(|x| lets(x, birds_eye, out, skipped)),
        TransitionStmt::Split(_, k, xs) => {
            if let SplitKind::Let(p, ty, lk, e) = &**k {
                let is_be = *lk == LetKind::BirdsEye;
                let ty = ty.as_ref().map(|t| quote! {: #t});
                // First pass (birds_eye == false): lets before the first birds_eye
                // let. Second pass: the birds_eye lets and everything after them.
                if is_be {
                    *skipped = true;
                }
                if birds_eye == *skipped {
                    out.push(quote! {let #p #ty = #e;});
                }
            }
            xs.iter().for_each(|x| lets(x, birds_eye, out, skipped));
        }
        _ => {}
    }
}

fn method(bundle: &SMBundle, tr: &Transition) -> Result<TokenStream, Error> {
    let sm = &bundle.sm;
    let parts = exchange_parts(bundle, tr, &HashMap::new())?;
    let (ret, req, ens) = signature_tokens(&parts);
    let name = &parts.exch_name;
    let in_params = &parts.in_params;
    let gen = if parts.use_explicit_lifetime { quote! {<'a>} } else { quote! {} };
    let fields: HashMap<_, _> = sm.fields.iter().map(|f| (f.name.to_string(), f)).collect();
    let mut params: Vec<Param> = vec![];
    for f in &sm.fields {
        for p in parts.params.get(&f.name.to_string()).into_iter().flatten() {
            params.push(Param { field: f, p });
        }
    }
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let span = tr.name.span();
    if tr.kind == TransitionKind::Init {
        return init_method(bundle, tr, &parts, &params, ret, req, ens);
    }
    let guard = params.iter().any(|q| q.p.inout_type == InoutType::BorrowOut);
    // Bind the transition's lets (except those depending on birds_eye reads).
    let mut early = vec![];
    let mut skipped = false;
    lets(&parts.body, false, &mut early, &mut skipped);
    let loc = quote! {self.__loc};
    let owned_ident = format_ident!("__tsm_owned", span = Span::mixed_site());
    let shared_ident = format_ident!("__tsm_shared", span = Span::mixed_site());
    let mut take_owned = vec![];
    let mut take_shared = vec![];
    let mut frames: Vec<(TokenStream, TokenStream)> = vec![];
    let mut owned_frags: Vec<TokenStream> = vec![];
    let mut coll_owned: Vec<(TokenStream, TokenStream)> = vec![];
    let mut incl_frames: Vec<(TokenStream, TokenStream)> = vec![];
    let mut shared_frags: Vec<TokenStream> = vec![];
    let mut owned_count = 0usize;
    let mut shared_count = 0usize;
    for q in &params {
        let (pname, f) = (&q.p.name, q.field);
        if f.stype.is_storage() {
            continue;
        }
        let data = token_data(f);
        let vals: Vec<TokenStream> = data
            .iter()
            .map(|(d, _)| quote! {#pname.#d})
            .collect();
        let tok_frag = single_fragment(f, &vals);
        let frame = frame_lemma(f, &vals, quote! {#tok_frag}, quote! {__tsm_full});
        let incl_lemma = included_lemma(f, &vals, quote! {#tok_frag}, None);
        match q.p.inout_type {
            InoutType::In if q.p.is_collection => {
                let Some(MonoidElt::General(e)) = q.p.elt.as_ref() else {
                    return err(f.name.span(), "unsupported consumed collection for generic field tokens");
                };
                let (coll_frag, coll_frame, join) = collection_input(f, pname, &loc, e)?;
                coll_owned.push((join, coll_frag.clone()));
                let observed = quote! {(#e)};
                incl_frames.push((coll_frag.clone(), included_lemma(f, &[], coll_frag.clone(), Some(observed))));
                frames.push((coll_frag, coll_frame));
                owned_count += 1;
            }
            InoutType::In => {
                let raw = format_ident!("__tsm_raw_{}", pname);
                take_owned.push((raw.clone(), quote! {let tracked #raw = #pname.__into_raw(#loc);}));
                owned_frags.push(tok_frag.clone());
                frames.push((tok_frag.clone(), frame));
                incl_frames.push((tok_frag.clone(), incl_lemma));
                owned_count += 1;
            }
            InoutType::BorrowIn => {
                if q.p.is_collection {
                    return err(f.name.span(), "generic field tokens do not yet support borrowed token collections");
                }
                let obs = format_ident!("__tsm_obs_{}", pname);
                take_shared.push((obs.clone(), quote! {let tracked #obs = #pname.__borrow_raw(#loc).observe();}));
                shared_frags.push(tok_frag.clone());
                frames.push((tok_frag.clone(), frame));
                incl_frames.push((tok_frag.clone(), incl_lemma));
                shared_count += 1;
            }
            InoutType::Out | InoutType::BorrowOut => {}
            InoutType::InOut => return err(f.name.span(), "generic field tokens do not yet support variable fields"),
        }
    }
    let _ = (owned_count, shared_count, fields);
    // Read-only operations (only borrowed tokens, no outputs or storage
    // changes) need no exchange: validate the borrowed tokens and reason
    // about a completion state.
    let read_only = take_owned.is_empty() && coll_owned.is_empty() && !guard
        && params.iter().all(|q| q.p.inout_type == InoutType::BorrowIn)
        && parts.out_params.iter().all(|o| matches!(o.2, crate::concurrency_tokens::Mode::Ghost));
    if read_only {
        return read_only_method(sm, tr, &parts, &take_shared, &frames, &shared_frags, ret, req, ens);
    }
    // Without any owned token, the method takes a unit token.
    let mut in_params = in_params.clone();
    let needs_unit = take_owned.is_empty() && !guard;
    if needs_unit {
        in_params.push(quote! {tracked __tsm_unit: Unit});
    }
    let unit_req = if needs_unit { quote! {__tsm_unit.instance_id() == (*self).id(),} } else { quote! {} };
    let req = if needs_unit {
        if req.is_empty() { quote! {requires #unit_req} } else { quote! {#req, #unit_req} }
    } else {
        req
    };
    let mut join_owned = vec![];
    for (_, frag) in &coll_owned {
        owned_frags.push(frag.clone());
    }
    if needs_unit {
        join_owned.push(quote! {
            ::vstd::prelude::use_type_invariant(&__tsm_unit);
            ::vstd::resource::tsm_instance_id_injective(__tsm_unit.raw.loc(), false, #loc, false);
            let tracked Unit {raw: __tsm_acc} = __tsm_unit;
        });
    } else if !guard {
        let mut first = true;
        for (raw, take) in &take_owned {
            join_owned.push(take.clone());
            if first {
                join_owned.push(quote! {let tracked __tsm_acc = #raw;});
                first = false;
            } else {
                join_owned.push(quote! {let tracked __tsm_acc = __tsm_acc.join(#raw);});
            }
        }
    }
    for (join, _) in &coll_owned {
        join_owned.push(join.clone());
    }
    let mut join_shared = vec![];
    let has_shared = !take_shared.is_empty();
    {
        let mut first = true;
        let mut shared_index = 0usize;
        for (obs, take) in &take_shared {
            join_shared.push(take.clone());
            let hacc = format_ident!("__tsm_hacc_{}", shared_index);
            if first {
                join_shared.push(quote! {let tracked #shared_ident = #obs; let ghost #hacc = #shared_ident.fragment();});
                first = false;
            } else {
                join_shared.push(quote! {let tracked #shared_ident = #shared_ident.join(&#obs); let ghost #hacc = #shared_ident.fragment();});
            }
            shared_index += 1;
        }
    }
    // Deposits: storage inputs.
    let mut deposits = vec![];
    let mut deposit_spec = quote! {::vstd::imap::IMap::<__StorageKey, __StorageValue>::empty()};
    let mut withdrawals = vec![];
    let mut guards = vec![];
    for q in &params {
        let f = q.field;
        if !f.stype.is_storage() {
            continue;
        }
        let pname = &q.p.name;
        let fname = &f.name;
        let elt = q.p.elt.as_ref().unwrap();
        match (q.p.inout_type, elt) {
            (InoutType::In, MonoidElt::SingletonKV(k, _)) => {
                deposits.push(quote! {
                    __tsm_deposit.tracked_insert(__StorageKey::#fname(#k), __StorageValue::#fname(#pname));
                });
                deposit_spec = quote! {#deposit_spec.insert(__StorageKey::#fname(#k), __StorageValue::#fname(#pname))};
            }
            (InoutType::In, MonoidElt::General(_)) => {
                let pack = format_ident!("__pack_{}", fname);
                let tag = format_ident!("__tag_{}", fname);
                deposits.push(quote! {
                    let tracked __tsm_packed = __StorageKey::#pack(#pname);
                    __tsm_deposit.tracked_union_prefer_right(__tsm_packed);
                });
                deposit_spec = quote! {#deposit_spec.union_prefer_right(__StorageKey::#tag((#pname).to_imap()))};
            }
            (InoutType::Out, MonoidElt::SingletonKV(k, _)) => withdrawals.push(quote! {
                let tracked #pname = __tsm_withdrawn.tracked_remove(__StorageKey::#fname(#k));
                let tracked #pname = match #pname {__StorageValue::#fname(x) => Some(x), _ => None};
                let tracked #pname = #pname.tracked_unwrap();
            }),
            (InoutType::Out, MonoidElt::General(e)) => {
                let tag = format_ident!("__tag_{}", fname);
                let unpack = format_ident!("__unpack_{}", fname);
                let untag = format_ident!("__untag_{}", fname);
                let tag_finite = format_ident!("__tag_finite_{}", fname);
                withdrawals.push(quote! {
                    let ghost __tsm_whole = __tsm_withdrawn;
                    let tracked __tsm_part = __tsm_withdrawn.tracked_remove_keys(
                        __StorageKey::#tag((#e).to_imap()).dom());
                    assert(::vstd::prelude::ext_equal(__tsm_part, __StorageKey::#tag((#e).to_imap())));
                    assert(::vstd::prelude::ext_equal(__StorageKey::#untag(__tsm_part), (#e).to_imap()));
                    __StorageKey::#tag_finite(#e);
                    let tracked #pname = __StorageKey::#unpack(__tsm_part);
                    assert(#pname.to_imap() == (#e).to_imap());
                    assert forall|k| #pname.dom().contains(k) == #[trigger] (#e).dom().contains(k) by {
                        assert(#pname.to_imap().contains_key(k) == (#e).to_imap().contains_key(k));
                    }
                    assert forall|k| #pname.dom().contains(k) implies #[trigger] #pname[k] == (#e)[k] by {
                        assert(#pname.to_imap()[k] == (#e).to_imap()[k]);
                    }
                    assert(::vstd::prelude::ext_equal(#pname, #e));
                })
            }
            (InoutType::BorrowOut, MonoidElt::SingletonKV(k, _)) => {
                let borrow = format_ident!("__borrow_{}", fname);
                guards.push(quote! {
                    let tracked #pname = __StorageKey::#borrow(__tsm_guard, #k).tracked_unwrap();
                })
            }
            _ => return err(f.name.span(), "unsupported storage operation for generic field tokens"),
        }
    }
    let reqs_name = format_ident!("{}_requires", tr.name);
    let witness = format_ident!("{}_witness", tr.name);
    let frame_fn = format_ident!("{}_frame", tr.name);
    let outputs_fn = format_ident!("{}_outputs", tr.name);
    let enabled = format_ident!("{}_enabled", tr.name);
    let deposited = format_ident!("{}_deposited", tr.name);
    let owners = format_ident!("{}_owners_enabled", tr.name);
    let safety = format_ident!("{}_safety", tr.name);
    let h = if has_shared { quote! {#shared_ident.fragment()} } else { quote! {Fragment::unit()} };
    let h_param = format_ident!("__tsm_h", span = Span::mixed_site());
    let lemmas = quote! {broadcast use {::vstd::map::group_map_lemmas, ::vstd::set::group_set_lemmas,
        ::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas};};
    // Late lets (after birds_eye reads become available from the witness).
    let mut late = vec![];
    let mut skipped2 = false;
    lets(&parts.body, true, &mut late, &mut skipped2);
    let nondet: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| parts.out_params.iter().any(|o| o.0.to_string() == format!("original_field_{}", f.name)))
        .map(|f| {
            let n = format_ident!("original_field_{}", f.name);
            let fname = &f.name;
            quote! {let #n = pre.#fname;}
        })
        .collect();
    let frames_at: Vec<_> = incl_frames.iter().map(|(frag, lemma)| quote! {{
        let __tsm_c = choose|__tsm_c: Fragment| Fragment::op(#frag, __tsm_c) == Fragment::op(#owned_ident, #h);
        assert(Fragment::op(#frag, __tsm_c) == Fragment::op(#owned_ident, #h));
        #lemma
    }}).collect();
    let frames_guard: Vec<_> = frames.iter().map(|(_, lemma)| lemma.clone()).collect();
    // The safety lemma supplies the transition's `assert` facts; its
    // postcondition is the whole strong enabling condition, so only call it
    // when the ensures can depend on an assert.
    fn has_assert(s: &TransitionStmt) -> bool {
        match s {
            TransitionStmt::Block(_, xs) => xs.iter().any(has_assert),
            TransitionStmt::Split(_, _, xs) => xs.iter().any(has_assert),
            TransitionStmt::Assert(..) => true,
            _ => false,
        }
    }
    // Assert facts for the ensures: safety at the witness state, plus the
    // frame facts linking that state to the input tokens.
    let safety_after = if has_assert(&tr.body) {
        quote! {
            {
                #(#frames_at)*
            }
            State::#safety(pre, #(#pn),*);
        }
    } else {
        quote! {}
    };
    let incl = inclusions(&owned_frags, &shared_frags, &h, &owned_ident);
    if guard {
        let guarded = format_ident!("{}_guarded", tr.name);
        let (single, take) = match (take_shared.len(), take_owned.len()) {
            (1, 0) => (take_shared[0].0.clone(), take_shared[0].1.clone()),
            _ => return err(span, "generic field tokens support guards with exactly one borrowed token"),
        };
        let ret_vals: Vec<_> = parts.out_params.iter().map(|o| {
            let n = &o.0;
            quote! {#n}
        }).collect();
        let result = if ret_vals.len() == 1 { quote! {#(#ret_vals)*} } else {
            return err(span, "generic field tokens support guards with one output");
        };
        return Ok(quote! {
            #[verifier::spinoff_prover]
            pub proof fn #name #gen (#(#in_params),*) #ret #req #ens {
                #lemmas
                #(#early)*
                #take
                let __tsm_f = #single.fragment();
                assert(Protocol::#reqs_name(__tsm_f, #(#pn),*)) by {
                    assert forall|__tsm_z: Fragment, pre: State| pre.invariant()
                        && Fragment::op(__tsm_f, __tsm_z) == <Protocol as ::vstd::resource::tsm::Machine>::embed(pre)
                        implies State::#owners(pre, __tsm_f, Fragment::unit(), #(#pn),*) && State::#enabled(pre, #(#pn),*) by {
                        let __tsm_full = __tsm_z;
                        #(#frames_guard)*
                    }
                }
                Protocol::#frame_fn(__tsm_f, #(#pn),*);
                let tracked __tsm_guard = #single.guard(Protocol::#guarded(__tsm_f, #(#pn),*));
                #(#guards)*
                #result
            }
        });
    }
    let ret_vals: Vec<_> = parts.out_params.iter().map(|o| {
        let n = &o.0;
        match o.2 {
            crate::concurrency_tokens::Mode::Ghost => quote! {Ghost(#n)},
            crate::concurrency_tokens::Mode::Tracked => quote! {Tracked(#n)},
        }
    }).collect();
    let result = match parts.out_params.len() {
        0 => quote! {},
        1 => {
            let n = &parts.out_params[0].0;
            quote! {#n}
        }
        _ => quote! {(#(#ret_vals),*)},
    };
    // Output tokens: split the new fragment.
    let mut outs: Vec<(TokenStream, TokenStream)> = vec![];
    for q in &params {
        let f = q.field;
        if f.stype.is_storage() || q.p.inout_type != InoutType::Out {
            continue;
        }
        let elt = q.p.elt.as_ref().unwrap();
        if q.p.is_collection {
            let MonoidElt::General(e) = elt else {
                return err(f.name.span(), "unsupported collection output for generic field tokens");
            };
            let pname = &q.p.name;
            let ty = format_ident!("{}", f.name);
            let split = format_ident!("__split_{}", f.name);
            let factory = format_ident!("field_{}", f.name);
            let mk = match kind(f).unwrap() {
                Kind::Map => quote! {
                    let tracked #pname = ::vstd::tokens::MapToken::from_map((*self).id(), #ty::#split(__tsm_piece, #e));
                    assert(::vstd::prelude::ext_equal(#pname.map(), #e));
                },
                Kind::Set => quote! {
                    let tracked #pname = ::vstd::tokens::SetToken::from_map((*self).id(), #ty::#split(__tsm_piece, #e));
                    assert(::vstd::prelude::ext_equal(#pname.set(), #e));
                },
                _ => return err(f.name.span(), "unsupported collection output for generic field tokens"),
            };
            outs.push((quote! {Fragment::#factory(#e)}, mk));
            continue;
        }
        let data: Vec<TokenStream> = match (kind(f).unwrap(), elt) {
            (Kind::Map, MonoidElt::SingletonKV(k, Some(v))) => vec![quote! {#k}, quote! {#v}],
            (Kind::Set, MonoidElt::SingletonSet(e)) => vec![quote! {#e}],
            (Kind::Bool, MonoidElt::True) => vec![],
            (Kind::PersistentOption, MonoidElt::OptionSome(Some(v))) => vec![quote! {#v}],
            _ => return err(f.name.span(), "unsupported output element for generic field tokens"),
        };
        let pname = &q.p.name;
        outs.push((single_fragment(f, &data), {
            let fname = &f.name;
            let ty = format_ident!("{}", fname);
            quote! {let tracked #pname = #ty::__from_raw(__tsm_piece, #(#data),*);}
        }));
    }
    let expected = outs.iter().rev().fold(quote! {Fragment::unit()}, |acc, (fr, _)| quote! {Fragment::op(#fr, #acc)});
    let ext: Vec<_> = sm.fields.iter().filter(|f| matches!(kind(f), Some(Kind::Map) | Some(Kind::Set))).map(|f| {
        let n = &f.name;
        quote! {::vstd::resource::tsm_collections::Pointwise::extensionality(__tsm_out_frag.#n, __tsm_expected.#n);}
    }).collect();
    let mut splits = vec![];
    let mut rest = quote! {__tsm_expected};
    for (i, (fr, mk)) in outs.iter().enumerate() {
        let tail = outs[i + 1..].iter().rev().fold(quote! {Fragment::unit()}, |acc, (fr2, _)| quote! {Fragment::op(#fr2, #acc)});
        let _ = &rest;
        splits.push(quote! {
            let tracked (__tsm_piece, __tsm_left) = __tsm_left.split(#fr, #tail);
            #mk
        });
        rest = tail;
    }
    let call = if has_shared {
        quote! {
            Protocol::#frame_fn(#owned_ident, #h, __tsm_deposit, #(#pn),*);
            let __tsm_outputs = ::vstd::iset::ISet::new(|__tsm_pair: (Fragment, ::vstd::imap::IMap<__StorageKey, __StorageValue>)|
                Protocol::#outputs_fn(#owned_ident, #h, __tsm_pair.0, __tsm_deposit, __tsm_pair.1, #(#pn),*));
            let tracked (__tsm_out, __tsm_withdrawn) =
                __tsm_acc.exchange_nondeterministic_with_observation(&#shared_ident, __tsm_deposit, __tsm_outputs);
        }
    } else {
        // The raw protocol operation does the frame and output lifting in its
        // own context.
        let has_deposit = params.iter().any(|q| q.field.stype.is_storage() && q.p.inout_type == InoutType::In);
        let has_withdraw = params.iter().any(|q| q.field.stype.is_storage() && q.p.inout_type == InoutType::Out);
        let dep_arg = if has_deposit { quote! {__tsm_deposit,} } else { quote! {} };
        let raw = &tr.name;
        if has_withdraw {
            quote! {
                #owned_ident.op_unit();
                let tracked (__tsm_out, __tsm_withdrawn) = Protocol::#raw(__tsm_acc, #dep_arg #(#pn),*);
            }
        } else {
            quote! {
                #owned_ident.op_unit();
                let tracked __tsm_out = Protocol::#raw(__tsm_acc, #dep_arg #(#pn),*);
                let tracked __tsm_withdrawn: ::vstd::imap::IMap<__StorageKey, __StorageValue> = ::vstd::imap::IMap::tracked_empty();
            }
        }
    };
    // Spec copies of the inputs, bound before any token is consumed.
    let mut ghost_binds = vec![];
    let mut ghost_args = vec![];
    let mut ghost_params = vec![];
    for q in &params {
        if matches!(q.p.inout_type, InoutType::In | InoutType::BorrowIn) {
            let pname = &q.p.name;
            let gname = format_ident!("__tsm_ghost_{}", pname);
            let ty = &q.p.ty;
            if q.p.inout_type == InoutType::BorrowIn {
                ghost_binds.push(quote! {let ghost #gname = *#pname;});
            } else {
                ghost_binds.push(quote! {let ghost #gname = #pname;});
            }
            ghost_args.push(quote! {#gname});
            ghost_params.push(quote! {#pname: #ty});
        }
    }
    let tparams: Vec<_> = tr.params.iter().map(|p| {
        let (n, t) = (&p.name, &p.ty);
        quote! {#n: #t}
    }).collect();
    let post_fn = format_ident!("__tsm_post_{}", tr.name);
    // Facts about withdrawn storage, for the withdrawal outputs.
    let mut withdraw_facts = vec![];
    for q in &params {
        let f = q.field;
        if !f.stype.is_storage() || q.p.inout_type != InoutType::Out {
            continue;
        }
        let fname = &f.name;
        match q.p.elt.as_ref() {
            Some(MonoidElt::SingletonKV(k, Some(v))) => withdraw_facts.push(quote! {
                __tsm_withdrawn.contains_key(__StorageKey::#fname(#k))
                && __tsm_withdrawn[__StorageKey::#fname(#k)] == __StorageValue::#fname(#v)
            }),
            Some(MonoidElt::General(e)) => {
                let tag = format_ident!("__tag_{}", fname);
                withdraw_facts.push(quote! {
                    __StorageKey::#tag((#e).to_imap()).submap_of(__tsm_withdrawn)
                    && (#e).dom().finite()
                })
            }
            _ => {}
        }
    }
    // Input tokens' data match the transition's elements (as in the API's requires).
    let mut match_conds = vec![];
    for q in &params {
        let f = q.field;
        if f.stype.is_storage() || !matches!(q.p.inout_type, InoutType::In | InoutType::BorrowIn) {
            continue;
        }
        let pname = &q.p.name;
        let Some(elt) = q.p.elt.as_ref() else { continue };
        let cond = match (kind(f), elt, q.p.is_collection) {
            (Some(Kind::Map), MonoidElt::SingletonKV(k, Some(v)), false) => quote! {#pname.__k == #k && #pname.__v == #v},
            (Some(Kind::Map), MonoidElt::SingletonKV(k, None), false) => quote! {#pname.__k == #k},
            (Some(Kind::Set), MonoidElt::SingletonSet(e), false) => quote! {#pname.__e == #e},
            (Some(Kind::PersistentOption), MonoidElt::OptionSome(Some(v)), false) => quote! {#pname.__v == #v},
            _ => continue,
        };
        match_conds.push(quote! {({ #(#early)* #cond })});
    }
    let owned_chain = if owned_frags.is_empty() {
        quote! {Fragment::unit()}
    } else {
        let mut it = owned_frags.iter();
        let first = it.next().unwrap().clone();
        it.fold(first, |acc, o| quote! {Fragment::op(#acc, #o)})
    };
    let incl_reqs: Vec<_> = incl_frames.iter().map(|(frag, _)| quote! {
        ::vstd::resource::tsm::fragment_included::<Protocol>(#frag, Fragment::op(#owned_ident, #h_param))
    }).collect();
    let frames_post: Vec<_> = incl_frames.iter().map(|(frag, lemma)| quote! {{
        let __tsm_c = choose|__tsm_c: Fragment| Fragment::op(#frag, __tsm_c) == Fragment::op(#owned_ident, #h_param);
        assert(Fragment::op(#frag, __tsm_c) == Fragment::op(#owned_ident, #h_param));
        #lemma
    }}).collect();
    let ready_fn = format_ident!("__tsm_ready_{}", tr.name);
    let api_reqs = &parts.reqs;
    let ready = quote! {
        #[verifier::spinoff_prover]
        proof fn #ready_fn(&self, #(#ghost_params,)* #(#tparams,)* #owned_ident: Fragment, #h_param: Fragment,
            __tsm_deposit: ::vstd::imap::IMap<__StorageKey, __StorageValue>)
            requires
                #(#api_reqs,)*
                #owned_ident == #owned_chain,
                #(#incl_reqs,)*
                __tsm_deposit == #deposit_spec,
            ensures Protocol::#reqs_name(#owned_ident, #h_param, __tsm_deposit, #(#pn),*),
        {
            hide(State::invariant);
            #lemmas
            #(#early)*
            assert forall|__tsm_z: Fragment, pre: State| pre.invariant()
                && Fragment::op(Fragment::op(#owned_ident, #h_param), __tsm_z) == <Protocol as ::vstd::resource::tsm::Machine>::embed(pre)
                implies State::#enabled(pre, #(#pn),*)
                    && __tsm_deposit == State::#deposited(pre, #(#pn),*)
                    && State::#owners(pre, #owned_ident, #h_param, #(#pn),*) by {
                #(#frames_post)*
                assert(::vstd::prelude::ext_equal(__tsm_deposit, State::#deposited(pre, #(#pn),*)));
            }
        }
    };
    let helper = quote! {
        #ready
        #[verifier::spinoff_prover]
        proof fn #post_fn(#(#ghost_params,)* #(#tparams,)* #owned_ident: Fragment, #h_param: Fragment,
            __tsm_out_frag: Fragment,
            __tsm_deposit: ::vstd::imap::IMap<__StorageKey, __StorageValue>,
            __tsm_withdrawn: ::vstd::imap::IMap<__StorageKey, __StorageValue>)
            -> (__tsm_r: (State, State, Fragment))
            requires
                Protocol::#outputs_fn(#owned_ident, #h_param, __tsm_out_frag, __tsm_deposit, __tsm_withdrawn, #(#pn),*),
                #owned_ident == #owned_chain,
                #(#incl_reqs,)*
                #(#match_conds,)*
            ensures
                __tsm_r.0.invariant(),
                Fragment::op(Fragment::op(#owned_ident, #h_param), __tsm_r.2)
                    == <Protocol as ::vstd::resource::tsm::Machine>::embed(__tsm_r.0),
                ({
                let pre = __tsm_r.0;
                #(#early)*
                #(#nondet)*
                #(#late)*
                __tsm_out_frag == #expected #(&& #withdraw_facts)*
            }),
        {
            hide(State::invariant);
            #lemmas
            let (pre, post, __tsm_z) = Protocol::#witness(#owned_ident, #h_param, __tsm_out_frag, __tsm_deposit, __tsm_withdrawn, #(#pn),*);
            #(#frames_post)*
            #(#early)*
            #(#nondet)*
            #(#late)*
            let __tsm_expected = #expected;
            assert(__tsm_out_frag == __tsm_expected) by {
                #(#ext)*
            }
            #(assert(#withdraw_facts);)*
            (pre, post, __tsm_z)
        }
    };
    Ok(quote! {
        #helper
        #[verifier::spinoff_prover]
            pub proof fn #name #gen (#(#in_params),*) #ret #req #ens {
            hide(State::invariant);
            #lemmas
            #(#ghost_binds)*
            #(#early)*
            #(#join_owned)*
            #(#join_shared)*
            let #owned_ident = __tsm_acc.fragment();
            #incl
            let tracked mut __tsm_deposit: ::vstd::imap::IMap<__StorageKey, __StorageValue> = ::vstd::imap::IMap::tracked_empty();
            #(#deposits)*
            assert(__tsm_deposit == #deposit_spec);
            self.#ready_fn(#(#ghost_args,)* #(#pn,)* #owned_ident, #h, __tsm_deposit);
            #call
            let (pre, post, __tsm_z) = Self::#post_fn(#(#ghost_args,)* #(#pn,)*
                #owned_ident, #h, __tsm_out.fragment(), __tsm_deposit, __tsm_withdrawn);
            #safety_after
            #(#nondet)*
            #(#late)*
            let __tsm_expected = #expected;
            assert(__tsm_out.fragment() == __tsm_expected);
            let tracked __tsm_left = __tsm_out;
            #(#splits)*
            let tracked mut __tsm_withdrawn = __tsm_withdrawn;
            #(#withdrawals)*
            #result
        }
    })
}

fn init_method(
    bundle: &SMBundle,
    tr: &Transition,
    parts: &crate::concurrency_tokens::ExchangeParts,
    params: &[Param],
    ret: TokenStream,
    req: TokenStream,
    ens: TokenStream,
) -> Result<TokenStream, Error> {
    let sm = &bundle.sm;
    let name = &parts.exch_name;
    let in_params = &parts.in_params;
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let mut early = vec![];
    let mut skipped = false;
    lets(&parts.body, false, &mut early, &mut skipped);
    let mut deposits = vec![];
    for f in &sm.fields {
        if !f.stype.is_storage() {
            continue;
        }
        let fname = &f.name;
        let arg = format_ident!("param_token_{}", fname);
        let pack = format_ident!("__pack_{}", fname);
        deposits.push(quote! {
            let tracked __tsm_packed = __StorageKey::#pack(#arg);
            __tsm_base.tracked_union_prefer_right(__tsm_packed);
        });
    }
    let _ = params;
    let mut takes = vec![];
    let mut outs = vec![];
    for f in &sm.fields {
        let Some(k) = kind(f) else { continue };
        let fname = &f.name;
        let arg = format_ident!("param_token_{}", fname);
        let take = format_ident!("take_{}", fname);
        let split = format_ident!("__split_{}", fname);
        let ty = format_ident!("{}", fname);
        takes.push(quote! {let tracked (__tsm_piece, __tsm_rest) = Protocol::#take(__tsm_rest);});
        let value = format_ident!("__tsm_init_{}", fname);
        let factory = format_ident!("field_{}", fname);
        match k {
            Kind::Map | Kind::Set => {
                let coll = match k {
                    Kind::Map => quote! {::vstd::tokens::MapToken::from_map},
                    _ => quote! {::vstd::tokens::SetToken::from_map},
                };
                outs.push(quote! {
                    let #value = post.#fname;
                    assert(__tsm_piece.fragment() == Fragment::#factory(#value)) by {
                        ::vstd::resource::tsm_collections::Pointwise::extensionality(
                            __tsm_piece.fragment().#fname, Fragment::#factory(#value).#fname);
                    }
                    let tracked #arg = #coll(instance.id(), #ty::#split(__tsm_piece, #value));
                });
            }
            Kind::Bool => outs.push(quote! {
                let tracked #arg = if post.#fname {
                    Some(#ty::__from_raw(__tsm_piece))
                } else {
                    None
                };
            }),
            Kind::PersistentOption => outs.push(quote! {
                let tracked #arg = if post.#fname is Some {
                    Some(#ty::__from_raw(__tsm_piece, post.#fname->Some_0))
                } else {
                    None
                };
            }),
        }
    }
    let ret_vals: Vec<_> = parts.out_params.iter().map(|o| {
        let n = &o.0;
        quote! {Tracked(#n)}
    }).collect();
    let _ = &pn;
    let init_fn = &tr.name;
    let init_strong = format_ident!("{}_strong", tr.name);
    Ok(quote! {
        #[verifier::spinoff_prover]
        pub proof fn #name(#(#in_params),*) #ret #req #ens {
            broadcast use {::vstd::map::group_map_lemmas, ::vstd::set::group_set_lemmas,
                ::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas};
            #(#early)*
            let tracked mut __tsm_base: ::vstd::imap::IMap<__StorageKey, __StorageValue> = ::vstd::imap::IMap::tracked_empty();
            #(#deposits)*
            assert forall|__tsm_s: State| State::#init_strong(__tsm_s, #(#pn),*) implies __tsm_base == __tsm_s.__storage() by {
                assert(::vstd::prelude::ext_equal(__tsm_base, __tsm_s.__storage()));
            }
            let tracked __tsm_all = Protocol::#init_fn(__tsm_base, #(#pn),*);
            let post = choose|post: State| State::#init_fn(post, #(#pn),*) && post.invariant()
                && __tsm_all.fragment() == <Protocol as ::vstd::resource::tsm::Machine>::embed(post);
            let tracked instance = Instance {__loc: __tsm_all.loc()};
            let tracked __tsm_rest = __tsm_all;
            #(#takes #outs)*
            (#(#ret_vals),*)
        }
    })
}

/// Append items to the last `verus! { .. }` block inside the generated module,
/// without re-parsing the module.
pub fn append_tokens(output: TokenStream, api: TokenStream) -> Result<TokenStream, Error> {
    use proc_macro2::{Delimiter, Group, TokenTree};
    fn inside(stream: TokenStream, api: &mut Option<TokenStream>) -> TokenStream {
        let trees: Vec<TokenTree> = stream.into_iter().collect();
        // Find the last `verus ! { .. }` at this level.
        let mut target = None;
        for i in 0..trees.len() {
            if let (TokenTree::Ident(id), Some(TokenTree::Punct(p)), Some(TokenTree::Group(g))) =
                (&trees[i], trees.get(i + 1), trees.get(i + 2))
            {
                if id == "verus" && p.as_char() == '!' && g.delimiter() == Delimiter::Brace {
                    target = Some(i + 2);
                }
            }
        }
        let mut out = vec![];
        for (i, t) in trees.into_iter().enumerate() {
            match t {
                TokenTree::Group(g) if Some(i) == target => {
                    let mut inner = g.stream();
                    inner.extend(api.take().unwrap());
                    let mut ng = Group::new(g.delimiter(), inner);
                    ng.set_span(g.span());
                    out.push(TokenTree::Group(ng));
                }
                TokenTree::Group(g) if target.is_none() && g.delimiter() == Delimiter::Brace && api.is_some() => {
                    let mut ng = Group::new(g.delimiter(), inside(g.stream(), api));
                    ng.set_span(g.span());
                    out.push(TokenTree::Group(ng));
                }
                t => out.push(t),
            }
        }
        out.into_iter().collect()
    }
    let mut api = Some(api);
    let out = inside(output, &mut api);
    if api.is_some() {
        return err(Span::call_site(), "checked field facade: generated verus block not found");
    }
    Ok(out)
}
