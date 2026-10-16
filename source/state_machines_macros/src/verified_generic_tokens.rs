//! Checked field-token API over the raw protocol, for any machine the raw
//! route accepts. The API (token types, `Instance` methods, their signatures
//! and specifications) is the one the trusted macro generates, taken from
//! `concurrency_tokens::exchange_parts`; every body here is a checked proof
//! that runs the corresponding raw protocol operation.
//!
//! Token values are kept as ghost data of a wrapper around a raw `Token`
//! whose fragment is exactly that value. Persistent tokens hold a leaked
//! `&'static` raw token, so (as in the trusted macro) they are `Copy`.
//! `arbitrary()` placeholders own a private resource instead; their instance
//! ids live in a disjoint id space (`tsm_instance_id`), so they never match
//! an instance and the token traits stay provable.
use crate::ast::*;
use crate::concurrency_tokens::{exchange_parts, signature_tokens, ExchangeParts, InoutType, Mode, TokenParam};
use crate::parse_token_stream::SMBundle;
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident, Type};

fn err<T>(span: Span, msg: &str) -> Result<T, Error> {
    Err(Error::new(span, msg))
}

/// Field kinds with a checked token type.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Variable,
    Option,
    PersistentOption,
    Map,
    PersistentMap,
    IMap,
    PersistentIMap,
    Set,
    PersistentSet,
    ISet,
    PersistentISet,
    Multiset,
    Bool,
    PersistentBool,
    Count,
    PersistentCount,
}

impl Kind {
    fn persistent(self) -> bool {
        matches!(
            self,
            Kind::PersistentOption
                | Kind::PersistentMap
                | Kind::PersistentIMap
                | Kind::PersistentSet
                | Kind::PersistentISet
                | Kind::PersistentBool
                | Kind::PersistentCount
        )
    }
    fn unique(self) -> bool {
        matches!(self, Kind::Variable | Kind::Option | Kind::Map | Kind::IMap | Kind::Set | Kind::ISet | Kind::Bool)
    }
    fn map_like(self) -> bool {
        matches!(self, Kind::Map | Kind::PersistentMap | Kind::IMap | Kind::PersistentIMap)
    }
    fn set_like(self) -> bool {
        matches!(self, Kind::Set | Kind::PersistentSet | Kind::ISet | Kind::PersistentISet)
    }
    /// `imap`/`iset` strategies: collections are `IMap`/`ISet` valued.
    fn infinite(self) -> bool {
        matches!(self, Kind::IMap | Kind::PersistentIMap | Kind::ISet | Kind::PersistentISet)
    }
    fn option_like(self) -> bool {
        matches!(self, Kind::Option | Kind::PersistentOption | Kind::Bool | Kind::PersistentBool)
    }
}

fn kind(f: &Field) -> Option<Kind> {
    match f.stype {
        ShardableType::Variable(_) => Some(Kind::Variable),
        ShardableType::Option(_) => Some(Kind::Option),
        ShardableType::PersistentOption(_) => Some(Kind::PersistentOption),
        ShardableType::Map(..) => Some(Kind::Map),
        ShardableType::PersistentMap(..) => Some(Kind::PersistentMap),
        ShardableType::IMap(..) => Some(Kind::IMap),
        ShardableType::PersistentIMap(..) => Some(Kind::PersistentIMap),
        ShardableType::ISet(_) => Some(Kind::ISet),
        ShardableType::PersistentISet(_) => Some(Kind::PersistentISet),
        ShardableType::Set(_) => Some(Kind::Set),
        ShardableType::PersistentSet(_) => Some(Kind::PersistentSet),
        ShardableType::Multiset(_) => Some(Kind::Multiset),
        ShardableType::Bool => Some(Kind::Bool),
        ShardableType::PersistentBool => Some(Kind::PersistentBool),
        ShardableType::Count => Some(Kind::Count),
        ShardableType::PersistentCount => Some(Kind::PersistentCount),
        _ => None,
    }
}

fn check_fields(sm: &SM) -> Result<(), Error> {
    for f in &sm.fields {
        match f.stype {
            ShardableType::NotTokenized(_)
            | ShardableType::Constant(_)
            | ShardableType::StorageMap(..)
            | ShardableType::StorageIMap(..)
            | ShardableType::StorageOption(_) => {}
            _ if kind(f).is_some() => {}
            _ => {
                return err(
                    f.name.span(),
                    "generic field tokens do not yet support imap, iset, persistent_imap and persistent_iset fields",
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

// ---------------------------------------------------------------------------
// Storage layout

#[derive(PartialEq, Eq)]
enum StoreKind {
    None,
    /// `__StorageKey`/`__StorageValue`, tagged by field.
    Carrier,
    /// The storage field's own key and value types (one map field, or
    /// storage options indexed by their position).
    Plain,
}

struct Store {
    kind: StoreKind,
    key: TokenStream,
    val: TokenStream,
    index: HashMap<String, usize>,
}

impl Store {
    fn new(sm: &SM) -> Result<Store, Error> {
        let fields: Vec<&Field> = sm.fields.iter().filter(|f| f.stype.is_storage()).collect();
        if fields.is_empty() {
            return Ok(Store { kind: StoreKind::None, key: quote! {()}, val: quote! {()}, index: HashMap::new() });
        }
        let has_option = fields.iter().any(|f| matches!(f.stype, ShardableType::StorageOption(_)));
        let map_count = fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::StorageMap(..) | ShardableType::StorageIMap(..)))
            .count();
        let mut names: Vec<String> = fields.iter().map(|f| f.name.to_string()).collect();
        names.sort();
        let index: HashMap<String, usize> = names.iter().enumerate().map(|(i, n)| (n.clone(), i)).collect();
        if fields.len() >= 2 && (has_option && map_count > 0 || map_count > 1) {
            if sm.fields.len() == 4
                && sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::Option(_))).count() == 1
                && sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::Map(..) | ShardableType::IMap(..))).count() == 1
                && has_option
                && map_count == 1
            {
                return err(sm.name.span(), "generic field tokens do not support this homogeneous storage layout");
            }
            return Ok(Store {
                kind: StoreKind::Carrier,
                key: quote! {__StorageKey},
                val: quote! {__StorageValue},
                index,
            });
        }
        match &fields[0].stype {
            ShardableType::StorageMap(k, v) | ShardableType::StorageIMap(k, v) => {
                Ok(Store { kind: StoreKind::Plain, key: quote! {#k}, val: quote! {#v}, index })
            }
            ShardableType::StorageOption(v) => Ok(Store { kind: StoreKind::Plain, key: quote! {int}, val: quote! {#v}, index }),
            _ => unreachable!(),
        }
    }
    fn has(&self) -> bool {
        self.kind != StoreKind::None
    }
    fn map_ty(&self) -> TokenStream {
        let (k, v) = (&self.key, &self.val);
        quote! {::vstd::imap::IMap<#k, #v>}
    }
    fn empty(&self) -> TokenStream {
        let (k, v) = (&self.key, &self.val);
        quote! {::vstd::imap::IMap::<#k, #v>::empty()}
    }
    fn option_index(&self, f: &Field) -> TokenStream {
        let lit = verus_syn::LitInt::new(&format!("{}int", self.index[&f.name.to_string()]), f.name.span());
        quote! {#lit}
    }
    /// The storage key of a singleton operand.
    fn key_of(&self, f: &Field, k: Option<&Expr>) -> TokenStream {
        let n = &f.name;
        match (&self.kind, k) {
            (StoreKind::Carrier, Some(k)) => quote! {__StorageKey::#n(#k)},
            (StoreKind::Carrier, None) => quote! {__StorageKey::#n},
            (_, Some(k)) => quote! {#k},
            (_, None) => self.option_index(f),
        }
    }
    fn wrap(&self, f: &Field, v: TokenStream) -> TokenStream {
        let n = &f.name;
        if self.kind == StoreKind::Carrier { quote! {__StorageValue::#n(#v)} } else { v }
    }
    /// Convert a tracked storage value into the field's payload.
    fn unwrap(&self, f: &Field, name: &Ident) -> TokenStream {
        let n = &f.name;
        if self.kind == StoreKind::Carrier {
            quote! {
                let tracked #name = match #name {__StorageValue::#n(x) => Some(x), _ => None};
                let tracked #name = #name.tracked_unwrap();
            }
        } else {
            quote! {}
        }
    }
    /// The storage map of a general operand `e` of field `f`.
    fn tagged(&self, f: &Field, e: &TokenStream) -> TokenStream {
        let n = &f.name;
        match (&self.kind, &f.stype) {
            (StoreKind::Carrier, ShardableType::StorageMap(..)) => {
                let tag = format_ident!("__tag_{}", n);
                quote! {__StorageKey::#tag((#e).to_imap())}
            }
            (StoreKind::Carrier, _) => {
                let tag = format_ident!("__tag_{}", n);
                quote! {__StorageKey::#tag(#e)}
            }
            (_, ShardableType::StorageMap(..)) => quote! {(#e).to_imap()},
            (_, ShardableType::StorageIMap(..)) => quote! {(#e)},
            (_, _) => {
                let i = self.option_index(f);
                let empty = self.empty();
                quote! {(match #e {Some(__tsm_v) => #empty.insert(#i, __tsm_v), None => #empty})}
            }
        }
    }
    /// Statements producing a tracked storage map `__tsm_packed` from the
    /// tracked general operand `p`, equal to `tagged(f, p)`.
    fn pack(&self, f: &Field, p: &TokenStream) -> TokenStream {
        let n = &f.name;
        match (&self.kind, &f.stype) {
            (StoreKind::Carrier, ShardableType::StorageIMap(..)) => {
                // The carrier packs finite maps.
                let pack = format_ident!("__pack_{}", n);
                quote! {
                    assert((#p).dom().finite());
                    let tracked __tsm_finite = ::vstd::resource::tsm_generic::tracked_imap_to_map(#p);
                    let tracked __tsm_packed = __StorageKey::#pack(__tsm_finite);
                }
            }
            (StoreKind::Carrier, _) => {
                let pack = format_ident!("__pack_{}", n);
                quote! {let tracked __tsm_packed = __StorageKey::#pack(#p);}
            }
            (_, ShardableType::StorageMap(..)) => {
                quote! {let tracked __tsm_packed = ::vstd::resource::tsm_generic::tracked_map_to_imap(#p);}
            }
            (_, ShardableType::StorageIMap(..)) => quote! {let tracked __tsm_packed = #p;},
            (_, _) => {
                let i = self.option_index(f);
                let map = self.map_ty();
                quote! {
                    let tracked mut __tsm_packed: #map = ::vstd::imap::IMap::tracked_empty();
                    let tracked __tsm_opt = #p;
                    if __tsm_opt is Some {
                        __tsm_packed.tracked_insert(#i, __tsm_opt.tracked_unwrap());
                    }
                }
            }
        }
    }
    /// Statements withdrawing the general operand `e` of `f` from the tracked
    /// map `__tsm_withdrawn` into `p`.
    fn unpack(&self, f: &Field, p: &Ident, e: &TokenStream) -> TokenStream {
        let n = &f.name;
        let tagged = self.tagged(f, e);
        match (&self.kind, &f.stype) {
            (StoreKind::Carrier, ShardableType::StorageMap(..)) => {
                let unpack = format_ident!("__unpack_{}", n);
                let untag = format_ident!("__untag_{}", n);
                let tag_finite = format_ident!("__tag_finite_{}", n);
                quote! {
                    let tracked __tsm_part = __tsm_withdrawn.tracked_remove_keys(#tagged.dom());
                    assert(::vstd::prelude::ext_equal(__tsm_part, #tagged));
                    assert(::vstd::prelude::ext_equal(__StorageKey::#untag(__tsm_part), (#e).to_imap()));
                    __StorageKey::#tag_finite(#e);
                    let tracked #p = __StorageKey::#unpack(__tsm_part);
                    assert(#p.to_imap() == (#e).to_imap());
                    assert forall|k| #p.dom().contains(k) == #[trigger] (#e).dom().contains(k) by {
                        assert(#p.to_imap().contains_key(k) == (#e).to_imap().contains_key(k));
                    }
                    assert forall|k| #p.dom().contains(k) implies #[trigger] #p[k] == (#e)[k] by {
                        assert(#p.to_imap()[k] == (#e).to_imap()[k]);
                    }
                    assert(::vstd::prelude::ext_equal(#p, #e));
                }
            }
            (StoreKind::Carrier, ShardableType::StorageIMap(..)) => quote! {
                compile_error!("generic field tokens do not support general withdrawals from a tagged storage_imap");
            },
            (StoreKind::Carrier, _) => {
                let unpack = format_ident!("__unpack_{}", n);
                let untag = format_ident!("__untag_{}", n);
                quote! {
                    let tracked __tsm_part = __tsm_withdrawn.tracked_remove_keys(#tagged.dom());
                    assert(::vstd::prelude::ext_equal(__tsm_part, #tagged));
                    assert(__StorageKey::#untag(__tsm_part) == #e);
                    let tracked #p = __StorageKey::#unpack(__tsm_part);
                }
            }
            (_, ShardableType::StorageMap(..)) => quote! {
                let tracked __tsm_part = __tsm_withdrawn.tracked_remove_keys(#tagged.dom());
                assert(::vstd::prelude::ext_equal(__tsm_part, #tagged));
                let tracked #p = ::vstd::resource::tsm_generic::tracked_imap_to_map(__tsm_part);
                assert(::vstd::prelude::ext_equal(#p, #e)) by {
                    assert forall|k| #p.dom().contains(k) == #[trigger] (#e).dom().contains(k) by {
                        assert(#p.to_imap().contains_key(k) == (#e).to_imap().contains_key(k));
                    }
                    assert forall|k| #p.dom().contains(k) implies #[trigger] #p[k] == (#e)[k] by {
                        assert(#p.to_imap()[k] == (#e).to_imap()[k]);
                    }
                }
            },
            (_, ShardableType::StorageIMap(..)) => quote! {
                let tracked #p = __tsm_withdrawn.tracked_remove_keys((#e).dom());
                assert(::vstd::prelude::ext_equal(#p, #e));
            },
            (_, _) => {
                let i = self.option_index(f);
                quote! {
                    let tracked #p = if (#e) is Some {
                        Some(__tsm_withdrawn.tracked_remove(#i))
                    } else {
                        None
                    };
                }
            }
        }
    }
    /// Facts making the general withdrawal of `e` possible.
    fn withdraw_general_fact(&self, f: &Field, e: &TokenStream) -> TokenStream {
        let tagged = self.tagged(f, e);
        match &f.stype {
            ShardableType::StorageMap(..) => quote! {#tagged.submap_of(__tsm_withdrawn) && (#e).dom().finite()},
            _ => quote! {#tagged.submap_of(__tsm_withdrawn)},
        }
    }
}

// ---------------------------------------------------------------------------
// Constants

/// A machine with `constant` fields: the instance and every token hold a
/// shared, leaked descriptor `d` (an agreement resource on the constants and
/// the protocol location), and every token and unit also holds its own copy of
/// the constants' agreement fragment `κ` (its `base`). The descriptor's type
/// involves no protocol type, so it needs no `'static` bound on the machine's
/// type parameters unless a constant's type mentions them.
struct Cm {
    d: TokenStream,
    consts: Vec<Field>,
}

impl Cm {
    fn new(sm: &SM) -> Option<Cm> {
        let consts: Vec<Field> = sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::Constant(_))).cloned().collect();
        if consts.is_empty() {
            return None;
        }
        let tys: Vec<_> = consts
            .iter()
            .map(|c| match &c.stype {
                ShardableType::Constant(t) => quote! {#t},
                _ => unreachable!(),
            })
            .collect();
        let d = quote! {::vstd::resource::pcm::Resource<Option<::vstd::resource::agree::AgreementRA<((#(#tys,)*), ::vstd::resource::Loc)>>>};
        Some(Cm { d, consts })
    }
    fn ok(&self, d: TokenStream) -> TokenStream {
        quote! {((#d).value() is Some && (#d).value()->Some_0 is Agree)}
    }
    fn val(&self, d: TokenStream) -> TokenStream {
        quote! {(#d).value()->Some_0->Agree_0}
    }
    fn ploc(&self, d: TokenStream) -> TokenStream {
        let v = self.val(d);
        quote! {(#v).1}
    }
    fn constant(&self, d: TokenStream, i: usize) -> TokenStream {
        let v = self.val(d);
        let i = verus_syn::Index::from(i);
        quote! {((#v).0).#i}
    }
    /// `κ` for the constants of descriptor `d`.
    fn kappa(&self, d: TokenStream) -> TokenStream {
        let vals: Vec<_> = (0..self.consts.len()).map(|i| self.constant(d.clone(), i)).collect();
        self.kappa_of(&vals)
    }
    fn kappa_of(&self, vals: &[TokenStream]) -> TokenStream {
        self.consts.iter().zip(vals).fold(quote! {Fragment::unit()}, |acc, (c, v)| {
            let w = format_ident!("with_{}", c.name);
            quote! {#acc.#w(#v)}
        })
    }
}

// ---------------------------------------------------------------------------
// Per-kind representation

/// The ghost data of a token: names and types. A `persistent_count` token
/// reports `__n` and owns the (possibly larger) lower bound `__m`.
fn token_data(f: &Field) -> Vec<(Ident, Type)> {
    let mk = |n: &str| Ident::new(n, Span::mixed_site());
    let nat: Type = verus_syn::parse_quote! {::vstd::prelude::nat};
    match &f.stype {
        ShardableType::Variable(t) | ShardableType::Option(t) | ShardableType::PersistentOption(t) => {
            vec![(mk("__v"), t.clone())]
        }
        ShardableType::Map(k, v) | ShardableType::PersistentMap(k, v)
        | ShardableType::IMap(k, v) | ShardableType::PersistentIMap(k, v) => {
            vec![(mk("__k"), k.clone()), (mk("__v"), v.clone())]
        }
        ShardableType::Set(e) | ShardableType::PersistentSet(e) | ShardableType::Multiset(e)
        | ShardableType::ISet(e) | ShardableType::PersistentISet(e) => {
            vec![(mk("__e"), e.clone())]
        }
        ShardableType::Bool | ShardableType::PersistentBool => vec![],
        ShardableType::Count => vec![(mk("__n"), nat)],
        ShardableType::PersistentCount => vec![(mk("__n"), nat.clone()), (mk("__m"), nat)],
        _ => unreachable!(),
    }
}

/// Fragment holding exactly one token's value.
fn single_fragment(f: &Field, data: &[TokenStream]) -> TokenStream {
    let factory = format_ident!("field_{}", f.name);
    let value = match kind(f).unwrap() {
        Kind::Variable | Kind::Count => data[0].clone(),
        Kind::PersistentCount => data[1].clone(),
        Kind::Option | Kind::PersistentOption => {
            let v = &data[0];
            quote! {Some(#v)}
        }
        Kind::Map | Kind::PersistentMap => {
            let (k, v) = (&data[0], &data[1]);
            quote! {::vstd::map::Map::empty().insert(#k, #v)}
        }
        Kind::IMap | Kind::PersistentIMap => {
            let (k, v) = (&data[0], &data[1]);
            quote! {::vstd::imap::IMap::empty().insert(#k, #v)}
        }
        Kind::Set | Kind::PersistentSet => {
            let e = &data[0];
            quote! {::vstd::set::Set::empty().insert(#e)}
        }
        Kind::ISet | Kind::PersistentISet => {
            let e = &data[0];
            quote! {::vstd::iset::ISet::empty().insert(#e)}
        }
        Kind::Multiset => {
            let e = &data[0];
            quote! {::vstd::multiset::Multiset::singleton(#e)}
        }
        Kind::Bool | Kind::PersistentBool => quote! {true},
    };
    quote! {Fragment::#factory(#value)}
}

/// Extra well-formedness of a real token's data.
fn extra_wf(f: &Field, me: &TokenStream) -> TokenStream {
    match kind(f).unwrap() {
        Kind::PersistentCount => quote! {&& #me.__n <= #me.__m},
        _ => quote! {},
    }
}

/// The type of the placeholder resource and its value.
fn fake_parts(f: &Field) -> (TokenStream, TokenStream, TokenStream) {
    let k = kind(f).unwrap();
    let data = token_data(f);
    let pcm = quote! {::vstd::resource::pcm::Resource};
    if k == Kind::Count {
        return (
            quote! {#pcm<::vstd::resource::tsm::CountRA>},
            quote! {::vstd::resource::tsm::CountRA {count: self.__n}},
            quote! {},
        );
    }
    if k.persistent() {
        let (tys, vals): (Vec<_>, Vec<_>) = if k == Kind::PersistentCount {
            (vec![], vec![])
        } else {
            (data.iter().map(|(_, t)| quote! {#t}).collect(), data.iter().map(|(n, _)| quote! {self.#n}).collect())
        };
        return (
            quote! {#pcm<Option<::vstd::resource::agree::AgreementRA<(#(#tys,)*)>>>},
            quote! {Some(::vstd::resource::agree::AgreementRA::Agree((#(#vals,)*)))},
            quote! {},
        );
    }
    let names: Vec<_> = data.iter().map(|(n, _)| n.clone()).collect();
    let tys: Vec<_> = data.iter().map(|(_, t)| t.clone()).collect();
    (
        quote! {#pcm<Option<::vstd::resource::exclusive::ExclusiveRA<()>>>},
        quote! {Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(()))},
        quote! {#(&& self.#names == ::vstd::prelude::arbitrary::<#tys>())*},
    )
}

/// A placeholder for the token type of `f`, resolved to `f` or `f::<args>`
/// once the machine's type parameters are applied (see `genericize`). It
/// keeps the type name apart from user bindings that share the field's name.
fn tyname(f: &Field) -> Ident {
    format_ident!("__TSM_TY_{}", f.name)
}

/// The trait path implemented by a token type (for its observers).
fn trait_path(f: &Field) -> TokenStream {
    match &f.stype {
        ShardableType::Map(k, v) | ShardableType::PersistentMap(k, v)
        | ShardableType::IMap(k, v) | ShardableType::PersistentIMap(k, v) => quote! {::vstd::tokens::KeyValueToken<#k, #v>},
        ShardableType::Set(e) | ShardableType::PersistentSet(e) | ShardableType::Multiset(e)
        | ShardableType::ISet(e) | ShardableType::PersistentISet(e) => {
            quote! {::vstd::tokens::ElementToken<#e>}
        }
        ShardableType::Variable(v) | ShardableType::Option(v) | ShardableType::PersistentOption(v) => {
            quote! {::vstd::tokens::ValueToken<#v>}
        }
        ShardableType::Bool | ShardableType::PersistentBool => quote! {::vstd::tokens::SimpleToken},
        ShardableType::PersistentCount => quote! {::vstd::tokens::MonotonicCountToken},
        ShardableType::Count => quote! {},
        _ => unreachable!(),
    }
}

/// `<t as Trait>::instance_id(&x)` (or the inherent method for counts).
fn id_call(f: &Field, x: TokenStream) -> TokenStream {
    let nt = tyname(f);
    if kind(f) == Some(Kind::Count) {
        quote! {#nt::instance_id(&#x)}
    } else {
        let tr = trait_path(f);
        quote! {<#nt as #tr>::instance_id(&#x)}
    }
}

fn token_type(f: &Field, store: &Store, generic: bool, cm: &Option<Cm>) -> TokenStream {
    let n = &f.name;
    let nt = tyname(f);
    let k = kind(f).unwrap();
    let persistent = k.persistent();
    let data_decl: Vec<_> = token_data(f).iter().map(|(n, t)| quote! {ghost #n: #t}).collect();
    let (fake, fake_value, fake_data) = fake_parts(f);
    let names: Vec<_> = token_data(f).iter().map(|(n, _)| n.clone()).collect();
    let self_data: Vec<_> = names.iter().map(|n| quote! {self.#n}).collect();
    let frag = single_fragment(f, &self_data);
    let params: Vec<_> = token_data(f).iter().map(|(n, t)| quote! {#n: #t}).collect();
    let pdata: Vec<_> = names.iter().map(|n| quote! {#n}).collect();
    let pfrag = single_fragment(f, &pdata);
    let me_extra = extra_wf(f, &quote! {self});
    let p_extra = if k == Kind::PersistentCount {
        let (a, b) = (&names[0], &names[1]);
        quote! {#a <= #b,}
    } else {
        quote! {}
    };
    let raw_ty = if persistent { quote! {&'static Token} } else { quote! {Token} };
    let fake_field = if persistent { quote! {&'static #fake} } else { quote! {#fake} };
    let fake_loc = quote! {self.fake->Some_0.loc()};
    // The location in a real token's instance id: the raw token's, or (with
    // constants) the instance descriptor's.
    let real_idloc = if cm.is_some() { quote! {self.desc->Some_0.loc()} } else { quote! {self.raw->Some_0.loc()} };
    let instance_id = quote! {
        if self.raw is Some { ::vstd::resource::tsm_instance_id(#real_idloc, false) }
        else { ::vstd::resource::tsm_instance_id(#fake_loc, true) }
    };
    // The placeholder's resource and data.
    let (fake_new, arbitrary_fields): (TokenStream, Vec<TokenStream>) = if k == Kind::Count {
        (
            quote! {let tracked fake = ::vstd::resource::pcm::Resource::<::vstd::resource::tsm::CountRA>::alloc(::vstd::resource::tsm::CountRA {count: 0});},
            vec![quote! {__n: 0}],
        )
    } else if persistent {
        let data = token_data(f);
        let ghosts: Vec<_> = data.iter().map(|(n, t)| quote! {let #n: #t = arbitrary();}).collect();
        let vals: Vec<_> = if k == Kind::PersistentCount { vec![] } else { names.iter().map(|n| quote! {#n}).collect() };
        (
            quote! {
                #(#ghosts)*
                let tracked fake = ::vstd::modes::tracked_static_ref(::vstd::resource::pcm::Resource::alloc(
                    Some(::vstd::resource::agree::AgreementRA::Agree((#(#vals,)*)))));
            },
            names.iter().map(|n| if k == Kind::PersistentCount { quote! {#n: 0} } else { quote! {#n: #n} }).collect(),
        )
    } else {
        (
            quote! {
                let tracked fake = ::vstd::resource::pcm::Resource::alloc(Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(())));
            },
            names.iter().map(|n| quote! {#n: arbitrary()}).collect(),
        )
    };
    let wrap = |x: TokenStream| if persistent { quote! {::vstd::modes::tracked_static_ref(#x)} } else { x };
    let wrap_raw = wrap(quote! {raw});
    let unwrap_field = |fld: TokenStream| if persistent { quote! {self.#fld.tracked_unwrap()} } else { quote! {self.#fld.tracked_borrow()} };
    let borrow_raw = unwrap_field(quote! {raw});
    let borrow_fake = unwrap_field(quote! {fake});
    let (derive, copy_impls) = copy_impls(&quote! {#nt}, persistent, generic);
    let clone = if persistent {
        quote! {
            /// Persistent tokens are `Copy`, as in the trusted macro.
            pub proof fn clone(tracked &self) -> (tracked s: Self) ensures s == *self {*self}
        }
    } else {
        quote! {}
    };
    let trait_impls = token_traits(f, &instance_id, store, cm);
    // Mode-dependent parts: without constants a token's link to its instance
    // is the location; with constants, the instance descriptor `d`, and the
    // token also holds its own copy of the constants' fragment (`base`).
    let (link_param, link_req, link_loc, extra_fields, real_extra, fake_extra, from_params, from_reqs, from_id, from_fields, lemma_ens, lemma_body, into_raw, borrow_base, link_body) =
        match cm {
            None => (
                quote! {loc: ::vstd::resource::Loc},
                quote! {self.__id() == ::vstd::resource::tsm_instance_id(loc, false)},
                quote! {loc},
                quote! {},
                quote! {},
                quote! {},
                quote! {},
                quote! {},
                quote! {raw.loc()},
                quote! {},
                quote! {},
                quote! {
                    if self.fake is Some {
                        ::vstd::resource::tsm_instance_id_injective(#fake_loc, true, loc, false);
                    } else {
                        ::vstd::resource::tsm_instance_id_injective(self.raw->Some_0.loc(), false, loc, false);
                    }
                },
                if persistent {
                    quote! {}
                } else {
                    quote! {
                        proof fn __into_raw(tracked self, loc: ::vstd::resource::Loc) -> (tracked out: Token)
                            requires self.__id() == ::vstd::resource::tsm_instance_id(loc, false),
                            ensures out.loc() == loc, out.fragment() == #frag,
                        {
                            self.__lemma_id(loc);
                            let tracked Self {raw, ..} = self;
                            raw.tracked_unwrap()
                        }
                    }
                },
                quote! {},
                quote! {
                    let a = if self.raw is Some { self.raw->Some_0.loc() } else { self.fake->Some_0.loc() };
                    let b = if other.raw is Some { other.raw->Some_0.loc() } else { other.fake->Some_0.loc() };
                    ::vstd::resource::tsm_instance_id_injective(a, self.fake is Some, b, other.fake is Some);
                },
            ),
            Some(cm) => {
                let dty = &cm.d;
                let d_ok = cm.ok(quote! {d});
                let d_ploc = cm.ploc(quote! {d});
                let d_kappa = cm.kappa(quote! {d});
                let s_ok = cm.ok(quote! {self.desc->Some_0});
                let s_ploc = cm.ploc(quote! {self.desc->Some_0});
                let s_kappa = cm.kappa(quote! {self.desc->Some_0});
                let desc_ok = cm.ok(quote! {desc});
                let desc_ploc = cm.ploc(quote! {desc});
                let desc_kappa = cm.kappa(quote! {desc});
                let wrap_base = wrap(quote! {base});
                let borrow_base_body = unwrap_field(quote! {base});
                (
                    quote! {tracked d: &#dty},
                    quote! {self.__id() == ::vstd::resource::tsm_instance_id(d.loc(), false), #d_ok},
                    d_ploc.clone(),
                    quote! {tracked base: Option<#raw_ty>, tracked desc: Option<&'static #dty>,},
                    quote! {&& self.base is Some && self.desc is Some && #s_ok
                        && self.raw->Some_0.loc() == #s_ploc && self.base->Some_0.loc() == #s_ploc
                        && self.base->Some_0.fragment() == #s_kappa},
                    quote! {&& self.base is None && self.desc is None},
                    quote! {tracked base: Token, tracked desc: &'static #dty,},
                    quote! {#desc_ok, raw.loc() == #desc_ploc, base.loc() == #desc_ploc, base.fragment() == #desc_kappa,},
                    quote! {desc.loc()},
                    quote! {base: Some(#wrap_base), desc: Some(desc),},
                    quote! {, self.base is Some, self.base->Some_0.loc() == #d_ploc, self.base->Some_0.fragment() == #d_kappa},
                    quote! {
                        if self.fake is Some {
                            ::vstd::resource::tsm_instance_id_injective(#fake_loc, true, d.loc(), false);
                        } else {
                            ::vstd::resource::tsm_instance_id_injective(self.desc->Some_0.loc(), false, d.loc(), false);
                            ::vstd::resource::tsm_generic::agreement_resources_agree(self.__desc(), d);
                        }
                    },
                    if persistent {
                        quote! {}
                    } else {
                        quote! {
                            proof fn __into_raw(tracked self, tracked d: &#dty) -> (tracked out: (Token, Token))
                                requires self.__id() == ::vstd::resource::tsm_instance_id(d.loc(), false), #d_ok,
                                ensures out.0.loc() == #d_ploc, out.0.fragment() == #frag,
                                    out.1.loc() == #d_ploc, out.1.fragment() == #d_kappa,
                            {
                                self.__lemma_id(d);
                                let tracked Self {raw, base, ..} = self;
                                (raw.tracked_unwrap(), base.tracked_unwrap())
                            }
                        }
                    },
                    quote! {
                        proof fn __desc(tracked &self) -> (tracked out: &'static #dty)
                            requires self.desc is Some,
                            ensures *out == self.desc->Some_0,
                        {self.desc.tracked_unwrap()}
                        proof fn __borrow_base<'a>(tracked &'a self, tracked d: &#dty) -> (tracked out: &'a Token)
                            requires self.__id() == ::vstd::resource::tsm_instance_id(d.loc(), false), #d_ok,
                            ensures out.loc() == #d_ploc, out.fragment() == #d_kappa,
                        {
                            self.__lemma_id(d);
                            #borrow_base_body
                        }
                    },
                    quote! {
                        let a = if self.raw is Some { self.desc->Some_0.loc() } else { self.fake->Some_0.loc() };
                        let b = if other.raw is Some { other.desc->Some_0.loc() } else { other.fake->Some_0.loc() };
                        ::vstd::resource::tsm_instance_id_injective(a, self.fake is Some, b, other.fake is Some);
                        if self.__id() == other.__id() && self.raw is Some {
                            ::vstd::resource::tsm_generic::agreement_resources_agree(self.__desc(), other.__desc());
                        }
                    },
                )
            }
        };
    let link_arg_self = if cm.is_some() { quote! {d} } else { quote! {loc} };
    let fake_extra_fields = if cm.is_some() { quote! {base: None, desc: None,} } else { quote! {} };
    quote! {
        #[allow(non_camel_case_types)]
        #derive
        pub tracked struct #n {
            tracked raw: Option<#raw_ty>,
            #extra_fields
            tracked fake: Option<#fake_field>,
            #(#data_decl,)*
        }
        impl #nt {
            #[verifier::type_invariant]
            spec fn __wf(self) -> bool {
                (self.raw is Some && self.fake is None && self.raw->Some_0.fragment() == #frag #me_extra #real_extra)
                || (self.raw is None && self.fake is Some && self.fake->Some_0.value() == #fake_value #fake_data #fake_extra)
            }
            #clone
            proof fn __from_raw(tracked raw: Token, #from_params #(#params),*) -> (tracked out: Self)
                requires raw.fragment() == #pfrag, #p_extra #from_reqs
                ensures out.__id() == ::vstd::resource::tsm_instance_id(#from_id, false),
                    #(out.#names == #names,)*
            {Self {raw: Some(#wrap_raw), #from_fields fake: None, #(#pdata),*}}
            spec fn __id(&self) -> ::vstd::resource::Loc {#instance_id}
            proof fn __lemma_id(tracked &self, #link_param)
                requires #link_req,
                ensures self.raw is Some, self.raw->Some_0.loc() == #link_loc, self.raw->Some_0.fragment() == #frag #me_extra #lemma_ens,
            {
                ::vstd::prelude::use_type_invariant(self);
                #lemma_body
            }
            /// Two tokens with one instance id are both real (at one location) or
            /// both placeholders (of one resource).
            proof fn __link(tracked &self, tracked other: &Self)
                ensures ::vstd::prelude::imply(self.__id() == other.__id(), (self.raw is Some) == (other.raw is Some)
                    && ::vstd::prelude::imply(self.raw is Some, self.raw->Some_0.loc() == other.raw->Some_0.loc())
                    && ::vstd::prelude::imply(self.fake is Some, self.fake->Some_0.loc() == other.fake->Some_0.loc())),
            {
                ::vstd::prelude::use_type_invariant(self);
                ::vstd::prelude::use_type_invariant(other);
                #link_body
            }
            proof fn __raw<'a>(tracked &'a self) -> (tracked out: &'a Token)
                requires self.raw is Some,
                ensures *out == self.raw->Some_0,
            {#borrow_raw}
            proof fn __fake<'a>(tracked &'a self) -> (tracked out: &'a #fake)
                requires self.fake is Some,
                ensures *out == self.fake->Some_0,
            {#borrow_fake}
            #into_raw
            #borrow_base
            proof fn __borrow_raw<'a>(tracked &'a self, #link_param) -> (tracked out: &'a Token)
                requires #link_req,
                ensures out.loc() == #link_loc, out.fragment() == #frag #me_extra,
            {
                self.__lemma_id(#link_arg_self);
                self.__raw()
            }
            proof fn __arbitrary() -> (tracked s: Self) {
                #fake_new
                Self {raw: None, #fake_extra_fields fake: Some(fake), #(#arbitrary_fields),*}
            }
        }
        #trait_impls
        #copy_impls
    }
}

/// `Clone`/`Copy` for a duplicable tracked type: derived when the machine has
/// no type parameters, otherwise implemented without bounds on them (as the
/// trusted macro does). The exec-mode `clone` is never callable on a tracked
/// value; the proof-mode inherent `clone` is the one clients use.
fn copy_impls(nt: &TokenStream, copy: bool, generic: bool) -> (TokenStream, TokenStream) {
    if !copy {
        (quote! {}, quote! {})
    } else if !generic {
        (quote! {#[derive(Clone, Copy)]}, quote! {})
    } else {
        (
            quote! {},
            quote! {
                #[verifier::external]
                impl ::core::clone::Clone for #nt {
                    fn clone(&self) -> Self { *self }
                }
                impl ::core::marker::Copy for #nt {}
            },
        )
    }
}

/// The component assertions that let two compatible real tokens of one field
/// agree (or conflict).
fn component(f: &Field, x: TokenStream, slot: &Option<TokenStream>) -> TokenStream {
    let n = &f.name;
    match slot {
        Some(s) => quote! {(#x).#n.at(#s)},
        None => quote! {(#x).#n},
    }
}

/// The vstd token trait implementations of one field token type.
fn token_traits(f: &Field, instance_id: &TokenStream, _store: &Store, cm: &Option<Cm>) -> TokenStream {
    let n = &f.name;
    let nt = tyname(f);
    let k = kind(f).unwrap();
    // The tracked fields besides `raw` and `fake` (with constants).
    let pat_extra = if cm.is_some() { quote! {base, desc,} } else { quote! {} };
    let embed = |s: TokenStream| quote! {<Protocol as ::vstd::resource::tsm::Machine>::embed(#s)};
    let slot_of = |who: &str| -> Option<TokenStream> {
        let w = format_ident!("{}", who);
        if k.map_like() {
            Some(quote! {#w.__k})
        } else if k.set_like() {
            Some(quote! {#w.__e})
        } else {
            None
        }
    };
    // Contradiction from two real tokens of the same exclusive slot.
    let real_conflict = {
        // (re-emit with the embed expression)
        let slot = slot_of("mine");
        let c_f = component(f, quote! {Fragment::op(f, frame)}, &slot);
        let c_e = component(f, embed(quote! {st}), &slot);
        let e_st = embed(quote! {st});
        quote! {
            let tracked mut r = raw.tracked_unwrap();
            r.validate_2(other.__raw());
            let f = Fragment::op(r.fragment(), other.raw->Some_0.fragment());
            let (frame, st) = choose|frame: Fragment, st: State|
                st.invariant() && Fragment::op(f, frame) == #e_st;
            assert(#c_f == #c_e);
            raw = Some(r);
        }
    };
    let unique_body = |same: TokenStream| {
        quote! {
            let tracked mut mine = Self::__arbitrary();
            ::vstd::modes::tracked_swap(self, &mut mine);
            ::vstd::prelude::use_type_invariant(&mine);
            ::vstd::prelude::use_type_invariant(other);
            mine.__link(other);
            let same = mine.__id() == other.__id() && #same;
            let ghost saved = mine;
            let tracked Self {raw, fake, #pat_extra ..} = mine;
            let tracked mut raw = raw;
            let tracked mut fake = fake;
            if same {
                if raw is Some {
                    #real_conflict
                } else {
                    let tracked mut x = fake.tracked_unwrap();
                    x.validate_2(other.__fake());
                    fake = Some(x);
                }
            }
            let tracked mut back = Self {raw, fake, #pat_extra ..saved};
            ::vstd::modes::tracked_swap(self, &mut back);
        }
    };
    // Agreement of two tokens on their value.
    let agree_body = |cond: TokenStream| {
        let slot = slot_of("self");
        let c1 = component(f, quote! {Fragment::op(self.raw->Some_0.fragment(), f1)}, &slot);
        let c2 = component(f, quote! {Fragment::op(other.raw->Some_0.fragment(), f2)}, &slot);
        let ce = component(f, embed(quote! {st}), &slot);
        let fake_case = if k.persistent() {
            quote! {
                let tracked j = self.__fake().join_shared(other.__fake());
                j.validate();
            }
        } else {
            quote! {}
        };
        quote! {
            ::vstd::prelude::use_type_invariant(self);
            ::vstd::prelude::use_type_invariant(other);
            if self.__id() == other.__id() #cond {
                self.__link(other);
                if self.raw is Some {
                    let (st, f1, f2) = self.__raw().compatible_with(other.__raw());
                    assert(#c1 == #ce);
                    assert(#c2 == #ce);
                } else {
                    #fake_case
                }
            }
        }
    };
    let arbitrary = quote! {proof fn arbitrary() -> (tracked s: Self) {Self::__arbitrary()}};
    let id_fn = quote! {closed spec fn instance_id(&self) -> ::vstd::tokens::InstanceId {#instance_id}};
    match &f.stype {
        ShardableType::Map(kt, v) | ShardableType::PersistentMap(kt, v)
        | ShardableType::IMap(kt, v) | ShardableType::PersistentIMap(kt, v) => {
            let agree = agree_body(quote! {&& self.__k == other.__k && self.__v != other.__v});
            let unique = if k.unique() {
                let body = unique_body(quote! {mine.__k == other.__k});
                quote! {
                    impl ::vstd::tokens::UniqueKeyValueToken<#kt, #v> for #nt {
                        proof fn unique(tracked &mut self, tracked other: &Self) {#body}
                    }
                }
            } else {
                quote! {}
            };
            quote! {
                impl ::vstd::tokens::KeyValueToken<#kt, #v> for #nt {
                    #id_fn
                    closed spec fn key(&self) -> #kt {self.__k}
                    closed spec fn value(&self) -> #v {self.__v}
                    proof fn agree(tracked &self, tracked other: &Self) {#agree}
                    #arbitrary
                }
                #unique
            }
        }
        ShardableType::Set(e) | ShardableType::PersistentSet(e) | ShardableType::Multiset(e)
        | ShardableType::ISet(e) | ShardableType::PersistentISet(e) => {
            let unique = if k.unique() {
                let body = unique_body(quote! {mine.__e == other.__e});
                quote! {
                    impl ::vstd::tokens::UniqueElementToken<#e> for #nt {
                        proof fn unique(tracked &mut self, tracked other: &Self) {#body}
                    }
                }
            } else {
                quote! {}
            };
            quote! {
                impl ::vstd::tokens::ElementToken<#e> for #nt {
                    #id_fn
                    closed spec fn element(&self) -> #e {self.__e}
                    #arbitrary
                }
                #unique
            }
        }
        ShardableType::Bool | ShardableType::PersistentBool => {
            let unique = if k.unique() {
                let body = unique_body(quote! {true});
                quote! {
                    impl ::vstd::tokens::UniqueSimpleToken for #nt {
                        proof fn unique(tracked &mut self, tracked other: &Self) {#body}
                    }
                }
            } else {
                quote! {}
            };
            quote! {
                impl ::vstd::tokens::SimpleToken for #nt {
                    #id_fn
                    #arbitrary
                }
                #unique
            }
        }
        ShardableType::Variable(v) | ShardableType::Option(v) | ShardableType::PersistentOption(v) => {
            let agree = agree_body(quote! {&& self.__v != other.__v});
            let unique = if k.unique() {
                let body = unique_body(quote! {true});
                quote! {
                    impl ::vstd::tokens::UniqueValueToken<#v> for #nt {
                        proof fn unique(tracked &mut self, tracked other: &Self) {#body}
                    }
                }
            } else {
                quote! {}
            };
            quote! {
                impl ::vstd::tokens::ValueToken<#v> for #nt {
                    #id_fn
                    closed spec fn value(&self) -> #v {self.__v}
                    proof fn agree(tracked &self, tracked other: &Self) {#agree}
                    #arbitrary
                }
                #unique
            }
        }
        ShardableType::PersistentCount => {
            let c_extra = if cm.is_some() { quote! {base: c.base, desc: c.desc,} } else { quote! {} };
            quote! {
            impl ::vstd::tokens::MonotonicCountToken for #nt {
                #id_fn
                closed spec fn count(&self) -> ::vstd::prelude::nat {self.__n}
                proof fn weaken(tracked &self, count: ::vstd::prelude::nat) -> (tracked s: Self) {
                    ::vstd::prelude::use_type_invariant(self);
                    let tracked c = *self;
                    Self {raw: c.raw, #c_extra fake: c.fake, __n: count, __m: c.__m}
                }
                #arbitrary
            }
        }},
        ShardableType::Count => {
            let factory = format_ident!("field_{}", n);
            // With constants, a split token gets its own copy of `κ`.
            let (split_base, base_a, base_b, pat_none) = match cm {
                None => (quote! {}, quote! {}, quote! {}, quote! {}),
                Some(cm) => {
                    let kappa = cm.kappa(quote! {desc->Some_0});
                    (
                        quote! {
                            let tracked bt = base.tracked_unwrap();
                            assert(bt.fragment() == Fragment::op(#kappa, #kappa));
                            let tracked (ba, bb) = bt.split(#kappa, #kappa);
                        },
                        quote! {base: Some(ba), desc,},
                        quote! {base: Some(bb), desc,},
                        quote! {base: None, desc: None,},
                    )
                }
            };
            quote! {
                /// `count` tokens provide the `vstd::tokens::CountToken` operations
                /// except `weaken_shared`, as inherent methods (see the chapter
                /// "Checked tokens: raw and generic interfaces").
                impl #nt {
                    pub closed spec fn instance_id(&self) -> ::vstd::tokens::InstanceId {#instance_id}
                    pub closed spec fn count(&self) -> ::vstd::prelude::nat {self.__n}
                    pub proof fn join(tracked &mut self, tracked other: Self)
                        requires old(self).instance_id() == other.instance_id(),
                        ensures final(self).instance_id() == old(self).instance_id(),
                            final(self).count() == old(self).count() + other.count(),
                    {
                        let tracked mut mine = Self::__arbitrary();
                        ::vstd::modes::tracked_swap(self, &mut mine);
                        ::vstd::prelude::use_type_invariant(&mine);
                        ::vstd::prelude::use_type_invariant(&other);
                        mine.__link(&other);
                        let ghost total = mine.__n + other.__n;
                        let tracked Self {raw, fake, #pat_extra ..} = mine;
                        let tracked Self {raw: oraw, fake: ofake, ..} = other;
                        let tracked mut back = if raw is Some {
                            Fragment::unit().op_unit();
                            let tracked r = raw.tracked_unwrap().join(oraw.tracked_unwrap());
                            assert(r.fragment() == Fragment::#factory(total));
                            Self {raw: Some(r), #pat_extra fake: None, __n: total}
                        } else {
                            let tracked r = fake.tracked_unwrap().join(ofake.tracked_unwrap());
                            Self {raw: None, #pat_extra fake: Some(r), __n: total}
                        };
                        ::vstd::modes::tracked_swap(self, &mut back);
                    }
                    pub proof fn split(tracked &mut self, count: ::vstd::prelude::nat) -> (tracked token: Self)
                        requires count <= old(self).count(),
                        ensures final(self).instance_id() == old(self).instance_id(),
                            final(self).count() == old(self).count() - count,
                            token.instance_id() == old(self).instance_id(),
                            token.count() == count,
                    {
                        let tracked mut mine = Self::__arbitrary();
                        ::vstd::modes::tracked_swap(self, &mut mine);
                        ::vstd::prelude::use_type_invariant(&mine);
                        let ghost left = (mine.__n - count) as nat;
                        let tracked Self {raw, fake, #pat_extra ..} = mine;
                        let tracked (mut back, token) = if raw is Some {
                            Fragment::unit().op_unit();
                            let tracked r = raw.tracked_unwrap();
                            assert(r.fragment() == Fragment::op(Fragment::#factory(left), Fragment::#factory(count)));
                            let tracked (a, b) = r.split(Fragment::#factory(left), Fragment::#factory(count));
                            #split_base
                            (Self {raw: Some(a), #base_a fake: None, __n: left}, Self {raw: Some(b), #base_b fake: None, __n: count})
                        } else {
                            let tracked (a, b) = fake.tracked_unwrap().split(
                                ::vstd::resource::tsm::CountRA {count: left}, ::vstd::resource::tsm::CountRA {count: count});
                            (Self {raw: None, #pat_none fake: Some(a), __n: left}, Self {raw: None, #pat_none fake: Some(b), __n: count})
                        };
                        ::vstd::modes::tracked_swap(self, &mut back);
                        token
                    }
                    pub proof fn arbitrary() -> (tracked s: Self) {Self::__arbitrary()}
                }
            }
        }
        _ => unreachable!(),
    }
}

// ---------------------------------------------------------------------------
// Collections

/// Split a bulk token into single-value tokens, and the reverse join, for one
/// collection field.
fn collection_helpers(f: &Field, cm: &Option<Cm>) -> TokenStream {
    let n = &f.name;
    let nt = tyname(f);
    let k = kind(f).unwrap();
    let factory = format_ident!("field_{}", n);
    let split = format_ident!("__split_{}", n);
    let join = format_ident!("__join_{}", n);
    let lemmas = quote! {broadcast use {::vstd::map::group_map_lemmas, ::vstd::set::group_set_lemmas,
        ::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas, ::vstd::multiset::group_multiset_axioms};};
    let pointwise = quote! {::vstd::resource::tsm_collections::Pointwise};
    let id_of = |x: TokenStream| id_call(f, x);
    // Mode-dependent pieces (see `Cm`): without constants a token is linked to
    // its instance by the location; with constants, by the descriptor `d`, and
    // each new token gets a copy of `κ`, split off `kappa`.
    let (sid, split_params, split_reqs, take_kp, kp_args, rec_split, link_param, lloc, lid, larg, into_suffix) = match cm {
        None => (
            quote! {::vstd::resource::tsm_instance_id(raw.loc(), false)},
            quote! {},
            quote! {},
            quote! {},
            quote! {},
            quote! {},
            quote! {loc: ::vstd::resource::Loc},
            quote! {loc},
            quote! {loc},
            quote! {loc},
            quote! {},
        ),
        Some(cm) => {
            let dty = &cm.d;
            let d_ok = cm.ok(quote! {d});
            let ploc = cm.ploc(quote! {d});
            let kappa = cm.kappa(quote! {d});
            (
                quote! {::vstd::resource::tsm_instance_id(d.loc(), false)},
                quote! {tracked kappa: Token, tracked d: &'static #dty,},
                quote! {#d_ok, raw.loc() == #ploc, kappa.loc() == #ploc, kappa.fragment() == #kappa,},
                quote! {
                    Fragment::unit().op_unit();
                    assert(kappa.fragment() == Fragment::op(#kappa, #kappa));
                    let tracked (__tsm_kp, kappa) = kappa.split(#kappa, #kappa);
                },
                quote! {__tsm_kp, d,},
                quote! {, kappa, d},
                quote! {tracked d: &#dty},
                ploc.clone(),
                quote! {d.loc()},
                quote! {d},
                quote! {.0},
            )
        }
    };
    let lreq = match cm {
        None => quote! {},
        Some(cm) => {
            let ok = cm.ok(quote! {d});
            quote! {#ok,}
        }
    };
    // `imap`/`iset` collections use infinite maps and sets; splitting and
    // joining them recurses on a finite domain.
    let fin = !k.infinite();
    let (map_t, set_t) = if fin {
        (quote! {::vstd::map::Map}, quote! {::vstd::set::Set})
    } else {
        (quote! {::vstd::imap::IMap}, quote! {::vstd::iset::ISet})
    };
    let mlen = if fin { quote! {m.len()} } else { quote! {m.dom().len()} };
    let (fin_m, fin_s) = if fin { (quote! {}, quote! {}) } else { (quote! {m.dom().finite(),}, quote! {s.finite(),}) };
    match &f.stype {
        ShardableType::Map(kt, v) | ShardableType::PersistentMap(kt, v)
        | ShardableType::IMap(kt, v) | ShardableType::PersistentIMap(kt, v) => {
            let out_id = id_of(quote! {out[key]});
            let vals = quote! {|key: #kt| ::vstd::tokens::KeyValueToken::value(&m[key])};
            let all_vals = if fin {
                quote! {::vstd::map::Map::new(m.dom(), #vals)}
            } else {
                quote! {::vstd::imap::IMap::new(|__tsm_key: #kt| m.dom().contains(__tsm_key), #vals)}
            };
            let mut s = quote! {
                proof fn #split(tracked raw: Token, m: #map_t<#kt, #v>, #split_params)
                    -> (tracked out: #map_t<#kt, #nt>)
                    requires raw.fragment() == Fragment::#factory(m), #fin_m #split_reqs
                    ensures out.dom() == m.dom(),
                        forall|key: #kt| ::vstd::prelude::imply(#[trigger] out.dom().contains(key),
                            ::vstd::tokens::KeyValueToken::key(&out[key]) == key
                            && ::vstd::tokens::KeyValueToken::value(&out[key]) == m[key]
                            && #out_id == #sid),
                    decreases #mlen,
                {
                    #lemmas
                    if #mlen == 0 {
                        assert(::vstd::prelude::ext_equal(m.dom(), #set_t::empty()));
                        #map_t::tracked_empty()
                    } else {
                        let key = m.dom().choose();
                        let rest = m.remove(key);
                        let one = Fragment::#factory(#map_t::empty().insert(key, m[key]));
                        let others = Fragment::#factory(rest);
                        assert(raw.fragment() == Fragment::op(one, others)) by {
                            Fragment::unit().op_unit();
                            assert forall|kk: #kt| #[trigger] raw.fragment().#n.at(kk) == Fragment::op(one, others).#n.at(kk) by {
                                if kk == key {} else {}
                            }
                            #pointwise::extensionality(raw.fragment().#n, Fragment::op(one, others).#n);
                        }
                        let tracked (a, b) = raw.split(one, others);
                        #take_kp
                        let tracked mut out = Self::#split(b, rest #rec_split);
                        out.tracked_insert(key, Self::__from_raw(a, #kp_args key, m[key]));
                        assert(::vstd::prelude::ext_equal(out.dom(), m.dom()));
                        out
                    }
                }
            };
            if !k.persistent() {
                s.extend(quote! {
                    proof fn #join(tracked acc: Token, tracked m: #map_t<#kt, #nt>, #link_param)
                        -> (tracked out: Token)
                        requires acc.loc() == #lloc, #lreq #fin_m
                            forall|key: #kt| ::vstd::prelude::imply(#[trigger] m.dom().contains(key),
                                m[key].__id() == ::vstd::resource::tsm_instance_id(#lid, false)
                                && ::vstd::tokens::KeyValueToken::key(&m[key]) == key),
                        ensures out.loc() == #lloc,
                            out.fragment() == Fragment::op(acc.fragment(), Fragment::#factory(#all_vals)),
                        decreases #mlen,
                    {
                        #lemmas
                        let all = #all_vals;
                        if #mlen == 0 {
                            Fragment::unit().op_unit();
                            acc.fragment().op_unit();
                            assert(Fragment::#factory(all) == Fragment::unit()) by {
                                assert(::vstd::prelude::ext_equal(all, #map_t::empty()));
                                #pointwise::extensionality(Fragment::#factory(all).#n, Fragment::unit().#n);
                            }
                            acc
                        } else {
                            let key = m.dom().choose();
                            assert(m.dom().contains(key));
                            assert(m[key].__id() == ::vstd::resource::tsm_instance_id(#lid, false));
                            let tracked mut m = m;
                            let tracked t = m.tracked_remove(key);
                            let v = ::vstd::tokens::KeyValueToken::value(&t);
                            let tracked raw = t.__into_raw(#larg)#into_suffix;
                            let tracked acc2 = acc.join(raw);
                            let rest = #all_vals;
                            let tracked out = Self::#join(acc2, m, #larg);
                            let one = Fragment::#factory(#map_t::empty().insert(key, v));
                            Fragment::unit().op_unit();
                            assert(Fragment::op(one, Fragment::#factory(rest)) == Fragment::#factory(all)) by {
                                assert forall|kk: #kt| #[trigger] Fragment::op(one, Fragment::#factory(rest)).#n.at(kk)
                                    == Fragment::#factory(all).#n.at(kk) by {
                                    if kk == key {} else {}
                                }
                                #pointwise::extensionality(
                                    Fragment::op(one, Fragment::#factory(rest)).#n, Fragment::#factory(all).#n);
                            }
                            Fragment::associative(acc.fragment(), one, Fragment::#factory(rest));
                            out
                        }
                    }
                });
            }
            quote! {impl #nt {#s}}
        }
        ShardableType::Set(e) | ShardableType::PersistentSet(e)
        | ShardableType::ISet(e) | ShardableType::PersistentISet(e) => {
            let out_id = id_of(quote! {out[x]});
            let mut s = quote! {
                proof fn #split(tracked raw: Token, s: #set_t<#e>, #split_params)
                    -> (tracked out: #map_t<#e, #nt>)
                    requires raw.fragment() == Fragment::#factory(s), #fin_s #split_reqs
                    ensures out.dom() == s,
                        forall|x: #e| ::vstd::prelude::imply(#[trigger] out.dom().contains(x),
                            ::vstd::tokens::ElementToken::element(&out[x]) == x
                            && #out_id == #sid),
                    decreases s.len(),
                {
                    #lemmas
                    if s.len() == 0 {
                        assert(::vstd::prelude::ext_equal(s, #set_t::empty()));
                        #map_t::tracked_empty()
                    } else {
                        let x = s.choose();
                        let rest = s.remove(x);
                        let one = Fragment::#factory(#set_t::empty().insert(x));
                        let others = Fragment::#factory(rest);
                        assert(raw.fragment() == Fragment::op(one, others)) by {
                            Fragment::unit().op_unit();
                            assert forall|kk: #e| #[trigger] raw.fragment().#n.at(kk) == Fragment::op(one, others).#n.at(kk) by {
                                if kk == x {} else {}
                            }
                            #pointwise::extensionality(raw.fragment().#n, Fragment::op(one, others).#n);
                        }
                        let tracked (a, b) = raw.split(one, others);
                        #take_kp
                        let tracked mut out = Self::#split(b, rest #rec_split);
                        out.tracked_insert(x, Self::__from_raw(a, #kp_args x));
                        assert(::vstd::prelude::ext_equal(out.dom(), s));
                        out
                    }
                }
            };
            if !k.persistent() {
                s.extend(quote! {
                    proof fn #join(tracked acc: Token, tracked m: #map_t<#e, #nt>, #link_param)
                        -> (tracked out: Token)
                        requires acc.loc() == #lloc, #lreq #fin_m
                            forall|x: #e| ::vstd::prelude::imply(#[trigger] m.dom().contains(x),
                                m[x].__id() == ::vstd::resource::tsm_instance_id(#lid, false)
                                && ::vstd::tokens::ElementToken::element(&m[x]) == x),
                        ensures out.loc() == #lloc,
                            out.fragment() == Fragment::op(acc.fragment(), Fragment::#factory(m.dom())),
                        decreases #mlen,
                    {
                        #lemmas
                        if #mlen == 0 {
                            Fragment::unit().op_unit();
                            acc.fragment().op_unit();
                            assert(Fragment::#factory(m.dom()) == Fragment::unit()) by {
                                assert(::vstd::prelude::ext_equal(m.dom(), #set_t::empty()));
                                #pointwise::extensionality(Fragment::#factory(m.dom()).#n, Fragment::unit().#n);
                            }
                            acc
                        } else {
                            let x = m.dom().choose();
                            assert(m.dom().contains(x));
                            assert(m[x].__id() == ::vstd::resource::tsm_instance_id(#lid, false));
                            let all = m.dom();
                            let tracked mut m = m;
                            let tracked t = m.tracked_remove(x);
                            let tracked raw = t.__into_raw(#larg)#into_suffix;
                            let tracked acc2 = acc.join(raw);
                            let rest = m.dom();
                            let tracked out = Self::#join(acc2, m, #larg);
                            let one = Fragment::#factory(#set_t::empty().insert(x));
                            Fragment::unit().op_unit();
                            assert(Fragment::op(one, Fragment::#factory(rest)) == Fragment::#factory(all)) by {
                                assert forall|kk: #e| #[trigger] Fragment::op(one, Fragment::#factory(rest)).#n.at(kk)
                                    == Fragment::#factory(all).#n.at(kk) by {
                                    if kk == x {} else {}
                                }
                                #pointwise::extensionality(
                                    Fragment::op(one, Fragment::#factory(rest)).#n, Fragment::#factory(all).#n);
                            }
                            Fragment::associative(acc.fragment(), one, Fragment::#factory(rest));
                            out
                        }
                    }
                });
            }
            quote! {impl #nt {#s}}
        }
        ShardableType::Multiset(e) => {
            let ms = quote! {::vstd::multiset::Multiset<#e>};
            let tok = quote! {::vstd::tokens::MultisetToken<#e, #nt>};
            let tok_expr = quote! {::vstd::tokens::MultisetToken::<#e, #nt>};
            quote! {
                impl #nt {
                    proof fn #split(tracked raw: Token, m: #ms, #split_params) -> (tracked out: #tok)
                        requires raw.fragment() == Fragment::#factory(m), m.len() >= 0, #split_reqs
                        ensures out.multiset() == m,
                            out.instance_id() == #sid,
                        decreases m.len(),
                    {
                        #lemmas
                        if m.len() == 0 {
                            assert(::vstd::prelude::ext_equal(m, ::vstd::multiset::Multiset::empty()));
                            #tok_expr::empty(#sid)
                        } else {
                            let x = m.choose();
                            let rest = m.remove(x);
                            let one = Fragment::#factory(::vstd::multiset::Multiset::singleton(x));
                            let others = Fragment::#factory(rest);
                            assert(raw.fragment() == Fragment::op(one, others)) by {
                                Fragment::unit().op_unit();
                                assert(::vstd::prelude::ext_equal(::vstd::multiset::Multiset::singleton(x).add(rest), m));
                            }
                            let tracked (a, b) = raw.split(one, others);
                            #take_kp
                            let tracked mut out = Self::#split(b, rest #rec_split);
                            let tracked t = Self::__from_raw(a, #kp_args x);
                            assert(::vstd::tokens::ElementToken::instance_id(&t) == out.instance_id());
                            out.insert(t);
                            assert(::vstd::prelude::ext_equal(out.multiset(), m));
                            out
                        }
                    }
                    proof fn #join(tracked acc: Token, tracked tokens: #tok, e: #ms, #link_param)
                        -> (tracked out: Token)
                        requires acc.loc() == #lloc, #lreq e.subset_of(tokens.multiset()),
                            tokens.instance_id() == ::vstd::resource::tsm_instance_id(#lid, false),
                        ensures out.loc() == #lloc,
                            out.fragment() == Fragment::op(acc.fragment(), Fragment::#factory(e)),
                        decreases e.len(),
                    {
                        #lemmas
                        if e.len() == 0 {
                            Fragment::unit().op_unit();
                            acc.fragment().op_unit();
                            assert(::vstd::prelude::ext_equal(e, ::vstd::multiset::Multiset::empty()));
                            acc
                        } else {
                            let x = e.choose();
                            assert(e.count(x) > 0);
                            let tracked mut tokens = tokens;
                            let tracked t = tokens.remove(x);
                            assert(t.__id() == ::vstd::resource::tsm_instance_id(#lid, false));
                            let tracked raw = t.__into_raw(#larg)#into_suffix;
                            let tracked acc2 = acc.join(raw);
                            let rest = e.remove(x);
                            let tracked out = Self::#join(acc2, tokens, rest, #larg);
                            let one = Fragment::#factory(::vstd::multiset::Multiset::singleton(x));
                            Fragment::unit().op_unit();
                            assert(Fragment::op(one, Fragment::#factory(rest)) == Fragment::#factory(e)) by {
                                assert(::vstd::prelude::ext_equal(::vstd::multiset::Multiset::singleton(x).add(rest), e));
                            }
                            Fragment::associative(acc.fragment(), one, Fragment::#factory(rest));
                            out
                        }
                    }
                }
            }
        }
        ShardableType::Option(_) | ShardableType::PersistentOption(_) | ShardableType::Bool | ShardableType::PersistentBool => {
            let boolean = matches!(k, Kind::Bool | Kind::PersistentBool);
            let v = match &f.stype {
                ShardableType::Option(v) | ShardableType::PersistentOption(v) => quote! {#v},
                _ => quote! {()},
            };
            let (ety, is_some, value, data) = if boolean {
                (quote! {bool}, quote! {e}, quote! {true}, quote! {})
            } else {
                (quote! {Option<#v>}, quote! {e is Some}, quote! {Some(e->Some_0)}, quote! {, e->Some_0})
            };
            let rel = if boolean {
                quote! {::vstd::tokens::bool_value_eq_option_token(e, out, #sid)}
            } else {
                quote! {::vstd::tokens::option_value_eq_option_token(e, out, #sid)}
            };
            let mut s = quote! {
                proof fn #split(tracked raw: Token, e: #ety, #split_params) -> (tracked out: Option<#nt>)
                    requires raw.fragment() == Fragment::#factory(e), #split_reqs
                    ensures #rel,
                {
                    if #is_some {
                        assert(Fragment::#factory(e) == Fragment::#factory(#value));
                        Some(Self::__from_raw(raw #rec_split #data))
                    } else {
                        None
                    }
                }
            };
            if !k.persistent() {
                let id_t = id_call(f, quote! {t});
                let le = if boolean {
                    quote! {::vstd::tokens::bool_value_le_option_token(e, t, ::vstd::resource::tsm_instance_id(#lid, false))}
                } else {
                    quote! {::vstd::tokens::option_value_le_option_token(e, t, ::vstd::resource::tsm_instance_id(#lid, false))}
                };
                s.extend(quote! {
                    proof fn #join(tracked acc: Token, tracked t: Option<#nt>, e: #ety, #link_param)
                        -> (tracked out: Token)
                        requires acc.loc() == #lloc, #lreq #le,
                        ensures out.loc() == #lloc, out.fragment() == Fragment::op(acc.fragment(), Fragment::#factory(e)),
                    {
                        if #is_some {
                            let tracked t = t.tracked_unwrap();
                            assert(t.__id() == #id_t);
                            assert(Fragment::#factory(e) == Fragment::#factory(#value));
                            acc.join(t.__into_raw(#larg)#into_suffix)
                        } else {
                            acc.fragment().op_unit();
                            acc
                        }
                    }
                });
            }
            quote! {impl #nt {#s}}
        }
        _ => quote! {},
    }
}

// ---------------------------------------------------------------------------
// Operation proofs

/// The included-owned lemma for one input token, given `op(op(tok, rest), z) == embed(pre)`.
fn included_lemma(f: &Field, vals: &[TokenStream], tok: TokenStream, coll: Option<TokenStream>) -> TokenStream {
    let n = &f.name;
    let c = quote! {::vstd::resource::tsm_collections};
    let g = quote! {::vstd::resource::tsm_generic};
    let rest = quote! {__tsm_c.#n};
    let z = quote! {__tsm_z.#n};
    let k = kind(f).unwrap();
    if let Some(observed) = coll {
        return match k {
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
            Kind::Set => quote! {
                #c::set_included_owned_many((#tok).#n, #rest, #z, pre.#n.to_iset(), (#observed).to_iset());
                assert forall|k| (#observed).contains(k) implies #[trigger] pre.#n.contains(k) by {
                    assert((#observed).to_iset().contains(k));
                }
                assert((#observed).subset_of(pre.#n));
            },
            Kind::IMap => quote! {#c::map_included_owned_many((#tok).#n, #rest, #z, pre.#n, #observed);},
            Kind::ISet => quote! {#c::set_included_owned_many((#tok).#n, #rest, #z, pre.#n, #observed);},
            Kind::Multiset => quote! {#g::multiset_included_many((#tok).#n, #rest, #z, pre.#n, #observed);},
            Kind::Option => quote! {#g::option_included_general((#tok).#n, #rest, #z, pre.#n, #observed);},
            Kind::PersistentOption => quote! {#g::persistent_option_included_general((#tok).#n, #rest, #z, pre.#n, #observed);},
            Kind::Bool => quote! {#g::bool_included_general((#tok).#n, #rest, #z, pre.#n, #observed);},
            Kind::PersistentBool => quote! {#g::persistent_bool_included_general((#tok).#n, #rest, #z, pre.#n, #observed);},
            _ => quote! {},
        };
    }
    match k {
        Kind::Map => {
            let (kk, v) = (&vals[0], &vals[1]);
            quote! {#c::map_included_owned_at((#tok).#n, #rest, #z, pre.#n.to_imap(), #kk, #v);}
        }
        Kind::PersistentMap => {
            let (kk, v) = (&vals[0], &vals[1]);
            quote! {#g::persistent_map_included_owned_at((#tok).#n, #rest, #z, pre.#n.to_imap(), #kk, #v);}
        }
        Kind::Set => {
            let e = &vals[0];
            quote! {#c::set_included_owned_at((#tok).#n, #rest, #z, pre.#n.to_iset(), #e);}
        }
        Kind::IMap => {
            let (kk, v) = (&vals[0], &vals[1]);
            quote! {#c::map_included_owned_at((#tok).#n, #rest, #z, pre.#n, #kk, #v);}
        }
        Kind::PersistentIMap => {
            let (kk, v) = (&vals[0], &vals[1]);
            quote! {#g::persistent_map_included_owned_at((#tok).#n, #rest, #z, pre.#n, #kk, #v);}
        }
        Kind::ISet => {
            let e = &vals[0];
            quote! {#c::set_included_owned_at((#tok).#n, #rest, #z, pre.#n, #e);}
        }
        Kind::PersistentISet => {
            let e = &vals[0];
            quote! {#g::persistent_set_included_owned_at((#tok).#n, #rest, #z, pre.#n, #e);}
        }
        Kind::PersistentSet => {
            let e = &vals[0];
            quote! {#g::persistent_set_included_owned_at((#tok).#n, #rest, #z, pre.#n.to_iset(), #e);}
        }
        Kind::Multiset => {
            let e = &vals[0];
            quote! {#g::multiset_included_owned((#tok).#n, #rest, #z, pre.#n, #e);}
        }
        Kind::Bool => quote! {::vstd::resource::tsm_bool::bool_included_owned((#tok).#n, #rest, #z, pre.#n);},
        Kind::PersistentBool => quote! {#g::persistent_bool_included_owned((#tok).#n, #rest, #z, pre.#n);},
        Kind::PersistentOption => {
            let v = &vals[0];
            quote! {#c::persistent_option_included_owned((#tok).#n, #rest, #z, pre.#n, #v);}
        }
        Kind::Option => {
            let v = &vals[0];
            quote! {#g::option_included_owned((#tok).#n, #rest, #z, pre.#n, #v);}
        }
        Kind::Variable => {
            let v = &vals[0];
            quote! {#g::exclusive_included_owned((#tok).#n, #rest, #z, pre.#n, #v);}
        }
        Kind::Count => {
            let v = &vals[0];
            quote! {#g::count_included_owned((#tok).#n, #rest, #z, pre.#n, #v);}
        }
        Kind::PersistentCount => {
            let v = &vals[1];
            quote! {#g::persistent_count_included_owned((#tok).#n, #rest, #z, pre.#n, #v);}
        }
    }
}

/// The constant's included lemma, for the instance's constant fragment.
fn constant_lemma(f: &Field, frag: &TokenStream) -> TokenStream {
    let n = &f.name;
    quote! {::vstd::resource::tsm_generic::agree_included_owned((#frag).#n, __tsm_c.#n, __tsm_z.#n, pre.#n, (*self).#n());}
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

/// Replace `old(p)` (with any path prefix) by `with(p)` for the given params.
fn rewrite_old(ts: TokenStream, with: &dyn Fn(&str) -> Option<TokenStream>) -> TokenStream {
    let trees: Vec<TokenTree> = ts.into_iter().collect();
    let mut out: Vec<TokenTree> = vec![];
    let mut i = 0;
    while i < trees.len() {
        if let (TokenTree::Ident(id), Some(TokenTree::Group(g))) = (&trees[i], trees.get(i + 1)) {
            if id == "old" && g.delimiter() == proc_macro2::Delimiter::Parenthesis {
                let inner: Vec<TokenTree> = g.stream().into_iter().collect();
                if inner.len() == 1 {
                    if let TokenTree::Ident(p) = &inner[0] {
                        if let Some(rep) = with(&p.to_string()) {
                            // Drop a preceding path (`::vstd::prelude::`).
                            loop {
                                let l = out.len();
                                if l >= 2 {
                                    if let (TokenTree::Punct(a), TokenTree::Punct(b)) = (&out[l - 2], &out[l - 1]) {
                                        if a.as_char() == ':' && b.as_char() == ':' {
                                            out.truncate(l - 2);
                                            if let Some(TokenTree::Ident(_)) = out.last() {
                                                out.pop();
                                            }
                                            continue;
                                        }
                                    }
                                }
                                break;
                            }
                            let g2 = proc_macro2::Group::new(proc_macro2::Delimiter::Parenthesis, rep);
                            out.push(TokenTree::Group(g2));
                            i += 2;
                            continue;
                        }
                    }
                }
            }
        }
        match &trees[i] {
            TokenTree::Group(g) => {
                let mut g2 = proc_macro2::Group::new(g.delimiter(), rewrite_old(g.stream(), with));
                g2.set_span(g.span());
                out.push(TokenTree::Group(g2));
            }
            t => out.push(t.clone()),
        }
        i += 1;
    }
    out.into_iter().collect()
}

struct Param<'a> {
    field: &'a Field,
    p: &'a TokenParam,
}

/// Body statements binding the transition's `let`s and token patterns.
fn lets(s: &TransitionStmt, birds_eye: bool, out: &mut Vec<TokenStream>, skipped: &mut bool) {
    lets_with(s, birds_eye, out, skipped, &HashMap::new())
}

/// `lets`, with the values bound to withdrawn resources (`withdraw .. -= [k => let v]`
/// binds `v` to the output parameter) replaced by `subst`.
fn lets_with(s: &TransitionStmt, birds_eye: bool, out: &mut Vec<TokenStream>, skipped: &mut bool,
    subst: &HashMap<String, TokenStream>) {
    match s {
        TransitionStmt::Block(_, xs) => xs.iter().for_each(|x| lets_with(x, birds_eye, out, skipped, subst)),
        TransitionStmt::Split(_, k, xs) => {
            if let SplitKind::Let(p, ty, lk, e) = &**k {
                let e = match subst.get(&quote! {#e}.to_string()) {
                    Some(v) => v.clone(),
                    None => quote! {#e},
                };
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
            xs.iter().for_each(|x| lets_with(x, birds_eye, out, skipped, subst));
        }
        _ => {}
    }
}

/// Fields read by a transition (including birds_eye reads).
fn reads(sm: &SM, tr: &Transition) -> HashSet<String> {
    let fields: HashMap<_, _> = sm.fields.iter().map(|f| (f.name.to_string(), f.clone())).collect();
    let mut body = tr.body.clone();
    let mut errors = vec![];
    let (a, b) = crate::field_access_visitor::find_all_accesses(&mut body, &mut errors, &fields);
    a.union(&b).cloned().collect()
}

struct Ctx<'a> {
    sm: &'a SM,
    store: &'a Store,
    /// The instance holds a `&'static` token with the unit fragment (with
    /// constants: `κ`), for operations of a machine without storage that
    /// consume no token (`__base`).
    base: bool,
    cm: &'a Option<Cm>,
}

fn is_read_only(parts: &ExchangeParts, params: &[Param]) -> bool {
    let guard = params.iter().any(|q| q.p.inout_type == InoutType::BorrowOut);
    !guard
        && params.iter().all(|q| q.p.inout_type == InoutType::BorrowIn)
        && parts.var_updates.is_empty()
        && parts.out_params.iter().all(|o| matches!(o.2, Mode::Ghost))
        && !parts.in_params.iter().any(|p| p.to_string().contains("& mut"))
}

fn params_of<'a>(sm: &'a SM, parts: &'a ExchangeParts, var_params: &'a [TokenParam]) -> Vec<Param<'a>> {
    let mut params: Vec<Param> = vec![];
    for f in &sm.fields {
        for p in parts.params.get(&f.name.to_string()).into_iter().flatten() {
            params.push(Param { field: f, p });
        }
        for p in var_params.iter().filter(|p| p.name == format_ident!("param_token_{}", f.name)) {
            params.push(Param { field: f, p });
        }
    }
    params
}

/// Token params for `variable` fields, which `exchange_parts` does not
/// record in `params` (their inputs are `&` or `&mut`).
fn variable_params(sm: &SM, parts: &ExchangeParts) -> Vec<TokenParam> {
    let mut out = vec![];
    for f in &sm.fields {
        if !matches!(f.stype, ShardableType::Variable(_)) {
            continue;
        }
        let name = format_ident!("param_token_{}", f.name);
        let ty: Type = {
            let nt = tyname(f);
            verus_syn::parse_quote! {#nt}
        };
        let written = parts.var_updates.contains_key(&f.name.to_string());
        let present = parts.in_params.iter().any(|p| {
            let s = p.to_string();
            s.split_whitespace().any(|w| w == name.to_string() || w == format!("{}:", name))
        });
        if !present {
            continue;
        }
        out.push(TokenParam {
            inout_type: if written { InoutType::InOut } else { InoutType::BorrowIn },
            name,
            ty,
            is_collection: false,
            stmt: None,
            elt: None,
            pat: None,
        });
    }
    out
}

/// Whether a transition's checked body needs a unit resource.
fn needs_unit(sm: &SM, bundle: &SMBundle, tr: &Transition) -> Result<bool, Error> {
    if tr.kind == TransitionKind::Init || tr.kind == TransitionKind::ReadonlyTransition {
        return Ok(false);
    }
    let parts = exchange_parts(bundle, tr, &HashMap::new())?;
    let vars = variable_params(sm, &parts);
    let params = params_of(sm, &parts, &vars);
    let guard = params.iter().any(|q| q.p.inout_type == InoutType::BorrowOut);
    if guard || is_read_only(&parts, &params) {
        return Ok(false);
    }
    Ok(!params.iter().any(|q| {
        !q.field.stype.is_storage() && !q.p.is_collection && matches!(q.p.inout_type, InoutType::In | InoutType::InOut)
    }))
}

/// Output of the checked facade.
pub fn output(bundle: &SMBundle) -> Result<TokenStream, Error> {
    let sm = &bundle.sm;
    check_fields(sm)?;
    let store = Store::new(sm)?;
    let cm = Cm::new(sm);
    let mut any_unit = false;
    for tr in &sm.transitions {
        any_unit |= needs_unit(sm, bundle, tr)?;
    }
    let base = !store.has() && any_unit;
    let ctx = Ctx { sm, store: &store, base, cm: &cm };
    // The trusted macro's specifications call the token traits' methods.
    let mut items = vec![quote! {
        #[allow(unused_imports)]
        use ::vstd::tokens::{ValueToken, KeyValueToken, CountToken, MonotonicCountToken, ElementToken, SimpleToken,
            UniqueValueToken, UniqueKeyValueToken, UniqueElementToken, UniqueSimpleToken};
        #[allow(unused_imports)]
        use ::vstd::prelude::{Ghost, Tracked, arbitrary, OptionAdditionalFns};
    }];
    for f in &sm.fields {
        if kind(f).is_some() {
            items.push(token_type(f, &store, sm.generics.is_some(), &cm));
            items.push(collection_helpers(f, &cm));
        }
        // The trusted macro's collection aliases.
        let n = &f.name;
        let nt = tyname(f);
        match &f.stype {
            ShardableType::Map(k, v) | ShardableType::PersistentMap(k, v) => {
                let alias = format_ident!("{}_map", n);
                items.push(quote! {#[allow(non_camel_case_types)] pub type #alias = ::vstd::tokens::MapToken<#k, #v, #nt>;});
            }
            ShardableType::Set(e) | ShardableType::PersistentSet(e) => {
                let alias = format_ident!("{}_set", n);
                items.push(quote! {#[allow(non_camel_case_types)] pub type #alias = ::vstd::tokens::SetToken<#e, #nt>;});
            }
            ShardableType::IMap(k, v) | ShardableType::PersistentIMap(k, v) => {
                let alias = format_ident!("{}_map", n);
                items.push(quote! {#[allow(non_camel_case_types)] pub type #alias = ::vstd::tokens::IMapToken<#k, #v, #nt>;});
            }
            ShardableType::ISet(e) | ShardableType::PersistentISet(e) => {
                let alias = format_ident!("{}_set", n);
                items.push(quote! {#[allow(non_camel_case_types)] pub type #alias = ::vstd::tokens::ISetToken<#e, #nt>;});
            }
            ShardableType::Multiset(e) => {
                let alias = format_ident!("{}_multiset", n);
                items.push(quote! {#[allow(non_camel_case_types)] pub type #alias = ::vstd::tokens::MultisetToken<#e, #nt>;});
            }
            _ => {}
        }
    }
    // The instance: its location (or, with constants, the descriptor `d`),
    // and (if an operation of a machine without storage needs a unit) a leaked
    // token owning the unit fragment (with constants: `κ`).
    let generic = sm.generics.is_some();
    let (inst_derive, inst_copy) = copy_impls(&quote! {Instance}, true, generic);
    let generic_args = sm.generics.as_ref().map(|g| crate::to_token_stream::get_generic_args(&g.params));
    let phantom_field = match &generic_args {
        Some(args) if !base => quote! {ghost __tsm_phantom: ::core::marker::PhantomData<(#args,)>,},
        _ => quote! {},
    };
    let (loc_field, loc_spec, id_spec, const_fns, inst_inv, unit_def, base_kappa) = match &cm {
        None => (
            quote! {ghost __loc: Ghost<::vstd::resource::Loc>,},
            quote! {self.__loc@},
            quote! {::vstd::resource::tsm_instance_id(self.__loc@, false)},
            vec![],
            if base {
                quote! {self.__base.loc() == self.__loc@ && self.__base.fragment() == Fragment::unit()}
            } else {
                quote! {true}
            },
            quote! {
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
            },
            quote! {},
        ),
        Some(cm) => {
            let dty = &cm.d;
            let ok = cm.ok(quote! {self.__desc});
            let ploc = cm.ploc(quote! {self.__desc});
            let kappa = cm.kappa(quote! {self.__desc});
            let const_fns: Vec<_> = cm
                .consts
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    let n = &c.name;
                    let ShardableType::Constant(t) = &c.stype else { unreachable!() };
                    let v = cm.constant(quote! {self.__desc}, i);
                    quote! {pub closed spec fn #n(&self) -> #t {#v}}
                })
                .collect();
            let u_ok = cm.ok(quote! {self.desc});
            let u_ploc = cm.ploc(quote! {self.desc});
            let u_kappa = cm.kappa(quote! {self.desc});
            (
                quote! {tracked __desc: &'static #dty,},
                ploc.clone(),
                quote! {::vstd::resource::tsm_instance_id(self.__desc.loc(), false)},
                const_fns,
                if base {
                    quote! {#ok && self.__base.loc() == #ploc && self.__base.fragment() == #kappa}
                } else {
                    quote! {#ok}
                },
                quote! {
                    /// A unit token: the identity resource of an instance, for operations
                    /// that consume no other token (with a copy of the constants).
                    pub tracked struct Unit {tracked raw: Token, tracked base: Token, tracked desc: &'static #dty}
                    impl Unit {
                        #[verifier::type_invariant]
                        spec fn __wf(self) -> bool {
                            self.raw.fragment() == Fragment::unit()
                            && #u_ok
                            && self.raw.loc() == #u_ploc && self.base.loc() == #u_ploc
                            && self.base.fragment() == #u_kappa
                        }
                        pub closed spec fn instance_id(&self) -> ::vstd::tokens::InstanceId {
                            ::vstd::resource::tsm_instance_id(self.desc.loc(), false)
                        }
                    }
                },
                kappa,
            )
        }
    };
    let base_field = if base { quote! {tracked __base: &'static Token,} } else { quote! {} };
    items.push(quote! {
        /// The instance carries only its location (and shared, leaked
        /// resources), so it is freely duplicable (`Copy`, as in the trusted
        /// macro).
        #[allow(non_camel_case_types)]
        #inst_derive
        pub tracked struct Instance {#loc_field #base_field #phantom_field}
        #inst_copy
        impl Instance {
            #[verifier::type_invariant]
            spec fn __wf(self) -> bool {#inst_inv}
            /// The protocol location.
            spec fn __l(&self) -> ::vstd::resource::Loc {#loc_spec}
            pub closed spec fn id(&self) -> ::vstd::tokens::InstanceId {#id_spec}
            pub proof fn clone(tracked &self) -> (tracked s: Self) ensures s == *self {*self}
            #(#const_fns)*
        }
        #unit_def
    });
    let link = if cm.is_some() { quote! {self.__desc} } else { quote! {self.__l()} };
    let pat_extra = if cm.is_some() { quote! {base, desc,} } else { quote! {} };
    let mut unit_fns = vec![];
    for f in &sm.fields {
        let Some(k) = kind(f) else { continue };
        if k.persistent() {
            continue;
        }
        let n = &f.name;
        let nt = tyname(f);
        let fname = format_ident!("unit_from_{}", n);
        let id_old = id_call(f, quote! {*old(t)});
        let id_final = id_call(f, quote! {*final(t)});
        let tr_path = trait_path(f);
        let observers: Vec<Ident> = match k {
            Kind::Map | Kind::IMap => vec![format_ident!("key"), format_ident!("value")],
            Kind::Set | Kind::ISet | Kind::Multiset => vec![format_ident!("element")],
            Kind::Variable | Kind::Option => vec![format_ident!("value")],
            Kind::Count => vec![format_ident!("count")],
            _ => vec![],
        };
        let same: Vec<_> = observers
            .iter()
            .map(|o| {
                if k == Kind::Count {
                    quote! {#nt::#o(&*final(t)) == #nt::#o(&*old(t))}
                } else {
                    quote! {<#nt as #tr_path>::#o(&*final(t)) == <#nt as #tr_path>::#o(&*old(t))}
                }
            })
            .collect();
        let id_mine = id_call(f, quote! {mine});
        let (split_base, unit_value, back_extra) = match &cm {
            None => (quote! {}, quote! {Unit {raw: u}}, quote! {}),
            Some(_) => (
                quote! {
                    let tracked b = base.tracked_unwrap();
                    assert(b.fragment() == Fragment::op(#base_kappa, #base_kappa));
                    let tracked (b1, b2) = b.split(#base_kappa, #base_kappa);
                },
                quote! {Unit {raw: u, base: b1, desc: self.__desc}},
                quote! {base: Some(b2), desc,},
            ),
        };
        unit_fns.push(quote! {
            /// Split the unit resource off a token of this instance.
            pub proof fn #fname(tracked &self, tracked t: &mut #nt) -> (tracked u: Unit)
                requires #id_old == self.id(),
                ensures #id_final == self.id(), #(#same,)*
                    u.instance_id() == self.id(),
            {
                ::vstd::prelude::use_type_invariant(self);
                let tracked mut mine = #nt::__arbitrary();
                ::vstd::modes::tracked_swap(t, &mut mine);
                assert(mine.__id() == #id_mine);
                ::vstd::prelude::use_type_invariant(&mine);
                mine.__lemma_id(#link);
                let ghost saved = mine;
                let tracked #nt {raw, fake, #pat_extra ..} = mine;
                let tracked raw = raw.tracked_unwrap();
                let f = raw.fragment();
                f.op_unit();
                Fragment::commutative(Fragment::unit(), f);
                Fragment::unit().op_unit();
                let tracked (u, raw) = raw.split(Fragment::unit(), f);
                #split_base
                let tracked mut back = #nt {raw: Some(raw), #back_extra fake, ..saved};
                ::vstd::modes::tracked_swap(t, &mut back);
                #unit_value
            }
        });
    }
    if base && !store.has() {
        let unit_value = match &cm {
            None => quote! {Unit {raw: self.__base.empty()}},
            Some(_) => quote! {
                Fragment::unit().op_unit();
                assert(Fragment::op(#base_kappa, #base_kappa) == #base_kappa);
                Unit {raw: self.__base.empty(), base: self.__base.duplicate(), desc: self.__desc}
            },
        };
        unit_fns.push(quote! {
            /// A unit token of this instance.
            pub proof fn unit(tracked &self) -> (tracked u: Unit)
                ensures u.instance_id() == self.id(),
            {
                ::vstd::prelude::use_type_invariant(self);
                #unit_value
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
        match method(bundle, &ctx, tr) {
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
    let out = ghostify(quote! {#(#items)*}, proc_macro2::Delimiter::None);
    Ok(match &sm.generics {
        None => resolve_types(out, None),
        Some(_) => {
            let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
            let (decl, wc) = crate::to_token_stream::generics_for_decl(&generics);
            let args = crate::to_token_stream::get_generic_args(&sm.generics.as_ref().unwrap().params);
            let mut names: HashSet<String> =
                ["Fragment", "Protocol", "State", "Token", "Instance", "Unit", "__StorageKey", "__StorageValue"]
                    .iter().map(|s| s.to_string()).collect();
            let attrs = quote! {#(#attrs)*};
            // Leaked `&'static` tokens (the instance's base token and persistent
            // tokens) need the machine's type parameters to be `'static`.
            // (The descriptor needs it only if a constant's type mentions them.)
            fn mentions(ts: &TokenStream, names: &HashSet<String>) -> bool {
                ts.clone().into_iter().any(|t| match t {
                    TokenTree::Ident(id) => names.contains(&id.to_string()),
                    TokenTree::Group(g) => mentions(&g.stream(), names),
                    _ => false,
                })
            }
            let params: HashSet<String> = args.iter().map(|a| quote! {#a}.to_string()).collect();
            let needs_static = base
                || sm.fields.iter().any(|f| kind(f).is_some_and(|k| k.persistent()))
                || cm.as_ref().is_some_and(|cm| mentions(&cm.d, &params));
            let wc = if needs_static {
                let bounds: Vec<_> = args.iter().map(|a| quote! {#a: 'static}).collect();
                match &generics.as_ref().and_then(|g| g.where_clause.as_ref()) {
                    Some(w) if !w.predicates.is_empty() => {
                        let preds = &w.predicates;
                        quote! {where #preds, #(#bounds),*}
                    }
                    _ => quote! {where #(#bounds),*},
                }
            } else {
                wc
            };
            let args = quote! {#args};
            let out = genericize(out, &Gen { decl, wc, args: args.clone(), attrs, names: std::mem::take(&mut names) });
            resolve_types(out, Some(&args))
        }
    })
}

/// A consumed token collection: its fragment, observed value, and join statement.
/// The API only requires `e <= tokens`, so only the tokens for `e` are joined.
fn collection_input(f: &Field, pname: &Ident, loc: &TokenStream, e: &Expr) -> Result<(TokenStream, TokenStream), Error> {
    let n = &f.name;
    let nt = tyname(f);
    let factory = format_ident!("field_{}", n);
    let join = format_ident!("__join_{}", n);
    let frag = quote! {Fragment::#factory(#e)};
    match kind(f) {
        Some(Kind::Map) => Ok((frag, quote! {
            let tracked mut __tsm_tokens = #pname.into_map();
            let tracked __tsm_sel = __tsm_tokens.tracked_remove_keys((#e).dom());
            assert(::vstd::prelude::ext_equal(::vstd::map::Map::new(__tsm_sel.dom(),
                |k| ::vstd::tokens::KeyValueToken::value(&__tsm_sel[k])), #e));
            let tracked __tsm_acc = #nt::#join(__tsm_acc, __tsm_sel, #loc);
        })),
        Some(Kind::Set) | Some(Kind::ISet) => Ok((frag, quote! {
            let tracked mut __tsm_tokens = #pname.into_map();
            let tracked __tsm_sel = __tsm_tokens.tracked_remove_keys(#e);
            assert(::vstd::prelude::ext_equal(__tsm_sel.dom(), #e));
            let tracked __tsm_acc = #nt::#join(__tsm_acc, __tsm_sel, #loc);
        })),
        Some(Kind::IMap) => Ok((frag, quote! {
            let tracked mut __tsm_tokens = #pname.into_map();
            let tracked __tsm_sel = __tsm_tokens.tracked_remove_keys((#e).dom());
            assert(::vstd::prelude::ext_equal(::vstd::imap::IMap::new(|__tsm_key| __tsm_sel.dom().contains(__tsm_key),
                |k| ::vstd::tokens::KeyValueToken::value(&__tsm_sel[k])), #e));
            let tracked __tsm_acc = #nt::#join(__tsm_acc, __tsm_sel, #loc);
        })),
        Some(Kind::Multiset) => Ok((frag, quote! {
            let tracked __tsm_acc = #nt::#join(__tsm_acc, #pname, #e, #loc);
        })),
        Some(Kind::Option) | Some(Kind::Bool) => Ok((frag, quote! {
            let tracked __tsm_acc = #nt::#join(__tsm_acc, #pname, #e, #loc);
        })),
        _ => err(f.name.span(), "generic field tokens consume map, set, multiset, option and bool token collections only"),
    }
}

/// The pointwise extensionality step for an output fragment component.
fn ext_step(f: &Field, a: &TokenStream, b: &TokenStream) -> TokenStream {
    let n = &f.name;
    match kind(f) {
        Some(k) if k.map_like() || k.set_like() => {
            quote! {::vstd::resource::tsm_collections::Pointwise::extensionality((#a).#n, (#b).#n);}
        }
        Some(Kind::Multiset) => quote! {assert(::vstd::prelude::ext_equal((#a).#n.values, (#b).#n.values));},
        _ => quote! {},
    }
}

fn method(bundle: &SMBundle, ctx: &Ctx, tr: &Transition) -> Result<TokenStream, Error> {
    let sm = &bundle.sm;
    let store = ctx.store;
    let parts = exchange_parts(bundle, tr, &HashMap::new())?;
    let (ret, req, ens) = signature_tokens(&parts);
    let vars = variable_params(sm, &parts);
    let params = params_of(sm, &parts, &vars);
    if tr.kind == TransitionKind::Init {
        return init_method(bundle, ctx, tr, &parts, ret, req, ens);
    }
    let name = &parts.exch_name;
    let in_params = &parts.in_params;
    let gen = if parts.use_explicit_lifetime { quote! {<'a>} } else { quote! {} };
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let span = tr.name.span();
    let guard = params.iter().any(|q| q.p.inout_type == InoutType::BorrowOut);
    let inouts: HashSet<String> = params
        .iter()
        .filter(|q| q.p.inout_type == InoutType::InOut)
        .map(|q| q.p.name.to_string())
        .collect();
    // `old(p)` in the method body is the ghost copy taken on entry; in the
    // helper proofs, the (old) ghost parameter itself.
    let in_body = |ts: TokenStream| -> TokenStream {
        rewrite_old(ts, &|p: &str| {
            if inouts.contains(p) {
                let g = format_ident!("__tsm_ghost_{}", p);
                Some(quote! {#g})
            } else {
                None
            }
        })
    };
    let in_helper = |ts: TokenStream| -> TokenStream {
        rewrite_old(ts, &|p: &str| {
            if inouts.contains(p) {
                let g = format_ident!("{}", p);
                Some(quote! {#g})
            } else {
                None
            }
        })
    };
    // Values bound to withdrawn resources: unknown before the exchange, then
    // read from the withdrawn map.
    let mut withdrawn_arb = HashMap::new();
    let mut withdrawn_actual = HashMap::new();
    // The withdrawn values, once known (for variable updates that use them).
    let mut withdrawn_binds: Vec<TokenStream> = vec![];
    for q in &params {
        let f = q.field;
        if !f.stype.is_storage() || q.p.inout_type != InoutType::Out {
            continue;
        }
        let key = match q.p.elt.as_ref() {
            Some(MonoidElt::SingletonKV(k, _)) => store.key_of(f, Some(k)),
            Some(MonoidElt::OptionSome(_)) => store.key_of(f, None),
            _ => continue,
        };
        let ty = &q.p.ty;
        let fname = &f.name;
        let actual = if store.kind == StoreKind::Carrier {
            quote! {match __tsm_withdrawn[#key] {__StorageValue::#fname(__tsm_x) => __tsm_x, _ => ::vstd::prelude::arbitrary::<#ty>()}}
        } else {
            quote! {__tsm_withdrawn[#key]}
        };
        withdrawn_arb.insert(q.p.name.to_string(), quote! {::vstd::prelude::arbitrary::<#ty>()});
        let pname = &q.p.name;
        withdrawn_binds.push(quote! {let #pname: #ty = #actual;});
        withdrawn_actual.insert(q.p.name.to_string(), actual);
    }
    // Bind the transition's lets (except those depending on birds_eye reads).
    let mut early = vec![];
    let mut skipped = false;
    lets_with(&parts.body, false, &mut early, &mut skipped, &withdrawn_arb);
    let mut early_actual = vec![];
    let mut skipped = false;
    lets_with(&parts.body, false, &mut early_actual, &mut skipped, &withdrawn_actual);
    let mut late = vec![];
    let mut skipped2 = false;
    lets_with(&parts.body, true, &mut late, &mut skipped2, &withdrawn_actual);
    let early_body: Vec<_> = early.iter().map(|e| in_body(e.clone())).collect();
    let early_helper: Vec<_> = early.iter().map(|e| in_helper(e.clone())).collect();
    let early_actual_body: Vec<_> = early_actual.iter().map(|e| in_body(e.clone())).collect();
    let early_actual_helper: Vec<_> = early_actual.iter().map(|e| in_helper(e.clone())).collect();
    let late_body: Vec<_> = late.iter().map(|e| in_body(e.clone())).collect();
    let late_helper: Vec<_> = late.iter().map(|e| in_helper(e.clone())).collect();
    let loc = quote! {self.__l()};
    let cm = ctx.cm;
    // A token's link to the instance (see `Cm`).
    let link = if cm.is_some() { quote! {self.__desc} } else { quote! {self.__l()} };
    // With constants: the first consumed token's copy of `κ`, and the first
    // borrowed token (to observe its copy).
    let mut kappa_from: Option<Ident> = None;
    let mut first_borrow: Option<Ident> = None;
    let owned_ident = format_ident!("__tsm_owned", span = Span::mixed_site());
    let shared_ident = format_ident!("__tsm_shared", span = Span::mixed_site());
    let mut take_owned: Vec<(Ident, TokenStream)> = vec![];
    let mut take_shared: Vec<(Ident, TokenStream)> = vec![];
    // Input fragments in the helper proofs' names (ghost params) and in the
    // method body (where `&mut` inputs are read from their ghost copies).
    let mut owned_frags: Vec<TokenStream> = vec![];
    let mut owned_frags_body: Vec<TokenStream> = vec![];
    let mut coll_owned: Vec<(TokenStream, TokenStream)> = vec![];
    let mut incl_frames: Vec<(TokenStream, TokenStream)> = vec![];
    // The same, over the ghost copies bound in the method body.
    let mut incl_frames_body: Vec<(TokenStream, TokenStream)> = vec![];
    let mut shared_frags: Vec<TokenStream> = vec![];
    let mut shared_frags_body: Vec<TokenStream> = vec![];
    let mut extra_reqs: Vec<TokenStream> = vec![];
    for q in &params {
        let (pname, f) = (&q.p.name, q.field);
        if f.stype.is_storage() {
            continue;
        }
        let data = token_data(f);
        let vals: Vec<TokenStream> = data.iter().map(|(d, _)| quote! {#pname.#d}).collect();
        let tok_frag = single_fragment(f, &vals);
        let incl_lemma = included_lemma(f, &vals, quote! {#tok_frag}, None);
        let ghost = format_ident!("__tsm_ghost_{}", pname);
        let gvals: Vec<TokenStream> = data.iter().map(|(d, _)| quote! {#ghost.#d}).collect();
        let tok_frag_ghost = single_fragment(f, &gvals);
        let incl_lemma_ghost = included_lemma(f, &gvals, quote! {#tok_frag_ghost}, None);
        if kind(f) == Some(Kind::PersistentCount) && matches!(q.p.inout_type, InoutType::In | InoutType::BorrowIn) {
            extra_reqs.push(quote! {#pname.__n <= #pname.__m});
        }
        match q.p.inout_type {
            InoutType::In if q.p.is_collection => {
                let Some(MonoidElt::General(e)) = q.p.elt.as_ref() else {
                    return err(f.name.span(), "unsupported consumed collection for generic field tokens");
                };
                let (coll_frag, join) = collection_input(f, pname, &link, e)?;
                let e_body = in_body(quote! {#e});
                coll_owned.push((in_body(join), coll_frag.clone()));
                let observed = quote! {(#e)};
                incl_frames.push((coll_frag.clone(), included_lemma(f, &[], coll_frag.clone(), Some(observed.clone()))));
                incl_frames_body.push((in_body(coll_frag.clone()), in_body(included_lemma(f, &[], coll_frag.clone(), Some(observed)))));
                let _ = e_body;
            }
            InoutType::In => {
                let raw = format_ident!("__tsm_raw_{}", pname);
                let b = format_ident!("__tsm_base_{}", pname);
                if cm.is_some() && kappa_from.is_none() {
                    kappa_from = Some(b.clone());
                }
                take_owned.push((raw.clone(), if cm.is_some() {
                    quote! {let tracked (#raw, #b) = #pname.__into_raw(#link);}
                } else {
                    quote! {let tracked #raw = #pname.__into_raw(#link);}
                }));
                owned_frags.push(tok_frag.clone());
                owned_frags_body.push(tok_frag_ghost.clone());
                incl_frames.push((tok_frag.clone(), incl_lemma));
                incl_frames_body.push((tok_frag_ghost.clone(), incl_lemma_ghost));
            }
            InoutType::InOut => {
                let raw = format_ident!("__tsm_raw_{}", pname);
                let taken = format_ident!("__tsm_taken_{}", pname);
                let ty = tyname(f);
                let b = format_ident!("__tsm_base_{}", pname);
                if cm.is_some() && kappa_from.is_none() {
                    kappa_from = Some(b.clone());
                }
                let into = if cm.is_some() {
                    quote! {let tracked (#raw, #b) = #taken.__into_raw(#link);}
                } else {
                    quote! {let tracked #raw = #taken.__into_raw(#link);}
                };
                take_owned.push((raw.clone(), quote! {
                    let tracked mut #taken = #ty::__arbitrary();
                    ::vstd::modes::tracked_swap(#pname, &mut #taken);
                    #into
                }));
                owned_frags.push(tok_frag.clone());
                owned_frags_body.push(tok_frag_ghost.clone());
                incl_frames.push((tok_frag.clone(), incl_lemma));
                incl_frames_body.push((tok_frag_ghost.clone(), incl_lemma_ghost));
            }
            InoutType::BorrowIn => {
                if q.p.is_collection {
                    return err(f.name.span(), "generic field tokens do not yet support borrowed token collections");
                }
                let obs = format_ident!("__tsm_obs_{}", pname);
                if first_borrow.is_none() {
                    first_borrow = Some(pname.clone());
                }
                take_shared.push((obs.clone(), quote! {let tracked #obs = #pname.__borrow_raw(#link).observe();}));
                shared_frags.push(tok_frag.clone());
                shared_frags_body.push(tok_frag_ghost.clone());
                incl_frames.push((tok_frag.clone(), incl_lemma));
                incl_frames_body.push((tok_frag_ghost.clone(), incl_lemma_ghost));
            }
            InoutType::Out | InoutType::BorrowOut => {}
        }
    }
    // Constants read by the transition come from the instance's shared token.
    let read = reads(sm, tr);
    let read_consts: Vec<&Field> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(_)) && read.contains(&f.name.to_string()))
        .collect();
    if !read_consts.is_empty() {
        let constants: Vec<&Field> = sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::Constant(_))).collect();
        let base_frag = constants.iter().fold(quote! {Fragment::unit()}, |acc, c| {
            let w = format_ident!("with_{}", c.name);
            let n = &c.name;
            quote! {#acc.#w((*self).#n())}
        });
        let obs = format_ident!("__tsm_obs_constants");
        // The constants' fragment `κ`: a consumed token's (or the unit's) copy,
        // else a borrowed token's.
        let source = if kappa_from.is_some() || take_owned.is_empty() && !guard && !is_read_only(&parts, &params) {
            quote! {let tracked #obs = __tsm_kappa.observe();}
        } else if let Some(p) = &first_borrow {
            quote! {let tracked #obs = #p.__borrow_base(#link).observe();}
        } else {
            return err(span, "generic field tokens: an operation reading a constant needs a token of the instance");
        };
        take_shared.push((obs.clone(), quote! {
            ::vstd::prelude::use_type_invariant(self);
            #source
        }));
        shared_frags.push(base_frag.clone());
        shared_frags_body.push(base_frag.clone());
        for c in &read_consts {
            incl_frames.push((base_frag.clone(), constant_lemma(c, &base_frag)));
            incl_frames_body.push((base_frag.clone(), constant_lemma(c, &base_frag)));
        }
    }
    let _ = &kappa_from;
    // Read-only operations (only borrowed tokens, no outputs or storage
    // changes) need no exchange: validate the borrowed tokens and reason
    // about a completion state.
    if is_read_only(&parts, &params) && coll_owned.is_empty() {
        return read_only_method(ctx, tr, &parts, &take_shared, &incl_frames, &shared_frags, ret, req, ens, &early_body, &late_body);
    }
    if guard {
        return guard_method(ctx, tr, &parts, &params, &take_shared, &incl_frames, &shared_frags, ret, req, ens, &early_body);
    }
    // Without any owned token, the method takes a unit token (storage
    // machines) or splits one off the instance's shared token.
    let mut in_params = in_params.clone();
    let needs_unit = take_owned.is_empty();
    let unit_param = needs_unit && store.has();
    if unit_param {
        in_params.push(quote! {tracked __tsm_unit: Unit});
    }
    let mut unit_req = if unit_param { quote! {__tsm_unit.instance_id() == (*self).id(),} } else { quote! {} };
    // `imap`/`iset` token collections are finite (they are split and joined
    // token by token); the trusted interface does not require this.
    for q in &params {
        let Some(k) = kind(q.field) else { continue };
        if !k.infinite() || !q.p.is_collection {
            continue;
        }
        if let Some(MonoidElt::General(e)) = q.p.elt.as_ref() {
            let lets = &early;
            unit_req.extend(if k.map_like() {
                quote! {({ #(#lets)* (#e).dom().finite() }),}
            } else {
                quote! {({ #(#lets)* (#e).finite() }),}
            });
        }
    }
    let req = if !unit_req.is_empty() {
        if req.is_empty() { quote! {requires #unit_req} } else { quote! {#req, #unit_req} }
    } else {
        req
    };
    let mut join_owned = vec![];
    if needs_unit && !coll_owned.is_empty() {
        // The accumulator starts as the unit; collections are joined onto it.
        owned_frags.push(quote! {Fragment::unit()});
        owned_frags_body.push(quote! {Fragment::unit()});
    }
    for (_, frag) in &coll_owned {
        owned_frags.push(frag.clone());
        owned_frags_body.push(in_body(frag.clone()));
    }
    if needs_unit {
        if unit_param {
            join_owned.push(if cm.is_some() {
                quote! {
                    ::vstd::prelude::use_type_invariant(&__tsm_unit);
                    ::vstd::prelude::use_type_invariant(self);
                    ::vstd::resource::tsm_instance_id_injective(__tsm_unit.desc.loc(), false, self.__desc.loc(), false);
                    ::vstd::resource::tsm_generic::agreement_resources_agree(__tsm_unit.desc, self.__desc);
                    let tracked Unit {raw: __tsm_acc, base: __tsm_kappa, ..} = __tsm_unit;
                }
            } else {
                quote! {
                    ::vstd::prelude::use_type_invariant(&__tsm_unit);
                    ::vstd::prelude::use_type_invariant(self);
                    ::vstd::resource::tsm_instance_id_injective(__tsm_unit.raw.loc(), false, #loc, false);
                    let tracked Unit {raw: __tsm_acc} = __tsm_unit;
                }
            });
        } else {
            if !ctx.base {
                return err(span, "internal: generic field tokens need an instance base token");
            }
            join_owned.push(quote! {
                ::vstd::prelude::use_type_invariant(self);
                let tracked __tsm_acc = self.__base.empty();
            });
            if let Some(cm) = cm {
                let kappa = cm.kappa(quote! {self.__desc});
                join_owned.push(quote! {
                    Fragment::unit().op_unit();
                    assert(Fragment::op(#kappa, #kappa) == #kappa);
                    let tracked __tsm_kappa = self.__base.duplicate();
                });
            }
        }
    } else {
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
        if let Some(b) = &kappa_from {
            join_owned.push(quote! {let tracked __tsm_kappa = #b;});
        }
    }
    for (join, _) in &coll_owned {
        join_owned.push(join.clone());
    }
    let mut join_shared = vec![];
    let has_shared = !take_shared.is_empty();
    for (i, (obs, take)) in take_shared.iter().enumerate() {
        join_shared.push(take.clone());
        let hacc = format_ident!("__tsm_hacc_{}", i);
        if i == 0 {
            join_shared.push(quote! {let tracked #shared_ident = #obs; let ghost #hacc = #shared_ident.fragment();});
        } else {
            join_shared.push(quote! {let tracked #shared_ident = #shared_ident.join(&#obs); let ghost #hacc = #shared_ident.fragment();});
        }
    }
    // Deposits: storage inputs.
    let mut deposits = vec![];
    let mut deposit_spec = store.empty();
    let mut withdrawals = vec![];
    for q in &params {
        let f = q.field;
        if !f.stype.is_storage() {
            continue;
        }
        let pname = &q.p.name;
        let elt = q.p.elt.as_ref().unwrap();
        match (q.p.inout_type, elt) {
            (InoutType::In, MonoidElt::SingletonKV(k, _)) => {
                let key = store.key_of(f, Some(k));
                let val = store.wrap(f, quote! {#pname});
                deposits.push(in_body(quote! {__tsm_deposit.tracked_insert(#key, #val);}));
                deposit_spec = quote! {#deposit_spec.insert(#key, #val)};
            }
            (InoutType::In, MonoidElt::OptionSome(_)) => {
                let key = store.key_of(f, None);
                let val = store.wrap(f, quote! {#pname});
                deposits.push(quote! {__tsm_deposit.tracked_insert(#key, #val);});
                deposit_spec = quote! {#deposit_spec.insert(#key, #val)};
            }
            (InoutType::In, MonoidElt::General(_)) => {
                let pack = store.pack(f, &quote! {#pname});
                deposits.push(quote! {
                    #pack
                    __tsm_deposit.tracked_union_prefer_right(__tsm_packed);
                });
                let tagged = store.tagged(f, &quote! {#pname});
                deposit_spec = quote! {#deposit_spec.union_prefer_right(#tagged)};
            }
            (InoutType::Out, MonoidElt::SingletonKV(k, _)) => {
                let key = store.key_of(f, Some(k));
                let unwrap = store.unwrap(f, pname);
                withdrawals.push(in_body(quote! {
                    let tracked #pname = __tsm_withdrawn.tracked_remove(#key);
                    #unwrap
                }));
            }
            (InoutType::Out, MonoidElt::OptionSome(_)) => {
                let key = store.key_of(f, None);
                let unwrap = store.unwrap(f, pname);
                withdrawals.push(in_body(quote! {
                    let tracked #pname = __tsm_withdrawn.tracked_remove(#key);
                    #unwrap
                }));
            }
            (InoutType::Out, MonoidElt::General(e)) => {
                withdrawals.push(in_body(store.unpack(f, pname, &quote! {#e})));
            }
            _ => return err(f.name.span(), "unsupported storage operation for generic field tokens"),
        }
    }
    let deposit_spec_helper = in_helper(deposit_spec.clone());
    let withdrawn_binds_helper: Vec<_> = withdrawn_binds.iter().map(|b| in_helper(b.clone())).collect();
    let withdrawn_binds_body: Vec<_> = withdrawn_binds.iter().map(|b| in_body(b.clone())).collect();
    let deposit_spec_body = in_body(deposit_spec.clone());
    let deposits: Vec<_> = deposits.into_iter().map(|d| in_body(d)).collect();
    let reqs_name = format_ident!("{}_requires", tr.name);
    let witness = format_ident!("{}_witness", tr.name);
    let frame_fn = format_ident!("{}_frame", tr.name);
    let outputs_fn = format_ident!("{}_outputs", tr.name);
    let owned_post_fn = format_ident!("{}_owned_post", tr.name);
    let strong = format_ident!("{}_strong", tr.name);
    let enabled = format_ident!("{}_enabled", tr.name);
    let deposited = format_ident!("{}_deposited", tr.name);
    let owners = format_ident!("{}_owners_enabled", tr.name);
    let safety = format_ident!("{}_safety", tr.name);
    let h = if has_shared { quote! {__tsm_hv} } else { quote! {Fragment::unit()} };
    let h_param = format_ident!("__tsm_h", span = Span::mixed_site());
    let lemmas = quote! {broadcast use {::vstd::map::group_map_lemmas, ::vstd::set::group_set_lemmas,
        ::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas, ::vstd::multiset::group_multiset_axioms};};
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
    let frames_at: Vec<_> = incl_frames_body
        .iter()
        .map(|(frag, lemma)| {
            let frag = in_body(frag.clone());
            let lemma = in_body(lemma.clone());
            quote! {{
                let __tsm_c = choose|__tsm_c: Fragment| Fragment::op(#frag, __tsm_c) == Fragment::op(#owned_ident, #h);
                assert(Fragment::op(#frag, __tsm_c) == Fragment::op(#owned_ident, #h));
                #lemma
            }}
        })
        .collect();
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
    let shared_body: Vec<_> = shared_frags_body.iter().map(|s| in_body(s.clone())).collect();
    let incl = inclusions(&owned_frags_body, &shared_body, &h, &owned_ident);
    let ret_vals: Vec<_> = parts
        .out_params
        .iter()
        .map(|o| {
            let n = &o.0;
            match o.2 {
                Mode::Ghost => quote! {Ghost(#n)},
                Mode::Tracked => quote! {Tracked(#n)},
            }
        })
        .collect();
    let result = match parts.out_params.len() {
        0 => quote! {},
        1 => {
            let n = &parts.out_params[0].0;
            quote! {#n}
        }
        _ => quote! {(#(#ret_vals),*)},
    };
    // Output tokens: split the new fragment.
    let mut outs: Vec<(TokenStream, TokenStream, TokenStream)> = vec![];
    for q in &params {
        let f = q.field;
        if f.stype.is_storage() || !matches!(q.p.inout_type, InoutType::Out | InoutType::InOut) {
            continue;
        }
        let pname = &q.p.name;
        let ty = tyname(f);
        let factory = format_ident!("field_{}", f.name);
        // With constants, each new token gets its own copy of `κ`.
        let (kp, from_args, split_args) = match cm {
            None => (quote! {}, quote! {}, quote! {}),
            Some(cm) => {
                let kappa = cm.kappa(quote! {self.__desc});
                (
                    quote! {
                        Fragment::unit().op_unit();
                        assert(__tsm_kappa.fragment() == Fragment::op(#kappa, #kappa));
                        let tracked (__tsm_kp, __tsm_kappa) = __tsm_kappa.split(#kappa, #kappa);
                    },
                    quote! {__tsm_kp, self.__desc,},
                    quote! {, __tsm_kp, self.__desc},
                )
            }
        };
        if q.p.inout_type == InoutType::InOut {
            let Some(e) = parts.var_updates.get(&f.name.to_string()) else {
                return err(f.name.span(), "internal: missing variable update");
            };
            let eh = in_helper(quote! {#e});
            let eb = in_body(quote! {#e});
            let new = format_ident!("__tsm_new_{}", pname);
            outs.push((
                quote! {Fragment::#factory(#eh)},
                quote! {Fragment::#factory(#eb)},
                quote! {
                    #kp
                    let tracked mut #new = #ty::__from_raw(__tsm_piece, #from_args #eb);
                    ::vstd::modes::tracked_swap(#pname, &mut #new);
                },
            ));
            continue;
        }
        let elt = q.p.elt.as_ref().unwrap();
        if q.p.is_collection {
            let MonoidElt::General(e) = elt else {
                return err(f.name.span(), "unsupported collection output for generic field tokens");
            };
            let split = format_ident!("__split_{}", f.name);
            let k = kind(f).unwrap();
            let (mtok, stok) = if k.infinite() {
                (quote! {::vstd::tokens::IMapToken}, quote! {::vstd::tokens::ISetToken})
            } else {
                (quote! {::vstd::tokens::MapToken}, quote! {::vstd::tokens::SetToken})
            };
            let mk = if k.map_like() {
                quote! {
                    #kp
                    let tracked #pname = #mtok::from_map((*self).id(), #ty::#split(__tsm_piece, #e #split_args));
                    assert(::vstd::prelude::ext_equal(#pname.map(), #e));
                }
            } else if k.set_like() {
                quote! {
                    #kp
                    let tracked #pname = #stok::from_map((*self).id(), #ty::#split(__tsm_piece, #e #split_args));
                    assert(::vstd::prelude::ext_equal(#pname.set(), #e));
                }
            } else if k == Kind::Multiset || k.option_like() {
                quote! {#kp let tracked #pname = #ty::#split(__tsm_piece, #e #split_args);}
            } else {
                return err(f.name.span(), "unsupported collection output for generic field tokens");
            };
            let fr = quote! {Fragment::#factory(#e)};
            outs.push((in_helper(fr.clone()), in_body(fr), in_body(mk)));
            continue;
        }
        let data: Vec<TokenStream> = match (kind(f).unwrap(), elt) {
            (k, MonoidElt::SingletonKV(kk, Some(v))) if k.map_like() => vec![quote! {#kk}, quote! {#v}],
            (k, MonoidElt::SingletonSet(e)) if k.set_like() => vec![quote! {#e}],
            (Kind::Multiset, MonoidElt::SingletonMultiset(e)) => vec![quote! {#e}],
            (Kind::Bool | Kind::PersistentBool, MonoidElt::True) => vec![],
            (Kind::Option | Kind::PersistentOption, MonoidElt::OptionSome(Some(v))) => vec![quote! {#v}],
            (Kind::Count, MonoidElt::General(n)) => vec![quote! {#n}],
            (Kind::PersistentCount, MonoidElt::General(n)) => vec![quote! {#n}, quote! {#n}],
            _ => return err(f.name.span(), "unsupported output element for generic field tokens"),
        };
        let fr = single_fragment(f, &data);
        outs.push((
            in_helper(fr.clone()),
            in_body(fr),
            in_body(quote! {#kp let tracked #pname = #ty::__from_raw(__tsm_piece, #from_args #(#data),*);}),
        ));
    }
    let expected_helper = outs.iter().rev().fold(quote! {Fragment::unit()}, |acc, (fr, _, _)| quote! {Fragment::op(#fr, #acc)});
    let expected_body = outs.iter().rev().fold(quote! {Fragment::unit()}, |acc, (_, fr, _)| quote! {Fragment::op(#fr, #acc)});
    let ext: Vec<_> = sm.fields.iter().map(|f| ext_step(f, &quote! {__tsm_out_frag}, &quote! {__tsm_expected})).collect();
    let mut splits = vec![];
    for (i, (_, fr, mk)) in outs.iter().enumerate() {
        let tail = outs[i + 1..].iter().rev().fold(quote! {Fragment::unit()}, |acc, (_, fr2, _)| quote! {Fragment::op(#fr2, #acc)});
        splits.push(quote! {
            let tracked (__tsm_piece, __tsm_left) = __tsm_left.split(#fr, #tail);
            #mk
        });
    }
    let has_deposit = params.iter().any(|q| q.field.stype.is_storage() && q.p.inout_type == InoutType::In);
    let has_withdraw = params.iter().any(|q| q.field.stype.is_storage() && q.p.inout_type == InoutType::Out);
    let map_ty = store.map_ty();
    let call = match (store.has(), has_shared) {
        (true, true) => quote! {
            Protocol::#frame_fn(#owned_ident, #h, __tsm_deposit, #(#pn),*);
            let __tsm_outputs = ::vstd::iset::ISet::new(|__tsm_pair: (Fragment, #map_ty)|
                Protocol::#outputs_fn(#owned_ident, #h, __tsm_pair.0, __tsm_deposit, __tsm_pair.1, #(#pn),*));
            let tracked (__tsm_out, __tsm_withdrawn) =
                __tsm_acc.exchange_nondeterministic_with_observation(&#shared_ident, __tsm_deposit, __tsm_outputs);
        },
        (true, false) => {
            // The raw protocol operation does the frame and output lifting in its
            // own context.
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
                    let tracked __tsm_withdrawn: #map_ty = ::vstd::imap::IMap::tracked_empty();
                }
            }
        }
        (false, true) => quote! {
            Protocol::#frame_fn(#owned_ident, #h, #(#pn),*);
            let __tsm_outputs = ::vstd::iset::ISet::new(|__tsm_new: Fragment|
                Protocol::#outputs_fn(#owned_ident, #h, __tsm_new, #(#pn),*));
            let tracked __tsm_out = __tsm_acc.update_nondeterministic_with_observation(&#shared_ident, __tsm_outputs);
        },
        (false, false) => {
            let raw = &tr.name;
            quote! {
                #owned_ident.op_unit();
                let tracked __tsm_out = Protocol::#raw(__tsm_acc, #(#pn),*);
            }
        }
    };
    // Spec copies of the inputs, bound before any token is consumed.
    let mut ghost_binds = vec![];
    let mut ghost_args = vec![];
    let mut ghost_params = vec![];
    for q in &params {
        if matches!(q.p.inout_type, InoutType::In | InoutType::BorrowIn | InoutType::InOut) {
            let pname = &q.p.name;
            let gname = format_ident!("__tsm_ghost_{}", pname);
            let ty = &q.p.ty;
            if matches!(q.p.inout_type, InoutType::BorrowIn | InoutType::InOut) {
                ghost_binds.push(quote! {let ghost #gname = *#pname;});
            } else {
                ghost_binds.push(quote! {let ghost #gname = #pname;});
            }
            ghost_args.push(quote! {#gname});
            ghost_params.push(quote! {#pname: #ty});
        }
    }
    let use_invs: Vec<_> = params
        .iter()
        .filter(|q| kind(q.field) == Some(Kind::PersistentCount) && q.p.inout_type == InoutType::BorrowIn)
        .map(|q| {
            let pname = &q.p.name;
            quote! {::vstd::prelude::use_type_invariant(#pname);}
        })
        .collect();
    let tparams: Vec<_> = tr
        .params
        .iter()
        .map(|p| {
            let (n, t) = (&p.name, &p.ty);
            quote! {#n: #t}
        })
        .collect();
    let post_fn = format_ident!("__tsm_post_{}", tr.name);
    // Facts about withdrawn storage, for the withdrawal outputs.
    let mut withdraw_facts = vec![];
    for q in &params {
        let f = q.field;
        if !f.stype.is_storage() || q.p.inout_type != InoutType::Out {
            continue;
        }
        match q.p.elt.as_ref() {
            Some(MonoidElt::SingletonKV(k, Some(v))) => {
                let key = store.key_of(f, Some(k));
                let val = store.wrap(f, quote! {#v});
                withdraw_facts.push(quote! {__tsm_withdrawn.contains_key(#key) && __tsm_withdrawn[#key] == #val})
            }
            Some(MonoidElt::SingletonKV(k, None)) => {
                let key = store.key_of(f, Some(k));
                let fname = &f.name;
                let variant = if store.kind == StoreKind::Carrier { quote! {&& __tsm_withdrawn[#key] is #fname} } else { quote! {} };
                withdraw_facts.push(quote! {__tsm_withdrawn.contains_key(#key) #variant})
            }
            Some(MonoidElt::OptionSome(Some(v))) => {
                let key = store.key_of(f, None);
                let val = store.wrap(f, quote! {#v});
                withdraw_facts.push(quote! {__tsm_withdrawn.contains_key(#key) && __tsm_withdrawn[#key] == #val})
            }
            Some(MonoidElt::OptionSome(None)) => {
                let key = store.key_of(f, None);
                let fname = &f.name;
                let variant = if store.kind == StoreKind::Carrier { quote! {&& __tsm_withdrawn[#key] is #fname} } else { quote! {} };
                withdraw_facts.push(quote! {__tsm_withdrawn.contains_key(#key) #variant})
            }
            Some(MonoidElt::General(e)) => withdraw_facts.push(store.withdraw_general_fact(f, &quote! {#e})),
            _ => {}
        }
    }
    let withdraw_facts: Vec<_> = withdraw_facts.into_iter().map(|w| in_helper(w)).collect();
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
            (Some(kd), MonoidElt::SingletonKV(k, Some(v)), false) if kd.map_like() => quote! {#pname.__k == #k && #pname.__v == #v},
            (Some(kd), MonoidElt::SingletonKV(k, None), false) if kd.map_like() => quote! {#pname.__k == #k},
            (Some(kd), MonoidElt::SingletonSet(e), false) if kd.set_like() => quote! {#pname.__e == #e},
            (Some(Kind::Multiset), MonoidElt::SingletonMultiset(e), false) => quote! {#pname.__e == #e},
            (Some(Kind::Option | Kind::PersistentOption), MonoidElt::OptionSome(Some(v)), false) => quote! {#pname.__v == #v},
            (Some(Kind::Count | Kind::PersistentCount), MonoidElt::General(n), false) => quote! {#pname.__n == #n},
            _ => continue,
        };
        match_conds.push(in_helper(quote! {({ #(#early)* #cond })}));
    }
    let owned_chain = if owned_frags.is_empty() {
        quote! {Fragment::unit()}
    } else {
        let mut it = owned_frags.iter();
        let first = it.next().unwrap().clone();
        it.fold(first, |acc, o| quote! {Fragment::op(#acc, #o)})
    };
    let incl_reqs: Vec<_> = incl_frames
        .iter()
        .map(|(frag, _)| {
            quote! {
                ::vstd::resource::tsm::fragment_included::<Protocol>(#frag, Fragment::op(#owned_ident, #h_param))
            }
        })
        .collect();
    let frames_post: Vec<_> = incl_frames
        .iter()
        .map(|(frag, lemma)| {
            quote! {{
                let __tsm_c = choose|__tsm_c: Fragment| Fragment::op(#frag, __tsm_c) == Fragment::op(#owned_ident, #h_param);
                assert(Fragment::op(#frag, __tsm_c) == Fragment::op(#owned_ident, #h_param));
                #lemma
            }}
        })
        .collect();
    // Borrowed fragments are included in `h` itself, which separates them
    // from the owned fragment.
    let shared_incl_reqs: Vec<_> = shared_frags
        .iter()
        .map(|sf| quote! {::vstd::resource::tsm::fragment_included::<Protocol>(#sf, #h_param)})
        .collect();
    let shared_steps: Vec<_> = shared_frags
        .iter()
        .map(|sf| {
            quote! {{
                let __tsm_d = choose|__tsm_d: Fragment| Fragment::op(#sf, __tsm_d) == #h_param;
                assert(Fragment::op(#sf, __tsm_d) == #h_param);
            }}
        })
        .collect();
    let frames_ready: Vec<_> = shared_steps.iter().cloned().chain(frames_post.iter().cloned()).collect();
    let ready_fn = format_ident!("__tsm_ready_{}", tr.name);
    let api_reqs: Vec<_> = parts.reqs.iter().map(|r| in_helper(quote! {#r})).collect();
    let (dep_param, dep_arg, dep_req, dep_goal, dep_ext) = if store.has() {
        (
            quote! {__tsm_deposit: #map_ty},
            quote! {__tsm_deposit},
            quote! {({ #(#early_helper)* __tsm_deposit == #deposit_spec_helper }),},
            quote! {&& __tsm_deposit == State::#deposited(pre, #(#pn),*)},
            quote! {assert(::vstd::prelude::ext_equal(__tsm_deposit, State::#deposited(pre, #(#pn),*)));},
        )
    } else {
        (quote! {}, quote! {}, quote! {}, quote! {}, quote! {})
    };
    let dep_comma = if store.has() { quote! {,} } else { quote! {} };
    // The facts about `op(owned, h)` outside the completion quantifier
    // (ownership of read and updated variables) come from one completion.
    let (ready_req, ready_pre) = if has_shared {
        (
            quote! {::vstd::resource::tsm::completes::<Protocol>(Fragment::op(#owned_ident, #h_param)),},
            quote! {{
                let (__tsm_z, pre) = choose|__tsm_z: Fragment, pre: State| pre.invariant()
                    && Fragment::op(Fragment::op(#owned_ident, #h_param), __tsm_z) == <Protocol as ::vstd::resource::tsm::Machine>::embed(pre);
                #(#frames_ready)*
            }},
        )
    } else {
        (quote! {#h_param == Fragment::unit(),}, quote! {#owned_ident.op_unit();})
    };
    // A deposit may depend on a transition's `assert`s (the API's precondition
    // then only constrains it under them), which hold by the safety lemma.
    let ready_safety = if store.has() && has_assert(&tr.body) {
        quote! {State::#safety(pre, #(#pn),*);}
    } else {
        quote! {}
    };
    let ready = quote! {
        #[verifier::spinoff_prover]
        proof fn #ready_fn(&self, #(#ghost_params,)* #(#tparams,)* #owned_ident: Fragment, #h_param: Fragment #dep_comma #dep_param)
            requires
                #(#api_reqs,)*
                #(#extra_reqs,)*
                #owned_ident == #owned_chain,
                #(#incl_reqs,)*
                #(#shared_incl_reqs,)*
                #ready_req
                #dep_req
            ensures Protocol::#reqs_name(#owned_ident, #h_param, #dep_arg #dep_comma #(#pn),*),
        {
            hide(State::invariant);
            #lemmas
            #(#early_helper)*
            #ready_pre
            assert forall|__tsm_z: Fragment, pre: State| pre.invariant()
                && Fragment::op(Fragment::op(#owned_ident, #h_param), __tsm_z) == <Protocol as ::vstd::resource::tsm::Machine>::embed(pre)
                implies State::#enabled(pre, #(#pn),*)
                    #dep_goal
                    && State::#owners(pre, #owned_ident, #h_param, #(#pn),*) by {
                #(#frames_ready)*
                #ready_safety
                #dep_ext
            }
        }
    };
    let (post_store_params, _post_store_args, witness_call) = if store.has() {
        (
            quote! {__tsm_deposit: #map_ty, __tsm_withdrawn: #map_ty,},
            quote! {__tsm_deposit, __tsm_withdrawn,},
            quote! {
                let (pre, post, __tsm_z) = Protocol::#witness(#owned_ident, #h_param, __tsm_out_frag, __tsm_deposit, __tsm_withdrawn, #(#pn),*);
            },
        )
    } else {
        (
            quote! {},
            quote! {},
            quote! {
                let (__tsm_z, pre, post) = choose|__tsm_z: Fragment, pre: State, post: State| pre.invariant()
                    && Fragment::op(Fragment::op(#owned_ident, #h_param), __tsm_z) == <Protocol as ::vstd::resource::tsm::Machine>::embed(pre)
                    && State::#strong(pre, post, #(#pn),*) && post.invariant()
                    && __tsm_out_frag == Protocol::#owned_post_fn(#owned_ident, pre, post, #(#pn),*)
                    && Fragment::op(Fragment::op(__tsm_out_frag, #h_param), __tsm_z) == <Protocol as ::vstd::resource::tsm::Machine>::embed(post);
            },
        )
    };
    let outputs_req = if store.has() {
        quote! {Protocol::#outputs_fn(#owned_ident, #h_param, __tsm_out_frag, __tsm_deposit, __tsm_withdrawn, #(#pn),*)}
    } else {
        quote! {Protocol::#outputs_fn(#owned_ident, #h_param, __tsm_out_frag, #(#pn),*)}
    };
    let helper = quote! {
        #ready
        #[verifier::spinoff_prover]
        proof fn #post_fn(&self, #(#ghost_params,)* #(#tparams,)* #owned_ident: Fragment, #h_param: Fragment,
            __tsm_out_frag: Fragment, #post_store_params)
            -> (__tsm_r: (State, State, Fragment))
            requires
                #outputs_req,
                #(#extra_reqs,)*
                #owned_ident == #owned_chain,
                #(#incl_reqs,)*
                #(#match_conds,)*
            ensures
                __tsm_r.0.invariant(),
                Fragment::op(Fragment::op(#owned_ident, #h_param), __tsm_r.2)
                    == <Protocol as ::vstd::resource::tsm::Machine>::embed(__tsm_r.0),
                ({
                let pre = __tsm_r.0;
                #(#early_actual_helper)*
                #(#withdrawn_binds_helper)*
                #(#nondet)*
                #(#late_helper)*
                __tsm_out_frag == #expected_helper #(&& #withdraw_facts)*
            }),
        {
            hide(State::invariant);
            #lemmas
            #witness_call
            #(#frames_post)*
            #(#early_actual_helper)*
            #(#withdrawn_binds_helper)*
            #(#nondet)*
            #(#late_helper)*
            let __tsm_expected = #expected_helper;
            assert(__tsm_out_frag == __tsm_expected) by {
                #(#ext)*
            }
            #(assert(#withdraw_facts);)*
            (pre, post, __tsm_z)
        }
    };
    let deposit_stmts = if store.has() {
        quote! {
            let tracked mut __tsm_deposit: #map_ty = ::vstd::imap::IMap::tracked_empty();
            #(#deposits)*
            assert(__tsm_deposit == #deposit_spec_body);
        }
    } else {
        quote! {}
    };
    let withdraw_stmts = if store.has() {
        quote! {
            let tracked mut __tsm_withdrawn = __tsm_withdrawn;
            #(#withdrawals)*
        }
    } else {
        quote! {}
    };
    let validate_shared = if has_shared {
        quote! {
            let tracked mut __tsm_acc = __tsm_acc;
            __tsm_acc.validate_with_observation(&#shared_ident);
        }
    } else {
        quote! {}
    };
    let bind_h = if has_shared { quote! {let ghost __tsm_hv = #shared_ident.fragment();} } else { quote! {} };
    let post_args = if store.has() { quote! {__tsm_deposit, __tsm_withdrawn} } else { quote! {} };
    // The trusted macro's specifications use the old `&mut` postcondition style.
    let mut_style = if inouts.is_empty() {
        quote! {}
    } else {
        quote! {#[verifier::deprecated_postcondition_mut_ref_style(true)]}
    };
    Ok(quote! {
        #helper
        #[verifier::spinoff_prover]
        #mut_style
        pub proof fn #name #gen (#(#in_params),*) #ret #req #ens {
            hide(State::invariant);
            #lemmas
            #(#ghost_binds)*
            #(#use_invs)*
            ::vstd::prelude::use_type_invariant(self);
            #(#early_body)*
            #(#join_owned)*
            #(#join_shared)*
            #bind_h
            let #owned_ident = __tsm_acc.fragment();
            #incl
            #deposit_stmts
            #validate_shared
            self.#ready_fn(#(#ghost_args,)* #(#pn,)* #owned_ident, #h #dep_comma #dep_arg);
            #call
            let (pre, post, __tsm_z) = self.#post_fn(#(#ghost_args,)* #(#pn,)*
                #owned_ident, #h, __tsm_out.fragment(), #post_args);
            #safety_after
            #(#early_actual_body)*
            #(#withdrawn_binds_body)*
            #(#nondet)*
            #(#late_body)*
            let __tsm_expected = #expected_body;
            assert(__tsm_out.fragment() == __tsm_expected);
            let tracked __tsm_left = __tsm_out;
            #(#splits)*
            #withdraw_stmts
            #result
        }
    })
}

/// A borrowed-tokens-only operation: its facts hold in any completion state.
#[allow(clippy::too_many_arguments)]
fn read_only_method(
    ctx: &Ctx,
    tr: &Transition,
    parts: &ExchangeParts,
    take_shared: &[(Ident, TokenStream)],
    incl_frames: &[(TokenStream, TokenStream)],
    shared_frags: &[TokenStream],
    ret: TokenStream,
    req: TokenStream,
    ens: TokenStream,
    early: &[TokenStream],
    late: &[TokenStream],
) -> Result<TokenStream, Error> {
    let sm = ctx.sm;
    let name = &parts.exch_name;
    let in_params = &parts.in_params;
    let gen = if parts.use_explicit_lifetime { quote! {<'a>} } else { quote! {} };
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let shared_ident = format_ident!("__tsm_shared", span = Span::mixed_site());
    let t = quote! {::vstd::resource::tsm};
    let safety = format_ident!("{}_safety", tr.name);
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
    let ret_vals: Vec<_> = parts
        .out_params
        .iter()
        .map(|o| {
            let n = &o.0;
            quote! {Ghost(#n)}
        })
        .collect();
    let result = match parts.out_params.len() {
        0 => quote! {},
        1 => quote! {#(#ret_vals)*},
        _ => quote! {(#(#ret_vals),*)},
    };
    if take_shared.is_empty() {
        // Nothing observed: the facts must hold in every reachable state, which
        // needs a token of the instance; this form is not supported.
        return err(tr.name.span(), "generic field tokens: a property must read at least one token or constant");
    }
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
    let frames_at: Vec<_> = incl_frames
        .iter()
        .map(|(frag, lemma)| {
            quote! {{
                let __tsm_c = choose|__tsm_c: Fragment| Fragment::op(#frag, __tsm_c) == #shared_ident.fragment();
                assert(Fragment::op(#frag, __tsm_c) == #shared_ident.fragment());
                #lemma
            }}
        })
        .collect();
    let use_invs = quote! {};
    Ok(quote! {
        #[verifier::spinoff_prover]
        pub proof fn #name #gen (#(#in_params),*) #ret #req #ens {
            hide(State::invariant);
            broadcast use {::vstd::map::group_map_lemmas, ::vstd::set::group_set_lemmas,
                ::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas, ::vstd::multiset::group_multiset_axioms};
            #use_invs
            ::vstd::prelude::use_type_invariant(self);
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

/// A storage guard: the guarded values are read from the borrowed tokens'
/// combined observation.
#[allow(clippy::too_many_arguments)]
fn guard_method(
    ctx: &Ctx,
    tr: &Transition,
    parts: &ExchangeParts,
    params: &[Param],
    take_shared: &[(Ident, TokenStream)],
    incl_frames: &[(TokenStream, TokenStream)],
    shared_frags: &[TokenStream],
    ret: TokenStream,
    req: TokenStream,
    ens: TokenStream,
    early: &[TokenStream],
) -> Result<TokenStream, Error> {
    let store = ctx.store;
    let span = tr.name.span();
    let name = &parts.exch_name;
    let in_params = &parts.in_params;
    let gen = if parts.use_explicit_lifetime { quote! {<'a>} } else { quote! {} };
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let t = quote! {::vstd::resource::tsm};
    let reqs_name = format_ident!("{}_requires", tr.name);
    let enabled = format_ident!("{}_enabled", tr.name);
    let owners = format_ident!("{}_owners_enabled", tr.name);
    let frame_fn = format_ident!("{}_frame", tr.name);
    let guarded = format_ident!("{}_guarded", tr.name);
    let shared_ident = format_ident!("__tsm_shared", span = Span::mixed_site());
    if take_shared.is_empty() {
        return err(span, "generic field tokens support guards with at least one borrowed token");
    }
    let mut joins = vec![];
    for (i, (obs, take)) in take_shared.iter().enumerate() {
        joins.push(take.clone());
        if i == 0 {
            joins.push(quote! {let tracked #shared_ident = #obs;});
        } else {
            joins.push(quote! {let tracked #shared_ident = #shared_ident.join(&#obs);});
        }
    }
    let hs: Vec<Ident> = (0..shared_frags.len()).map(|i| format_ident!("__tsm_hacc_{}", i)).collect();
    let mut incl = vec![];
    // Re-run the joins with ghost accumulators for the inclusion chain.
    let mut joins2 = vec![];
    for (i, (obs, take)) in take_shared.iter().enumerate() {
        let hacc = &hs[i];
        joins2.push(take.clone());
        if i == 0 {
            joins2.push(quote! {let tracked #shared_ident = #obs; let ghost #hacc = #shared_ident.fragment();});
        } else {
            joins2.push(quote! {let tracked #shared_ident = #shared_ident.join(&#obs); let ghost #hacc = #shared_ident.fragment();});
        }
    }
    let _ = joins;
    for (i, sf) in shared_frags.iter().enumerate() {
        if i == 0 {
            incl.push(quote! {#t::fragment_included_reflexive::<Protocol>(#sf);});
        }
        for j in (i + 1)..shared_frags.len() {
            let (b, c) = (&hs[j - 1], &hs[j]);
            incl.push(quote! {#t::fragment_included_transitive::<Protocol>(#sf, #b, #c);});
        }
    }
    let frames: Vec<_> = incl_frames
        .iter()
        .map(|(frag, lemma)| {
            quote! {{
                let __tsm_c = choose|__tsm_c: Fragment| Fragment::op(#frag, __tsm_c) == __tsm_f;
                assert(Fragment::op(#frag, __tsm_c) == __tsm_f);
                #lemma
            }}
        })
        .collect();
    let mut guards = vec![];
    for q in params {
        let f = q.field;
        if q.p.inout_type != InoutType::BorrowOut {
            continue;
        }
        let pname = &q.p.name;
        let fname = &f.name;
        match (&store.kind, q.p.elt.as_ref()) {
            (StoreKind::Carrier, Some(MonoidElt::SingletonKV(k, _))) => {
                let borrow = format_ident!("__borrow_{}", fname);
                guards.push(quote! {let tracked #pname = __StorageKey::#borrow(__tsm_guard, #k).tracked_unwrap();})
            }
            (StoreKind::Carrier, Some(MonoidElt::OptionSome(_))) => {
                let borrow = format_ident!("__borrow_{}", fname);
                guards.push(quote! {let tracked #pname = __StorageKey::#borrow(__tsm_guard).tracked_unwrap();})
            }
            (StoreKind::Plain, Some(MonoidElt::SingletonKV(k, _))) => {
                guards.push(quote! {let tracked #pname = __tsm_guard.tracked_borrow(#k);})
            }
            (StoreKind::Plain, Some(MonoidElt::OptionSome(_))) => {
                let i = store.option_index(f);
                guards.push(quote! {let tracked #pname = __tsm_guard.tracked_borrow(#i);})
            }
            _ => return err(f.name.span(), "unsupported storage guard for generic field tokens"),
        }
    }
    let ret_vals: Vec<_> = parts.out_params.iter().map(|o| o.0.clone()).collect();
    let result = if ret_vals.len() == 1 {
        quote! {#(#ret_vals)*}
    } else {
        return err(span, "generic field tokens support guards with one output");
    };
    Ok(quote! {
        #[verifier::spinoff_prover]
        pub proof fn #name #gen (#(#in_params),*) #ret #req #ens {
            broadcast use {::vstd::map::group_map_lemmas, ::vstd::set::group_set_lemmas,
                ::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas, ::vstd::multiset::group_multiset_axioms};
            ::vstd::prelude::use_type_invariant(self);
            #(#early)*
            #(#joins2)*
            #(#incl)*
            let __tsm_f = #shared_ident.fragment();
            #shared_ident.validate();
            {
                let (__tsm_z, pre) = choose|__tsm_z: Fragment, pre: State| pre.invariant()
                    && Fragment::op(__tsm_f, __tsm_z) == <Protocol as ::vstd::resource::tsm::Machine>::embed(pre);
                #(#frames)*
            }
            assert(Protocol::#reqs_name(__tsm_f, #(#pn),*)) by {
                assert forall|__tsm_z: Fragment, pre: State| pre.invariant()
                    && Fragment::op(__tsm_f, __tsm_z) == <Protocol as ::vstd::resource::tsm::Machine>::embed(pre)
                    implies State::#owners(pre, __tsm_f, Fragment::unit(), #(#pn),*) && State::#enabled(pre, #(#pn),*) by {
                    #(#frames)*
                }
            }
            Protocol::#frame_fn(__tsm_f, #(#pn),*);
            let tracked __tsm_guard = #shared_ident.guard(Protocol::#guarded(__tsm_f, #(#pn),*));
            #(#guards)*
            #result
        }
    })
}

fn init_method(
    bundle: &SMBundle,
    ctx: &Ctx,
    tr: &Transition,
    parts: &ExchangeParts,
    ret: TokenStream,
    req: TokenStream,
    ens: TokenStream,
) -> Result<TokenStream, Error> {
    let sm = &bundle.sm;
    let store = ctx.store;
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
        let arg = format_ident!("param_token_{}", f.name);
        let pack = store.pack(f, &quote! {#arg});
        deposits.push(quote! {
            #pack
            __tsm_base.tracked_union_prefer_right(__tsm_packed);
        });
    }
    let cm = ctx.cm;
    let id = if cm.is_some() {
        quote! {::vstd::resource::tsm_instance_id(__tsm_desc.loc(), false)}
    } else {
        quote! {::vstd::resource::tsm_instance_id(__tsm_all.loc(), false)}
    };
    let mut takes = vec![];
    // With constants: take their pieces first, join them into `κ`, and
    // allocate the descriptor; every token then gets a copy of `κ`.
    let (kp, from_args, split_args) = match cm {
        None => (quote! {}, quote! {}, quote! {}),
        Some(cm) => {
            let mut pieces = vec![];
            for c in &cm.consts {
                let take = format_ident!("take_{}", c.name);
                let piece = format_ident!("__tsm_const_{}", c.name);
                takes.push(quote! {let tracked (#piece, __tsm_rest) = Protocol::#take(__tsm_rest);});
                pieces.push(piece);
            }
            let first = &pieces[0];
            takes.push(quote! {let tracked __tsm_kappa = #first;});
            for p in &pieces[1..] {
                takes.push(quote! {let tracked __tsm_kappa = __tsm_kappa.join(#p);});
            }
            let vals: Vec<_> = cm.consts.iter().map(|c| {
                let n = &c.name;
                quote! {post.#n}
            }).collect();
            let kappa = cm.kappa(quote! {__tsm_desc});
            takes.push(quote! {
                let tracked __tsm_desc = ::vstd::modes::tracked_static_ref(::vstd::resource::pcm::Resource::alloc(
                    Some(::vstd::resource::agree::AgreementRA::Agree(((#(#vals,)*), __tsm_all_loc)))));
                Fragment::unit().op_unit();
                assert(__tsm_kappa.fragment() == #kappa);
            });
            (
                quote! {
                    assert(__tsm_kappa.fragment() == Fragment::op(#kappa, #kappa));
                    let tracked (__tsm_kp, __tsm_kappa) = __tsm_kappa.split(#kappa, #kappa);
                },
                quote! {__tsm_kp, __tsm_desc,},
                quote! {, __tsm_kp, __tsm_desc},
            )
        }
    };
    for f in &sm.fields {
        let fname = &f.name;
        let arg = format_ident!("param_token_{}", fname);
        let take = format_ident!("take_{}", fname);
        let factory = format_ident!("field_{}", fname);
        let split = format_ident!("__split_{}", fname);
        let ty = tyname(f);
        let Some(k) = kind(f) else { continue };
        takes.push(quote! {let tracked (__tsm_piece, __tsm_rest) = Protocol::#take(__tsm_rest);});
        let value = quote! {post.#fname};
        let stmt = match k {
            k if k.map_like() || k.set_like() => {
                let coll = match (k.map_like(), k.infinite()) {
                    (true, false) => quote! {::vstd::tokens::MapToken::from_map},
                    (true, true) => quote! {::vstd::tokens::IMapToken::from_map},
                    (false, false) => quote! {::vstd::tokens::SetToken::from_map},
                    (false, true) => quote! {::vstd::tokens::ISetToken::from_map},
                };
                // An initial `imap`/`iset` collection must be finite to be split
                // into tokens.
                let finite = match (k.map_like(), k.infinite()) {
                    (true, true) => quote! {assert(#value.dom().finite());},
                    (false, true) => quote! {assert(#value.finite());},
                    _ => quote! {},
                };
                quote! {
                    #finite
                    assert(__tsm_piece.fragment() == Fragment::#factory(#value)) by {
                        ::vstd::resource::tsm_collections::Pointwise::extensionality(
                            __tsm_piece.fragment().#fname, Fragment::#factory(#value).#fname);
                    }
                    #kp
                    let tracked #arg = #coll(#id, #ty::#split(__tsm_piece, #value #split_args));
                }
            }
            Kind::Multiset | Kind::Option | Kind::PersistentOption | Kind::Bool | Kind::PersistentBool => quote! {
                assert(__tsm_piece.fragment() == Fragment::#factory(#value));
                #kp
                let tracked #arg = #ty::#split(__tsm_piece, #value #split_args);
            },
            Kind::Variable | Kind::Count => quote! {
                assert(__tsm_piece.fragment() == Fragment::#factory(#value));
                #kp
                let tracked #arg = #ty::__from_raw(__tsm_piece, #from_args #value);
            },
            Kind::PersistentCount => quote! {
                assert(__tsm_piece.fragment() == Fragment::#factory(#value));
                #kp
                let tracked #arg = #ty::__from_raw(__tsm_piece, #from_args #value, #value);
            },
            _ => unreachable!(),
        };
        takes.push(stmt);
    }
    let phantom = if sm.generics.is_some() && !ctx.base { quote! {, __tsm_phantom: ::core::marker::PhantomData} } else { quote! {} };
    let base_stmt = match (cm, ctx.base) {
        (None, true) => quote! {
            let tracked __tsm_base_tok = __tsm_rest.empty();
            let tracked instance = Instance {__loc: Ghost(__tsm_all_loc), __base: ::vstd::modes::tracked_static_ref(__tsm_base_tok)};
        },
        (None, false) => quote! {let tracked instance = Instance {__loc: Ghost(__tsm_all_loc) #phantom};},
        (Some(cm), true) => {
            let kappa = cm.kappa(quote! {__tsm_desc});
            quote! {
                assert(__tsm_kappa.fragment() == Fragment::op(#kappa, #kappa));
                let tracked (__tsm_base_tok, __tsm_kappa) = __tsm_kappa.split(#kappa, #kappa);
                let tracked instance = Instance {__desc: __tsm_desc, __base: ::vstd::modes::tracked_static_ref(__tsm_base_tok)};
            }
        }
        (Some(_), false) => quote! {let tracked instance = Instance {__desc: __tsm_desc #phantom};},
    };
    let ret_vals: Vec<_> = parts
        .out_params
        .iter()
        .map(|o| {
            let n = &o.0;
            quote! {Tracked(#n)}
        })
        .collect();
    let result = if ret_vals.len() == 1 { quote! {#(#ret_vals)*} } else { quote! {(#(#ret_vals),*)} };
    let result = if parts.out_params.len() == 1 {
        let n = &parts.out_params[0].0;
        quote! {#n}
    } else {
        result
    };
    let init_fn = &tr.name;
    let init_strong = format_ident!("{}_strong", tr.name);
    let (base_init, call) = if store.has() {
        let map_ty = store.map_ty();
        (
            quote! {
                let tracked mut __tsm_base: #map_ty = ::vstd::imap::IMap::tracked_empty();
                #(#deposits)*
                assert forall|__tsm_s: State| State::#init_strong(__tsm_s, #(#pn),*) implies __tsm_base == __tsm_s.__storage() by {
                    assert(::vstd::prelude::ext_equal(__tsm_base, __tsm_s.__storage()));
                }
            },
            quote! {let tracked __tsm_all = Protocol::#init_fn(__tsm_base, #(#pn),*);},
        )
    } else {
        (quote! {}, quote! {let tracked __tsm_all = Protocol::#init_fn(#(#pn),*);})
    };
    Ok(quote! {
        #[verifier::spinoff_prover]
        pub proof fn #name(#(#in_params),*) #ret #req #ens {
            broadcast use {::vstd::map::group_map_lemmas, ::vstd::set::group_set_lemmas,
                ::vstd::imap::group_imap_lemmas, ::vstd::iset::group_iset_lemmas, ::vstd::multiset::group_multiset_axioms};
            #(#early)*
            #base_init
            #call
            let post = choose|post: State| State::#init_fn(post, #(#pn),*) && post.invariant()
                && __tsm_all.fragment() == <Protocol as ::vstd::resource::tsm::Machine>::embed(post);
            let ghost __tsm_all_loc = __tsm_all.loc();
            let tracked __tsm_rest = __tsm_all;
            #(#takes)*
            #base_stmt
            #result
        }
    })
}

/// Store tokens' ghost data in `Ghost<..>` fields, so that persistent token
/// types are `Copy` for any data type: declarations `ghost d: T` become
/// `ghost d: Ghost<T>`, field reads `x.d` become `x.d@`, and field
/// initializers `d: e` (or `d`) become `d: Ghost(e)`. The data names are
/// generated (`__k`, `__v`, `__e`, `__n`, `__m`).
fn ghostify(ts: TokenStream, delim: proc_macro2::Delimiter) -> TokenStream {
    use proc_macro2::{Delimiter, Group, Punct, Spacing};
    let data = ["__k", "__v", "__e", "__n", "__m"];
    let trees: Vec<TokenTree> = ts.into_iter().collect();
    let punct = |t: Option<&TokenTree>, c: char| matches!(t, Some(TokenTree::Punct(p)) if p.as_char() == c);
    let mut out: Vec<TokenTree> = vec![];
    let mut i = 0;
    // The tokens up to the next top-level `,` (or the end).
    // The tokens up to the next `,` outside angle brackets (or the end).
    let until_comma = |j: usize| -> usize {
        let mut k = j;
        let mut depth = 0i32;
        while k < trees.len() {
            if let TokenTree::Punct(p) = &trees[k] {
                let arrow = p.as_char() == '>' && k > 0 && matches!(&trees[k - 1], TokenTree::Punct(q) if q.as_char() == '-');
                match p.as_char() {
                    ',' if depth == 0 => break,
                    '<' => depth += 1,
                    '>' if !arrow => depth -= 1,
                    _ => {}
                }
            }
            k += 1;
        }
        k
    };
    while i < trees.len() {
        if let TokenTree::Ident(id) = &trees[i] {
            if data.contains(&id.to_string().as_str()) {
                let prev = if i > 0 { trees.get(i - 1) } else { None };
                let next = trees.get(i + 1);
                let next2 = trees.get(i + 2);
                // A single `:` (a `::` path separator starts with a joint `:`).
                let is_field_colon = matches!(next, Some(TokenTree::Punct(p)) if p.as_char() == ':' && p.spacing() == Spacing::Alone);
                let _ = next2;
                if punct(prev, '.') {
                    out.push(trees[i].clone());
                    out.push(TokenTree::Punct(Punct::new('@', Spacing::Alone)));
                    i += 1;
                    continue;
                }
                if matches!(prev, Some(TokenTree::Ident(g)) if g == "ghost") && is_field_colon {
                    let end = until_comma(i + 2);
                    let ty: TokenStream = trees[i + 2..end].iter().cloned().collect();
                    let ty = ghostify(ty, Delimiter::None);
                    out.push(trees[i].clone());
                    out.extend(quote! {: ::vstd::prelude::Ghost<#ty>});
                    i = end;
                    continue;
                }
                let after_let = matches!(prev, Some(TokenTree::Ident(g)) if g == "let" || g == "mut");
                if delim == Delimiter::Brace && is_field_colon && !after_let {
                    let end = until_comma(i + 2);
                    let e: TokenStream = trees[i + 2..end].iter().cloned().collect();
                    let e = ghostify(e, Delimiter::None);
                    out.push(trees[i].clone());
                    out.extend(quote! {: Ghost(#e)});
                    i = end;
                    continue;
                }
                if delim == Delimiter::Brace
                    && (prev.is_none() || punct(prev, ','))
                    && (next.is_none() || punct(next, ','))
                {
                    let name = trees[i].clone();
                    out.push(name.clone());
                    out.extend(quote! {: Ghost(#name)});
                    i += 1;
                    continue;
                }
            }
        }
        match &trees[i] {
            TokenTree::Group(g) => {
                let mut ng = Group::new(g.delimiter(), ghostify(g.stream(), g.delimiter()));
                ng.set_span(g.span());
                out.push(TokenTree::Group(ng));
            }
            t => out.push(t.clone()),
        }
        i += 1;
    }
    out.into_iter().collect()
}

/// Resolve the token type placeholders of `tyname`.
fn resolve_types(ts: TokenStream, args: Option<&TokenStream>) -> TokenStream {
    let mut out = vec![];
    for t in ts {
        match t {
            TokenTree::Group(gr) => {
                let mut ng = proc_macro2::Group::new(gr.delimiter(), resolve_types(gr.stream(), args));
                ng.set_span(gr.span());
                out.push(TokenTree::Group(ng));
            }
            TokenTree::Ident(id) if id.to_string().starts_with("__TSM_TY_") => {
                let name = Ident::new(&id.to_string()["__TSM_TY_".len()..], id.span());
                match args {
                    None => out.push(TokenTree::Ident(name)),
                    Some(a) => out.extend(quote! {#name::<#a>}),
                }
            }
            t => out.push(t),
        }
    }
    out.into_iter().collect()
}

/// The machine's type parameters, applied to the generated items.
struct Gen {
    decl: TokenStream,
    wc: TokenStream,
    args: TokenStream,
    attrs: TokenStream,
    /// Generated generic types, whose bare uses get the machine's arguments.
    names: HashSet<String>,
}

/// Give every generated item the machine's type parameters: headers of
/// structs, type aliases and impls get the declaration and where clause, and
/// each bare use of a generated generic type gets `::<args>` (valid in both
/// type and expression position).
fn genericize(ts: TokenStream, g: &Gen) -> TokenStream {
    let trees: Vec<TokenTree> = ts.into_iter().collect();
    let mut out: Vec<TokenTree> = vec![];
    let mut i = 0;
    let is_ident = |t: &TokenTree, s: &str| matches!(t, TokenTree::Ident(id) if id == s);
    while i < trees.len() {
        let t = &trees[i];
        if is_ident(t, "impl") {
            // impl header up to the body.
            out.push(t.clone());
            out.extend(g.decl.clone());
            let mut header = vec![];
            i += 1;
            while i < trees.len() && !matches!(&trees[i], TokenTree::Group(gr) if gr.delimiter() == proc_macro2::Delimiter::Brace) {
                header.push(trees[i].clone());
                i += 1;
            }
            out.extend(turbofish(header.into_iter().collect(), g));
            out.extend(g.wc.clone());
            if i < trees.len() {
                if let TokenTree::Group(gr) = &trees[i] {
                    let mut ng = proc_macro2::Group::new(gr.delimiter(), turbofish(gr.stream(), g));
                    ng.set_span(gr.span());
                    out.push(TokenTree::Group(ng));
                }
            }
            i += 1;
            continue;
        }
        if is_ident(t, "struct") || is_ident(t, "type") {
            let alias = is_ident(t, "type");
            if !alias {
                // Datatype attributes go before the visibility and `tracked`.
                let mut moved = vec![];
                while let Some(TokenTree::Ident(id)) = out.last() {
                    if id == "pub" || id == "tracked" {
                        moved.push(out.pop().unwrap());
                    } else {
                        break;
                    }
                }
                out.extend(g.attrs.clone());
                out.extend(moved.into_iter().rev());
            }
            out.push(t.clone());
            if let Some(name) = trees.get(i + 1) {
                out.push(name.clone());
                out.extend(g.decl.clone());
            }
            i += 2;
            let mut rest = vec![];
            while i < trees.len() {
                let stop = matches!(&trees[i], TokenTree::Group(gr) if gr.delimiter() == proc_macro2::Delimiter::Brace && !alias)
                    || matches!(&trees[i], TokenTree::Punct(p) if p.as_char() == '=' && alias);
                if stop {
                    break;
                }
                rest.push(trees[i].clone());
                i += 1;
            }
            out.extend(turbofish(rest.into_iter().collect(), g));
            out.extend(g.wc.clone());
            continue;
        }
        match t {
            TokenTree::Group(gr) => {
                // Not an item header: rewrite uses.
                let mut ng = proc_macro2::Group::new(gr.delimiter(), turbofish(gr.stream(), g));
                ng.set_span(gr.span());
                out.push(TokenTree::Group(ng));
                i += 1;
            }
            _ => {
                let one: TokenStream = std::iter::once(t.clone()).collect();
                // Decide using the neighbours, as `turbofish` does.
                let window: TokenStream = trees[i.saturating_sub(2)..(i + 4).min(trees.len())].iter().cloned().collect();
                let _ = window;
                out.extend(turbofish_at(&trees, i, g).unwrap_or(one));
                i += 1;
            }
        }
    }
    out.into_iter().collect()
}

/// The rewrite of `trees[i]` if it is a bare use of a generated generic type.
fn turbofish_at(trees: &[TokenTree], i: usize, g: &Gen) -> Option<TokenStream> {
    let TokenTree::Ident(id) = &trees[i] else { return None };
    if !g.names.contains(&id.to_string()) {
        return None;
    }
    let punct = |j: usize, c: char| matches!(trees.get(j), Some(TokenTree::Punct(p)) if p.as_char() == c);
    if i >= 1 && punct(i - 1, '.') {
        return None;
    }
    if i >= 2 && punct(i - 1, ':') && punct(i - 2, ':') {
        return None;
    }
    if i >= 1 {
        if let TokenTree::Ident(prev) = &trees[i - 1] {
            if ["struct", "enum", "type", "fn", "mod", "trait", "use"].contains(&prev.to_string().as_str()) {
                return None;
            }
        }
    }
    if punct(i + 1, '<') || punct(i + 1, '!') {
        return None;
    }
    if punct(i + 1, ':') && punct(i + 2, ':') && punct(i + 3, '<') {
        return None;
    }
    let args = &g.args;
    Some(quote! {#id::<#args>})
}

fn turbofish(ts: TokenStream, g: &Gen) -> TokenStream {
    let trees: Vec<TokenTree> = ts.into_iter().collect();
    let mut out = vec![];
    for i in 0..trees.len() {
        // `hide`/`reveal` name the function by an untyped path.
        let after_hide = i >= 1 && matches!(&trees[i - 1], TokenTree::Ident(id) if id == "hide" || id == "reveal");
        match &trees[i] {
            TokenTree::Group(gr) if after_hide => out.push(TokenTree::Group(gr.clone())),
            TokenTree::Group(gr) => {
                let mut ng = proc_macro2::Group::new(gr.delimiter(), turbofish(gr.stream(), g));
                ng.set_span(gr.span());
                out.push(TokenTree::Group(ng));
            }
            t => match turbofish_at(&trees, i, g) {
                Some(r) => out.extend(r),
                None => out.push(t.clone()),
            },
        }
    }
    out.into_iter().collect()
}

/// Append items to the last `verus! { .. }` block inside the generated module,
/// without re-parsing the module.
pub fn append_tokens(output: TokenStream, api: TokenStream) -> Result<TokenStream, Error> {
    use proc_macro2::{Delimiter, Group};
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
