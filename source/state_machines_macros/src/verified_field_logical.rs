//! Genuine logical entry/element and bulk field owners over checked resources.
//! The root facade dispatcher appends these items inside the existing machine.
use crate::ast::{Field, ShardableType, TransitionKind, TransitionStmt, SM};
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

pub fn needed(sm: &SM) -> bool {
    (sm.fields.len() == 1 && matches!(sm.fields[0].stype, ShardableType::Count))
        || sm.fields.iter().any(|f| {
            crate::verified_field_collections::supported(&f.stype)
                || matches!(
                    f.stype,
                    ShardableType::Bool
                        | ShardableType::Option(..)
                        | ShardableType::PersistentOption(..)
                        | ShardableType::PersistentBool
                        | ShardableType::PersistentCount
                )
        })
}

pub(crate) struct Generics {
    decl: TokenStream,
    wc: TokenStream,
    attrs: Vec<verus_syn::Attribute>,
    pub(crate) types: TokenStream,
    pub(crate) expr: TokenStream,
}
pub(crate) fn generics(sm: &SM) -> Generics {
    let (generic, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generic);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    Generics {
        decl,
        wc,
        attrs,
        types: args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default(),
        expr: args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default(),
    }
}

pub(crate) fn fresh(sm: &SM, params: &[crate::ast::TransitionParam], label: &str) -> Ident {
    let unavailable: HashSet<_> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(params.iter().map(|p| p.name.to_string()))
        .collect();
    let mut name = format!("__tsm_logical_{label}");
    while unavailable.contains(&name) {
        name.push('_');
    }
    Ident::new(&name, Span::mixed_site())
}

/// Bulk wrappers share the approved checked methods; present entries/elements
/// always contain an actual sparse resource and never represent an absent slot.
pub fn collection_wrappers(sm: &SM) -> Result<TokenStream, Error> {
    let Generics {
        decl,
        wc,
        attrs,
        types,
        expr: _,
    } = generics(sm);
    let fragment = quote! {Fragment #types};
    let token = quote! {Token #types};
    let mut output = Vec::new();
    for field in sm
        .fields
        .iter()
        .filter(|f| crate::verified_field_collections::supported(&f.stype))
    {
        let name = &field.name;
        let bulk = format_ident!("{}_collection", name);
        let factory = format_ident!("field_{}", name);
        let native = field.get_type();
        let entry = quote! {#name #types};
        let methods = crate::verified_field_collections::methods(field, &fragment, &token, &entry)?;
        let persistent = if field.stype.is_persistent() {
            crate::verified_field_collections::persistent_collection_methods(field, &fragment)?
        } else {
            quote! {}
        };
        let entry_methods = if field.stype.is_persistent() {
            crate::verified_field_collections::entry_methods(field, &fragment)?
        } else {
            quote! {}
        };
        let (metadata, getters, ctor_params, singleton, ctor_metadata, ctor_ensures, view) =
            match &field.stype {
                ShardableType::Map(k, v)
                | ShardableType::IMap(k, v)
                | ShardableType::PersistentMap(k, v)
                | ShardableType::PersistentIMap(k, v) => (
                    quote! {(#k,#v)},
                    quote! {pub closed spec fn key(&self)->#k{self.native.0}
                    pub closed spec fn value(&self)->#v{self.native.1}},
                    quote! {key:#k,value:#v},
                    quote! {<#native>::empty().insert(key,value)},
                    quote! {(key,value)},
                    quote! {out.key()==key,out.value()==value},
                    quote! {map},
                ),
                ShardableType::Set(k)
                | ShardableType::ISet(k)
                | ShardableType::PersistentSet(k)
                | ShardableType::PersistentISet(k) => (
                    quote! {#k},
                    quote! {pub closed spec fn element(&self)->#k{self.native}},
                    quote! {key:#k},
                    quote! {<#native>::empty().insert(key)},
                    quote! {key},
                    quote! {out.element()==key},
                    quote! {set},
                ),
                ShardableType::Multiset(k) => (
                    quote! {#k},
                    quote! {pub closed spec fn element(&self)->#k{self.native}},
                    quote! {key:#k},
                    quote! {<#native>::singleton(key)},
                    quote! {key},
                    quote! {out.element()==key},
                    quote! {multiset},
                ),
                _ => unreachable!(),
            };
        let invariant_singleton = match &field.stype {
            ShardableType::Map(..)
            | ShardableType::IMap(..)
            | ShardableType::PersistentMap(..)
            | ShardableType::PersistentIMap(..) => {
                quote! {<#native>::empty().insert(self.native.0,self.native.1)}
            }
            ShardableType::Multiset(..) => quote! {<#native>::singleton(self.native)},
            _ => quote! {<#native>::empty().insert(self.native)},
        };
        output.push(quote! {
            #(#attrs)*#[allow(non_camel_case_types)]
            pub tracked struct #name #decl #wc {raw:#token,ghost native:#metadata}
            impl #decl #name #types #wc {
                #[verifier::type_invariant]
                spec fn invariant(self)->bool {
                    self.raw.fragment()==<#fragment>::#factory(#invariant_singleton)
                }
                pub closed spec fn instance_id(&self)->::vstd::resource::Loc{self.raw.loc()}
                #getters
                proof fn __from_token(tracked raw:#token,#ctor_params)->(tracked out:Self)
                    requires raw.fragment()==<#fragment>::#factory(#singleton),
                    ensures out.instance_id()==raw.loc(),#ctor_ensures,
                {Self{raw,native:#ctor_metadata}}
                #entry_methods
            }
            #(#attrs)*#[allow(non_camel_case_types)]
            pub tracked struct #bulk #decl #wc {
                raw:Tracked<Option<#token>>,native:Ghost<#native>,ghost id: ::vstd::resource::Loc,
            }
            impl #decl #bulk #types #wc {
                #[verifier::type_invariant]
                spec fn invariant(self)->bool {Self::__slots(self.raw@,self.native@,self.id)}
                pub closed spec fn instance_id(&self)->::vstd::resource::Loc{self.id}
                pub closed spec fn #view(&self)->#native{self.native@}
                pub closed spec fn has_resource(&self)->bool{self.raw@ is Some}
                /// Only an actual Some owner can be borrowed for machine facts.
                pub proof fn borrow_token(tracked &self)->(tracked out:&#token)
                    requires self.has_resource(),
                    ensures out.loc()==self.instance_id(),
                        out.fragment()==<#fragment>::#factory(self.#view()),
                {::vstd::prelude::use_type_invariant(self);self.raw.borrow().tracked_borrow()}
                proof fn __from_token(tracked raw:#token,native:#native)->(tracked out:Self)
                    requires raw.fragment()==<#fragment>::#factory(native),
                    ensures out.instance_id()==raw.loc(),out.#view()==native,out.has_resource(),
                {{let id=raw.loc();Self{raw:Tracked(Some(raw)),native:Ghost(native),id}}}
                #methods
                #persistent
            }
        });
    }
    Ok(quote! {#(#output)*})
}

fn initial_values(
    stmt: &TransitionStmt,
    out: &mut HashMap<String, Expr>,
    req: &mut Vec<Expr>,
) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                initial_values(child, out, req)?;
            }
        }
        TransitionStmt::Initialize(_, field, value) => {
            out.insert(field.to_string(), value.clone());
        }
        TransitionStmt::Require(_, value) => req.push(value.clone()),
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "logical initializer currently requires straight-line field initialization",
            ))
        }
    }
    Ok(())
}

/// Initial scope: complete logical collection wrappers and checked initializers.
/// Transition/property emission is a separate checked extension of this module.
pub fn output(sm: &SM) -> Result<TokenStream, Error> {
    if sm.fields.iter().any(|f| {
        !crate::verified_field_collections::supported(&f.stype)
            && !matches!(
                f.stype,
                ShardableType::Variable(..)
                    | ShardableType::Constant(..)
                    | ShardableType::Count
                    | ShardableType::PersistentCount
                    | ShardableType::PersistentBool
                    | ShardableType::Bool
                    | ShardableType::Option(..)
                    | ShardableType::PersistentOption(..)
            )
    }) {
        return Err(Error::new(
            sm.name.span(),
            "logical field facade does not support storage or untracked fields yet",
        ));
    }
    if let Some(generics) = &sm.generics {
        for parameter in &generics.params {
            if let verus_syn::GenericParam::Type(parameter) = parameter {
                if sm.fields.iter().any(|field| field.name == parameter.ident) {
                    return Err(Error::new(
                        parameter.ident.span(),
                        "generic type parameter conflicts with a generated logical field token",
                    ));
                }
            }
        }
    }
    let mut reserved: HashSet<String> = ["State", "Protocol", "Fragment", "Token", "Instance"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    for field in &sm.fields {
        if !reserved.insert(field.name.to_string()) {
            return Err(Error::new(
                field.name.span(),
                "field token name conflicts with a generated machine type",
            ));
        }
    }
    for field in sm
        .fields
        .iter()
        .filter(|f| crate::verified_field_collections::supported(&f.stype))
    {
        if !reserved.insert(format!("{}_collection", field.name)) {
            return Err(Error::new(
                field.name.span(),
                "bulk field token name conflicts with another field type",
            ));
        }
    }
    let mut instance_methods: HashSet<String> = ["id", "clone", "invariant", "__lower_completion"]
        .iter()
        .map(|n| n.to_string())
        .collect();
    for field in sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(..)))
    {
        if !instance_methods.insert(field.name.to_string()) {
            return Err(Error::new(
                field.name.span(),
                "constant getter conflicts with a generated Instance method",
            ));
        }
    }
    for tr in &sm.transitions {
        if !instance_methods.insert(tr.name.to_string()) {
            return Err(Error::new(
                tr.name.span(),
                "transition conflicts with a generated Instance method",
            ));
        }
    }
    let mut wrappers = collection_wrappers(sm)?;
    if crate::verified_field_top_sort::supports(sm) {
        wrappers.extend(crate::verified_field_top_sort::aliases(sm)?);
    }
    wrappers.extend(crate::verified_field_variable_map::aliases(sm)?);
    wrappers.extend(crate::verified_field_persistent_maps::accessors(sm));
    for field in &sm.fields {
        if crate::verified_field_collections::supported(&field.stype) {
            continue;
        }
        let scalar = if matches!(
            field.stype,
            ShardableType::Bool | ShardableType::Option(..) | ShardableType::PersistentOption(..)
        ) {
            optional_wrapper(sm, field)?
        } else {
            crate::verified_field_scalars::scalar_wrapper(sm, field)?
        };
        wrappers.extend(scalar);
    }
    let Generics {
        decl,
        wc,
        attrs,
        types,
        expr,
    } = generics(sm);
    let token = quote! {Token #types};
    let fragment = quote! {Fragment #types};
    let constants: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(..)))
        .collect();
    let owners: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| !matches!(f.stype, ShardableType::Constant(..)))
        .collect();
    let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
    let cty: Vec<_> = constants.iter().map(|f| f.get_type()).collect();
    let cget: Vec<_> = cn.iter().map(|n| format_ident!("value_{n}")).collect();
    let context_shape = constants
        .iter()
        .fold(quote! {<#fragment>::empty()}, |out, f| {
            let set = format_ident!("with_{}", f.name);
            let get = format_ident!("value_{}", f.name);
            quote! {#out.#set(self.context.fragment().#get())}
        });
    let mut methods = Vec::new();
    for tr in &sm.transitions {
        if tr.kind != TransitionKind::Init {
            if crate::verified_field_top_sort::supports(sm) {
                methods.push(crate::verified_field_top_sort::method(sm, tr)?);
                continue;
            }
            if crate::verified_field_variable_map::supports(sm) {
                methods.push(crate::verified_field_variable_map::method(sm,tr)?);
                continue;
            }
            if crate::verified_field_interner::supports(sm) {
                methods.push(crate::verified_field_interner::method(sm,tr)?);
                continue;
            }
            if crate::verified_field_sets::supports(sm,tr) {
                methods.push(crate::verified_field_sets::method(sm,tr)?);
                continue;
            }
            if crate::verified_field_set_mixed::supports(sm, tr) {
                methods.push(crate::verified_field_set_mixed::method(sm, tr)?);
                continue;
            }
            if crate::verified_field_persistent_maps::supports(sm, tr) {
                methods.push(crate::verified_field_persistent_maps::method(sm, tr)?);
                continue;
            }
            if crate::verified_field_map_ordered::supports(sm, tr) {
                methods.push(crate::verified_field_map_ordered::method(sm, tr)?);
                continue;
            }
            if crate::verified_field_mixed::supports(sm, tr) {
                methods.push(crate::verified_field_mixed::method(sm, tr)?);
                continue;
            }
            if crate::verified_field_optional::supports(sm, tr) {
                methods.push(crate::verified_field_optional::method(sm, tr)?);
                continue;
            }
            methods.push(native_method(sm, tr)?);
            continue;
        }
        let mut values = HashMap::new();
        let mut req = Vec::new();
        initial_values(&tr.body, &mut values, &mut req)?;
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
        let fields: Vec<_> = owners.iter().map(|f| &f.name).collect();
        let returns: Vec<_> = owners
            .iter()
            .map(|f| {
                let n = &f.name;
                if crate::verified_field_collections::supported(&f.stype) {
                    let bulk = format_ident!("{}_collection", n);
                    quote! {#bulk #types}
                } else if matches!(
                    f.stype,
                    ShardableType::Bool
                        | ShardableType::PersistentBool
                        | ShardableType::Option(..)
                        | ShardableType::PersistentOption(..)
                ) {
                    quote! {Option<#n #types>}
                } else {
                    quote! {#n #types}
                }
            })
            .collect();
        let initial: Vec<_> = owners
            .iter()
            .map(|f| {
                let ty = f.get_type();
                let value = &values[&f.name.to_string()];
                let local = fresh(sm, &tr.params, &format!("native_{}", f.name));
                quote! {((|#local:#ty|#local)(#value))}
            })
            .collect();
        let constvalues: Vec<_> = cn.iter().map(|n| &values[&n.to_string()]).collect();
        let remaining = fresh(sm, &tr.params, "remaining");
        let names: Vec<_> = fields
            .iter()
            .map(|f| fresh(sm, &tr.params, &format!("init_{f}")))
            .collect();
        let takes: Vec<_> = fields
            .iter()
            .zip(&names)
            .map(|(f, n)| {
                let take = format_ident!("take_{f}");
                quote! {let tracked (#n,#remaining)=Protocol #expr::#take(#remaining);}
            })
            .collect();
        let indexes: Vec<_> = (1..=fields.len()).map(verus_syn::Index::from).collect();
        let mut observations = Vec::new();
        let mut constructions = Vec::new();
        for (((field, value), index), raw) in owners.iter().zip(&initial).zip(&indexes).zip(&names)
        {
            let n = &field.name;
            if crate::verified_field_collections::supported(&field.stype) {
                let bulk = format_ident!("{}_collection", n);
                let view = match field.stype {
                    ShardableType::Map(..)
                    | ShardableType::IMap(..)
                    | ShardableType::PersistentMap(..)
                    | ShardableType::PersistentIMap(..) => quote! {map},
                    ShardableType::Multiset(..) => quote! {multiset},
                    _ => quote! {set},
                };
                observations.push(quote!{out.#index@.instance_id()==out.0@.id(),out.#index@.#view()==#value,out.#index@.has_resource(),});
                constructions.push(quote! {Tracked(<#bulk #types>::__from_token(#raw,#value))});
            } else if matches!(
                field.stype,
                ShardableType::Bool | ShardableType::PersistentBool
            ) {
                observations.push(quote!{(out.#index@ is Some)==(#value),
                    ::vstd::prelude::imply(out.#index@ is Some,out.#index@->Some_0.instance_id()==out.0@.id()),});
                constructions.push(
                    quote! {Tracked(if #value{Some(<#n #types>::__from_token(#raw))}else{None})},
                );
            } else if matches!(
                field.stype,
                ShardableType::Option(..) | ShardableType::PersistentOption(..)
            ) {
                observations.push(quote!{(out.#index@ is Some)==((#value) is Some),
                    ::vstd::prelude::imply(out.#index@ is Some,out.#index@->Some_0.instance_id()==out.0@.id()
                        && out.#index@->Some_0.value()==(#value)->Some_0),});
                constructions.push(quote!{Tracked(if (#value) is Some{Some(<#n #types>::__from_token(#raw))}else{None})});
            } else {
                let view = if matches!(
                    field.stype,
                    ShardableType::Count | ShardableType::PersistentCount
                ) {
                    quote! {count}
                } else {
                    quote! {value}
                };
                observations.push(
                    quote! {out.#index@.instance_id()==out.0@.id(),out.#index@.#view()==#value,},
                );
                constructions.push(quote! {Tracked(<#n #types>::__from_token(#raw))});
            }
        }
        methods.push(quote! {
            pub proof fn #name(#(#params),*)->(tracked out:(Tracked<Self>,#(Tracked<#returns>),*))
                requires #(#req,)*
                ensures #(#observations)*#(out.0@.#cn()==#constvalues,)*
            {
                let tracked #remaining=Protocol #expr::#name(#(#args),*);
                #(#takes)*
                (Tracked(Self{context:#remaining}),#(#constructions),*)
            }
        });
    }
    let adapters = if sm
        .transitions
        .iter()
        .any(|tr| tr.kind != TransitionKind::Init)
    {
        observation_adapters(sm)?
    } else {
        quote! {}
    };
    Ok(quote! {
        #wrappers
        #adapters
        #(#attrs)*pub tracked struct Instance #decl #wc{context:#token}
        impl #decl Instance #types #wc {
            #[verifier::type_invariant]
            spec fn invariant(self)->bool{self.context.fragment()==#context_shape}
            pub closed spec fn id(&self)->::vstd::resource::Loc{self.context.loc()}
            #(pub closed spec fn #cn(&self)->#cty{self.context.fragment().#cget()})*
            /// Lift one actually supplied lower observation through the common
            /// borrowed upper and the owned/global frame. This creates no owner.
            proof fn __lower_completion(owned:Fragment #types,upper:Fragment #types,
                outer:Fragment #types,lower:Fragment #types,state:State #types)
                ->(frame:Fragment #types)
                requires
                    Fragment #expr::op(Fragment #expr::op(owned,upper),outer)==Protocol #expr::embed(state),
                    ::vstd::resource::tsm::fragment_included::<Protocol #types>(lower,upper),
                ensures Fragment #expr::op(lower,frame)==Protocol #expr::embed(state),
            {
                let remainder=choose|remainder:Fragment #types|Fragment #expr::op(lower,remainder)==upper;
                Fragment #expr::commutative(owned,upper);
                Fragment #expr::associative(lower,remainder,owned);
                Fragment #expr::associative(lower,Fragment #expr::op(remainder,owned),outer);
                Fragment #expr::op(Fragment #expr::op(remainder,owned),outer)
            }
            pub proof fn clone(tracked &self)->(tracked out:Self)
                ensures out.id()==self.id(),#(out.#cn()==self.#cn(),)*
            {
                ::vstd::prelude::use_type_invariant(self);
                <#fragment>::op_unit(<#fragment>::unit());
                let tracked context=self.context.duplicate();Self{context}
            }
            #(#methods)*
        }
    })
}

/// Optional owners are strictly PRESENT; None is represented by Option<FIELD>
/// at facade boundaries and carries no resource or machine fact.
fn optional_wrapper(sm: &SM, field: &Field) -> Result<TokenStream, Error> {
    let Generics {
        decl,
        wc,
        attrs,
        types,
        expr,
    } = generics(sm);
    let name = &field.name;
    let factory = format_ident!("field_{}", name);
    let getter = format_ident!("value_{}", name);
    let owns = format_ident!("owns_{}", name);
    let (ty, native, value) = match &field.stype {
        ShardableType::Bool => (quote! {bool}, quote! {true}, quote! {true}),
        ShardableType::Option(ty) | ShardableType::PersistentOption(ty) => (
            quote! {#ty},
            quote! {Some(self.value())},
            quote! {self.raw.fragment().#getter()->Some_0},
        ),
        _ => return Err(Error::new(name.span(), "unsupported optional field role")),
    };
    let shape = if matches!(field.stype, ShardableType::Bool) {
        quote! {Fragment #expr::#factory(true)}
    } else {
        quote! {Fragment #expr::#factory(self.raw.fragment().#getter())}
    };
    let rawshape = if matches!(field.stype, ShardableType::Bool) {
        quote! {Fragment #expr::#factory(true)}
    } else {
        quote! {Fragment #expr::#factory(raw.fragment().#getter())}
    };
    let observed = if matches!(field.stype, ShardableType::Bool) {
        quote! {true}
    } else {
        quote! {raw.fragment().#getter()->Some_0}
    };
    let clone = if matches!(field.stype, ShardableType::PersistentOption(..)) {
        quote! {
            pub proof fn agree(tracked &self,tracked other:&Self)
                requires self.instance_id()==other.instance_id(),
                ensures self.value()==other.value(),
            {
                ::vstd::prelude::use_type_invariant(self);::vstd::prelude::use_type_invariant(other);
                let (state,left,right)=self.raw.compatible_with(&other.raw);
                ::vstd::resource::tsm_collections::persistent_option_owned_frame(self.raw.fragment().#name,left.#name,state.#name,self.value());
                ::vstd::resource::tsm_collections::persistent_option_owned_frame(other.raw.fragment().#name,right.#name,state.#name,other.value());
            }
            pub proof fn clone(tracked &self)->(tracked out:Self)
                ensures out.instance_id()==self.instance_id(),out.value()==self.value(),
            {
                ::vstd::prelude::use_type_invariant(self);
                ::vstd::resource::tsm_collections::persistent_option_idempotent(Some(self.value()));
                Fragment #expr::op_unit(Fragment #expr::unit());
                assert(Fragment #expr::op(self.raw.fragment(),self.raw.fragment())==self.raw.fragment());
                let tracked raw=self.raw.duplicate();Self::__from_token(raw)
            }
        }
    } else {
        quote! {}
    };
    Ok(quote! {
        #(#attrs)*#[allow(non_camel_case_types)]pub tracked struct #name #decl #wc{raw:Token #types}
        impl #decl #name #types #wc {
            #[verifier::type_invariant]spec fn invariant(self)->bool{
                self.raw.fragment().#owns() && self.raw.fragment()==#shape
            }
            pub closed spec fn instance_id(&self)->::vstd::resource::Loc{self.raw.loc()}
            pub closed spec fn value(&self)->#ty{#value}
            pub proof fn borrow_token(tracked &self)->(tracked out:&Token #types)
                ensures out.loc()==self.instance_id(),out.fragment()==Fragment #expr::#factory(#native),
            {::vstd::prelude::use_type_invariant(self);&self.raw}
            proof fn __from_token(tracked raw:Token #types)->(tracked out:Self)
                requires raw.fragment().#owns(),raw.fragment()==#rawshape,
                ensures out.instance_id()==raw.loc(),out.value()==#observed,
            {Self{raw}}
            #clone
        }
    })
}

/// Private low-level adapters reuse the exact checked operation frame theorem.
/// Public nominal methods must separately enforce capacities on the supplied
/// current field owners; an upper observation never supplies extra native rights.
pub fn observation_adapters(sm: &SM) -> Result<TokenStream, Error> {
    if !crate::verified_general::needed(sm)
        && !(sm.fields.len() == 1 && matches!(sm.fields[0].stype, ShardableType::Count))
    {
        return Err(Error::new(
            sm.name.span(),
            "logical observation adapters require the checked general backend",
        ));
    }
    let Generics {
        decl,
        wc,
        types,
        expr,
        ..
    } = generics(sm);
    let mut methods = Vec::new();
    let names: HashSet<_> = sm
        .transitions
        .iter()
        .map(|tr| tr.name.to_string())
        .collect();
    for tr in sm
        .transitions
        .iter()
        .filter(|tr| tr.kind != TransitionKind::Init)
    {
        let adapter = format_ident!("__field_{}_with_observation", tr.name);
        if names.contains(&adapter.to_string()) {
            return Err(Error::new(
                tr.name.span(),
                "transition conflicts with generated observation adapter",
            ));
        }
        let req = format_ident!("{}_requires", tr.name);
        let frame = format_ident!("{}_frame", tr.name);
        let output = format_ident!("{}_outputs", tr.name);
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
        let owned = fresh(sm, &tr.params, "owned");
        let observed = fresh(sm, &tr.params, "observed");
        let outputs = fresh(sm, &tr.params, "outputs");
        let next = fresh(sm, &tr.params, "next");
        methods.push(quote! {
            proof fn #adapter(tracked #owned:Token #types,
                tracked #observed:&::vstd::resource::tsm::Observation<Protocol #types>,#(#params),*)
                ->(tracked out:Token #types)
                requires #owned.loc()==#observed.loc(),
                    Self::#req(#owned.fragment(),#observed.fragment(),#(#args),*),
                ensures out.loc()==#owned.loc(),
                    Self::#output(#owned.fragment(),#observed.fragment(),out.fragment(),#(#args),*),
            {
                Self::#frame(#owned.fragment(),#observed.fragment(),#(#args),*);
                let #outputs=::vstd::iset::ISet::new(|#next:Fragment #types|
                    Self::#output(#owned.fragment(),#observed.fragment(),#next,#(#args),*));
                #owned.update_nondeterministic_with_observation(#observed,#outputs)
            }
        });
    }
    Ok(quote! {impl #decl Protocol #types #wc{#(#methods)*}})
}

#[derive(Default)]
struct HaveOnly {
    have: Vec<(Ident, crate::ast::SpecialOp, Option<Box<verus_syn::Pat>>)>,
    require: Vec<Expr>,
    assertions: Vec<Expr>,
}
fn collect_have_only(stmt: &TransitionStmt, out: &mut HaveOnly) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                collect_have_only(child, out)?;
            }
        }
        TransitionStmt::Require(_, expr) => out.require.push(expr.clone()),
        TransitionStmt::Assert(_, expr, _) => out.assertions.push(expr.clone()),
        TransitionStmt::Split(_, kind, children) => {
            if let crate::ast::SplitKind::Special(name, op, _, pattern) = &**kind {
                if op.stmt.is_have() {
                    out.have.push((name.clone(), op.clone(), pattern.clone()));
                    for child in children {
                        collect_have_only(child, out)?;
                    }
                    return Ok(());
                }
            }
            return Err(Error::new(
                *stmt.get_span(),
                "first logical read facade supports unbound Have operations",
            ));
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "logical read facade does not modify fields",
            ))
        }
    }
    Ok(())
}

/// First public transition slice: one supplied PRESENT map entry observed by a
/// read-only protocol step. All user assertions and requirements are retained.
/// Additional roles/control are separate checked compiler extensions.
fn have_only_method(sm: &SM, tr: &crate::ast::Transition) -> Result<TokenStream, Error> {
    let mut flat = HaveOnly::default();
    collect_have_only(&tr.body, &mut flat)?;
    if flat.have.len() == 1
        && matches!(
            sm.fields
                .iter()
                .find(|f| f.name == flat.have[0].0)
                .unwrap()
                .stype,
            ShardableType::Count | ShardableType::PersistentCount
        )
    {
        return count_read_method(sm, tr, flat);
    }
    if flat.have.len() != 1 || flat.have[0].2.is_some() {
        return scalar_read_method(sm, tr, flat);
    }
    let (field_name, op, _) = &flat.have[0];
    if !matches!(
        sm.fields
            .iter()
            .find(|f| f.name == *field_name)
            .unwrap()
            .stype,
        ShardableType::Map(..)
            | ShardableType::IMap(..)
            | ShardableType::PersistentMap(..)
            | ShardableType::PersistentIMap(..)
    ) {
        return scalar_read_method(sm, tr, flat);
    }
    let field = sm.fields.iter().find(|f| f.name == *field_name).unwrap();
    let (key, value) = if let crate::ast::MonoidElt::SingletonKV(key, Some(value)) = &op.elt {
        (key, value)
    } else {
        return Err(Error::new(
            tr.name.span(),
            "first logical read facade needs an explicit singleton map entry",
        ));
    };
    let (key_ty, val_ty, finite, persistent) = match &field.stype {
        ShardableType::Map(k, v) => (k, v, true, false),
        ShardableType::IMap(k, v) => (k, v, false, false),
        ShardableType::PersistentMap(k, v) => (k, v, true, true),
        ShardableType::PersistentIMap(k, v) => (k, v, false, true),
        _ => {
            return Err(Error::new(
                field_name.span(),
                "first logical read facade supports map entry observations",
            ))
        }
    };
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let check = |expr: &Expr| -> Result<(), Error> {
        let mut expr = expr.clone();
        let mut errors = Vec::new();
        crate::field_access_visitor::visit_field_accesses(
            &mut expr,
            |errors, field, _| {
                errors.push(Error::new(
                    field.name.span(),
                    "first logical read facade assertions must use explicit parameters",
                ));
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
    for expression in flat.require.iter().chain(&flat.assertions) {
        check(expression)?;
    }
    check(key)?;
    check(value)?;
    let Generics { types, expr, .. } = generics(sm);
    let name = &tr.name;
    let req = format_ident!("{}_requires", name);
    let output = format_ident!("{}_outputs", name);
    let enabled = format_ident!("{}_enabled", name);
    let owners = format_ident!("{}_owners_enabled", name);
    let strong = format_ident!("{}_strong", name);
    let owned_post = format_ident!("{}_owned_post", name);
    let adapter = format_ident!("__field_{}_with_observation", name);
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
    let token = fresh(sm, &tr.params, &format!("input_{field_name}"));
    let observed = fresh(sm, &tr.params, "read_observation");
    let owned = fresh(sm, &tr.params, "read_owned");
    let before = fresh(sm, &tr.params, "read_before");
    let returned = fresh(sm, &tr.params, "read_returned");
    let pre = fresh(sm, &tr.params, "read_pre");
    let post = fresh(sm, &tr.params, "read_post");
    let outer = fresh(sm, &tr.params, "read_outer");
    let lower = fresh(sm, &tr.params, "read_lower");
    let actual_key = fresh(sm, &tr.params, "read_key");
    let actual_value = fresh(sm, &tr.params, "read_value");
    let witness_frame = fresh(sm, &tr.params, "read_frame");
    let group = if finite {
        quote! {.to_imap()}
    } else {
        quote! {}
    };
    let owned_frame = if persistent {
        quote! {persistent_map_owned_frame}
    } else {
        quote! {map_owned_frame}
    };
    let requirement = &flat.require;
    let assertion = &flat.assertions;
    Ok(quote! {
        pub proof fn #name(tracked &self,#(#params,)*tracked #token:&#field_name #types)
            requires #token.instance_id()==self.id(),#token.key()==#key,#token.value()==#value,#(#requirement,)*
            ensures #(#assertion,)*
        {
            ::vstd::prelude::use_type_invariant(self);
            ::vstd::prelude::use_type_invariant(#token);
            let #actual_key:#key_ty=#key;let #actual_value:#val_ty=#value;
            let tracked #observed=#token.raw.observe();
            Fragment #expr::op_unit(Fragment #expr::unit());
            assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());
            let tracked #owned=self.context.duplicate();
            let #before=#owned.fragment();
            #token.raw.fragment().op_unit();
            assert(Fragment #expr::op(#token.raw.fragment(),Fragment #expr::unit())==#observed.fragment());
            assert(::vstd::resource::tsm::fragment_included::<Protocol #types>(#token.raw.fragment(),#observed.fragment()));
            assert(Protocol #expr::#req(#before,#observed.fragment(),#(#args),*)) by {
                assert forall|#outer:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#args),*)
                        &&State #expr::#owners(#pre,#before,#observed.fragment(),#(#args),*) by {
                    assert(::vstd::resource::tsm::fragment_included::<Protocol #types>(#token.raw.fragment(),#observed.fragment()));
                    let #lower=Self::__lower_completion(#before,#observed.fragment(),#outer,#token.raw.fragment(),#pre);
                    ::vstd::resource::tsm_collections::#owned_frame(#token.raw.fragment().#field_name,
                        #lower.#field_name,#pre.#field_name #group,#actual_key,#actual_value);
                }
            }
            let tracked #returned=Protocol #expr::#adapter(#owned,&#observed,#(#args),*);
            let (#witness_frame,#pre,#post)=choose|#witness_frame:Fragment #types,#pre:State #types,#post:State #types|
                #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#witness_frame)==Protocol #expr::embed(#pre)
                &&State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()
                &&#returned.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
                &&Fragment #expr::op(Fragment #expr::op(#returned.fragment(),#observed.fragment()),#witness_frame)==Protocol #expr::embed(#post);
        }
    })
}

/// Straight-line scalar resource exchange. Every removed owner is consumed and
/// every returned owner is extracted from the actual checked update result.
fn native_method(sm: &SM, tr: &crate::ast::Transition) -> Result<TokenStream, Error> {
    let mut reads = HaveOnly::default();
    if collect_have_only(&tr.body, &mut reads).is_ok() {
        return have_only_method(sm, tr);
    }
    let mut flat = ScalarExchange::default();
    collect_scalar_exchange(&tr.body, &mut flat)?;
    if flat.ops.iter().all(|(_, op)| op.stmt.is_have()) {
        return have_only_method(sm, tr);
    }
    if flat.ops.iter().any(|(name, _)| {
        matches!(
            sm.fields.iter().find(|f| f.name == *name).unwrap().stype,
            ShardableType::Map(..) | ShardableType::IMap(..)
        )
    }) {
        return map_exchange_method(sm, tr, flat);
    }
    if flat.ops.len() == 1
        && flat.ops[0].1.is_add()
        && matches!(
            sm.fields
                .iter()
                .find(|f| f.name == flat.ops[0].0)
                .unwrap()
                .stype,
            ShardableType::Count | ShardableType::PersistentCount
        )
    {
        return count_add_method(sm, tr, flat);
    }
    if flat.ops.len() == 1
        && flat.ops[0].1.is_remove()
        && matches!(
            sm.fields
                .iter()
                .find(|f| f.name == flat.ops[0].0)
                .unwrap()
                .stype,
            ShardableType::Count
        )
    {
        return count_remove_method(sm, tr, flat);
    }
    scalar_exchange_method(sm, tr, flat)
}
#[derive(Default)]
struct ScalarExchange {
    ops: Vec<(Ident, crate::ast::SpecialOp)>,
    require: Vec<Expr>,
    assertions: Vec<Expr>,
}
fn collect_scalar_exchange(stmt: &TransitionStmt, out: &mut ScalarExchange) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                collect_scalar_exchange(child, out)?;
            }
        }
        TransitionStmt::Require(_, expr) => out.require.push(expr.clone()),
        TransitionStmt::Assert(_, expr, _) => out.assertions.push(expr.clone()),
        TransitionStmt::Split(_, kind, children) => {
            if let crate::ast::SplitKind::Special(name, op, _, None) = &**kind {
                out.ops.push((name.clone(), op.clone()));
                for child in children {
                    collect_scalar_exchange(child, out)?;
                }
                return Ok(());
            }
            return Err(Error::new(
                *stmt.get_span(),
                "logical native exchange currently needs explicit straight-line operands",
            ));
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "logical native exchange currently supports scalar Add/Remove",
            ))
        }
    }
    Ok(())
}
fn scalar_exchange_method(
    sm: &SM,
    tr: &crate::ast::Transition,
    flat: ScalarExchange,
) -> Result<TokenStream, Error> {
    let Generics { types, expr, .. } = generics(sm);
    let mut seen = HashSet::new();
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    let mut body = Vec::new();
    let mut bounds = Vec::new();
    let mut facts = Vec::new();
    let mut returned_types = Vec::new();
    let mut returned_ensures = Vec::new();
    let mut extract = Vec::new();
    let mut returned = Vec::new();
    let owned = fresh(sm, &tr.params, "exchange_owned");
    let obs = fresh(sm, &tr.params, "exchange_observed");
    let before = fresh(sm, &tr.params, "exchange_before");
    let next = fresh(sm, &tr.params, "exchange_next");
    let pre = fresh(sm, &tr.params, "exchange_pre");
    let post = fresh(sm, &tr.params, "exchange_post");
    let frame = fresh(sm, &tr.params, "exchange_frame");
    let rest = fresh(sm, &tr.params, "exchange_rest");
    for (field_name, op) in &flat.ops {
        if !seen.insert(field_name.to_string()) {
            return Err(Error::new(
                field_name.span(),
                "first logical scalar exchange supports one operation per field",
            ));
        }
        let field = sm.fields.iter().find(|f| f.name == *field_name).unwrap();
        let native = match (&field.stype, &op.elt) {
            (ShardableType::Bool, crate::ast::MonoidElt::True) => quote! {true},
            (
                ShardableType::Option(..) | ShardableType::PersistentOption(..),
                crate::ast::MonoidElt::OptionSome(Some(v)),
            ) => quote! {#v},
            _ => {
                return Err(Error::new(
                    field_name.span(),
                    "logical scalar exchange needs true or explicit Some(value)",
                ))
            }
        };
        match op.stmt {
            crate::ast::MonoidStmtType::Remove => {
                if field.stype.is_persistent() {
                    return Err(Error::new(
                        field_name.span(),
                        "persistent field owners cannot be removed",
                    ));
                }
                let input = fresh(sm, &tr.params, &format!("consume_{field_name}"));
                inputs.push(quote! {tracked #input:#field_name #types});
                bounds.push(quote! {#input.instance_id()==self.id()});
                if !matches!(field.stype, ShardableType::Bool) {
                    bounds.push(quote! {#input.value()==#native});
                }
                body.push(quote!{::vstd::prelude::use_type_invariant(&#input);let tracked #owned=#owned.join(#input.raw);});
                let remainder = quote! {Fragment #expr::op(#obs.fragment(),#frame).#field_name};
                if matches!(field.stype, ShardableType::Bool) {
                    facts.push(quote!{::vstd::resource::tsm_bool::bool_owned_frame(#before.#field_name,#remainder,#pre.#field_name);});
                } else {
                    facts.push(quote!{::vstd::resource::tsm_collections::option_owned_frame(#before.#field_name,#remainder,#pre.#field_name,#native);});
                }
            }
            crate::ast::MonoidStmtType::Add(_) => {
                let index = verus_syn::Index::from(outputs.len());
                outputs.push(field_name);
                returned_types.push(quote! {Tracked<#field_name #types>});
                returned_ensures.push(quote! {out.#index@.instance_id()==self.id()});
                if !matches!(field.stype, ShardableType::Bool) {
                    returned_ensures.push(quote! {out.#index@.value()==#native});
                }
                let field_raw = fresh(sm, &tr.params, &format!("return_{field_name}"));
                let take = format_ident!("take_{field_name}");
                extract.push(quote! {let tracked (#field_raw,#rest)=Protocol #expr::#take(#rest);});
                returned.push(quote! {Tracked(<#field_name #types>::__from_token(#field_raw))});
            }
            _ => {
                return Err(Error::new(
                    field_name.span(),
                    "logical scalar exchange first slice does not mix Have with modifications",
                ))
            }
        }
    }
    if outputs.is_empty() {
        return Err(Error::new(
            tr.name.span(),
            "first scalar exchange requires a returned present owner",
        ));
    }
    let name = &tr.name;
    let req = format_ident!("{}_requires", name);
    let enabled = format_ident!("{}_enabled", name);
    let owners = format_ident!("{}_owners_enabled", name);
    let strong = format_ident!("{}_strong", name);
    let owned_post = format_ident!("{}_owned_post", name);
    let adapter = format_ident!("__field_{}_with_observation", name);
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
    let requirement = &flat.require;
    let assertions = &flat.assertions;
    Ok(quote! {
        pub proof fn #name(tracked &self,#(#params,)*#(#inputs),*)->(tracked out:(#(#returned_types,)*))
            requires #(#bounds,)*#(#requirement,)*
            ensures #(#returned_ensures,)*#(#assertions,)*
        {
            ::vstd::prelude::use_type_invariant(self);
            assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());
            let tracked #owned=self.context.duplicate();#(#body)*
            let #before=#owned.fragment();let tracked #obs=self.context.observe();
            assert(Protocol #expr::#req(#before,#obs.fragment(),#(#args),*)) by {
                assert forall|#frame:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#obs.fragment()),#frame)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#obs.fragment(),#(#args),*) by {
                    Fragment #expr::associative(#before,#obs.fragment(),#frame);#(#facts)*
                }
            }
            let tracked #next=Protocol #expr::#adapter(#owned,&#obs,#(#args),*);
            let (#frame,#pre,#post)=choose|#frame:Fragment #types,#pre:State #types,#post:State #types|
                #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#obs.fragment()),#frame)==Protocol #expr::embed(#pre)
                &&State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()
                &&#next.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
                &&Fragment #expr::op(Fragment #expr::op(#next.fragment(),#obs.fragment()),#frame)==Protocol #expr::embed(#post);
            let tracked #rest=#next;#(#extract)*
            (#(#returned,)*)
        }
    })
}

/// Two PRESENT scalar observations share a real common borrowed upper. Each
/// supplied owner has its own inclusion remainder; aliases are never summed.
fn scalar_read_method(
    sm: &SM,
    tr: &crate::ast::Transition,
    flat: HaveOnly,
) -> Result<TokenStream, Error> {
    if flat.have.len() != 2 {
        return Err(Error::new(
            tr.name.span(),
            "scalar read facade currently supports two Have operands",
        ));
    }
    let Generics { types, expr, .. } = generics(sm);
    let observed = fresh(sm, &tr.params, "scalar_observed");
    let owned = fresh(sm, &tr.params, "scalar_owned");
    let before = fresh(sm, &tr.params, "scalar_before");
    let next = fresh(sm, &tr.params, "scalar_next");
    let outer = fresh(sm, &tr.params, "scalar_outer");
    let pre = fresh(sm, &tr.params, "scalar_pre");
    let post = fresh(sm, &tr.params, "scalar_post");
    let frame = fresh(sm, &tr.params, "scalar_frame");
    let mut inputs = Vec::new();
    let mut bounds = Vec::new();
    let mut setup = Vec::new();
    let mut observations = Vec::new();
    let mut facts = Vec::new();
    let mut bound_names = HashSet::new();
    for (index, (field_name, op, pattern)) in flat.have.iter().enumerate() {
        let field = sm.fields.iter().find(|f| f.name == *field_name).unwrap();
        let token = fresh(sm, &tr.params, &format!("read_{index}_{field_name}"));
        inputs.push(quote! {tracked #token:&#field_name #types});
        bounds.push(quote! {#token.instance_id()==self.id()});
        let observation = fresh(sm, &tr.params, &format!("observation_{index}_{field_name}"));
        observations.push(observation.clone());
        setup.push(quote!{::vstd::prelude::use_type_invariant(#token);let tracked #observation=#token.raw.observe();});
        let lower = fresh(sm, &tr.params, &format!("lower_{index}_{field_name}"));
        let fact = match (&field.stype, &op.elt) {
            (ShardableType::Bool, crate::ast::MonoidElt::True) => quote! {
                ::vstd::resource::tsm_bool::bool_owned_frame(#token.raw.fragment().#field_name,#lower.#field_name,#pre.#field_name);
            },
            (ShardableType::PersistentBool, crate::ast::MonoidElt::True) => quote! {
                ::vstd::resource::tsm_persistent::persistent_bool_owned_frame(#token.raw.fragment().#field_name,#lower.#field_name,#pre.#field_name);
            },
            (
                ShardableType::Option(..) | ShardableType::PersistentOption(..),
                crate::ast::MonoidElt::OptionSome(value),
            ) => {
                if let Some(value) = value {
                    bounds.push(quote! {#token.value()==#value});
                } else if let Some(pattern) = pattern {
                    if let verus_syn::Pat::Ident(pat) = &**pattern {
                        bound_names.insert(pat.ident.to_string());
                    } else {
                        return Err(Error::new(
                            field_name.span(),
                            "scalar bound Have currently supports one identifier",
                        ));
                    }
                } else {
                    return Err(Error::new(
                        field_name.span(),
                        "Some observation needs a value or binding",
                    ));
                }
                let helper = if field.stype.is_persistent() {
                    quote! {persistent_option_owned_frame}
                } else {
                    quote! {option_owned_frame}
                };
                quote! {::vstd::resource::tsm_collections::#helper(#token.raw.fragment().#field_name,#lower.#field_name,#pre.#field_name,#token.value());}
            }
            _ => {
                return Err(Error::new(
                    field_name.span(),
                    "two scalar Have facade supports Bool and Option present owners",
                ))
            }
        };
        facts.push(quote!{
            let #lower=Self::__lower_completion(#before,#observed.fragment(),#outer,#token.raw.fragment(),#pre);
            #fact
        });
    }
    // Bound patterns are native observations, but exposing them as public output
    // expressions needs a later scoped expression compiler. Fail closed here.
    use verus_syn::visit::Visit;
    struct BoundUse<'a> {
        names: &'a HashSet<String>,
        used: bool,
    }
    impl<'ast> Visit<'ast> for BoundUse<'_> {
        fn visit_expr_path(&mut self, p: &'ast verus_syn::ExprPath) {
            if p.path.segments.len() == 1
                && self.names.contains(&p.path.segments[0].ident.to_string())
            {
                self.used = true;
            }
            verus_syn::visit::visit_expr_path(self, p);
        }
    }
    for expression in flat.require.iter().chain(&flat.assertions) {
        let mut visitor = BoundUse {
            names: &bound_names,
            used: false,
        };
        visitor.visit_expr(expression);
        if visitor.used {
            return Err(Error::new(
                tr.name.span(),
                "bound Have values in public expressions require scoped lowering",
            ));
        }
    }
    let first = &observations[0];
    let second = &observations[1];
    let name = &tr.name;
    let req = format_ident!("{}_requires", name);
    let enabled = format_ident!("{}_enabled", name);
    let owners = format_ident!("{}_owners_enabled", name);
    let strong = format_ident!("{}_strong", name);
    let owned_post = format_ident!("{}_owned_post", name);
    let adapter = format_ident!("__field_{}_with_observation", name);
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
    let requirement = &flat.require;
    let assertions = &flat.assertions;
    Ok(quote! {
        pub proof fn #name(tracked &self,#(#params,)*#(#inputs),*)
            requires #(#bounds,)*#(#requirement,)*
            ensures #(#assertions,)*
        {
            ::vstd::prelude::use_type_invariant(self);#(#setup)*
            let tracked #observed=#first.join(&#second);
            assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());
            let tracked #owned=self.context.duplicate();let #before=#owned.fragment();
            assert(Protocol #expr::#req(#before,#observed.fragment(),#(#args),*)) by {
                assert forall|#outer:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#observed.fragment(),#(#args),*) by {
                    #(#facts)*
                }
            }
            let tracked #next=Protocol #expr::#adapter(#owned,&#observed,#(#args),*);
            let (#frame,#pre,#post)=choose|#frame:Fragment #types,#pre:State #types,#post:State #types|
                #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#frame)==Protocol #expr::embed(#pre)
                &&State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()
                &&#next.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
                &&Fragment #expr::op(Fragment #expr::op(#next.fragment(),#observed.fragment()),#frame)==Protocol #expr::embed(#post);
        }
    })
}

/// A singleton map replacement consumes exactly the supplied current entry.
/// The machine invariant and original transition safety must establish all
/// additional global enablement; cached entry membership cannot assert absence.
fn map_exchange_method(
    sm: &SM,
    tr: &crate::ast::Transition,
    flat: ScalarExchange,
) -> Result<TokenStream, Error> {
    if flat.ops.len() != 2 {
        return Err(Error::new(
            tr.name.span(),
            "first map exchange needs remove followed by add",
        ));
    }
    let (field_name, remove) = &flat.ops[0];
    let (add_name, add) = &flat.ops[1];
    if field_name != add_name || !remove.is_remove() || !add.is_add() {
        return Err(Error::new(
            tr.name.span(),
            "first map exchange needs one current entry replaced on the same field",
        ));
    }
    let field = sm.fields.iter().find(|f| f.name == *field_name).unwrap();
    let (key_ty, value_ty, finite) = match &field.stype {
        ShardableType::Map(k, v) => (k, v, true),
        ShardableType::IMap(k, v) => (k, v, false),
        _ => {
            return Err(Error::new(
                field_name.span(),
                "first map exchange supports exclusive maps",
            ))
        }
    };
    let (old_key, old_value) = match &remove.elt {
        crate::ast::MonoidElt::SingletonKV(k, Some(v)) => (k, v),
        _ => {
            return Err(Error::new(
                field_name.span(),
                "first map exchange requires an explicit removed entry",
            ))
        }
    };
    let (new_key, new_value) = match &add.elt {
        crate::ast::MonoidElt::SingletonKV(k, Some(v)) => (k, v),
        _ => {
            return Err(Error::new(
                field_name.span(),
                "first map exchange requires an explicit added entry",
            ))
        }
    };
    let Generics { types, expr, .. } = generics(sm);
    let field_ty = field.get_type();
    let input = fresh(sm, &tr.params, "replace_entry");
    let old_k = fresh(sm, &tr.params, "replace_old_key");
    let old_v = fresh(sm, &tr.params, "replace_old_value");
    let new_k = fresh(sm, &tr.params, "replace_new_key");
    let new_v = fresh(sm, &tr.params, "replace_new_value");
    let owned = fresh(sm, &tr.params, "replace_owned");
    let observed = fresh(sm, &tr.params, "replace_observed");
    let before = fresh(sm, &tr.params, "replace_before");
    let next = fresh(sm, &tr.params, "replace_next");
    let outer = fresh(sm, &tr.params, "replace_outer");
    let pre = fresh(sm, &tr.params, "replace_pre");
    let post = fresh(sm, &tr.params, "replace_post");
    let raw = fresh(sm, &tr.params, "replace_raw");
    let rest = fresh(sm, &tr.params, "replace_rest");
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
    let requirement = &flat.require;
    let assertions = &flat.assertions;
    Ok(quote! {
        pub proof fn #name(tracked &self,#(#params,)*tracked #input:#field_name #types)->(tracked out:#field_name #types)
            requires #input.instance_id()==self.id(),#input.key()==#old_key,#input.value()==#old_value,#(#requirement,)*
            ensures out.instance_id()==self.id(),out.key()==#new_key,out.value()==#new_value,#(#assertions,)*
        {
            broadcast use ::vstd::imap::group_imap_lemmas;
            broadcast use ::vstd::iset::group_iset_lemmas;
            broadcast use ::vstd::map::group_map_lemmas;
            broadcast use ::vstd::set::group_set_lemmas;
            Fragment #expr::op_unit(Fragment #expr::unit());
            ::vstd::prelude::use_type_invariant(self);::vstd::prelude::use_type_invariant(&#input);
            let #old_k:#key_ty=#old_key;let #old_v:#value_ty=#old_value;let #new_k:#key_ty=#new_key;let #new_v:#value_ty=#new_value;
            assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());
            let tracked #owned=self.context.duplicate().join(#input.raw);
            let #before=#owned.fragment();let tracked #observed=self.context.observe();
            assert(Protocol #expr::#req(#before,#observed.fragment(),#(#args),*)) by {
                assert forall|#outer:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#observed.fragment(),#(#args),*) by {
                    Fragment #expr::associative(#before,#observed.fragment(),#outer);
                    ::vstd::resource::tsm_collections::map_owned_frame(#before.#field_name,
                        Fragment #expr::op(#observed.fragment(),#outer).#field_name,#pre.#field_name #group,#old_k,#old_v);
                }
            }
            let tracked #next=Protocol #expr::#adapter(#owned,&#observed,#(#args),*);
            let (#outer,#pre,#post)=choose|#outer:Fragment #types,#pre:State #types,#post:State #types|
                #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                &&State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()
                &&#next.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
                &&Fragment #expr::op(Fragment #expr::op(#next.fragment(),#observed.fragment()),#outer)==Protocol #expr::embed(#post);
            let removed=<#field_ty>::empty().insert(#old_k,#old_v) #group;
            assert(::vstd::prelude::ext_equal(removed,::vstd::imap::IMap::empty().insert(#old_k,#old_v)));
            let cleared=::vstd::resource::tsm_collections::map_remove_many(#before.#field_name,removed.dom());
            assert forall|key:#key_ty|#[trigger] cleared.at(key)==::vstd::resource::tsm_collections::MapFragment::unit().at(key) by {};
            ::vstd::resource::tsm_collections::MapFragment::extensionality(cleared,::vstd::resource::tsm_collections::MapFragment::unit());
            let native_new=<#field_ty>::empty().insert(#new_k,#new_v);
            assert(::vstd::prelude::ext_equal(native_new #group,::vstd::imap::IMap::empty().insert(#new_k,#new_v)));
            ::vstd::resource::tsm_collections::MapFragment::op_unit(::vstd::resource::tsm_collections::map_frag(native_new #group));
            ::vstd::resource::tsm_collections::MapFragment::commutative(::vstd::resource::tsm_collections::MapFragment::unit(),::vstd::resource::tsm_collections::map_frag(native_new #group));
            let tracked (#raw,#rest)=Protocol #expr::#take(#next);
            <#field_name #types>::__from_token(#raw,#new_k,#new_v)
        }
    })
}

/// A current native lower-bound owner supplies the capacity of this unary Have.
fn count_read_method(
    sm: &SM,
    tr: &crate::ast::Transition,
    flat: HaveOnly,
) -> Result<TokenStream, Error> {
    let (field_name, op, _) = &flat.have[0];
    let amount = if let crate::ast::MonoidElt::General(value) = &op.elt {
        value
    } else {
        return Err(Error::new(
            field_name.span(),
            "count Have needs a native amount",
        ));
    };
    let Generics { types, expr, .. } = generics(sm);
    let token = count_fresh(sm, tr, "count_input");
    let observed = count_fresh(sm, tr, "count_observed");
    let owned = count_fresh(sm, tr, "count_owned");
    let before = count_fresh(sm, tr, "count_before");
    let outer = count_fresh(sm, tr, "count_outer");
    let lower = count_fresh(sm, tr, "count_lower");
    let pre = count_fresh(sm, tr, "count_pre");
    let post = count_fresh(sm, tr, "count_post");
    let next = count_fresh(sm, tr, "count_next");
    let name = &tr.name;
    let req = format_ident!("{}_requires", name);
    let enabled = format_ident!("{}_enabled", name);
    let owners = format_ident!("{}_owners_enabled", name);
    let strong = format_ident!("{}_strong", name);
    let owned_post = format_ident!("{}_owned_post", name);
    let adapter = format_ident!("__field_{}_with_observation", name);
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
    let requirement = &flat.require;
    let assertions = &flat.assertions;
    let bounds = if matches!(
        sm.fields
            .iter()
            .find(|f| f.name == *field_name)
            .unwrap()
            .stype,
        ShardableType::Count
    ) {
        quote! {assert(#pre.#field_name==#token.raw.fragment().#field_name.count+#lower.#field_name.count);}
    } else {
        quote! {::vstd::resource::tsm_persistent::persistent_count_owned_frame(#token.raw.fragment().#field_name,#lower.#field_name,#pre.#field_name);}
    };
    Ok(quote! {
        pub proof fn #name(tracked &self,#(#params,)*tracked #token:&#field_name #types)
            requires #token.instance_id()==self.id(),#token.count()>=#amount,#(#requirement,)*
            ensures #(#assertions,)*
        {
            ::vstd::prelude::use_type_invariant(self);::vstd::prelude::use_type_invariant(#token);
            let tracked #observed=#token.raw.observe();
            Fragment #expr::op_unit(Fragment #expr::unit());
            assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());
            let tracked #owned=self.context.duplicate();let #before=#owned.fragment();
            #token.raw.fragment().op_unit();
            assert(::vstd::resource::tsm::fragment_included::<Protocol #types>(#token.raw.fragment(),#observed.fragment()));
            assert(Protocol #expr::#req(#before,#observed.fragment(),#(#args),*)) by {
                assert forall|#outer:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#observed.fragment(),#(#args),*) by {
                    let #lower=Self::__lower_completion(#before,#observed.fragment(),#outer,#token.raw.fragment(),#pre);
                    #bounds
                }
            }
            let tracked #next=Protocol #expr::#adapter(#owned,&#observed,#(#args),*);
            let (#outer,#pre,#post)=choose|#outer:Fragment #types,#pre:State #types,#post:State #types|
                #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                &&State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()
                &&#next.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
                &&Fragment #expr::op(Fragment #expr::op(#next.fragment(),#observed.fragment()),#outer)==Protocol #expr::embed(#post);
        }
    })
}
/// Ordinary/persistent addition returns actual new Count ownership derived by the
/// checked additive/max-count update; it does not manufacture a cached count owner.
fn count_add_method(
    sm: &SM,
    tr: &crate::ast::Transition,
    flat: ScalarExchange,
) -> Result<TokenStream, Error> {
    let (field_name, op) = &flat.ops[0];
    let amount = if let crate::ast::MonoidElt::General(value) = &op.elt {
        value
    } else {
        return Err(Error::new(
            field_name.span(),
            "count Add needs a native amount",
        ));
    };
    let Generics { types, expr, .. } = generics(sm);
    let observed = count_fresh(sm, tr, "count_observed");
    let owned = count_fresh(sm, tr, "count_owned");
    let before = count_fresh(sm, tr, "count_before");
    let outer = count_fresh(sm, tr, "count_outer");
    let pre = count_fresh(sm, tr, "count_pre");
    let post = count_fresh(sm, tr, "count_post");
    let next = count_fresh(sm, tr, "count_next");
    let raw = count_fresh(sm, tr, "count_result");
    let rest = count_fresh(sm, tr, "count_rest");
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
    let requirement = &flat.require;
    let assertions = &flat.assertions;
    Ok(quote! {
        pub proof fn #name(tracked &self,#(#params),*)->(tracked out:#field_name #types)
            requires #(#requirement,)*
            ensures out.instance_id()==self.id(),out.count()==#amount,#(#assertions,)*
        {
            ::vstd::prelude::use_type_invariant(self);Fragment #expr::op_unit(Fragment #expr::unit());
            assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());
            let tracked #owned=self.context.duplicate();let #before=#owned.fragment();let tracked #observed=self.context.observe();
            assert(Protocol #expr::#req(#before,#observed.fragment(),#(#args),*)) by {
                assert forall|#outer:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#observed.fragment(),#(#args),*) by {}
            }
            let tracked #next=Protocol #expr::#adapter(#owned,&#observed,#(#args),*);
            let (#outer,#pre,#post)=choose|#outer:Fragment #types,#pre:State #types,#post:State #types|
                #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                &&State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()
                &&#next.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
                &&Fragment #expr::op(Fragment #expr::op(#next.fragment(),#observed.fragment()),#outer)==Protocol #expr::embed(#post);
            let tracked (#raw,#rest)=Protocol #expr::#take(#next);<#field_name #types>::__from_token(#raw)
        }
    })
}

/// Removing an exact unary count consumes only that current owner. Any outside
/// count is retained in the checked frame, and no borrowed count is spent.
fn count_remove_method(
    sm: &SM,
    tr: &crate::ast::Transition,
    flat: ScalarExchange,
) -> Result<TokenStream, Error> {
    let (field_name, op) = &flat.ops[0];
    let amount = if let crate::ast::MonoidElt::General(value) = &op.elt {
        value
    } else {
        return Err(Error::new(
            field_name.span(),
            "count Remove needs a native amount",
        ));
    };
    let Generics { types, expr, .. } = generics(sm);
    let input = count_fresh(sm, tr, "count_input");
    let before = count_fresh(sm, tr, "count_before");
    let observed = count_fresh(sm, tr, "count_observed");
    let outer = count_fresh(sm, tr, "count_outer");
    let pre = count_fresh(sm, tr, "count_pre");
    let next = count_fresh(sm, tr, "count_next");
    let name = &tr.name;
    let req = format_ident!("{}_requires", name);
    let enabled = format_ident!("{}_enabled", name);
    let owners = format_ident!("{}_owners_enabled", name);
    let adapter = format_ident!("__field_{}_with_observation", name);
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
    let requirement = &flat.require;
    let assertions = &flat.assertions;
    Ok(quote! {
    pub proof fn #name(tracked &self,#(#params,)*tracked #input:#field_name #types)
    requires #input.instance_id()==self.id(),#input.count()==#amount,#(#requirement,)*
    ensures #(#assertions,)*
    {
     ::vstd::prelude::use_type_invariant(self);::vstd::prelude::use_type_invariant(&#input);
     let #before=#input.raw.fragment();let tracked #observed=self.context.observe();
     assert(Protocol #expr::#req(#before,#observed.fragment(),#(#args),*)) by {
      assert forall|#outer:Fragment #types,#pre:State #types|
       #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
       implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#observed.fragment(),#(#args),*) by {}
     }
     let tracked #next=Protocol #expr::#adapter(#input.raw,&#observed,#(#args),*);
    }
    })
}

fn count_fresh(sm: &SM, tr: &crate::ast::Transition, label: &str) -> Ident {
    let mut names: HashSet<String> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .collect();
    fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
        for token in tokens {
            match token {
                proc_macro2::TokenTree::Ident(id) => {
                    names.insert(id.to_string());
                }
                proc_macro2::TokenTree::Group(group) => reserve(group.stream(), names),
                _ => {}
            }
        }
    }
    fn visit(stmt: &TransitionStmt, names: &mut HashSet<String>) {
        match stmt {
            TransitionStmt::Block(_, children) => {
                for child in children {
                    visit(child, names);
                }
            }
            TransitionStmt::Require(_, e)
            | TransitionStmt::Assert(_, e, _)
            | TransitionStmt::Initialize(_, _, e)
            | TransitionStmt::Update(_, _, e) => reserve(quote! {#e}, names),
            TransitionStmt::Split(_, kind, children) => {
                if let crate::ast::SplitKind::Special(_, op, _, _) = &**kind {
                    if let crate::ast::MonoidElt::General(e) = &op.elt {
                        reserve(quote! {#e}, names);
                    }
                }
                for child in children {
                    visit(child, names);
                }
            }
            _ => {}
        }
    }
    visit(&tr.body, &mut names);
    let mut name = format!("__tsm_logical_{label}");
    while names.contains(&name) {
        name.push('_');
    }
    Ident::new(&name, Span::mixed_site())
}
