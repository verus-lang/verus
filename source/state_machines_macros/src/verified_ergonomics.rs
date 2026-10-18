//! Checked conveniences over the current fragment, without assuming a field is present.
use crate::ast::*;
use crate::verified_monoids as monoids;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;
use verus_syn::{Error, Ident};

pub fn field_api(
    sm: &SM,
    fragment: &TokenStream,
    token: &TokenStream,
    names: &[&Ident],
    types: &[TokenStream],
) -> Result<(TokenStream, TokenStream), Error> {
    validate_names(sm, names)?;
    // Both unit laws of every component, proved once: the projection laws
    // below only need them, so each costs one call instead of one per field.
    let unit_laws: Vec<_> = names
        .iter()
        .zip(types)
        .map(|(n, ty)| quote! {<#ty>::op(<#ty>::unit(),self.#n)==self.#n,<#ty>::op(self.#n,<#ty>::unit())==self.#n})
        .collect();
    let unit_calls: Vec<_> =
        names.iter().zip(types).map(|(n, ty)| quote! {::vstd::resource::tsm::pcm_units::<#ty>(self.#n);}).collect();
    let mut specs = vec![quote! {
        pub open spec fn empty()->Self {Self::unit()}
        pub open spec fn combine(self, other:Self)->Self {Self::op(self,other)}
        pub proof fn __tsm_unit_laws(self) ensures #(#unit_laws),* {#(#unit_calls)*}
    }];
    let mut proofs = vec![];
    let constants: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(_)))
        .map(|f| f.name.clone())
        .collect();
    for (index, name) in names.iter().enumerate() {
        let field = sm.fields.iter().find(|f| f.name == **name).unwrap();
        let ty = field.get_type();
        let native = match &field.stype {
            ShardableType::Variable(_) => quote! {
                Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(value))
            },
            ShardableType::Constant(_) => quote! {
                Some(::vstd::resource::agree::AgreementRA::Agree(value))
            },
            s if monoids::supported(s) => monoids::embed(s, quote! {value}),
            _ => unreachable!(),
        };
        let factory = format_ident!("field_{}", name);
        let with = format_ident!("with_{}", name);
        specs.push(quote! {
            /// Construct a sparse specification fragment; this creates no tracked ownership.
            pub open spec fn #factory(value:#ty)->Self {
                Self{#name:#native,..Self::unit()}
            }
            pub open spec fn #with(self,value:#ty)->Self { Self{#name:#native,..self} }
        });
        specs.push(accessors(field));
        let mut group = vec![index];
        projection(
            names,
            types,
            &group,
            name,
            fragment,
            token,
            sm,
            &mut specs,
            &mut proofs,
        )?;
        if !constants.is_empty() && !matches!(field.stype, ShardableType::Constant(_)) {
            group.extend(
                names
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| constants.iter().any(|c| *c == ***n))
                    .map(|(i, _)| i),
            );
            let grouped = format_ident!("{}_with_constants", name);
            projection(
                names,
                types,
                &group,
                &grouped,
                fragment,
                token,
                sm,
                &mut specs,
                &mut proofs,
            )?;
        }
        if matches!(field.stype, ShardableType::Count) {
            let split = format_ident!("split_{}", name);
            check_operation_name(sm, &split)?;
            let remaining = format_ident!("remove_{}", name);
            let law = format_ident!("split_{}_law", name);
            specs.push(quote! {
                pub open spec fn #remaining(self,amount:nat)->Self {
                    Self{#name: ::vstd::resource::tsm::CountRA{count:(self.#name.count-amount) as nat},..self}
                }
                pub proof fn #law(self,amount:nat)
                    requires amount<=self.#name.count
                    ensures Self::op(Self::#factory(amount),self.#remaining(amount))==self
                {
                    self.__tsm_unit_laws();
                    assert(amount+(self.#name.count-amount) as nat==self.#name.count);
                }
            });
            proofs.push(quote! {
                pub proof fn #split(tracked token:#token,amount:nat)->(tracked out:(#token,#token))
                    requires amount<=token.fragment().#name.count
                    ensures out.0.loc()==token.loc(),out.1.loc()==token.loc(),
                        out.0.fragment()==<#fragment>::#factory(amount),
                        out.1.fragment()==token.fragment().#remaining(amount)
                {
                    let before=token.fragment();
                    before.#law(amount);
                    token.split(<#fragment>::#factory(amount),before.#remaining(amount))
                }
            });
        }
    }
    Ok((quote! {#(#specs)*}, quote! {#(#proofs)*}))
}

fn validate_names(sm: &SM, names: &[&Ident]) -> Result<(), Error> {
    let mut fragment = HashSet::from(["empty".to_string(), "combine".to_string()]);
    let mut protocol = HashSet::new();
    let constants = sm
        .fields
        .iter()
        .any(|f| matches!(f.stype, ShardableType::Constant(_)));
    for name in names {
        let field = sm.fields.iter().find(|f| f.name == **name).unwrap();
        let mut methods = vec![format!("field_{name}"), format!("with_{name}")];
        let mut groups = vec![name.to_string()];
        if constants && !matches!(field.stype, ShardableType::Constant(_)) {
            groups.push(format!("{name}_with_constants"));
        }
        for group in groups {
            methods.extend([
                format!("select_{group}"),
                format!("without_{group}"),
                format!("take_{group}_law"),
            ]);
            if !protocol.insert(format!("take_{group}")) {
                return Err(Error::new(
                    name.span(),
                    "field names conflict with generated field helpers",
                ));
            }
        }
        match &field.stype {
            ShardableType::Map(..)
            | ShardableType::IMap(..)
            | ShardableType::PersistentMap(..)
            | ShardableType::PersistentIMap(..) => {
                methods.extend([format!("owns_{name}_at"), format!("value_{name}_at")]);
            }
            ShardableType::Set(_)
            | ShardableType::ISet(_)
            | ShardableType::PersistentSet(_)
            | ShardableType::PersistentISet(_) => {
                methods.push(format!("contains_{name}"));
            }
            ShardableType::Multiset(_) => methods.push(format!("value_{name}")),
            _ => methods.extend([format!("owns_{name}"), format!("value_{name}")]),
        }
        if matches!(field.stype, ShardableType::Count) {
            methods.extend([format!("remove_{name}"), format!("split_{name}_law")]);
            if !protocol.insert(format!("split_{name}")) {
                return Err(Error::new(
                    name.span(),
                    "field names conflict with generated field helpers",
                ));
            }
        }
        for method in methods {
            if !fragment.insert(method) {
                return Err(Error::new(
                    name.span(),
                    "field names conflict with generated field helpers",
                ));
            }
        }
    }
    Ok(())
}

fn check_operation_name(sm: &SM, name: &Ident) -> Result<(), Error> {
    for tr in &sm.transitions {
        for suffix in [
            "",
            "_with_shared",
            "_requires",
            "_outputs",
            "_frame",
            "_witness",
            "_owned_post",
            "_guarded",
            "_fragment",
            "_facts",
            "_shared_requires",
            "_owned_fragment",
            "_shared_frame",
            "_deposit",
            "_withdraw",
        ] {
            if format!("{}{}", tr.name, suffix) == name.to_string() {
                return Err(Error::new(
                    name.span(),
                    "transition name conflicts with a generated field helper",
                ));
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn projection(
    names: &[&Ident],
    types: &[TokenStream],
    selected: &[usize],
    label: &Ident,
    _fragment: &TokenStream,
    token: &TokenStream,
    sm: &SM,
    specs: &mut Vec<TokenStream>,
    proofs: &mut Vec<TokenStream>,
) -> Result<(), Error> {
    let select = format_ident!("select_{}", label);
    let without = format_ident!("without_{}", label);
    let law = format_ident!("take_{}_law", label);
    let take = format_ident!("take_{}", label);
    check_operation_name(sm, &take)?;
    let entries: Vec<_> = selected
        .iter()
        .map(|i| {
            let n = names[*i];
            quote! {#n:self.#n}
        })
        .collect();
    let removed: Vec<_> = selected
        .iter()
        .map(|i| {
            let n = names[*i];
            let ty = &types[*i];
            quote! {#n:<#ty>::unit()}
        })
        .collect();
    specs.push(quote! {
        pub open spec fn #select(self)->Self {Self{#(#entries),*,..Self::unit()}}
        pub open spec fn #without(self)->Self {Self{#(#removed),*,..self}}
        pub proof fn #law(self)
            ensures Self::op(self.#select(),self.#without())==self
        {self.__tsm_unit_laws();}
    });
    proofs.push(quote! {
        pub proof fn #take(tracked token:#token)->(tracked out:(#token,#token))
            ensures out.0.loc()==token.loc(),out.1.loc()==token.loc(),
                out.0.fragment()==token.fragment().#select(),
                out.1.fragment()==token.fragment().#without()
        {
            let before=token.fragment();
            before.#law();
            token.split(before.#select(),before.#without())
        }
    });
    Ok(())
}

fn accessors(field: &Field) -> TokenStream {
    let name = &field.name;
    let owns = format_ident!("owns_{}", name);
    let value = format_ident!("value_{}", name);
    match &field.stype {
        ShardableType::Variable(ty) | ShardableType::Constant(ty) => {
            let (valid, read) = if matches!(field.stype, ShardableType::Variable(_)) {
                (
                    quote! {self.#name is Some &&self.#name->Some_0 is Exclusive},
                    quote! {self.#name->Some_0->Exclusive_0},
                )
            } else {
                (
                    quote! {self.#name is Some &&self.#name->Some_0 is Agree},
                    quote! {self.#name->Some_0->Agree_0},
                )
            };
            quote! {
                pub open spec fn #owns(self)->bool {#valid}
                pub open spec fn #value(self)->#ty recommends self.#owns() {#read}
            }
        }
        ShardableType::Count | ShardableType::PersistentCount => quote! {
            pub open spec fn #owns(self)->bool {self.#name.count>0}
            /// The current local count; persistent counts express a lower bound.
            pub open spec fn #value(self)->nat {self.#name.count}
        },
        ShardableType::Bool | ShardableType::PersistentBool => quote! {
            pub open spec fn #owns(self)->bool {self.#name.count==1}
            /// Whether this fragment has local true evidence; false is not global absence.
            pub open spec fn #value(self)->bool recommends self.#name.count<=1 {self.#name.count==1}
        },
        ShardableType::Multiset(ty) => quote! {
            pub open spec fn #value(self)->::vstd::multiset::Multiset<#ty> {self.#name.values}
        },
        ShardableType::Option(ty) | ShardableType::PersistentOption(ty) => {
            let (tag, read) = if matches!(field.stype, ShardableType::Option(_)) {
                (quote! {Exclusive}, quote! {self.#name->Some_0->Exclusive_0})
            } else {
                (quote! {Agree}, quote! {self.#name->Some_0->Agree_0})
            };
            quote! {
                pub open spec fn #owns(self)->bool {self.#name is Some &&self.#name->Some_0 is #tag}
                /// The locally owned optional value; None is not global absence.
                pub open spec fn #value(self)->Option<#ty>
                    recommends self.#name is None || self.#owns()
                {if self.#owns(){Some(#read)}else{None}}
            }
        }
        ShardableType::Map(k, v)
        | ShardableType::IMap(k, v)
        | ShardableType::PersistentMap(k, v)
        | ShardableType::PersistentIMap(k, v) => {
            let owns_at = format_ident!("owns_{}_at", name);
            let value_at = format_ident!("value_{}_at", name);
            let (tag, read) = if field.stype.is_persistent() {
                (quote! {Agree}, quote! {self.#name.at(key)->Some_0->Agree_0})
            } else {
                (
                    quote! {Exclusive},
                    quote! {self.#name.at(key)->Some_0->Exclusive_0},
                )
            };
            quote! {
                pub open spec fn #owns_at(self,key:#k)->bool {
                    self.#name.at(key) is Some &&self.#name.at(key)->Some_0 is #tag
                }
                /// Read a locally known map entry.
                pub open spec fn #value_at(self,key:#k)->#v recommends self.#owns_at(key) {#read}
            }
        }
        ShardableType::Set(k)
        | ShardableType::ISet(k)
        | ShardableType::PersistentSet(k)
        | ShardableType::PersistentISet(k) => {
            let contains = format_ident!("contains_{}", name);
            let tag = if field.stype.is_persistent() {
                quote! {::vstd::resource::agree::AgreementRA::Agree(())}
            } else {
                quote! {::vstd::resource::exclusive::ExclusiveRA::Exclusive(())}
            };
            quote! {pub open spec fn #contains(self,key:#k)->bool {self.#name.at(key)==Some(#tag)}}
        }
        _ => unreachable!(),
    }
}
