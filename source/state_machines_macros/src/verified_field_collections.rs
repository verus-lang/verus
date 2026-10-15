//! Checked operations on bulk logical collection owners.
//!
//! A bulk empty container may have no resource. That case is only zero local
//! ownership, and never supplies a machine completion. Present entries/elements
//! always contain an actual token. Native metadata uses Ghost so raw ownership
//! and its description can be restored within the same mutable helper boundary.
use crate::ast::{Field, ShardableType};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use verus_syn::Error;

pub fn supported(stype: &ShardableType) -> bool {
    matches!(
        stype,
        ShardableType::Map(..)
            | ShardableType::IMap(..)
            | ShardableType::PersistentMap(..)
            | ShardableType::PersistentIMap(..)
            | ShardableType::Set(..)
            | ShardableType::ISet(..)
            | ShardableType::PersistentSet(..)
            | ShardableType::PersistentISet(..)
            | ShardableType::Multiset(..)
    )
}

/// Items inside the bulk FIELD_collection impl. The generator supplies raw:
/// Option<Token>, native: Ghost<Native>, ghost id: Loc and an invariant matching
/// __slots below. The strict present entry type exposes __from_token and native
/// key/value or element observations, with raw private to the machine module.
pub fn methods(
    field: &Field,
    fragment: &TokenStream,
    token: &TokenStream,
    entry: &TokenStream,
) -> Result<TokenStream, Error> {
    let factory = format_ident!("field_{}", field.name);
    let native = field.get_type();
    let persistent = field.stype.is_persistent();
    let (
        args,
        member,
        singleton,
        remove,
        insert,
        observes,
        returned,
        native_getter,
        initial_law,
        inserted_law,
        conservation,
        admissible,
    ) = match &field.stype {
        ShardableType::Map(k, v)
        | ShardableType::IMap(k, v)
        | ShardableType::PersistentMap(k, v)
        | ShardableType::PersistentIMap(k, v) => {
            let finite = matches!(
                &field.stype,
                ShardableType::Map(..) | ShardableType::PersistentMap(..)
            );
            let as_imap = if finite {
                quote! { .to_imap() }
            } else {
                quote! {}
            };
            let join = if persistent {
                quote! {persistent_map_join}
            } else {
                quote! {map_join}
            };
            let singleton = quote! {<#native>::empty().insert(key, value)};
            let conversion_remove = if finite {
                quote! {
                    assert(::vstd::prelude::ext_equal(singleton.to_imap().union_prefer_right(remainder.to_imap()),original.to_imap()));
                }
            } else {
                quote! {}
            };
            let conversion_insert = if finite {
                quote! {
                    assert(::vstd::prelude::ext_equal(original.to_imap().union_prefer_right(singleton.to_imap()),updated.to_imap()));
                }
            } else {
                quote! {}
            };
            let initial_law = quote! {
                assert(singleton.dom().disjoint(remainder.dom()));
                ::vstd::resource::tsm_collections::#join(singleton #as_imap, remainder #as_imap);
                assert(::vstd::prelude::ext_equal(singleton.union_prefer_right(remainder),original));
                #conversion_remove
                <#fragment>::op_unit(<#fragment>::unit());
                assert(<#fragment>::op(<#fragment>::#factory(singleton),
                    <#fragment>::#factory(remainder)) == <#fragment>::#factory(original));
            };
            let inserted_law = quote! {
                ::vstd::resource::tsm_collections::#join(original #as_imap, singleton #as_imap);
                assert(::vstd::prelude::ext_equal(original.union_prefer_right(singleton),updated));
                #conversion_insert
                <#fragment>::op_unit(<#fragment>::unit());
                assert(<#fragment>::op(<#fragment>::#factory(original),
                    <#fragment>::#factory(singleton)) == <#fragment>::#factory(updated));
            };
            (
                quote! {key:#k},
                quote! {original.dom().contains(key)},
                singleton,
                quote! {original.remove(key)},
                quote! {original.insert(key,value)},
                quote! {let key = item.key(); let value = item.value();},
                quote! {<#entry>::__from_token(out,key,value)},
                quote! {map},
                initial_law,
                inserted_law,
                quote! {let value: #v = original[key];},
                // Conservative local absence, even for persistent insertion. A
                // later union API may combine equal overlapping evidence.
                quote! {!old(self).map().dom().contains(item.key())},
            )
        }
        ShardableType::Set(k)
        | ShardableType::ISet(k)
        | ShardableType::PersistentSet(k)
        | ShardableType::PersistentISet(k) => {
            let finite = matches!(
                &field.stype,
                ShardableType::Set(..) | ShardableType::PersistentSet(..)
            );
            let as_iset = if finite {
                quote! {.to_iset()}
            } else {
                quote! {}
            };
            let join = if persistent {
                quote! {persistent_set_join}
            } else {
                quote! {set_join}
            };
            let conversion_remove = if finite {
                quote! {
                    assert(::vstd::prelude::ext_equal(singleton.to_iset().union(remainder.to_iset()),original.to_iset()));
                }
            } else {
                quote! {}
            };
            let conversion_insert = if finite {
                quote! {
                    assert(::vstd::prelude::ext_equal(original.to_iset().union(singleton.to_iset()),updated.to_iset()));
                }
            } else {
                quote! {}
            };
            let initial_law = quote! {
                assert(singleton.disjoint(remainder));
                ::vstd::resource::tsm_collections::#join(singleton #as_iset,remainder #as_iset);
                assert(::vstd::prelude::ext_equal(singleton.union(remainder),original));
                #conversion_remove
                <#fragment>::op_unit(<#fragment>::unit());
                assert(<#fragment>::op(<#fragment>::#factory(singleton),
                    <#fragment>::#factory(remainder)) == <#fragment>::#factory(original));
            };
            let inserted_disjoint = if persistent {
                quote! {}
            } else {
                quote! {assert(original.disjoint(singleton));}
            };
            let inserted_law = quote! {
                #inserted_disjoint
                ::vstd::resource::tsm_collections::#join(original #as_iset,singleton #as_iset);
                assert(::vstd::prelude::ext_equal(original.union(singleton),updated));
                #conversion_insert
                <#fragment>::op_unit(<#fragment>::unit());
                assert(<#fragment>::op(<#fragment>::#factory(original),
                    <#fragment>::#factory(singleton)) == <#fragment>::#factory(updated));
            };
            (
                quote! {key:#k},
                quote! {original.contains(key)},
                quote! {<#native>::empty().insert(key)},
                quote! {original.remove(key)},
                quote! {original.insert(key)},
                quote! {let key = item.element();},
                quote! {<#entry>::__from_token(out,key)},
                quote! {set},
                initial_law,
                inserted_law,
                quote! {},
                if persistent {
                    quote! {true}
                } else {
                    quote! {!old(self).set().contains(item.element())}
                },
            )
        }
        ShardableType::Multiset(k) => {
            let initial_law = quote! {
                broadcast use ::vstd::multiset::group_multiset_axioms;
                assert(::vstd::prelude::ext_equal(singleton.add(remainder),original));
                ::vstd::resource::tsm_finite_multiset::finite_multiset_join(singleton,remainder);
                <#fragment>::op_unit(<#fragment>::unit());
                assert(<#fragment>::op(<#fragment>::#factory(singleton),
                    <#fragment>::#factory(remainder)) == <#fragment>::#factory(original));
            };
            let inserted_law = quote! {
                broadcast use ::vstd::multiset::group_multiset_axioms;
                ::vstd::resource::tsm_finite_multiset::finite_multiset_join(original,singleton);
                assert(original.add(singleton) == updated);
                <#fragment>::op_unit(<#fragment>::unit());
                assert(<#fragment>::op(<#fragment>::#factory(original),
                    <#fragment>::#factory(singleton)) == <#fragment>::#factory(updated));
            };
            (
                quote! {key:#k},
                quote! {original.count(key)>0},
                quote! {<#native>::singleton(key)},
                quote! {original.remove(key)},
                quote! {original.insert(key)},
                quote! {let key = item.element();},
                quote! {<#entry>::__from_token(out,key)},
                quote! {multiset},
                initial_law,
                inserted_law,
                quote! {},
                quote! {true},
            )
        }
        _ => {
            return Err(Error::new(
                field.name.span(),
                "unsupported nominal collection strategy",
            ))
        }
    };
    let inserted_predicate = if matches!(
        &field.stype,
        ShardableType::Multiset(..)
            | ShardableType::PersistentSet(..)
            | ShardableType::PersistentISet(..)
    ) {
        quote! {true}
    } else {
        quote! {!(#member)}
    };
    let entry_observation = if matches!(
        &field.stype,
        ShardableType::Map(..)
            | ShardableType::IMap(..)
            | ShardableType::PersistentMap(..)
            | ShardableType::PersistentIMap(..)
    ) {
        quote! {out.key()==key && out.value()==original[key]}
    } else {
        quote! {out.element()==key}
    };
    fn reserve_membership(tokens: TokenStream, names: &mut std::collections::HashSet<String>) {
        for token in tokens {
            match token {
                proc_macro2::TokenTree::Ident(name) => {
                    names.insert(name.to_string().trim_start_matches("r#").to_string());
                }
                proc_macro2::TokenTree::Group(group) => reserve_membership(group.stream(), names),
                _ => {}
            }
        }
    }
    let mut membership_names = std::collections::HashSet::new();
    reserve_membership(
        quote! {#fragment #token #entry #native},
        &mut membership_names,
    );
    let mut membership_name = "__tsm_collection_member".to_string();
    while membership_names.contains(&membership_name) {
        membership_name.push('_');
    }
    let member_query = verus_syn::Ident::new(&membership_name, proc_macro2::Span::mixed_site());
    let (contains, remove_membership, insert_membership) = match &field.stype {
        ShardableType::Set(k)
        | ShardableType::ISet(k)
        | ShardableType::PersistentSet(k)
        | ShardableType::PersistentISet(k) => (
            quote! {pub open spec fn contains(&self,key:#k)->bool{self.set().contains(key)}},
            quote! {forall|#member_query:#k|#[trigger]final(self).contains(#member_query)==(old(self).contains(#member_query)&&#member_query!=key),},
            quote! {forall|#member_query:#k|#[trigger]final(self).contains(#member_query)==(old(self).contains(#member_query)||#member_query==item.element()),},
        ),
        _ => (quote! {}, quote! {}, quote! {}),
    };
    let empty = quote! {<#native>::empty()};
    Ok(quote! {
        #contains
        #[verifier::inline]
        spec fn __slots(raw:Option<#token>, native:#native, id: ::vstd::resource::Loc)->bool {
            match raw {
                None => native == #empty,
                Some(raw) => raw.loc()==id && raw.fragment()==<#fragment>::#factory(native),
            }
        }

        pub proof fn empty(id: ::vstd::resource::Loc)->(tracked out:Self)
            ensures out.instance_id()==id, out.#native_getter()==#empty,
        {Self{raw:Tracked(None),native:Ghost(#empty),id}}

        proof fn __remove_raw(tracked raw:&mut Tracked<Option<#token>>,
            tracked native:&mut Ghost<#native>, id: ::vstd::resource::Loc, #args)
            ->(tracked out:#token)
            requires
                Self::__slots(old(raw)@,old(native)@,id),
                {let original=old(native)@; #member},
            ensures
                Self::__slots(final(raw)@,final(native)@,id),
                {let original=old(native)@; final(native)@ == #remove},
                out.loc()==id,
                {let original=old(native)@; #conservation out.fragment()==<#fragment>::#factory(#singleton)},
        {
            broadcast use ::vstd::map::group_map_lemmas;
            broadcast use ::vstd::set::group_set_lemmas;
            broadcast use ::vstd::imap::group_imap_lemmas;
            broadcast use ::vstd::iset::group_iset_lemmas;
            let original=native@;
            #conservation
            let singleton=#singleton;
            let remainder=#remove;
            #initial_law
            assert(raw@ is Some);
            let tracked owned=raw.borrow_mut().tracked_take();
            let tracked (out,rest)=owned.split(<#fragment>::#factory(singleton),
                <#fragment>::#factory(remainder));
            *raw=Tracked(if remainder==#empty {None} else {Some(rest)});
            *native=Ghost(remainder);
            out
        }

        pub proof fn remove(tracked &mut self,#args)->(tracked out:#entry)
            requires {let original=old(self).#native_getter(); #member},
            ensures
                final(self).instance_id()==old(self).instance_id(),
                {let original=old(self).#native_getter(); final(self).#native_getter()==#remove},
                out.instance_id()==old(self).instance_id(),
                #remove_membership
                {let original=old(self).#native_getter(); #entry_observation},
        {
            ::vstd::prelude::use_type_invariant(&*self);
            let original=self.native@;
            #conservation
            let tracked out=Self::__remove_raw(&mut self.raw,&mut self.native,self.id,key);
            #returned
        }

        proof fn __insert_raw(tracked raw:&mut Tracked<Option<#token>>,
            tracked native:&mut Ghost<#native>,id: ::vstd::resource::Loc,
            tracked item:#entry)
            requires
                Self::__slots(old(raw)@,old(native)@,id),
                item.instance_id()==id,
                {let self_before=old(native)@; let original=self_before; #observes
                    // The caller supplies exclusive absence where applicable.
                    #inserted_predicate },
            ensures
                Self::__slots(final(raw)@,final(native)@,id),
                {let original=old(native)@; #observes final(native)@==#insert},
        {
            ::vstd::prelude::use_type_invariant(&item);
            broadcast use ::vstd::map::group_map_lemmas;
            broadcast use ::vstd::set::group_set_lemmas;
            broadcast use ::vstd::imap::group_imap_lemmas;
            broadcast use ::vstd::iset::group_iset_lemmas;
            let original=native@;
            #observes
            let singleton=#singleton;
            let updated=#insert;
            if raw@ is Some {
                #inserted_law
                let tracked owned=raw.borrow_mut().tracked_take();
                *raw=Tracked(Some(owned.join(item.raw)));
            } else {
                assert(original==#empty);
                assert(updated==singleton);
                *raw=Tracked(Some(item.raw));
            }
            *native=Ghost(updated);
        }

        pub proof fn insert(tracked &mut self,tracked item:#entry)
            requires
                old(self).instance_id()==item.instance_id(),
                #admissible,
            ensures
                final(self).instance_id()==old(self).instance_id(),
                #insert_membership
                {let original=old(self).#native_getter(); #observes
                    final(self).#native_getter()==#insert},
        {
            ::vstd::prelude::use_type_invariant(&*self);
            ::vstd::prelude::use_type_invariant(&item);
            Self::__insert_raw(&mut self.raw,&mut self.native,self.id,item);
        }
    })
}

fn idempotence(
    field: &Field,
    fragment: &TokenStream,
    native: &TokenStream,
) -> Result<TokenStream, Error> {
    let factory = format_ident!("field_{}", field.name);
    let proof = match &field.stype {
        ShardableType::PersistentMap(..) => quote! {
            ::vstd::resource::tsm_collections::persistent_map_idempotent((#native).to_imap());
        },
        ShardableType::PersistentIMap(..) => quote! {
            ::vstd::resource::tsm_collections::persistent_map_idempotent(#native);
        },
        ShardableType::PersistentSet(..) => quote! {
            ::vstd::resource::tsm_collections::persistent_set_idempotent((#native).to_iset());
        },
        ShardableType::PersistentISet(..) => quote! {
            ::vstd::resource::tsm_collections::persistent_set_idempotent(#native);
        },
        _ => {
            return Err(Error::new(
                field.name.span(),
                "only persistent collections can duplicate",
            ))
        }
    };
    Ok(quote! {
        #proof
        <#fragment>::op_unit(<#fragment>::unit());
        assert(<#fragment>::op(<#fragment>::#factory(#native),<#fragment>::#factory(#native))
            ==<#fragment>::#factory(#native));
    })
}

/// Clone a PRESENT persistent entry/element from its actual idempotent resource.
pub fn entry_methods(field: &Field, fragment: &TokenStream) -> Result<TokenStream, Error> {
    let native = field.get_type();
    let (observations, singleton, constructor, post) = match &field.stype {
        ShardableType::PersistentMap(..) | ShardableType::PersistentIMap(..) => (
            quote! {let key=self.key();let value=self.value();},
            quote! {<#native>::empty().insert(key,value)},
            quote! {Self::__from_token(raw,key,value)},
            quote! {out.key()==self.key(),out.value()==self.value()},
        ),
        ShardableType::PersistentSet(..) | ShardableType::PersistentISet(..) => (
            quote! {let key=self.element();},
            quote! {<#native>::empty().insert(key)},
            quote! {Self::__from_token(raw,key)},
            quote! {out.element()==self.element()},
        ),
        _ => {
            return Err(Error::new(
                field.name.span(),
                "only persistent entries can duplicate",
            ))
        }
    };
    let law = idempotence(field, fragment, &singleton)?;
    Ok(quote! {
        pub proof fn clone(tracked &self)->(tracked out:Self)
            ensures out.instance_id()==self.instance_id(),#post,
        {
            ::vstd::prelude::use_type_invariant(self);
            #observations
            #law
            let tracked raw=self.raw.duplicate();
            #constructor
        }
    })
}

/// Clone a bulk persistent collection. None is copied as local zero ownership;
/// Some is duplicated only by the checked underlying idempotence operation.
pub fn persistent_collection_methods(
    field: &Field,
    fragment: &TokenStream,
) -> Result<TokenStream, Error> {
    let getter = match &field.stype {
        ShardableType::PersistentMap(..) | ShardableType::PersistentIMap(..) => quote! {map},
        ShardableType::PersistentSet(..) | ShardableType::PersistentISet(..) => quote! {set},
        _ => {
            return Err(Error::new(
                field.name.span(),
                "only persistent collections can duplicate",
            ))
        }
    };
    let law = idempotence(field, fragment, &quote! {self.native@})?;
    Ok(quote! {
        pub proof fn clone(tracked &self)->(tracked out:Self)
            ensures out.instance_id()==self.instance_id(),out.#getter()==self.#getter(),
        {
            ::vstd::prelude::use_type_invariant(self);
            if self.raw@ is Some {
                #law
                let tracked raw=self.raw.borrow().tracked_borrow().duplicate();
                Self{raw:Tracked(Some(raw)),native:Ghost(self.native@),id:self.id}
            }else{Self::empty(self.id)}
        }
    })
}
