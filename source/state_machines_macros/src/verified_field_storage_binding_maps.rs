//! Actual storage-backed ordinary Map/IMap owners for bound storage exchanges.
//! The reviewed IMap custody discipline is retained; finite maps use native Map views.
use crate::ast::{Field, ShardableType};
use crate::verified_field_storage_roles::Context;
use proc_macro2::{TokenStream, TokenTree};
use quote::{format_ident, quote};
use verus_syn::Error;

pub fn wrapper(
    field: &Field,
    cx: &Context<'_>,
    reservation: &TokenStream,
) -> Result<TokenStream, Error> {
    let (key_type, value_type, finite) = match &field.stype {
        ShardableType::Map(k, v) => (k, v, true),
        ShardableType::IMap(k, v) => (k, v, false),
        _ => {
            return Err(Error::new(
                field.name.span(),
                "binding map roles require ordinary Map/IMap",
            ))
        }
    };
    let native_map = if finite {
        quote! {::vstd::map::Map::<#key_type,#value_type>}
    } else {
        quote! {::vstd::imap::IMap::<#key_type,#value_type>}
    };
    let native_type = if finite {
        quote! {::vstd::map::Map<#key_type,#value_type>}
    } else {
        quote! {::vstd::imap::IMap<#key_type,#value_type>}
    };
    let native_set = if finite {
        quote! {::vstd::set::Set<#key_type>}
    } else {
        quote! {::vstd::iset::ISet<#key_type>}
    };
    let singleton_imap = if finite {
        quote! {singleton.to_imap()}
    } else {
        quote! {singleton}
    };
    let rest_imap = if finite {
        quote! {rest.to_imap()}
    } else {
        quote! {rest}
    };
    let values_imap = if finite {
        quote! {values.to_imap()}
    } else {
        quote! {values}
    };
    let split_view = if finite {
        quote! {
            assert(::vstd::prelude::ext_equal(singleton.to_imap().union_prefer_right(rest.to_imap()),values.to_imap()));
        }
    } else {
        quote! {}
    };
    let join_view = if finite {
        quote! {
            assert(::vstd::prelude::ext_equal(values.to_imap().union_prefer_right(singleton.to_imap()),values.insert(key,value).to_imap()));
        }
    } else {
        quote! {}
    };
    let Context {
        decl,
        types,
        expr,
        where_clause,
        attrs,
        token,
        descriptor,
        protocol_location,
        constants,
    } = cx;
    let name = &field.name;
    let collection = format_ident!("{name}_collection");
    let map_alias = format_ident!("{name}_map");
    let factory = format_ident!("field_{name}");
    let getter = format_ident!("value_{name}_at");
    let owns = format_ident!("owns_{name}_at");
    let setters: Vec<_> = constants
        .iter()
        .map(|f| format_ident!("with_{}", f.name))
        .collect();
    let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
    fn reserved(tokens: TokenStream, wanted: &str) -> bool {
        tokens.into_iter().any(|token| match token {
            TokenTree::Ident(name) => name.to_string().trim_start_matches("r#") == wanted,
            TokenTree::Group(group) => reserved(group.stream(), wanted),
            _ => false,
        })
    }
    let mut contents_name = format!("{name}_collection_contents");
    while reserved(reservation.clone(), &contents_name) || reserved((*decl).clone(), &contents_name)
    {
        contents_name.push('_');
    }
    let contents = format_ident!("{contents_name}");
    Ok(quote! {
        #[allow(non_camel_case_types)] pub type #map_alias #decl #where_clause = #collection #types;
        #(#attrs)*#[allow(non_camel_case_types)]
        pub tracked struct #name #decl #where_clause {
            raw:Tracked<Option<#token>>,metadata:#descriptor,
            ghost entry_key:#key_type,
        }
        impl #decl #name #types #where_clause {
            #[verifier::type_invariant]
            spec fn invariant(self)->bool {
                self.raw@ is Some && self.raw@->Some_0.loc()==self.metadata.value().#protocol_location
                && self.raw@->Some_0.fragment().#owns(self.entry_key)
                && self.raw@->Some_0.fragment()==
                    Fragment #expr::#factory(#native_map::empty().insert(self.entry_key,self.value()))
                        #(.#setters(self.metadata.value().#cn))*
            }
            pub closed spec fn instance_id(&self)->::vstd::resource::Loc {self.metadata.id()}
            pub closed spec fn resource_location(&self)->::vstd::resource::Loc {self.raw@->Some_0.loc()}
            pub closed spec fn raw_fragment(&self)->Fragment #types {self.raw@->Some_0.fragment()}
            pub closed spec fn key(&self)->#key_type {self.entry_key}
            pub closed spec fn value(&self)->#value_type {self.raw@->Some_0.fragment().#getter(self.entry_key)}
            pub proof fn borrow_token(tracked &self)->(tracked out:&#token)
                ensures out.loc()==self.resource_location(),out.fragment()==self.raw_fragment(),
            {::vstd::prelude::use_type_invariant(self);self.raw.borrow().tracked_borrow()}
            proof fn __from_token(tracked raw:#token,tracked metadata:#descriptor,key:#key_type,value:#value_type)->(tracked out:Self)
                requires raw.loc()==metadata.value().#protocol_location,
                    raw.fragment()==Fragment #expr::#factory(#native_map::empty().insert(key,value))
                        #(.#setters(metadata.value().#cn))*,
                ensures out.instance_id()==metadata.id(),out.resource_location()==raw.loc(),
                    out.raw_fragment()==raw.fragment(),out.key()==key,out.value()==value,
            {Self{raw:Tracked(Some(raw)),metadata,entry_key:key}}
        }
        #(#attrs)*#[allow(non_camel_case_types)]
        tracked struct #contents #decl #where_clause {token:Option<#token>,ghost values:#native_type}
        #(#attrs)*#[allow(non_camel_case_types)]
        pub tracked struct #collection #decl #where_clause {raw:Tracked<#contents #types>,metadata:#descriptor}
        impl #decl #collection #types #where_clause {
            #[verifier::type_invariant]
            spec fn invariant(self)->bool {
                self.raw@.token is Some && self.raw@.token->Some_0.loc()==self.metadata.value().#protocol_location
                && self.raw@.token->Some_0.fragment()==Fragment #expr::#factory(self.raw@.values)
                    #(.#setters(self.metadata.value().#cn))*
            }
            pub closed spec fn instance_id(&self)->::vstd::resource::Loc {self.metadata.id()}
            pub closed spec fn resource_location(&self)->::vstd::resource::Loc {self.raw@.token->Some_0.loc()}
            pub closed spec fn raw_fragment(&self)->Fragment #types {self.raw@.token->Some_0.fragment()}
            pub closed spec fn map(&self)->#native_type {self.raw@.values}
            pub open spec fn dom(&self)->#native_set{self.map().dom()}
            pub open spec fn index(&self,key:#key_type)->#value_type{self.map()[key]}
            pub proof fn borrow_token(tracked &self)->(tracked out:&#token)
                ensures out.loc()==self.resource_location(),out.fragment()==self.raw_fragment(),
            {::vstd::prelude::use_type_invariant(self);self.raw.borrow().token.tracked_borrow()}
            proof fn __from_token(tracked raw:#token,tracked metadata:#descriptor,values:#native_type)->(tracked out:Self)
                requires raw.loc()==metadata.value().#protocol_location,
                    raw.fragment()==Fragment #expr::#factory(values)#(.#setters(metadata.value().#cn))*,
                ensures out.instance_id()==metadata.id(),out.resource_location()==raw.loc(),
                    out.raw_fragment()==raw.fragment(),out.map()==values,
            {Self{raw:Tracked(#contents{token:Some(raw),values}),metadata}}
            proof fn __split_raw(tracked slot:&mut Tracked<#contents #types>,
                selected:Fragment #types,remainder:Fragment #types,values:#native_type)->(tracked out:#token)
                requires old(slot)@.token is Some,
                    old(slot)@.token->Some_0.fragment()==Fragment #expr::op(selected,remainder),
                ensures final(slot)@.token is Some,final(slot)@.values==values,
                    final(slot)@.token->Some_0.loc()==old(slot)@.token->Some_0.loc(),
                    final(slot)@.token->Some_0.fragment()==remainder,
                    out.loc()==old(slot)@.token->Some_0.loc(),out.fragment()==selected,
            {
                let tracked current=slot.borrow_mut().token.tracked_take();
                let tracked (selected,remainder)=current.split(selected,remainder);
                *slot=Tracked(#contents{token:Some(remainder),values});selected
            }
            proof fn __join_raw(tracked slot:&mut Tracked<#contents #types>,
                tracked other:#token,combined:Fragment #types,values:#native_type)
                requires old(slot)@.token is Some,old(slot)@.token->Some_0.loc()==other.loc(),
                    combined==Fragment #expr::op(old(slot)@.token->Some_0.fragment(),other.fragment()),
                ensures final(slot)@.token is Some,final(slot)@.values==values,
                    final(slot)@.token->Some_0.loc()==old(slot)@.token->Some_0.loc(),
                    final(slot)@.token->Some_0.fragment()==combined,
            {
                let tracked current=slot.borrow_mut().token.tracked_take();
                let tracked joined=current.join(other);
                *slot=Tracked(#contents{token:Some(joined),values});
            }
            pub proof fn remove(tracked &mut self,key:#key_type)->(tracked out:#name #types)
                requires old(self).map().contains_key(key),
                ensures final(self).instance_id()==old(self).instance_id(),
                    final(self).map()==old(self).map().remove(key),
                    final(self).dom()==old(self).dom().remove(key),
                    forall|other:#key_type| #![trigger final(self).index(other)] !(other!=key && old(self).dom().contains(other)) || final(self).index(other)==old(self).index(other),
                    out.instance_id()==old(self).instance_id(),out.key()==key,out.value()==old(self).map()[key],
            {
                broadcast use {::vstd::map::group_map_lemmas,::vstd::set::group_set_lemmas,::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas};
                ::vstd::prelude::use_type_invariant(&*self);
                let values=self.map();let value=values[key];
                let singleton=#native_map::empty().insert(key,value);let rest=values.remove(key);
                ::vstd::resource::tsm_collections::map_join(#singleton_imap,#rest_imap);
                assert(::vstd::prelude::ext_equal(singleton.union_prefer_right(rest),values));
                #split_view
                Fragment #expr::unit().op_unit();
                let selected=Fragment #expr::#factory(singleton)#(.#setters(self.metadata.value().#cn))*;
                let remainder=Fragment #expr::#factory(rest)#(.#setters(self.metadata.value().#cn))*;
                assert(Fragment #expr::op(selected,remainder)==self.raw_fragment());
                let tracked metadata=self.metadata.clone();
                let tracked selected=Self::__split_raw(&mut self.raw,selected,remainder,rest);
                <#name #types>::__from_token(selected,metadata,key,value)
            }
            pub proof fn insert(tracked &mut self,tracked entry:#name #types)
                requires old(self).instance_id()==entry.instance_id(),!old(self).map().contains_key(entry.key()),
                ensures final(self).instance_id()==old(self).instance_id(),
                    final(self).map()==old(self).map().insert(entry.key(),entry.value()),
            {
                broadcast use {::vstd::map::group_map_lemmas,::vstd::set::group_set_lemmas,::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas};
                ::vstd::prelude::use_type_invariant(&*self);::vstd::prelude::use_type_invariant(&entry);
                self.metadata.agrees(&entry.metadata);
                let values=self.map();let key=entry.key();let value=entry.value();
                let singleton=#native_map::empty().insert(key,value);
                ::vstd::resource::tsm_collections::map_join(#values_imap,#singleton_imap);
                assert(::vstd::prelude::ext_equal(values.union_prefer_right(singleton),values.insert(key,value)));
                #join_view
                Fragment #expr::unit().op_unit();
                let combined=Fragment #expr::op(self.raw_fragment(),entry.raw_fragment());
                assert(combined==Fragment #expr::#factory(values.insert(key,value))
                    #(.#setters(self.metadata.value().#cn))*);
                let tracked current=entry.raw.get().tracked_unwrap();
                Self::__join_raw(&mut self.raw,current,combined,values.insert(key,value));
            }
        }
    })
}
