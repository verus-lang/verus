//! Actual finite persistent-map collection owners for mixed physical protocols.
use crate::ast::{Field,ShardableType};
use crate::verified_field_storage_roles::Context;
use proc_macro2::TokenStream;
use quote::{format_ident,quote};
use verus_syn::Error;

pub fn wrapper(field:&Field,cx:&Context<'_>,reservation:&TokenStream)->Result<TokenStream,Error>{
    let ShardableType::PersistentMap(key_type,value_type)=&field.stype else{
        return Err(Error::new(field.name.span(),"storage map collections require finite PersistentMap"));
    };
    let Context{decl,types,expr,where_clause,attrs,token,descriptor,protocol_location,constants}=cx;
    fn reserved(tokens:TokenStream,wanted:&str)->bool{
        tokens.into_iter().any(|token|match token{
            proc_macro2::TokenTree::Ident(name)=>name==wanted,
            proc_macro2::TokenTree::Group(group)=>reserved(group.stream(),wanted),_=>false,
        })
    }
    let name=format_ident!("{}_collection",field.name);
    let mut contents_name=format!("{}_collection_contents",field.name);
    while reserved((*decl).clone(),&contents_name)||reserved(reservation.clone(),&contents_name){contents_name.push('_');}
    let contents=format_ident!("{contents_name}");
    let entry=&field.name;let factory=format_ident!("field_{entry}");
    let cn:Vec<_>=constants.iter().map(|f|&f.name).collect();
    let setters:Vec<_>=cn.iter().map(|n|format_ident!("with_{n}")).collect();
    Ok(quote!{
        #(#attrs)*#[allow(non_camel_case_types)]
        tracked struct #contents #decl #where_clause{
            token:Option<#token>,ghost elements: ::vstd::map::Map<#key_type,#value_type>,
        }
        #(#attrs)*#[allow(non_camel_case_types)]
        pub tracked struct #name #decl #where_clause{raw:Tracked<#contents #types>,metadata:#descriptor}
        impl #decl #name #types #where_clause{
            #[verifier::type_invariant]
            spec fn invariant(self)->bool{
                self.raw@.token is Some&&self.raw@.token->Some_0.loc()==self.metadata.value().#protocol_location
                &&self.raw@.token->Some_0.fragment()==Fragment #expr::#factory(self.raw@.elements)
                    #(.#setters(self.metadata.value().#cn))*
            }
            pub closed spec fn instance_id(&self)->::vstd::resource::Loc{self.metadata.id()}
            pub closed spec fn resource_location(&self)->::vstd::resource::Loc{self.raw@.token->Some_0.loc()}
            pub closed spec fn raw_fragment(&self)->Fragment #types{self.raw@.token->Some_0.fragment()}
            pub closed spec fn map(&self)->::vstd::map::Map<#key_type,#value_type>{self.raw@.elements}
            pub closed spec fn len(&self)->nat{self.map().len()}
            pub proof fn borrow_token(tracked &self)->(tracked out:&#token)
                ensures out.loc()==self.resource_location(),out.fragment()==self.raw_fragment(),
            {::vstd::prelude::use_type_invariant(self);self.raw.borrow().token.tracked_borrow()}
            proof fn __from_token(tracked raw:#token,tracked metadata:#descriptor,elements: ::vstd::map::Map<#key_type,#value_type>)->(tracked out:Self)
                requires raw.loc()==metadata.value().#protocol_location,
                    raw.fragment()==Fragment #expr::#factory(elements)#(.#setters(metadata.value().#cn))*,
                ensures out.instance_id()==metadata.id(),out.resource_location()==raw.loc(),
                    out.raw_fragment()==raw.fragment(),out.map()==elements,
            {Self{raw:Tracked(#contents{token:Some(raw),elements}),metadata}}
            proof fn __split_raw(tracked slot:&mut Tracked<#contents #types>,selected:Fragment #types,remainder:Fragment #types,
                elements: ::vstd::map::Map<#key_type,#value_type>)->(tracked out:#token)
                requires old(slot)@.token is Some,old(slot)@.token->Some_0.fragment()==Fragment #expr::op(selected,remainder),
                ensures final(slot)@.token is Some,final(slot)@.elements==elements,
                    final(slot)@.token->Some_0.loc()==old(slot)@.token->Some_0.loc(),final(slot)@.token->Some_0.fragment()==remainder,
                    out.loc()==old(slot)@.token->Some_0.loc(),out.fragment()==selected,
            {let tracked raw=slot.borrow_mut().token.tracked_take();let tracked(selected,remainder)=raw.split(selected,remainder);
                *slot=Tracked(#contents{token:Some(remainder),elements});selected}
            proof fn __join_raw(tracked slot:&mut Tracked<#contents #types>,tracked other:#token,combined:Fragment #types,
                elements: ::vstd::map::Map<#key_type,#value_type>)
                requires old(slot)@.token is Some,old(slot)@.token->Some_0.loc()==other.loc(),
                    combined==Fragment #expr::op(old(slot)@.token->Some_0.fragment(),other.fragment()),
                ensures final(slot)@.token is Some,final(slot)@.elements==elements,
                    final(slot)@.token->Some_0.loc()==old(slot)@.token->Some_0.loc(),final(slot)@.token->Some_0.fragment()==combined,
            {let tracked raw=slot.borrow_mut().token.tracked_take();let tracked joined=raw.join(other);
                *slot=Tracked(#contents{token:Some(joined),elements});}
            pub proof fn clone(tracked &mut self)->(tracked out:Self)
                ensures out.instance_id()==old(self).instance_id(),out.map()==old(self).map(),
                    final(self).instance_id()==old(self).instance_id(),final(self).map()==old(self).map(),
            {
                ::vstd::prelude::use_type_invariant(&*self);
                let values=self.map();let before=self.raw_fragment();
                let tracked metadata=self.metadata.clone();
                Fragment #expr::unit().op_unit();
                ::vstd::resource::tsm_collections::persistent_map_idempotent(values.to_imap());
                assert(Fragment #expr::op(before,before)==before);
                let tracked raw=Self::__split_raw(&mut self.raw,before,before,values);
                Self::__from_token(raw,metadata,values)
            }
            pub proof fn empty(tracked &mut self)->(tracked out:Self)
                ensures out.instance_id()==old(self).instance_id(),out.map()==::vstd::map::Map::empty(),
                    final(self).instance_id()==old(self).instance_id(),final(self).map()==old(self).map(),
            {
                ::vstd::prelude::use_type_invariant(&*self);let values=self.map();let before=self.raw_fragment();
                let tracked metadata=self.metadata.clone();Fragment #expr::unit().op_unit();
                ::vstd::resource::tsm_collections::persistent_map_join(::vstd::map::Map::<#key_type,#value_type>::empty().to_imap(),values.to_imap());
                assert(::vstd::prelude::ext_equal(::vstd::map::Map::<#key_type,#value_type>::empty().to_imap().union_prefer_right(values.to_imap()),values.to_imap()));
                let selected=Fragment #expr::#factory(::vstd::map::Map::empty())#(.#setters(self.metadata.value().#cn))*;
                assert(Fragment #expr::op(selected,before)==before);
                let tracked raw=Self::__split_raw(&mut self.raw,selected,before,values);
                Self::__from_token(raw,metadata,::vstd::map::Map::empty())
            }
            pub proof fn remove(tracked &mut self,key:#key_type)->(tracked out:#entry #types)
                requires old(self).map().contains_key(key),
                ensures out.instance_id()==old(self).instance_id(),out.key()==key,out.value()==old(self).map()[key],
                    final(self).instance_id()==old(self).instance_id(),final(self).map()==old(self).map().remove(key),
            {
                ::vstd::prelude::use_type_invariant(&*self);let values=self.map();let value=values[key];
                let singleton=::vstd::map::Map::empty().insert(key,value);let remainder_values=values.remove(key);
                let before=self.raw_fragment();let tracked metadata=self.metadata.clone();Fragment #expr::unit().op_unit();
                ::vstd::resource::tsm_collections::persistent_map_join(singleton.to_imap(),remainder_values.to_imap());
                assert(::vstd::prelude::ext_equal(singleton.to_imap().union_prefer_right(remainder_values.to_imap()),values.to_imap()));
                let selected=Fragment #expr::#factory(singleton)#(.#setters(self.metadata.value().#cn))*;
                let remainder=Fragment #expr::#factory(remainder_values)#(.#setters(self.metadata.value().#cn))*;
                assert(Fragment #expr::op(selected,remainder)==before);
                let tracked raw=Self::__split_raw(&mut self.raw,selected,remainder,remainder_values);
                <#entry #types>::__from_token(raw,metadata,key,value)
            }
            pub proof fn insert(tracked &mut self,tracked item:#entry #types)
                requires old(self).instance_id()==item.instance_id(),!old(self).map().contains_key(item.key()),
                ensures final(self).instance_id()==old(self).instance_id(),
                    final(self).map()==old(self).map().insert(item.key(),item.value()),
            {
                ::vstd::prelude::use_type_invariant(&*self);::vstd::prelude::use_type_invariant(&item);
                self.metadata.agrees(&item.metadata);let values=self.map();let key=item.key();let value=item.value();
                let singleton=::vstd::map::Map::empty().insert(key,value);Fragment #expr::unit().op_unit();
                ::vstd::resource::tsm_collections::persistent_map_join(values.to_imap(),singleton.to_imap());
                assert(::vstd::prelude::ext_equal(values.to_imap().union_prefer_right(singleton.to_imap()),values.insert(key,value).to_imap()));
                let combined=Fragment #expr::#factory(values.insert(key,value))#(.#setters(self.metadata.value().#cn))*;
                assert(combined==Fragment #expr::op(self.raw_fragment(),item.raw_fragment()));
                let tracked raw=item.raw.get().tracked_unwrap();Self::__join_raw(&mut self.raw,raw,combined,values.insert(key,value));
            }
        }
    })
}
