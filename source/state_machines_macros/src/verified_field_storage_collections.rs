//! Finite collection owners retain actual protocol resources for every element.
use crate::ast::{Field, ShardableType};
use crate::verified_field_storage_roles::Context;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use verus_syn::Error;

/// A bulk owner complements the strict singleton owner for a field. Empty
/// collections come from a checked split of a real mutable owner; the
/// original rights are restored and only constant agreements are duplicated.
pub fn wrapper(field: &Field, cx: &Context<'_>, reservation: &TokenStream) -> Result<TokenStream, Error> {
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
    let singleton = &field.name;
    let accessor = match &field.stype {
        ShardableType::Set(_) => format_ident!("set"),
        _ => format_ident!("multiset"),
    };
    let factory = format_ident!("field_{singleton}");
    let setters: Vec<_> =
        constants.iter().map(|f| format_ident!("with_{}", f.name)).collect();
    let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
    let (name, collection, element, empty, unit, remove, member, size) =
        match &field.stype {
            ShardableType::Multiset(element) => (
                format_ident!("{singleton}_collection"),
                quote! {::vstd::multiset::Multiset<#element>},
                element,
                quote! {::vstd::multiset::Multiset::<#element>::empty()},
                quote! {::vstd::multiset::Multiset::<#element>::singleton(element)},
                quote! {values.remove(element)},
                quote! {old(self).#accessor().count(element)>0},
                quote! {self.#accessor().len()},
            ),
            ShardableType::Set(element) => (
                format_ident!("{singleton}_collection"),
                quote! {::vstd::set::Set<#element>},
                element,
                quote! {::vstd::set::Set::<#element>::empty()},
                quote! {::vstd::set::Set::<#element>::empty().insert(element)},
                quote! {values.remove(element)},
                quote! {old(self).#accessor().contains(element)},
                quote! {self.#accessor().len()},
            ),
            _ => return Err(Error::new(singleton.span(), "bulk owners require Set or Multiset")),
        };
    fn reserves(tokens:TokenStream,wanted:&str)->bool{
        tokens.into_iter().any(|token|match token{
            proc_macro2::TokenTree::Ident(name)=>name==wanted,
            proc_macro2::TokenTree::Group(group)=>reserves(group.stream(),wanted),_=>false,
        })
    }
    let mut contents_name=format!("{singleton}_collection_contents");
    while reserves((*decl).clone(),&contents_name) || reserves(reservation.clone(),&contents_name){contents_name.push('_');}
    let contents = format_ident!("{contents_name}");
    let removal_normalization=match &field.stype {
        ShardableType::Multiset(_)=>quote! {assert(::vstd::prelude::ext_equal(values,::vstd::multiset::Multiset::singleton(element).add(values.remove(element))));},
        ShardableType::Set(_)=>quote! {assert(::vstd::prelude::ext_equal(values,::vstd::set::Set::empty().insert(element).union(values.remove(element))));},
        _=>unreachable!(),
    };
    let empty_normalization=if matches!(field.stype,ShardableType::Set(_)) {quote! {
        ::vstd::resource::tsm_collections::set_join(::vstd::set::Set::<#element>::empty().to_iset(),values.to_iset());
        assert(::vstd::prelude::ext_equal(::vstd::set::Set::<#element>::empty().to_iset().union(values.to_iset()),values.to_iset()));
    }}else{quote!{}};
    let removal_carrier_normalization=if matches!(field.stype,ShardableType::Set(_)) {quote! {
        let singleton=::vstd::set::Set::empty().insert(element);
        let remainder_values=values.remove(element);
        assert(singleton.to_iset().disjoint(remainder_values.to_iset()));
        ::vstd::resource::tsm_collections::set_join(singleton.to_iset(),remainder_values.to_iset());
        assert(::vstd::prelude::ext_equal(singleton.to_iset().union(remainder_values.to_iset()),values.to_iset()));
    }}else{quote!{}};
    let insertion_carrier_normalization=if matches!(field.stype,ShardableType::Set(_)) {quote! {
        let singleton=::vstd::set::Set::empty().insert(element);
        assert(values.to_iset().disjoint(singleton.to_iset()));
        ::vstd::resource::tsm_collections::set_join(values.to_iset(),singleton.to_iset());
        assert(::vstd::prelude::ext_equal(values.to_iset().union(singleton.to_iset()),values.insert(element).to_iset()));
    }}else{quote!{}};
    let join_carrier_normalization=if matches!(field.stype,ShardableType::Set(_)) {quote! {
        assert(values.to_iset().disjoint(other_values.to_iset()));
        ::vstd::resource::tsm_collections::set_join(values.to_iset(),other_values.to_iset());
        assert(::vstd::prelude::ext_equal(values.to_iset().union(other_values.to_iset()),values.union(other_values).to_iset()));
    }}else{quote!{}};
    let insert_requires = match &field.stype {
        ShardableType::Set(_) => quote! {!old(self).#accessor().contains(single.element()),},
        _ => quote! {},
    };
    let insert_shape = match &field.stype {
        ShardableType::Multiset(_) => quote! {
            old(self).#accessor().add(::vstd::multiset::Multiset::singleton(single.element()))
        },
        ShardableType::Set(_) => quote! {old(self).#accessor().insert(single.element())},
        _ => unreachable!(),
    };
    let merge_requires = match &field.stype {
        ShardableType::Set(_) => quote! {old(self).#accessor().disjoint(other.#accessor()),},
        _ => quote! {},
    };
    let merge_shape = match &field.stype {
        ShardableType::Multiset(_) => quote! {
            old(self).#accessor().add(other.#accessor())
        },
        ShardableType::Set(_) => quote! {
            old(self).#accessor().union(other.#accessor())
        },
        _ => unreachable!(),
    };
    let merge_value = match &field.stype {
        ShardableType::Multiset(_) => quote! {values.add(other_values)},
        ShardableType::Set(_) => quote! {values.union(other_values)},
        _ => unreachable!(),
    };
    Ok(quote! {
        #(#attrs)*#[allow(non_camel_case_types)]
        tracked struct #contents #decl #where_clause {
            token:Option<#token>,ghost elements:#collection,
        }
        #(#attrs)*#[allow(non_camel_case_types)]
        pub tracked struct #name #decl #where_clause {
            raw:Tracked<#contents #types>,metadata:#descriptor,
        }
        impl #decl #name #types #where_clause {
            #[verifier::type_invariant]
            spec fn invariant(self)->bool {
                self.raw@.token is Some
                && self.raw@.token->Some_0.loc()==self.metadata.value().#protocol_location
                && self.raw@.token->Some_0.fragment()==
                    Fragment #expr::#factory(self.raw@.elements)
                        #(.#setters(self.metadata.value().#cn))*
            }
            pub closed spec fn instance_id(&self)->::vstd::resource::Loc {self.metadata.id()}
            pub closed spec fn resource_location(&self)->::vstd::resource::Loc {self.raw@.token->Some_0.loc()}
            pub closed spec fn raw_fragment(&self)->Fragment #types {self.raw@.token->Some_0.fragment()}
            pub closed spec fn #accessor(&self)->#collection {self.raw@.elements}
            pub closed spec fn len(&self)->nat {#size}
            proof fn __from_token(tracked raw:#token,tracked metadata:#descriptor,elements:#collection)->(tracked out:Self)
                requires
                    raw.loc()==metadata.value().#protocol_location,
                    raw.fragment()==Fragment #expr::#factory(elements)
                        #(.#setters(metadata.value().#cn))*,
                ensures
                    out.instance_id()==metadata.id(),
                    out.resource_location()==raw.loc(),
                    out.raw_fragment()==raw.fragment(),
                    out.#accessor()==elements,
            {Self{raw:Tracked(#contents{token:Some(raw),elements}),metadata}}
            pub proof fn borrow_token(tracked &self)->(tracked out:&#token)
                ensures out.loc()==self.resource_location(),out.fragment()==self.raw_fragment()
            {
                ::vstd::prelude::use_type_invariant(self);
                self.raw.borrow().token.tracked_borrow()
            }
            proof fn __split_raw(tracked slot:&mut Tracked<#contents #types>,
                selected:Fragment #types,remainder:Fragment #types,elements:#collection)->(tracked out:#token)
                requires old(slot)@.token is Some,
                    old(slot)@.token->Some_0.fragment()==Fragment #expr::op(selected,remainder),
                ensures final(slot)@.token is Some,final(slot)@.elements==elements,
                    final(slot)@.token->Some_0.loc()==old(slot)@.token->Some_0.loc(),
                    final(slot)@.token->Some_0.fragment()==remainder,
                    out.loc()==old(slot)@.token->Some_0.loc(),out.fragment()==selected,
            {
                let tracked current=slot.borrow_mut().token.tracked_take();
                let tracked (selected,remainder)=current.split(selected,remainder);
                *slot=Tracked(#contents{token:Some(remainder),elements});
                selected
            }
            proof fn __join_raw(tracked slot:&mut Tracked<#contents #types>,
                tracked other:#token,combined:Fragment #types,elements:#collection)
                requires old(slot)@.token is Some,old(slot)@.token->Some_0.loc()==other.loc(),
                    combined==Fragment #expr::op(old(slot)@.token->Some_0.fragment(),other.fragment()),
                ensures final(slot)@.token is Some,final(slot)@.elements==elements,
                    final(slot)@.token->Some_0.loc()==old(slot)@.token->Some_0.loc(),
                    final(slot)@.token->Some_0.fragment()==combined,
            {
                let tracked current=slot.borrow_mut().token.tracked_take();
                let tracked joined=current.join(other);
                *slot=Tracked(#contents{token:Some(joined),elements});
            }
            pub proof fn empty(tracked &mut self)->(tracked out:Self)
                ensures
                    out.instance_id()==old(self).instance_id(),out.#accessor()==#empty,
                    final(self).instance_id()==old(self).instance_id(),
                    final(self).#accessor()==old(self).#accessor(),
            {
                broadcast use ::vstd::multiset::group_multiset_axioms;
                Fragment #expr::unit().op_unit();
                ::vstd::prelude::use_type_invariant(&*self);
                let before=self.raw_fragment();
                before.op_unit();
                Fragment #expr::commutative(Fragment #expr::unit(),before);
                let values=self.#accessor();
                let tracked metadata=self.metadata.clone();
                let target=Fragment #expr::#factory(#empty)
                    #(.#setters(self.metadata.value().#cn))*;
                #empty_normalization
                assert(Fragment #expr::op(target,before)==before);
                let tracked empty=Self::__split_raw(&mut self.raw,target,before,values);
                Self::__from_token(empty,metadata,#empty)
            }
            pub proof fn remove(tracked &mut self,element:#element)->(tracked out:#singleton #types)
                requires #member,
                ensures
                    final(self).instance_id()==old(self).instance_id(),
                    final(self).#accessor()==old(self).#accessor().remove(element),
                    out.instance_id()==old(self).instance_id(),out.element()==element,
            {
                broadcast use ::vstd::multiset::group_multiset_axioms;
                Fragment #expr::unit().op_unit();
                ::vstd::prelude::use_type_invariant(&*self);
                let values=self.#accessor();
                let before=self.raw_fragment();
                let tracked metadata=self.metadata.clone();
                let selected=Fragment #expr::#factory(#unit)
                    #(.#setters(self.metadata.value().#cn))*;
                let remainder=Fragment #expr::#factory(#remove)
                    #(.#setters(self.metadata.value().#cn))*;
                #removal_normalization
                #removal_carrier_normalization
                assert(Fragment #expr::op(selected,remainder)==before);
                let tracked selected=Self::__split_raw(&mut self.raw,selected,remainder,values.remove(element));
                <#singleton #types>::__from_token(selected,metadata,element)
            }
            pub proof fn insert(tracked &mut self,tracked single:#singleton #types)
                requires
                    old(self).instance_id()==single.instance_id(),
                    #insert_requires
                ensures
                    final(self).instance_id()==old(self).instance_id(),
                    final(self).#accessor()==#insert_shape,
            {
                broadcast use ::vstd::multiset::group_multiset_axioms;
                Fragment #expr::unit().op_unit();
                ::vstd::prelude::use_type_invariant(&*self);
                ::vstd::prelude::use_type_invariant(&single);
                self.metadata.agrees(&single.metadata);
                let values=self.#accessor();
                let element=single.element();
                let combined=Fragment #expr::op(self.raw_fragment(),single.raw_fragment());
                #insertion_carrier_normalization
                assert(combined==Fragment #expr::#factory(values.insert(element))
                    #(.#setters(self.metadata.value().#cn))*);
                let tracked single_raw=single.raw.get().tracked_unwrap();
                Self::__join_raw(&mut self.raw,single_raw,combined,values.insert(element));
            }
            pub proof fn join(tracked &mut self,tracked other:Self)
                requires
                    old(self).instance_id()==other.instance_id(),
                    #merge_requires
                ensures
                    final(self).instance_id()==old(self).instance_id(),
                    final(self).#accessor()==#merge_shape,
            {
                broadcast use ::vstd::multiset::group_multiset_axioms;
                Fragment #expr::unit().op_unit();
                ::vstd::prelude::use_type_invariant(&*self);
                ::vstd::prelude::use_type_invariant(&other);
                self.metadata.agrees(&other.metadata);
                let values=self.#accessor();
                let other_values=other.#accessor();
                let combined=Fragment #expr::op(self.raw_fragment(),other.raw_fragment());
                #join_carrier_normalization
                assert(combined==Fragment #expr::#factory(#merge_value)
                    #(.#setters(self.metadata.value().#cn))*);
                let tracked other_raw=other.raw.get().token.tracked_unwrap();
                Self::__join_raw(&mut self.raw,other_raw,combined,#merge_value);
            }
        }
    })
}
