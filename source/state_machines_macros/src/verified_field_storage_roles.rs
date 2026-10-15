//! Storage role owners always retain an actual token. Ghost payload observations
//! describe the owned role; they never stand in for the physical permission.
use crate::ast::{Field, ShardableType};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use verus_syn::{Attribute, Error, Ident};

pub struct Context<'a> {
    pub decl: &'a TokenStream,
    pub types: &'a TokenStream,
    pub expr: &'a TokenStream,
    pub where_clause: &'a TokenStream,
    pub attrs: &'a [Attribute],
    pub token: &'a TokenStream,
    pub descriptor: &'a TokenStream,
    pub protocol_location: &'a Ident,
    pub constants: &'a [&'a Field],
}

/// Strict PRESENT Bool/Option/Set/Multiset owners and actual Count contributions.
/// Initializer/transition adapters must obtain the constructor input by an
/// actual checked split or exchange; no public wrapping or empty allocation.
pub fn wrapper(field: &Field, cx: &Context<'_>) -> Result<TokenStream, Error> {
    wrapper_mode(field, cx, false)
}

/// Wide adapters restore a complete role through its private constructor.
/// Bind their immutable observation cache to the exact actual fragment shape.
pub fn wide_wrapper(field: &Field, cx: &Context<'_>) -> Result<TokenStream, Error> {
    wrapper_mode(field, cx, true)
}

fn wrapper_mode(field: &Field, cx: &Context<'_>, cached_option: bool) -> Result<TokenStream, Error> {
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
    let factory = format_ident!("field_{name}");
    let getter = format_ident!("value_{name}");
    let setters: Vec<_> = constants
        .iter()
        .map(|f| format_ident!("with_{}", f.name))
        .collect();
    let constant_names: Vec<_> = constants.iter().map(|f| &f.name).collect();
    let (payload, constructor_argument, constructor_value, native_value, getters, extra) =
        match &field.stype {
            ShardableType::Variable(value_type) => (
                quote! {},
                quote! {},
                quote! {},
                quote! {self.raw@->Some_0.fragment().#getter()},
                quote! {pub closed spec fn value(&self)->#value_type {self.raw@->Some_0.fragment().#getter()}},
                quote! {out.value()==raw.fragment().#getter(),},
            ),
            ShardableType::Count => (
                quote! {},
                quote! {},
                quote! {},
                quote! {self.raw@->Some_0.fragment().#getter()},
                quote! {pub closed spec fn count(&self)->nat {self.raw@->Some_0.fragment().#getter()}},
                quote! {},
            ),
            ShardableType::Bool | ShardableType::PersistentBool => (
                quote! {},
                quote! {},
                quote! {},
                quote! {true},
                quote! {pub open spec fn value(&self)->bool {true}},
                quote! {},
            ),
            ShardableType::Option(element) if !cached_option => (
                quote! {},
                quote! {element:#element,},
                quote! {},
                quote! {Some(self.raw@->Some_0.fragment().#getter()->Some_0)},
                quote! {pub closed spec fn value(&self)->#element {self.raw@->Some_0.fragment().#getter()->Some_0}},
                quote! {out.value()==element,},
            ),
            ShardableType::Option(element) | ShardableType::PersistentOption(element) => (
                quote! {ghost element_value:#element,},
                quote! {element:#element,},
                quote! {element_value:element,},
                quote! {Some(self.element_value)},
                quote! {pub closed spec fn value(&self)->#element {self.element_value}},
                quote! {out.value()==element,},
            ),
            ShardableType::Set(element) | ShardableType::PersistentSet(element) => (
                quote! {ghost element_value:#element,},
                quote! {element:#element,},
                quote! {element_value:element,},
                quote! {::vstd::set::Set::<#element>::empty().insert(self.element_value)},
                quote! {pub closed spec fn element(&self)->#element {self.element_value}},
                quote! {out.element()==element,},
            ),
            ShardableType::PersistentMap(key_type,value_type) => (
                quote! {ghost key_value:#key_type,ghost element_value:#value_type,},
                quote! {key:#key_type,value:#value_type,},
                quote! {key_value:key,element_value:value,},
                quote! {::vstd::map::Map::<#key_type,#value_type>::empty().insert(self.key_value,self.element_value)},
                quote! {pub closed spec fn key(&self)->#key_type {self.key_value} pub closed spec fn value(&self)->#value_type {self.element_value}},
                quote! {out.key()==key,out.value()==value,},
            ),
            ShardableType::Multiset(element) => (
                quote! {ghost element_value:#element,},
                quote! {element:#element,},
                quote! {element_value:element,},
                quote! {::vstd::multiset::Multiset::<#element>::singleton(self.element_value)},
                quote! {pub closed spec fn element(&self)->#element {self.element_value}},
                quote! {out.element()==element,},
            ),
            _ => {
                return Err(Error::new(
                    name.span(),
                    "unsupported strict physical role owner",
                ))
            }
        };
    let borrow_observation = match &field.stype {
        ShardableType::Variable(_) => {
            let owns = format_ident!("owns_{name}");
            quote! {out.fragment().#owns(),out.fragment().#getter()==self.value(),}
        }
        ShardableType::Count => quote! {out.fragment().#getter()==self.count(),},
        ShardableType::Bool | ShardableType::PersistentBool => quote! {out.fragment().#getter(),},
        ShardableType::Option(_) | ShardableType::PersistentOption(_) => quote! {out.fragment().#getter()==Some(self.value()),},
        ShardableType::Set(_) | ShardableType::PersistentSet(_) => {
            let contains = format_ident!("contains_{name}");
            quote! {out.fragment().#contains(self.element()),}
        }
        ShardableType::PersistentMap(..) => quote! {},
        ShardableType::Multiset(element) => {
            quote! {out.fragment().#getter()==::vstd::multiset::Multiset::<#element>::singleton(self.element()),}
        }
        _ => unreachable!(),
    };
    let constructor_native = match &field.stype {
        ShardableType::Variable(_) | ShardableType::Count => quote! {raw.fragment().#getter()},
        ShardableType::Bool | ShardableType::PersistentBool => quote! {true},
        ShardableType::Option(_) | ShardableType::PersistentOption(_) => quote! {Some(element)},
        ShardableType::Set(element) | ShardableType::PersistentSet(element) => {
            quote! {::vstd::set::Set::<#element>::empty().insert(element)}
        }
        ShardableType::PersistentMap(key_type,value_type) => quote! {::vstd::map::Map::<#key_type,#value_type>::empty().insert(key,value)},
        ShardableType::Multiset(element) => {
            quote! {::vstd::multiset::Multiset::<#element>::singleton(element)}
        }
        _ => unreachable!(),
    };
    let present = if matches!(field.stype, ShardableType::Option(..)) {
        quote! {&& self.raw@->Some_0.fragment().#getter() is Some}
    } else { quote! {} };
    Ok(quote! {
        #(#attrs)*#[allow(non_camel_case_types)]
        pub tracked struct #name #decl #where_clause {
            raw:Tracked<Option<#token>>,metadata:#descriptor,#payload
        }
        impl #decl #name #types #where_clause {
            #[verifier::type_invariant]
            spec fn invariant(self)->bool {
                self.raw@ is Some
                &&self.raw@->Some_0.loc()==self.metadata.value().#protocol_location
                #present
                &&self.raw@->Some_0.fragment()==Fragment #expr::#factory(#native_value)
                    #(.#setters(self.metadata.value().#constant_names))*
            }
            pub closed spec fn instance_id(&self)->::vstd::resource::Loc {self.metadata.id()}
            pub closed spec fn resource_location(&self)->::vstd::resource::Loc {self.raw@->Some_0.loc()}
            pub closed spec fn raw_fragment(&self)->Fragment #types {self.raw@->Some_0.fragment()}
            #getters
            pub proof fn borrow_token(tracked &self)->(tracked out:&#token)
                ensures out.loc()==self.resource_location(),out.fragment()==self.raw_fragment(),#borrow_observation
            {::vstd::prelude::use_type_invariant(self);self.raw.borrow().tracked_borrow()}
            proof fn __from_token(tracked raw:#token,tracked metadata:#descriptor,#constructor_argument)
                ->(tracked out:Self)
                requires raw.loc()==metadata.value().#protocol_location,
                    raw.fragment()==Fragment #expr::#factory(#constructor_native)
                        #(.#setters(metadata.value().#constant_names))*,
                ensures out.instance_id()==metadata.id(),out.resource_location()==raw.loc(),
                    out.raw_fragment()==raw.fragment(),#extra
            {Self{raw:Tracked(Some(raw)),metadata,#constructor_value}}
        }
    })
}

/// Original singleton reader Have/Guard property, checked for every compatible
/// completion. The result lifetime follows the real reader token, not Instance.
pub fn guard_method(
    field: &Field,
    property: &crate::ast::Transition,
    cx: &Context<'_>,
) -> Result<TokenStream, Error> {
    use crate::ast::{MonoidElt, MonoidStmtType, SpecialOp, SplitKind, TransitionStmt};
    use quote::ToTokens;
    fn collect<'a>(
        stmt: &'a TransitionStmt,
        out: &mut Vec<(&'a Ident, &'a SpecialOp)>,
    ) -> Result<(), Error> {
        match stmt {
            TransitionStmt::Block(_, children) => {
                for child in children {
                    collect(child, out)?;
                }
                Ok(())
            }
            TransitionStmt::Split(_, split, children) => {
                let SplitKind::Special(name, op, _, None) = &**split else {
                    return Err(Error::new(
                        *stmt.get_span(),
                        "physical reader guard requires singleton Have then Guard",
                    ));
                };
                out.push((name, op));
                for child in children {
                    collect(child, out)?;
                }
                Ok(())
            }
            _ => Err(Error::new(
                *stmt.get_span(),
                "physical reader guard requires singleton Have then Guard",
            )),
        }
    }
    let ShardableType::Multiset(element) = &field.stype else {
        return Err(Error::new(
            field.name.span(),
            "physical reader guard requires an actual multiset element owner",
        ));
    };
    let [parameter] = property.params.as_slice() else {
        return Err(Error::new(
            property.name.span(),
            "physical reader guard requires one element parameter",
        ));
    };
    let mut operations = Vec::new();
    collect(&property.body, &mut operations)?;
    let guard = match operations.as_slice() {
        [(
            name,
            SpecialOp {
                stmt: MonoidStmtType::Have,
                elt: MonoidElt::SingletonMultiset(value),
            },
        ), (
            _,
            SpecialOp {
                stmt: MonoidStmtType::Guard,
                elt: MonoidElt::OptionSome(Some(guard)),
            },
        )] if *name == &field.name
            && value.to_token_stream().to_string() == parameter.name.to_string() =>
        {
            guard
        }
        _ => {
            return Err(Error::new(
                property.name.span(),
                "physical reader guard requires singleton Have then optional Guard",
            ))
        }
    };
    let guard_type = if guard.to_token_stream().to_string() == parameter.name.to_string() {
        element.clone()
    } else if let verus_syn::Expr::Field(projection) = guard {
        if projection.base.to_token_stream().to_string() != parameter.name.to_string() {
            return Err(Error::new(
                property.name.span(),
                "physical reader guard projection must read its supplied element",
            ));
        }
        let verus_syn::Member::Unnamed(index) = &projection.member else {
            return Err(Error::new(
                property.name.span(),
                "physical reader guard supports tuple projections",
            ));
        };
        let verus_syn::Type::Tuple(tuple) = element else {
            return Err(Error::new(
                property.name.span(),
                "physical reader guard projection requires a tuple element",
            ));
        };
        tuple
            .elems
            .iter()
            .nth(index.index as usize)
            .cloned()
            .ok_or_else(|| {
                Error::new(
                    property.name.span(),
                    "physical reader guard tuple index out of range",
                )
            })?
    } else {
        return Err(Error::new(
            property.name.span(),
            "physical reader guard requires its supplied element or a tuple projection",
        ));
    };
    let mut occupied: std::collections::HashSet<_> =
        property.params.iter().map(|p| p.name.to_string()).collect();
    occupied.insert(field.name.to_string());
    for f in cx.constants {
        occupied.insert(f.name.to_string());
    }
    fn reserve(tokens: TokenStream, names: &mut std::collections::HashSet<String>) {
        for t in tokens {
            match t {
                proc_macro2::TokenTree::Ident(n) => {
                    names.insert(n.to_string());
                }
                proc_macro2::TokenTree::Group(g) => reserve(g.stream(), names),
                _ => {}
            }
        }
    }
    reserve(cx.decl.clone(), &mut occupied);
    reserve(cx.where_clause.clone(), &mut occupied);
    let field_type = field.get_type();
    reserve(quote! {#field_type}, &mut occupied);
    reserve(cx.descriptor.clone(), &mut occupied);
    for p in &property.params {
        let n = &p.name;
        let t = &p.ty;
        reserve(quote! {#n #t}, &mut occupied)
    }
    for (f, op) in &operations {
        reserve(quote! {#f}, &mut occupied);
        match &op.elt {
            MonoidElt::OptionSome(e) => reserve(quote! {#e}, &mut occupied),
            MonoidElt::SingletonKV(k, v) => reserve(quote! {#k #v}, &mut occupied),
            MonoidElt::SingletonMultiset(e)
            | MonoidElt::SingletonSet(e)
            | MonoidElt::General(e) => reserve(quote! {#e}, &mut occupied),
            _ => {}
        }
    }
    let lifetime_occupied = occupied.clone();
    let mut fresh = |label: &str| {
        let mut name = format!("__tsm_reader_guard_{label}");
        while occupied.contains(&name) {
            name.push('_');
        }
        occupied.insert(name.clone());
        Ident::new(&name, proc_macro2::Span::mixed_site())
    };
    let output = fresh("result");
    let mut lifetime_name = "__tsm_reader_guard".to_string();
    while lifetime_occupied.contains(&lifetime_name) {
        lifetime_name.push('_');
    }
    let lifetime = verus_syn::Lifetime::new(
        &format!("'{lifetime_name}"),
        proc_macro2::Span::mixed_site(),
    );
    let input = fresh("owner");
    let fragment = fresh("fragment");
    let frame = fresh("frame");
    let pre = fresh("pre");
    let name = &property.name;
    let field_name = &field.name;
    let parameter_name = &parameter.name;
    let parameter_type = &parameter.ty;
    let types = cx.types;
    let expr = cx.expr;
    let enabled = format_ident!("{}_enabled", name);
    let owners = format_ident!("{}_owners_enabled", name);
    let guard_frame = format_ident!("{}_frame", name);
    let guarded = format_ident!("{}_guarded", name);
    Ok(quote! {
        pub proof fn #name<#lifetime>(tracked &self,#parameter_name:#parameter_type,
            tracked #input:&#lifetime #field_name #types)
            ->(tracked #output:&#lifetime #guard_type)
            requires #input.instance_id()==self.id(),#input.element()==#parameter_name,
            ensures *#output==#guard,
        {
            ::vstd::prelude::use_type_invariant(#input);
            self.metadata.agrees(&#input.metadata);
            let #fragment=#input.raw@->Some_0.fragment();
            assert forall|#frame:Fragment #types,#pre:State #types|
                #pre.invariant()&&Fragment #expr::op(#fragment,#frame)==Protocol #expr::embed(#pre)
                implies State #expr::#enabled(#pre,#parameter_name)
                    &&State #expr::#owners(#pre,#fragment,Fragment #expr::empty(),#parameter_name) by {
                assert(#pre.#field_name.count(#parameter_name)>=1);
            }
            Protocol #expr::#guard_frame(#fragment,#parameter_name);
            assert(Protocol #expr::#guarded(#fragment,#parameter_name)==IMap::empty().insert(0int,#guard));
            ::vstd::resource::tsm_helpers::guard_value(#input.borrow_token(),0int,#guard)
        }
    })
}

/// Split CURRENT Count ownership by consuming the actual slot owner and restoring
/// it before the nominal invariant boundary. No borrowed owned-empty primitive.
pub fn count_split_method(field: &Field, cx: &Context<'_>) -> Result<TokenStream, Error> {
    if !matches!(field.stype, ShardableType::Count) {
        return Err(Error::new(
            field.name.span(),
            "physical split requires a Count owner",
        ));
    }
    let name = &field.name;
    let factory = format_ident!("field_{name}");
    let getter = format_ident!("value_{name}");
    let token = cx.token;
    let types = cx.types;
    let expr = cx.expr;
    let setters: Vec<_> = cx
        .constants
        .iter()
        .map(|f| format_ident!("with_{}", f.name))
        .collect();
    let getters: Vec<_> = cx
        .constants
        .iter()
        .map(|f| format_ident!("value_{}", f.name))
        .collect();
    let law = format_ident!("split_{}_law", name);
    Ok(quote! {
        proof fn __split_raw(tracked slot:&mut Tracked<Option<#token>>,amount:nat)->(tracked out:#token)
            requires old(slot)@ is Some,
                amount<=old(slot)@->Some_0.fragment().#getter(),
                old(slot)@->Some_0.fragment()==Fragment #expr::#factory(old(slot)@->Some_0.fragment().#getter())
                    #(.#setters(old(slot)@->Some_0.fragment().#getters()))*,
            ensures final(slot)@ is Some,
                final(slot)@->Some_0.loc()==old(slot)@->Some_0.loc(),out.loc()==old(slot)@->Some_0.loc(),
                out.fragment()==Fragment #expr::#factory(amount)
                    #(.#setters(old(slot)@->Some_0.fragment().#getters()))*,
                final(slot)@->Some_0.fragment()==Fragment #expr::#factory((old(slot)@->Some_0.fragment().#getter()-amount) as nat)
                    #(.#setters(old(slot)@->Some_0.fragment().#getters()))*,
        {
            let before=slot@->Some_0.fragment();
            let tracked owned=slot.borrow_mut().tracked_take();
            before.#law(amount);
            let selected=Fragment #expr::#factory(amount)#(.#setters(before.#getters()))*;
            let remainder=Fragment #expr::#factory((before.#getter()-amount) as nat)#(.#setters(before.#getters()))*;
            assert(Fragment #expr::op(selected,remainder)==before);
            let tracked (selected,remainder)=owned.split(selected,remainder);
            *slot=Tracked(Some(remainder));selected
        }
        pub proof fn split(tracked &mut self,amount:nat)->(tracked out:Self)
            requires amount<=old(self).count(),
            ensures final(self).instance_id()==old(self).instance_id(),out.instance_id()==old(self).instance_id(),
                out.count()==amount,final(self).count()==old(self).count()-amount,
        {
            ::vstd::prelude::use_type_invariant(&*self);
            let tracked metadata=self.metadata.clone();
            let tracked selected=Self::__split_raw(&mut self.raw,amount);
            Self::__from_token(selected,metadata)
        }
    })
}

pub fn count_join_method(field: &Field, cx: &Context<'_>) -> Result<TokenStream, Error> {
    if !matches!(field.stype, ShardableType::Count) {
        return Err(Error::new(
            field.name.span(),
            "physical join requires Count ownership",
        ));
    }
    let name = &field.name;
    let factory = format_ident!("field_{name}");
    let getter = format_ident!("value_{name}");
    let token = cx.token;
    let expr = cx.expr;
    let law = format_ident!("split_{}_law", name);
    let setters: Vec<_> = cx
        .constants
        .iter()
        .map(|f| format_ident!("with_{}", f.name))
        .collect();
    let getters: Vec<_> = cx
        .constants
        .iter()
        .map(|f| format_ident!("value_{}", f.name))
        .collect();
    Ok(quote! {
        proof fn __join_raw(tracked slot:&mut Tracked<Option<#token>>,tracked other:#token)
            requires old(slot)@ is Some,old(slot)@->Some_0.loc()==other.loc(),
                old(slot)@->Some_0.fragment()==Fragment #expr::#factory(old(slot)@->Some_0.fragment().#getter())
                    #(.#setters(old(slot)@->Some_0.fragment().#getters()))*,
                other.fragment()==Fragment #expr::#factory(other.fragment().#getter())
                    #(.#setters(old(slot)@->Some_0.fragment().#getters()))*,
            ensures final(slot)@ is Some,final(slot)@->Some_0.loc()==old(slot)@->Some_0.loc(),
                final(slot)@->Some_0.fragment()==Fragment #expr::#factory(old(slot)@->Some_0.fragment().#getter()+other.fragment().#getter())
                    #(.#setters(old(slot)@->Some_0.fragment().#getters()))*,
        {
            let first=slot@->Some_0.fragment();let second=other.fragment();
            let combined=Fragment #expr::#factory(first.#getter()+second.#getter())#(.#setters(first.#getters()))*;
            combined.#law(first.#getter());
            assert(Fragment #expr::op(first,second)==combined);
            let tracked first=slot.borrow_mut().tracked_take();
            let tracked combined=first.join(other);*slot=Tracked(Some(combined));
        }
        pub proof fn join(tracked &mut self,tracked other:Self)
            requires old(self).instance_id()==other.instance_id(),
            ensures final(self).instance_id()==old(self).instance_id(),final(self).count()==old(self).count()+other.count(),
        {
            ::vstd::prelude::use_type_invariant(&*self);::vstd::prelude::use_type_invariant(&other);
            self.metadata.agrees(&other.metadata);
            Self::__join_raw(&mut self.raw,other.raw.get().tracked_unwrap());
        }
    })
}

/// Persistent owners duplicate by splitting their actual idempotent fragment.
/// The mutable source retains its real token before its invariant closes.
pub fn persistent_clone_method(field:&Field,cx:&Context<'_>)->Result<TokenStream,Error>{
    let name=&field.name;
    let token=cx.token;
    let expr=cx.expr;
    let (arguments,preservation)=match &field.stype{
        ShardableType::PersistentBool=>(quote!{},quote!{out.value()==old(self).value(),final(self).value()==old(self).value(),}),
        ShardableType::PersistentOption(_)=>(quote!{self.value(),},quote!{out.value()==old(self).value(),final(self).value()==old(self).value(),}),
        ShardableType::PersistentSet(_)=>(quote!{self.element(),},quote!{out.element()==old(self).element(),final(self).element()==old(self).element(),}),
        ShardableType::PersistentMap(..)=>(quote!{self.key(),self.value(),},quote!{out.key()==old(self).key(),out.value()==old(self).value(),final(self).key()==old(self).key(),final(self).value()==old(self).value(),}),
        _=>return Err(Error::new(name.span(),"persistent clone requires persistent Bool, Option, Set or Map")),
    };
    let normalization=match &field.stype{
        ShardableType::PersistentBool=>quote!{::vstd::resource::tsm_persistent::persistent_count_idempotent(self.raw_fragment().#name);},
        ShardableType::PersistentOption(_)=>quote!{::vstd::resource::tsm_collections::persistent_option_idempotent(Some(self.value()));},
        ShardableType::PersistentSet(_)=>quote!{::vstd::resource::tsm_collections::persistent_set_idempotent(::vstd::set::Set::empty().insert(self.element()).to_iset());},
        ShardableType::PersistentMap(..)=>quote!{::vstd::resource::tsm_collections::persistent_map_idempotent(::vstd::map::Map::empty().insert(self.key(),self.value()).to_imap());},
        _=>unreachable!(),
    };
    Ok(quote!{
        proof fn __persistent_clone_raw(tracked slot:&mut Tracked<Option<#token>>)->(tracked out:#token)
            requires old(slot)@ is Some,
                Fragment #expr::op(old(slot)@->Some_0.fragment(),old(slot)@->Some_0.fragment())==old(slot)@->Some_0.fragment(),
            ensures final(slot)@ is Some,
                final(slot)@->Some_0.loc()==old(slot)@->Some_0.loc(),
                final(slot)@->Some_0.fragment()==old(slot)@->Some_0.fragment(),
                out.loc()==old(slot)@->Some_0.loc(),out.fragment()==old(slot)@->Some_0.fragment(),
        {
            let tracked actual=slot.borrow_mut().tracked_take();
            let tracked (retained,produced)=actual.split(actual.fragment(),actual.fragment());
            *slot=Tracked(Some(retained));produced
        }
        pub proof fn clone(tracked &mut self)->(tracked out:Self)
            ensures out.instance_id()==old(self).instance_id(),
                final(self).instance_id()==old(self).instance_id(),
                out.raw_fragment()==old(self).raw_fragment(),
                final(self).raw_fragment()==old(self).raw_fragment(),#preservation
        {
            ::vstd::prelude::use_type_invariant(&*self);
            Fragment #expr::unit().op_unit();#normalization
            assert(Fragment #expr::op(self.raw_fragment(),self.raw_fragment())==self.raw_fragment());
            let tracked produced=Self::__persistent_clone_raw(&mut self.raw);
            Self::__from_token(produced,self.metadata.clone(),#arguments)
        }
    })
}
