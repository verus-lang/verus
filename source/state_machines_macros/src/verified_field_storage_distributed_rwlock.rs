//! Checked field-token facade for a distributed optional-storage protocol.
use crate::ast::*;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use crate::verified_field_storage_roles as roles;
use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use std::collections::{HashMap, HashSet};
use verus_syn::Error;

pub fn needed(sm: &SM) -> bool {
    sm.fields.len() == 8
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::Constant(..)))
            .count()
            == 1
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::Variable(..)))
            .count()
            == 1
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::StorageOption(..)))
            .count()
            == 1
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::IMap(..)))
            .count()
            == 1
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::Option(..)))
            .count()
            == 2
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::Multiset(..)))
            .count()
            == 2
}
fn initial(
    stmt: &TransitionStmt,
    values: &mut HashMap<String, verus_syn::Expr>,
    requirements: &mut Vec<verus_syn::Expr>,
) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                initial(child, values, requirements)?;
            }
        }
        TransitionStmt::Initialize(_, field, value) => {
            values.insert(field.to_string(), value.clone());
        }
        TransitionStmt::Require(_, value) => requirements.push(value.clone()),
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "distributed initializer requires straight-line initialization",
            ))
        }
    }
    Ok(())
}
pub fn output(sm: &SM, _selected: &HashSet<String>) -> Result<TokenStream, Error> {
    if !needed(sm) {
        return Err(Error::new(
            sm.name.span(),
            "distributed facade requires its complete eight-role profile",
        ));
    }
    let constants: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(..)))
        .collect();
    let storage = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::StorageOption(..)))
        .unwrap();
    let ShardableType::StorageOption(permission) = &storage.stype else {
        unreachable!()
    };
    let ordinary: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| !f.stype.is_storage() && !matches!(f.stype, ShardableType::Constant(..)))
        .collect();
    let mut generated_types: HashSet<String> = [
        "State",
        "Fragment",
        "Protocol",
        "Token",
        "Instance",
        "TransitionObservation",
    ]
    .iter()
    .map(|n| n.to_string())
    .collect();
    for field in &ordinary {
        if !generated_types.insert(field.name.to_string()) {
            return Err(Error::new(
                field.name.span(),
                "distributed field type conflicts with another generated type",
            ));
        }
        if matches!(
            field.stype,
            ShardableType::IMap(..) | ShardableType::Multiset(..)
        ) {
            let bulk = format!("{}_collection", field.name);
            if !generated_types.insert(bulk) {
                return Err(Error::new(
                    field.name.span(),
                    "distributed collection type conflicts with another generated type",
                ));
            }
        }
        if matches!(field.stype, ShardableType::IMap(..)) {
            let alias = format!("{}_map", field.name);
            if !generated_types.insert(alias) {
                return Err(Error::new(
                    field.name.span(),
                    "distributed original map alias conflicts with another generated type",
                ));
            }
        }
    }
    if let Some(generics) = &sm.generics {
        for p in &generics.params {
            if let verus_syn::GenericParam::Type(p) = p {
                if generated_types.contains(&p.ident.to_string()) {
                    return Err(Error::new(
                        p.ident.span(),
                        "distributed generic type conflicts with a generated field type",
                    ));
                }
            }
        }
    }
    let mut generated_methods: HashSet<String> = ["id", "clone", "invariant"]
        .iter()
        .map(|n| n.to_string())
        .collect();
    for tr in &sm.transitions {
        if tr.kind == TransitionKind::Transition {
            generated_methods.insert(format!("__distributed_{}_raw", tr.name));
        }
    }
    for field in &constants {
        if !generated_methods.insert(field.name.to_string()) {
            return Err(Error::new(
                field.name.span(),
                "distributed constant getter conflicts with a generated Instance method",
            ));
        }
    }
    for tr in &sm.transitions {
        if !generated_methods.insert(tr.name.to_string()) {
            return Err(Error::new(
                tr.name.span(),
                "distributed transition conflicts with a generated Instance method",
            ));
        }
    }
    let (g, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&g);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let token = quote! {Token #types};
    let mut occupied = reserved_names(sm);
    let mut fresh = |label: &str| {
        let mut name = format!("__tsm_dist_initial_{label}");
        while occupied.contains(&name) {
            name.push('_')
        }
        occupied.insert(name.clone());
        verus_syn::Ident::new(&name, proc_macro2::Span::mixed_site())
    };
    let metadata_name = fresh("Metadata");
    let location = fresh("protocol_location");
    let deposit = fresh("deposit");
    let actual = fresh("actual");
    let out = fresh("out");
    let remaining = fresh("remaining");
    let metadata = fresh("metadata");
    let marker = fresh("payload");
    let descriptor = quote! {::vstd::resource::tsm_context::Descriptor<#metadata_name #types>};
    let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
    let ct: Vec<_> = constants.iter().map(|f| f.get_type()).collect();
    let setters: Vec<_> = cn.iter().map(|n| format_ident!("with_{n}")).collect();
    let cx = roles::Context {
        decl: &decl,
        types: &types,
        expr: &expr,
        where_clause: &wc,
        attrs: &attrs,
        token: &token,
        descriptor: &descriptor,
        protocol_location: &location,
        constants: &constants,
    };
    let original_fields = &sm.fields_named_ast;
    let reservation = quote! {#g #original_fields};
    let mut wrappers = vec![];
    for field in &ordinary {
        if matches!(field.stype, ShardableType::IMap(..)) {
            wrappers.push(crate::verified_field_storage_imap_roles::wrapper(
                field,
                &cx,
                &reservation,
            )?);
        } else {
            wrappers.push(roles::wrapper(field, &cx)?);
            if matches!(field.stype, ShardableType::Multiset(..)) {
                wrappers.push(crate::verified_field_storage_collections::wrapper(
                    field,
                    &cx,
                    &reservation,
                )?);
            }
        }
    }
    let mut methods = vec![];
    for transition in &sm.transitions {
        if transition.kind == TransitionKind::Property {
            let reader=ordinary.iter().find(|f|matches!(&f.stype,ShardableType::Multiset(ty) if transition.params.len()==1 && ty.to_token_stream().to_string()==transition.params[0].ty.to_token_stream().to_string())).ok_or_else(||Error::new(transition.name.span(),"distributed property requires its #actual multiset element owner"))?;
            methods.push(roles::guard_method(reader, transition, &cx)?);
            continue;
        }
        if transition.kind != TransitionKind::Init {
            if let Some(method) = map_increment(sm, transition, &cx)? {
                methods.push(method);
            } else if let Some(method) = variable_add(sm, transition, &cx)? {
                methods.push(method);
            } else if let Some(method) = option_withdraw(sm, transition, &cx)? {
                methods.push(method);
            } else if let Some(method) = option_check(sm, transition, &cx)? {
                methods.push(method);
            } else if let Some(method) = variable_deposit(sm, transition, &cx)? {
                methods.push(method);
            } else if let Some(method) = birds_eye_reader(sm, transition, &cx)? {
                methods.push(method);
            } else if let Some(method) = map_decrement(sm, transition, &cx)? {
                methods.push(method);
            } else {
                return Err(Error::new(
                    transition.name.span(),
                    "distributed transition is outside the checked native adapter scope",
                ));
            }
            continue;
        }
        let mut values = HashMap::new();
        let mut requirements = vec![];
        initial(&transition.body, &mut values, &mut requirements)?;
        if values.len() != sm.fields.len() {
            return Err(Error::new(
                transition.name.span(),
                "distributed initializer requires all original fields",
            ));
        }
        let name = &transition.name;
        let params: Vec<_> = transition
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let t = &p.ty;
                quote! {#n:#t}
            })
            .collect();
        let pn: Vec<_> = transition.params.iter().map(|p| &p.name).collect();
        let initial_constants: Vec<_> = cn.iter().map(|n| &values[&n.to_string()]).collect();
        let storage_value = &values[&storage.name.to_string()];
        let mut returns = vec![];
        let mut observations = vec![];
        let mut splits = vec![];
        let mut constructions = vec![];
        for (offset, field) in ordinary.iter().enumerate() {
            let n = &field.name;
            let value = &values[&n.to_string()];
            let ix = verus_syn::Index::from(offset + 1);
            if matches!(field.stype, ShardableType::Option(..)) {
                if value.to_token_stream().to_string() != "Option :: None"
                    && value.to_token_stream().to_string() != "None"
                {
                    return Err(Error::new(
                        n.span(),
                        "distributed optional initialization requires None",
                    ));
                }
                returns.push(quote! {Tracked<Option<#n #types>>});
                observations.push(quote! {#out.#ix@ is None,});
                constructions.push(quote! {Tracked(None)});
                continue;
            }
            let raw = fresh(&format!("field_{n}"));
            let selected = fresh(&format!("selected_{n}"));
            let rest = fresh(&format!("rest_{n}"));
            let select = format_ident!("select_{n}");
            let without = format_ident!("without_{n}");
            let law = format_ident!("take_{n}_law");
            splits.push(quote! {
                #remaining.fragment().#law();
                let #selected=#remaining.fragment().#select()#(.#setters(#initial_constants))*;
                let #rest=#remaining.fragment().#without();
                assert(Fragment #expr::op(#selected,#rest)==#remaining.fragment());
                let tracked(#raw,#remaining)=#remaining.split(#selected,#rest);
            });
            let (role, constructor, getter) = match &field.stype {
                ShardableType::Variable(_) => (
                    n.clone(),
                    quote! {<#n #types>::__from_token(#raw,#metadata.clone())},
                    format_ident!("value"),
                ),
                ShardableType::IMap(..) => {
                    let bulk = format_ident!("{n}_collection");
                    (
                        bulk.clone(),
                        quote! {<#bulk #types>::__from_token(#raw,#metadata.clone(),#value)},
                        format_ident!("map"),
                    )
                }
                ShardableType::Multiset(..) => {
                    let bulk = format_ident!("{n}_collection");
                    (
                        bulk.clone(),
                        quote! {<#bulk #types>::__from_token(#raw,#metadata.clone(),#value)},
                        format_ident!("multiset"),
                    )
                }
                _ => return Err(Error::new(n.span(), "unsupported distributed initial role")),
            };
            returns.push(quote! {Tracked<#role #types>});
            observations
                .push(quote! {#out.#ix@.instance_id()==#out.0@.id(),#out.#ix@.#getter()==#value,});
            constructions.push(quote! {Tracked(#constructor)});
        }
        methods.push(quote!{
            pub proof fn #name(#(#params,)*tracked #actual:Option<#permission>)->(tracked #out:(Tracked<Self>,#(#returns),*))
                requires #(#requirements,)*#actual==#storage_value,
                ensures #(#observations)*#(#out.0@.#cn()==#initial_constants,)*
            {
                let tracked #deposit=match #actual{Some(#actual)=>::vstd::resource::tsm_helpers::singleton_map(0int,#actual),None=>IMap::<int,#permission>::tracked_empty()};
                let tracked #remaining=Protocol #expr::#name(#deposit,#(#pn),*);
                let tracked #metadata=::vstd::resource::tsm_context::Descriptor::alloc(#metadata_name #expr{#location:#remaining.loc(),#(#cn:#initial_constants,)*#marker:core::marker::PhantomData});
                #(#splits)*
                (Tracked(Self{metadata:#metadata.clone()}),#(#constructions),*)
            }
        });
    }
    Ok(quote! {
        #(#attrs)*struct #metadata_name #decl #wc{ghost #location: ::vstd::resource::Loc,#(ghost #cn:#ct,)*ghost #marker:core::marker::PhantomData<#permission>}
        #(#wrappers)*
        #(#attrs)*pub tracked struct Instance #decl #wc{metadata:#descriptor}
        impl #decl Instance #types #wc{
            pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}
            #(pub closed spec fn #cn(&self)->#ct{self.metadata.value().#cn})*
            pub proof fn clone(tracked &self)->(tracked #out:Self)
                ensures #out.id()==self.id(),#(#out.#cn()==self.#cn(),)*
            {Self{metadata:self.metadata.clone()}}
            #(#methods)*
        }
    })
}

fn map_decrement(
    sm: &SM,
    tr: &Transition,
    cx: &roles::Context<'_>,
) -> Result<Option<TokenStream>, Error> {
    struct Ops {
        special: Vec<(verus_syn::Ident, SpecialOp, Option<Box<verus_syn::Pat>>)>,
        local: Vec<(
            Box<verus_syn::Pat>,
            Option<Box<verus_syn::Type>>,
            verus_syn::Expr,
        )>,
    }
    fn collect(stmt: &TransitionStmt, ops: &mut Ops) -> bool {
        match stmt {
            TransitionStmt::Block(_, children) => children.iter().all(|s| collect(s, ops)),
            TransitionStmt::Assert(..) => true,
            TransitionStmt::Split(_, split, children) => {
                match &**split {
                    SplitKind::Special(field, op, _, binding) => {
                        ops.special
                            .push((field.clone(), op.clone(), binding.clone()));
                    }
                    SplitKind::Let(pattern, ty, LetKind::Normal, value) => {
                        ops.local.push((pattern.clone(), ty.clone(), value.clone()));
                    }
                    _ => return false,
                }
                children.iter().all(|s| collect(s, ops))
            }
            _ => false,
        }
    }
    let mut ops = Ops {
        special: vec![],
        local: vec![],
    };
    if !collect(&tr.body, &mut ops) || ops.special.len() != 3 || ops.local.len() != 1 {
        return Ok(None);
    }
    let (bag_name, bag_remove, _) = &ops.special[0];
    let (map_name, remove, binding) = &ops.special[1];
    let (map_add_name, add, _) = &ops.special[2];
    let Some(map) = sm.fields.iter().find(|f| f.name == *map_name) else {
        return Ok(None);
    };
    let Some(bag) = sm.fields.iter().find(|f| f.name == *bag_name) else {
        return Ok(None);
    };
    let (ShardableType::IMap(key_type, value_type), ShardableType::Multiset(element_type)) =
        (&map.stype, &bag.stype)
    else {
        return Ok(None);
    };
    if map_name != map_add_name || !bag_remove.is_remove() || !remove.is_remove() || !add.is_add() {
        return Ok(None);
    }
    let (
        MonoidElt::SingletonMultiset(element),
        MonoidElt::SingletonKV(key, None),
        MonoidElt::SingletonKV(new_key, Some(new_value)),
    ) = (&bag_remove.elt, &remove.elt, &add.elt)
    else {
        return Ok(None);
    };
    if key.to_token_stream().to_string() != new_key.to_token_stream().to_string() {
        return Err(Error::new(
            tr.name.span(),
            "distributed release keeps its current entry key",
        ));
    }
    let Some(binding) = binding else {
        return Ok(None);
    };
    let verus_syn::Pat::Ident(bound) = &**binding else {
        return Err(Error::new(
            tr.name.span(),
            "distributed release binds one current map payload",
        ));
    };
    let bound = &bound.ident;
    let (local_pattern, local_type, local_value) = &ops.local[0];
    if !matches!(&**local_pattern, verus_syn::Pat::Ident(_)) {
        return Err(Error::new(
            tr.name.span(),
            "distributed release binds one local key",
        ));
    }
    let local = match local_type {
        Some(ty) => quote! {let #local_pattern:#ty=#local_value;},
        None => quote! {let #local_pattern=#local_value;},
    };
    let scoped_key = quote! {{#local #key}};
    let mut names = reserved_names(sm);
    let mut fresh = |label: &str| {
        let mut n = format!("__tsm_dist_release_{label}");
        while names.contains(&n) {
            n.push('_');
        }
        names.insert(n.clone());
        verus_syn::Ident::new(&n, proc_macro2::Span::mixed_site())
    };
    let slot = fresh("slot");
    let consumed = fresh("consumed");
    let owner = fresh("owner");
    let input = fresh("input");
    let current = fresh("current");
    let before = fresh("before");
    let width = fresh("width");
    let frame = fresh("frame");
    let pre = fresh("pre");
    let post = fresh("post");
    let map_middle = fresh("map_middle");
    let point = fresh("point");
    let bag_element = fresh("bag_element");
    let expected = fresh("expected");
    let raw_name = format_ident!("__distributed_{}_raw", tr.name);
    let name = &tr.name;
    let req = format_ident!("{name}_requires");
    let enabled = format_ident!("{name}_enabled");
    let owners = format_ident!("{name}_owners_enabled");
    let deposited = format_ident!("{name}_deposited");
    let witness = format_ident!("{name}_witness");
    let map_effect = format_ident!("{name}_{map_name}_effect");
    let types = cx.types;
    let expr = cx.expr;
    let token = cx.token;
    let constant = &cx.constants[0].name;
    let setter = format_ident!("with_{constant}");
    let mf = format_ident!("field_{map_name}");
    let mg = format_ident!("value_{map_name}_at");
    let mo = format_ident!("owns_{map_name}_at");
    let bf = format_ident!("field_{bag_name}");
    let params: Vec<_> = tr
        .params
        .iter()
        .map(|p| {
            let n = &p.name;
            let t = &p.ty;
            quote! {#n:#t}
        })
        .collect();
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let bag_norm: Vec<_> = sm.fields.iter().filter_map(|field| {
        let ShardableType::Multiset(ty) = &field.stype else {return None;};
        let n = &field.name;
        Some(quote! {
            assert forall|#bag_element:#ty| #[trigger] #current.fragment().#n.values.count(#bag_element)==0 by{};
            assert(::vstd::prelude::ext_equal(#current.fragment().#n.values,Multiset::<#ty>::empty()));
        })
    }).collect();
    Ok(Some(quote! {
        proof fn #raw_name(tracked #slot:&mut Tracked<Option<#token>>,tracked #consumed:#token,#width:int,#(#params),*)
            requires old(#slot)@ is Some,
                old(#slot)@->Some_0.loc()==#consumed.loc(),
                old(#slot)@->Some_0.fragment().#mo(#scoped_key),
                old(#slot)@->Some_0.fragment()==Fragment #expr::#mf(IMap::<#key_type,#value_type>::empty().insert(#scoped_key,old(#slot)@->Some_0.fragment().#mg(#scoped_key))).#setter(#width),
                #consumed.fragment()==Fragment #expr::#bf(Multiset::<#element_type>::singleton(#element)).#setter(#width),
            ensures final(#slot)@ is Some,
                final(#slot)@->Some_0.loc()==old(#slot)@->Some_0.loc(),
                final(#slot)@->Some_0.fragment()==Fragment #expr::#mf(IMap::<#key_type,#value_type>::empty().insert(#scoped_key,{#local let #bound=old(#slot)@->Some_0.fragment().#mg(#key);#new_value})).#setter(#width),
        {
            broadcast use {::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas,::vstd::multiset::group_multiset_axioms};
            #local
            let tracked #current=#slot.borrow_mut().tracked_take();
            #current.fragment().op_unit();#consumed.fragment().op_unit();
            let tracked #current=#current.join(#consumed);
            let #before=#current.fragment();
            let #bound=#before.#mg(#key);
            assert(#before.#map_name.at(#key)==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(#bound)));
            assert(#before.#bag_name.values==Multiset::<#element_type>::singleton(#element));
            assert(Protocol #expr::#req(#before,Fragment #expr::unit(),IMap::empty(),#(#pn),*)) by{
                assert forall|#frame:Fragment #types,#pre:State #types|
                    #pre.invariant() && Fragment #expr::op(Fragment #expr::op(#before,Fragment #expr::unit()),#frame)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#pn),*) && IMap::<int,_>::empty()==State #expr::#deposited(#pre,#(#pn),*) && State #expr::#owners(#pre,#before,Fragment #expr::unit(),#(#pn),*) by{
                        Fragment #expr::unit().op_unit();
                        ::vstd::resource::tsm_collections::map_owned_frame(#before.#map_name,#frame.#map_name,#pre.#map_name,#key,#bound);
                        ::vstd::resource::tsm_finite_multiset::finite_multiset_owned_frame(#before.#bag_name,#frame.#bag_name,#pre.#bag_name,#element);
                        assert(#pre.#map_name.contains_key(#key));assert(#pre.#map_name[#key]==#bound);
                        assert(#pre.#bag_name.count(#element)>0);
                    }
            }
            let tracked #current=Protocol #expr::#name(#current,#(#pn),*);
            let (#pre,#post,#frame)=Protocol #expr::#witness(#before,Fragment #expr::unit(),#current.fragment(),IMap::empty(),IMap::empty(),#(#pn),*);
            ::vstd::resource::tsm_collections::map_owned_frame(#before.#map_name,#frame.#map_name,#pre.#map_name,#key,#bound);
            assert(State #expr::#map_effect(#pre,#(#pn),*)==Some((IMap::<#key_type,#value_type>::empty().insert(#key,#bound),IMap::<#key_type,#value_type>::empty().insert(#key,#new_value))));
            let #map_middle=::vstd::resource::tsm_collections::map_remove_many(#before.#map_name,IMap::<#key_type,#value_type>::empty().insert(#key,#bound).dom());
            assert forall|#point:#key_type| #[trigger] #map_middle.at(#point)==::vstd::resource::tsm_collections::MapFragment::<#key_type,#value_type>::unit().at(#point) by{};
            ::vstd::resource::tsm_collections::Pointwise::extensionality(#map_middle,::vstd::resource::tsm_collections::MapFragment::<#key_type,#value_type>::unit());
            let #expected=Fragment #expr::#mf(IMap::<#key_type,#value_type>::empty().insert(#key,#new_value)).#setter(#width);
            #expected.#map_name.op_unit();
            ::vstd::resource::tsm_collections::MapFragment::commutative(::vstd::resource::tsm_collections::MapFragment::unit(),#expected.#map_name);
            #(#bag_norm)*Fragment #expr::unit().op_unit();
            assert(#current.fragment()==#expected);
            *#slot=Tracked(Some(#current));
        }
        pub proof fn #name(tracked &self,#(#params,)*tracked #owner:&mut #map_name #types,tracked #input:#bag_name #types)
            requires old(#owner).instance_id()==self.id(),#input.instance_id()==self.id(),
                old(#owner).key()==#scoped_key,#input.element()==#element,
            ensures final(#owner).instance_id()==self.id(),final(#owner).key()==old(#owner).key(),
                final(#owner).value()=={#local let #bound=old(#owner).value();#new_value},
        {
            ::vstd::prelude::use_type_invariant(&*#owner);::vstd::prelude::use_type_invariant(&#input);
            self.metadata.agrees(&#owner.metadata);self.metadata.agrees(&#input.metadata);
            let tracked #consumed=#input.raw.get().tracked_unwrap();
            Self::#raw_name(&mut #owner.raw,#consumed,self.#constant(),#(#pn),*);
        }
    }))
}

// Structural singleton map replacement followed by a singleton multiset Add.
// Bound map payloads are read from the CURRENT actual sparse entry.
fn map_increment(
    sm: &SM,
    tr: &Transition,
    cx: &roles::Context<'_>,
) -> Result<Option<TokenStream>, Error> {
    fn collect(
        stmt: &TransitionStmt,
        ops: &mut Vec<(verus_syn::Ident, SpecialOp, Option<Box<verus_syn::Pat>>)>,
    ) -> bool {
        match stmt {
            TransitionStmt::Block(_, children) => children.iter().all(|s| collect(s, ops)),
            TransitionStmt::Split(_, split, children) => {
                if let SplitKind::Special(field, op, _, binding) = &**split {
                    ops.push((field.clone(), op.clone(), binding.clone()));
                    children.iter().all(|s| collect(s, ops))
                } else {
                    false
                }
            }
            _ => false,
        }
    }
    let mut ops = vec![];
    if !collect(&tr.body, &mut ops) || ops.len() != 3 {
        return Ok(None);
    }
    let (map_name, remove, binding) = &ops[0];
    let (map_add_name, add, _) = &ops[1];
    let (bag_name, bag_add, _) = &ops[2];
    let Some(map) = sm.fields.iter().find(|f| f.name == *map_name) else {
        return Ok(None);
    };
    let Some(bag) = sm.fields.iter().find(|f| f.name == *bag_name) else {
        return Ok(None);
    };
    if !matches!(map.stype, ShardableType::IMap(..))
        || !matches!(bag.stype, ShardableType::Multiset(..))
        || map_name != map_add_name
        || !remove.is_remove()
        || !add.is_add()
        || !bag_add.is_add()
    {
        return Ok(None);
    }
    let MonoidElt::SingletonKV(key, None) = &remove.elt else {
        return Ok(None);
    };
    let MonoidElt::SingletonKV(new_key, Some(new_value)) = &add.elt else {
        return Ok(None);
    };
    let MonoidElt::SingletonMultiset(element) = &bag_add.elt else {
        return Ok(None);
    };
    if key.to_token_stream().to_string() != new_key.to_token_stream().to_string() {
        return Err(Error::new(
            tr.name.span(),
            "distributed map step keeps its current entry key",
        ));
    }
    let Some(binding) = binding else {
        return Ok(None);
    };
    let verus_syn::Pat::Ident(bound) = &**binding else {
        return Err(Error::new(
            tr.name.span(),
            "distributed map payload binding must be an identifier",
        ));
    };
    let bound = &bound.ident;
    let ShardableType::IMap(key_type, value_type) = &map.stype else {
        unreachable!()
    };
    let ShardableType::Multiset(element_type) = &bag.stype else {
        unreachable!()
    };
    fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
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
    let mut names: HashSet<String> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(sm.transitions.iter().map(|t| t.name.to_string()))
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .collect();
    let fields = &sm.fields_named_ast;
    let generics = &sm.generics;
    reserve(
        quote! {#fields #generics #key #new_key #new_value #element #binding},
        &mut names,
    );
    let mut fresh = |label: &str| {
        let mut n = format!("__tsm_dist_map_{label}");
        while names.contains(&n) {
            n.push('_')
        }
        names.insert(n.clone());
        verus_syn::Ident::new(&n, proc_macro2::Span::mixed_site())
    };
    let slot = fresh("slot");
    let owner = fresh("owner");
    let current = fresh("current");
    let before = fresh("before");
    let width = fresh("width");
    let frame = fresh("frame");
    let pre = fresh("pre");
    let post = fresh("post");
    let result = fresh("result");
    let selected = fresh("selected");
    let remainder = fresh("remainder");
    let produced = fresh("produced");
    let map_middle = fresh("map_middle");
    let point = fresh("point");
    let bag_element = fresh("bag_element");
    let raw_name = format_ident!("__distributed_{}_raw", tr.name);
    let name = &tr.name;
    let req = format_ident!("{name}_requires");
    let enabled = format_ident!("{name}_enabled");
    let owners = format_ident!("{name}_owners_enabled");
    let deposited = format_ident!("{name}_deposited");
    let witness = format_ident!("{name}_witness");
    let map_effect = format_ident!("{name}_{map_name}_effect");
    let types = cx.types;
    let expr = cx.expr;
    let token = cx.token;
    let constant = cx.constants[0];
    let constant_name = &constant.name;
    let constant_setter = format_ident!("with_{constant_name}");
    let mf = format_ident!("field_{map_name}");
    let mg = format_ident!("value_{map_name}_at");
    let mo = format_ident!("owns_{map_name}_at");
    let bg = format_ident!("field_{bag_name}");
    let params: Vec<_> = tr
        .params
        .iter()
        .map(|p| {
            let n = &p.name;
            let t = &p.ty;
            quote! {#n:#t}
        })
        .collect();
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let component_equalities: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| !f.stype.is_storage())
        .map(|f| {
            let n = &f.name;
            quote! {assert(Fragment #expr::op(#selected,#remainder).#n==#current.fragment().#n);}
        })
        .collect();
    Ok(Some(quote! {
        proof fn #raw_name(tracked #slot:&mut Tracked<Option<#token>>,#width:int,#(#params),*) ->(tracked #result:#token)
            requires old(#slot)@ is Some,old(#slot)@->Some_0.fragment().#mo(#key),
                old(#slot)@->Some_0.fragment()==Fragment #expr::#mf(IMap::<#key_type,#value_type>::empty().insert(#key,old(#slot)@->Some_0.fragment().#mg(#key))).#constant_setter(#width),
            ensures final(#slot)@ is Some,
                final(#slot)@->Some_0.loc()==old(#slot)@->Some_0.loc(),
                final(#slot)@->Some_0.fragment()==Fragment #expr::#mf(IMap::<#key_type,#value_type>::empty().insert(#key,{let #bound=old(#slot)@->Some_0.fragment().#mg(#key);#new_value})).#constant_setter(#width),
                #result.loc()==old(#slot)@->Some_0.loc(),
                #result.fragment()==Fragment #expr::#bg(Multiset::<#element_type>::singleton(#element)).#constant_setter(#width),
        {
            broadcast use {::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas,::vstd::multiset::group_multiset_axioms};
            let tracked #current=#slot.borrow_mut().tracked_take();
            let #before=#current.fragment();
            let #bound=#before.#mg(#key);
            #before.op_unit();
            assert(#before.#map_name.at(#key)==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(#bound)));
            assert(Protocol #expr::#req(#before,Fragment #expr::unit(),IMap::empty(),#(#pn),*)) by{
                assert forall|#frame:Fragment #types,#pre:State #types|
                    #pre.invariant() && Fragment #expr::op(Fragment #expr::op(#before,Fragment #expr::unit()),#frame)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#pn),*) && IMap::<int,_>::empty()==State #expr::#deposited(#pre,#(#pn),*) && State #expr::#owners(#pre,#before,Fragment #expr::unit(),#(#pn),*) by{
                        Fragment #expr::unit().op_unit();
                        ::vstd::resource::tsm_collections::map_owned_frame(#before.#map_name,#frame.#map_name,#pre.#map_name,#key,#bound);
                        assert(#pre.#map_name.contains_key(#key));assert(#pre.#map_name[#key]==#bound);
                    }
            }
            let tracked #current=Protocol #expr::#name(#current,#(#pn),*);
            let (#pre,#post,#frame)=Protocol #expr::#witness(#before,Fragment #expr::unit(),#current.fragment(),IMap::empty(),IMap::empty(),#(#pn),*);
            ::vstd::resource::tsm_collections::map_owned_frame(#before.#map_name,#frame.#map_name,#pre.#map_name,#key,#bound);
            assert(State #expr::#map_effect(#pre,#(#pn),*)==Some((IMap::<#key_type,#value_type>::empty().insert(#key,#bound),IMap::<#key_type,#value_type>::empty().insert(#key,#new_value))));
            let #map_middle=::vstd::resource::tsm_collections::map_remove_many(#before.#map_name,IMap::<#key_type,#value_type>::empty().insert(#key,#bound).dom());
            assert forall|#point:#key_type| #[trigger] #map_middle.at(#point)==::vstd::resource::tsm_collections::MapFragment::<#key_type,#value_type>::unit().at(#point) by{};
            ::vstd::resource::tsm_collections::Pointwise::extensionality(#map_middle,::vstd::resource::tsm_collections::MapFragment::<#key_type,#value_type>::unit());
            let #selected=Fragment #expr::#bg(Multiset::<#element_type>::singleton(#element)).#constant_setter(#width);
            let #remainder=Fragment #expr::#mf(IMap::<#key_type,#value_type>::empty().insert(#key,#new_value)).#constant_setter(#width);
            #remainder.#map_name.op_unit();
            ::vstd::resource::tsm_collections::MapFragment::commutative(::vstd::resource::tsm_collections::MapFragment::unit(),#remainder.#map_name);
            assert forall|#bag_element:#element_type| #[trigger] #current.fragment().#bag_name.values.count(#bag_element)==Multiset::<#element_type>::singleton(#element).count(#bag_element) by{};
            assert(::vstd::prelude::ext_equal(#current.fragment().#bag_name.values,Multiset::<#element_type>::singleton(#element)));
            assert(#current.fragment().#map_name==#remainder.#map_name);
            assert(#current.fragment().#bag_name==#selected.#bag_name);
            #selected.#bag_name.op_unit();
            Fragment #expr::unit().op_unit();
            #(#component_equalities)*
            assert(Fragment #expr::op(#selected,#remainder)==#current.fragment());
            let tracked(#produced,#current)=#current.split(#selected,#remainder);
            *#slot=Tracked(Some(#current));#produced
        }
        pub proof fn #name(tracked &self,#(#params,)*tracked #owner:&mut #map_name #types)->(tracked #result:#bag_name #types)
            requires old(#owner).instance_id()==self.id(),old(#owner).key()==#key,
            ensures final(#owner).instance_id()==self.id(),final(#owner).key()==old(#owner).key(),
                final(#owner).value()=={let #bound=old(#owner).value();#new_value},
                #result.instance_id()==self.id(),#result.element()==#element,
        {
            ::vstd::prelude::use_type_invariant(&*#owner);
            self.metadata.agrees(&#owner.metadata);
            let tracked #produced=Self::#raw_name(&mut #owner.raw,self.#constant_name(),#(#pn),*);
            <#bag_name #types>::__from_token(#produced,self.metadata.clone(),#element)
        }
    }))
}

fn variable_add(
    sm: &SM,
    tr: &Transition,
    cx: &roles::Context<'_>,
) -> Result<Option<TokenStream>, Error> {
    struct Ops {
        requirements: Vec<verus_syn::Expr>,
        update: Option<(verus_syn::Ident, verus_syn::Expr)>,
        add: Option<(verus_syn::Ident, verus_syn::Expr)>,
    }
    fn collect(stmt: &TransitionStmt, ops: &mut Ops) -> bool {
        match stmt {
            TransitionStmt::Block(_, children) => children.iter().all(|s| collect(s, ops)),
            TransitionStmt::Require(_, e) => {
                ops.requirements.push(e.clone());
                true
            }
            TransitionStmt::Update(_, f, e) if ops.update.is_none() => {
                ops.update = Some((f.clone(), e.clone()));
                true
            }
            TransitionStmt::Split(_, split, children) => {
                let SplitKind::Special(f, op, _, None) = &**split else {
                    return false;
                };
                let MonoidElt::OptionSome(Some(e)) = &op.elt else {
                    return false;
                };
                if !op.is_add() || ops.add.is_some() {
                    return false;
                }
                ops.add = Some((f.clone(), e.clone()));
                children.iter().all(|s| collect(s, ops))
            }
            _ => false,
        }
    }
    let mut ops = Ops {
        requirements: vec![],
        update: None,
        add: None,
    };
    if !collect(&tr.body, &mut ops) {
        return Ok(None);
    }
    let (Some((variable_name, update)), Some((added_name, element))) = (ops.update, ops.add) else {
        return Ok(None);
    };
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    if !matches!(
        fields[&variable_name.to_string()].stype,
        ShardableType::Variable(..)
    ) || !matches!(
        fields[&added_name.to_string()].stype,
        ShardableType::Option(..)
    ) {
        return Ok(None);
    }
    fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
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
    let original_fields = &sm.fields_named_ast;
    let generics = &sm.generics;
    let mut names: HashSet<_> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(sm.transitions.iter().map(|t| t.name.to_string()))
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .collect();
    reserve(
        quote! {#original_fields #generics #update #element},
        &mut names,
    );
    for e in &ops.requirements {
        reserve(quote! {#e}, &mut names)
    }
    let mut fresh = |label: &str| {
        let mut n = format!("__tsm_dist_var_{label}");
        while names.contains(&n) {
            n.push('_')
        }
        names.insert(n.clone());
        verus_syn::Ident::new(&n, proc_macro2::Span::mixed_site())
    };
    let slot = fresh("slot");
    let owner = fresh("owner");
    let width = fresh("width");
    let current = fresh("current");
    let certificate = fresh("certificate");
    let result = fresh("result");
    let selected = fresh("selected");
    let remainder = fresh("remainder");
    let produced = fresh("produced");
    let raw = format_ident!("__distributed_{}_raw", tr.name);
    let name = &tr.name;
    let getter = format_ident!("value_{variable_name}");
    let factory = format_ident!("field_{variable_name}");
    let added_factory = format_ident!("field_{added_name}");
    let constant = &cx.constants[0].name;
    let setter = format_ident!("with_{constant}");
    let types = cx.types;
    let expr = cx.expr;
    let token = cx.token;
    let params: Vec<_> = tr
        .params
        .iter()
        .map(|p| {
            let n = &p.name;
            let t = &p.ty;
            quote! {#n:#t}
        })
        .collect();
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let lower = |e: &verus_syn::Expr, value: TokenStream| -> Result<TokenStream, Error> {
        let mut e = e.clone();
        let mut errors = vec![];
        crate::field_access_visitor::visit_field_accesses(
            &mut e,
            |errors, f, slot| {
                if f.name == variable_name {
                    *slot = verus_syn::parse2(value.clone()).unwrap()
                } else {
                    errors.push(Error::new(
                        f.name.span(),
                        "distributed variable Add reads its supplied variable only",
                    ))
                }
            },
            &mut errors,
            &fields,
        );
        if let Some(e) = errors.into_iter().next() {
            Err(e)
        } else {
            Ok(quote! {#e})
        }
    };
    let raw_value = quote! {old(#slot)@->Some_0.fragment().#getter()};
    let public_value = quote! {old(#owner).value()};
    let raw_requirements: Vec<_> = ops
        .requirements
        .iter()
        .map(|e| lower(e, raw_value.clone()))
        .collect::<Result<_, _>>()?;
    let public_requirements: Vec<_> = ops
        .requirements
        .iter()
        .map(|e| lower(e, public_value.clone()))
        .collect::<Result<_, _>>()?;
    let raw_update = lower(&update, raw_value.clone())?;
    let public_update = lower(&update, public_value.clone())?;
    let local = format_ident!("{name}_local_requires");
    let observed = format_ident!("{name}_observed");
    Ok(Some(quote! {
        proof fn #raw(tracked #slot:&mut Tracked<Option<#token>>,#width:int,#(#params),*)->(tracked #result:#token)
            requires old(#slot)@ is Some,
                old(#slot)@->Some_0.fragment()==Fragment #expr::#factory(old(#slot)@->Some_0.fragment().#getter()).#setter(#width),#(#raw_requirements,)*
            ensures final(#slot)@ is Some,final(#slot)@->Some_0.loc()==old(#slot)@->Some_0.loc(),
                final(#slot)@->Some_0.fragment()==Fragment #expr::#factory(#raw_update).#setter(#width),
                #result.loc()==old(#slot)@->Some_0.loc(),#result.fragment()==Fragment #expr::#added_factory(Some(#element)).#setter(#width),
        {
            let tracked #current=#slot.borrow_mut().tracked_take();
            #current.fragment().op_unit();
            assert(Protocol #expr::#local(#current.fragment(),Fragment #expr::unit(),IMap::empty(),#(#pn),*));
            let tracked #certificate=Protocol #expr::#observed(#current,#(#pn),*);
            let #selected=Fragment #expr::#added_factory(Some(#element)).#setter(#width);
            let #remainder=Fragment #expr::#factory(#update).#setter(#width);
            Fragment #expr::unit().op_unit();
            assert(Fragment #expr::op(#selected,#remainder)==#certificate.token.fragment());
            let tracked(#produced,#current)=#certificate.token.split(#selected,#remainder);
            *#slot=Tracked(Some(#current));#produced
        }
        pub proof fn #name(tracked &self,#(#params,)*tracked #owner:&mut #variable_name #types)->(tracked #result:#added_name #types)
            requires old(#owner).instance_id()==self.id(),#(#public_requirements,)*
            ensures final(#owner).instance_id()==self.id(),final(#owner).value()==#public_update,
                #result.instance_id()==self.id(),#result.value()==#element,
        {
            ::vstd::prelude::use_type_invariant(&*#owner);self.metadata.agrees(&#owner.metadata);
            let tracked #produced=Self::#raw(&mut #owner.raw,self.#constant(),#(#pn),*);
            <#added_name #types>::__from_token(#produced,self.metadata.clone(),#element)
        }
    }))
}

fn option_withdraw(
    sm: &SM,
    tr: &Transition,
    cx: &roles::Context<'_>,
) -> Result<Option<TokenStream>, Error> {
    fn collect(stmt: &TransitionStmt, ops: &mut Vec<(verus_syn::Ident, SpecialOp)>) -> bool {
        match stmt {
            TransitionStmt::Block(_, children) => children.iter().all(|s| collect(s, ops)),
            TransitionStmt::Split(_, split, children) => {
                if let SplitKind::Special(f, op, _, _) = &**split {
                    ops.push((f.clone(), op.clone()));
                    children.iter().all(|s| collect(s, ops))
                } else {
                    false
                }
            }
            _ => false,
        }
    }
    let mut ops = vec![];
    if !collect(&tr.body, &mut ops) || ops.len() != 3 {
        return Ok(None);
    }
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let (removed, remove) = &ops[0];
    let (added, add) = &ops[1];
    let (storage, withdraw) = &ops[2];
    if !matches!(
        fields[&removed.to_string()].stype,
        ShardableType::Option(..)
    ) || !matches!(fields[&added.to_string()].stype, ShardableType::Option(..))
        || !matches!(withdraw.stmt, MonoidStmtType::Withdraw)
    {
        return Ok(None);
    }
    let ShardableType::StorageOption(permission) = &fields[&storage.to_string()].stype else {
        return Ok(None);
    };
    let (
        MonoidElt::OptionSome(Some(removed_value)),
        MonoidElt::OptionSome(Some(added_value)),
        MonoidElt::OptionSome(None),
    ) = (&remove.elt, &add.elt, &withdraw.elt)
    else {
        return Ok(None);
    };
    if !remove.is_remove() || !add.is_add() {
        return Ok(None);
    }
    fn reserve(t: TokenStream, n: &mut HashSet<String>) {
        for t in t {
            match t {
                proc_macro2::TokenTree::Ident(i) => {
                    n.insert(i.to_string());
                }
                proc_macro2::TokenTree::Group(g) => reserve(g.stream(), n),
                _ => {}
            }
        }
    }
    let fs = &sm.fields_named_ast;
    let g = &sm.generics;
    let mut names: HashSet<_> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(sm.transitions.iter().map(|t| t.name.to_string()))
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .collect();
    reserve(quote! {#fs #g #removed_value #added_value}, &mut names);
    let mut fresh = |label: &str| {
        let mut n = format!("__tsm_dist_wd_{label}");
        while names.contains(&n) {
            n.push('_')
        }
        names.insert(n.clone());
        verus_syn::Ident::new(&n, proc_macro2::Span::mixed_site())
    };
    let owned = fresh("owned");
    let input = fresh("input");
    let certificate = fresh("certificate");
    let result = fresh("result");
    let actual = fresh("actual");
    let width = fresh("width");
    let pre = fresh("pre");
    let post = fresh("post");
    let raw_name = format_ident!("__distributed_{}_raw", tr.name);
    let name = &tr.name;
    let local = format_ident!("{name}_local_requires");
    let observed = format_ident!("{name}_observed");
    let strong = format_ident!("{name}_strong");
    let constant = &cx.constants[0].name;
    let setter = format_ident!("with_{constant}");
    let removed_factory = format_ident!("field_{removed}");
    let added_factory = format_ident!("field_{added}");
    let types = cx.types;
    let expr = cx.expr;
    let token = cx.token;
    let params: Vec<_> = tr
        .params
        .iter()
        .map(|p| {
            let n = &p.name;
            let t = &p.ty;
            quote! {#n:#t}
        })
        .collect();
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let lower = |e: &verus_syn::Expr, replacement: TokenStream| -> Result<TokenStream, Error> {
        let mut e = e.clone();
        let mut errors = vec![];
        crate::field_access_visitor::visit_field_accesses(
            &mut e,
            |errors, f, slot| {
                if f.name == *constant {
                    *slot = verus_syn::parse2(replacement.clone()).unwrap()
                } else {
                    errors.push(Error::new(
                        f.name.span(),
                        "distributed optional withdrawal reads its constant observation only",
                    ))
                }
            },
            &mut errors,
            &fields,
        );
        if let Some(e) = errors.into_iter().next() {
            Err(e)
        } else {
            Ok(quote! {#e})
        }
    };
    let raw_removed = lower(removed_value, quote! {#width})?;
    let public_removed = lower(removed_value, quote! {self.#constant()})?;
    Ok(Some(quote! {
        proof fn #raw_name(tracked #owned:#token,#width:int,#(#params),*)->(tracked #result:(Tracked<#token>,Tracked<#permission>))
            requires #owned.fragment()==Fragment #expr::#removed_factory(Some(#raw_removed)).#setter(#width),
            ensures #result.0@.loc()==#owned.loc(),#result.0@.fragment()==Fragment #expr::#added_factory(Some(#added_value)).#setter(#width),
                exists|#pre:State #types,#post:State #types|#pre.invariant()&&#post.invariant()&&#pre.#constant==#width&&State #expr::#strong(#pre,#post,#(#pn),*)&&#pre.#storage==Some(#result.1@),
        {
            #owned.fragment().op_unit();
            assert(Protocol #expr::#local(#owned.fragment(),Fragment #expr::unit(),IMap::empty(),#(#pn),*));
            let tracked #certificate=Protocol #expr::#observed(#owned,#(#pn),*);
            assert(#certificate.before.#storage is Some);assert(#certificate.after.#storage is None);
            assert(#certificate.before.#constant==#width);
            assert(#certificate.withdrawn==IMap::<int,#permission>::empty().insert(0int,#certificate.before.#storage->Some_0));
            assert(#certificate.token.fragment()==Fragment #expr::#added_factory(Some(#added_value)).#setter(#width));
            let tracked #actual=::vstd::resource::tsm_helpers::take_singleton(#certificate.withdrawn,0int);
            assert(State #expr::#strong(#certificate.before,#certificate.after,#(#pn),*));
            (Tracked(#certificate.token),Tracked(#actual))
        }
        pub proof fn #name(tracked &self,#(#params,)*tracked #input:#removed #types)->(tracked #result:(Tracked<#added #types>,Tracked<#permission>))
            requires #input.instance_id()==self.id(),#input.value()==#public_removed,
            ensures #result.0@.instance_id()==self.id(),#result.0@.value()==#added_value,
                exists|#pre:State #types,#post:State #types|#pre.invariant()&&#post.invariant()&&#pre.#constant==self.#constant()&&State #expr::#strong(#pre,#post,#(#pn),*)&&#pre.#storage==Some(#result.1@),
        {
            ::vstd::prelude::use_type_invariant(&#input);self.metadata.agrees(&#input.metadata);
            let tracked #owned=#input.raw.get().tracked_unwrap();
            let tracked(Tracked(#owned),#actual)=Self::#raw_name(#owned,self.#constant(),#(#pn),*);
            (Tracked(<#added #types>::__from_token(#owned,self.metadata.clone(),#added_value)),#actual)
        }
    }))
}

fn reserve_tokens(tokens: TokenStream, names: &mut HashSet<String>) {
    for token in tokens {
        match token {
            proc_macro2::TokenTree::Ident(id) => {
                names.insert(id.to_string());
            }
            proc_macro2::TokenTree::Group(g) => reserve_tokens(g.stream(), names),
            _ => {}
        }
    }
}
fn reserve_statement(stmt: &TransitionStmt, names: &mut HashSet<String>) {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                reserve_statement(child, names)
            }
        }
        TransitionStmt::Initialize(_, field, e) | TransitionStmt::Update(_, field, e) => {
            reserve_tokens(quote! {#field #e}, names)
        }
        TransitionStmt::Require(_, e)
        | TransitionStmt::Assert(_, e, _)
        | TransitionStmt::PostCondition(_, e) => reserve_tokens(quote! {#e}, names),
        TransitionStmt::SubUpdate(_, field, _, e) => reserve_tokens(quote! {#field #e}, names),
        TransitionStmt::Split(_, split, children) => {
            match &**split {
                SplitKind::If(e) => reserve_tokens(quote! {#e}, names),
                SplitKind::Match(e, arms) => {
                    reserve_tokens(quote! {#e}, names);
                    for arm in arms {
                        let p = &arm.pat;
                        reserve_tokens(quote! {#p}, names);
                        if let Some((_, e)) = &arm.guard {
                            reserve_tokens(quote! {#e}, names)
                        }
                    }
                }
                SplitKind::Let(p, t, _, e) => reserve_tokens(quote! {#p #t #e}, names),
                SplitKind::Special(f, op, _, p) => {
                    reserve_tokens(quote! {#f #p}, names);
                    match &op.elt {
                        MonoidElt::OptionSome(e) => reserve_tokens(quote! {#e}, names),
                        MonoidElt::SingletonKV(k, v) => reserve_tokens(quote! {#k #v}, names),
                        MonoidElt::SingletonMultiset(e)
                        | MonoidElt::SingletonSet(e)
                        | MonoidElt::General(e) => reserve_tokens(quote! {#e}, names),
                        _ => {}
                    }
                }
            }
            for child in children {
                reserve_statement(child, names)
            }
        }
    }
}
fn reserved_names(sm: &SM) -> HashSet<String> {
    let mut names: HashSet<String> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(sm.transitions.iter().map(|t| t.name.to_string()))
        .collect();
    let fields = &sm.fields_named_ast;
    let g = &sm.generics;
    reserve_tokens(quote! {#fields #g}, &mut names);
    for tr in &sm.transitions {
        for p in &tr.params {
            let n = &p.name;
            let t = &p.ty;
            reserve_tokens(quote! {#n #t}, &mut names)
        }
        reserve_statement(&tr.body, &mut names)
    }
    names
}

fn option_check(
    sm: &SM,
    tr: &Transition,
    cx: &roles::Context<'_>,
) -> Result<Option<TokenStream>, Error> {
    fn collect(
        stmt: &TransitionStmt,
        ops: &mut Vec<(verus_syn::Ident, SpecialOp, Option<Box<verus_syn::Pat>>)>,
    ) -> bool {
        match stmt {
            TransitionStmt::Block(_, children) => children.iter().all(|s| collect(s, ops)),
            TransitionStmt::Split(_, split, children) => {
                if let SplitKind::Special(f, op, _, p) = &**split {
                    ops.push((f.clone(), op.clone(), p.clone()));
                    children.iter().all(|s| collect(s, ops))
                } else {
                    false
                }
            }
            _ => false,
        }
    }
    let mut ops = vec![];
    if !collect(&tr.body, &mut ops) || ops.len() != 3 {
        return Ok(None);
    }
    let (option, remove, binding) = &ops[0];
    let (map, have, _) = &ops[1];
    let (option_add, add, _) = &ops[2];
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    if option != option_add
        || !remove.is_remove()
        || !matches!(have.stmt, MonoidStmtType::Have)
        || !add.is_add()
        || !matches!(fields[&option.to_string()].stype, ShardableType::Option(..))
        || !matches!(fields[&map.to_string()].stype, ShardableType::IMap(..))
    {
        return Ok(None);
    }
    let (
        MonoidElt::OptionSome(None),
        MonoidElt::SingletonKV(key, Some(value)),
        MonoidElt::OptionSome(Some(updated)),
    ) = (&remove.elt, &have.elt, &add.elt)
    else {
        return Ok(None);
    };
    let Some(binding) = binding else {
        return Ok(None);
    };
    let verus_syn::Pat::Ident(bound) = &**binding else {
        return Err(Error::new(
            tr.name.span(),
            "distributed pending binding must be an identifier",
        ));
    };
    let bound = &bound.ident;
    if key.to_token_stream().to_string() != bound.to_string() {
        return Err(Error::new(
            tr.name.span(),
            "distributed pending observation reads its bound index",
        ));
    }
    let ShardableType::IMap(key_type, value_type) = &fields[&map.to_string()].stype else {
        unreachable!()
    };
    let mut names = reserved_names(sm);
    let mut fresh = |label: &str| {
        let mut n = format!("__tsm_dist_check_{label}");
        while names.contains(&n) {
            n.push('_')
        }
        names.insert(n.clone());
        verus_syn::Ident::new(&n, proc_macro2::Span::mixed_site())
    };
    let slot = fresh("slot");
    let shared = fresh("shared");
    let owner = fresh("owner");
    let have_owner = fresh("have");
    let current = fresh("current");
    let before = fresh("before");
    let width = fresh("width");
    let combined = fresh("combined");
    let frame = fresh("frame");
    let pre = fresh("pre");
    let post = fresh("post");
    let raw_name = format_ident!("__distributed_{}_raw", tr.name);
    let name = &tr.name;
    let req = format_ident!("{name}_requires");
    let enabled = format_ident!("{name}_enabled");
    let owners = format_ident!("{name}_owners_enabled");
    let deposited = format_ident!("{name}_deposited");
    let with_shared = format_ident!("{name}_with_shared");
    let witness = format_ident!("{name}_witness");
    let constant = &cx.constants[0].name;
    let setter = format_ident!("with_{constant}");
    let getter = format_ident!("value_{option}");
    let factory = format_ident!("field_{option}");
    let map_factory = format_ident!("field_{map}");
    let types = cx.types;
    let expr = cx.expr;
    let token = cx.token;
    let params: Vec<_> = tr
        .params
        .iter()
        .map(|p| {
            let n = &p.name;
            let t = &p.ty;
            quote! {#n:#t}
        })
        .collect();
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    Ok(Some(quote! {
        proof fn #raw_name(tracked #slot:&mut Tracked<Option<#token>>,tracked #shared:&#token,#width:int,#(#params),*)
            requires old(#slot)@ is Some,old(#slot)@->Some_0.fragment().#getter() is Some,
                #shared.loc()==old(#slot)@->Some_0.loc(),
                old(#slot)@->Some_0.fragment()==Fragment #expr::#factory(old(#slot)@->Some_0.fragment().#getter()).#setter(#width),
                #shared.fragment()==Fragment #expr::#map_factory(IMap::<#key_type,#value_type>::empty().insert(old(#slot)@->Some_0.fragment().#getter()->Some_0,#value)).#setter(#width),
            ensures final(#slot)@ is Some,final(#slot)@->Some_0.loc()==old(#slot)@->Some_0.loc(),
                final(#slot)@->Some_0.fragment()==Fragment #expr::#factory(Some({let #bound=old(#slot)@->Some_0.fragment().#getter()->Some_0;#updated})).#setter(#width),
        {
            broadcast use {::vstd::imap::group_imap_lemmas,::vstd::iset::group_iset_lemmas};
            let tracked #current=#slot.borrow_mut().tracked_take();let #before=#current.fragment();let #bound=#before.#getter()->Some_0;
            let #combined=Fragment #expr::op(#before,#shared.fragment());
            assert(#combined.#map.at(#bound)==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(#value)));
            assert(Protocol #expr::#req(#before,#shared.fragment(),IMap::empty(),#(#pn),*)) by{
                assert forall|#frame:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(#combined,#frame)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#pn),*)&&IMap::<int,_>::empty()==State #expr::#deposited(#pre,#(#pn),*)&&State #expr::#owners(#pre,#before,#shared.fragment(),#(#pn),*) by{
                        ::vstd::resource::tsm_collections::option_owned_frame(#combined.#option,#frame.#option,#pre.#option,#bound);
                        ::vstd::resource::tsm_collections::map_owned_frame(#combined.#map,#frame.#map,#pre.#map,#bound,#value);
                        assert(#pre.#option==Some(#bound));assert(#pre.#map.contains_key(#bound));assert(#pre.#map[#bound]==#value);
                    }
            }
            let tracked #current=Protocol #expr::#with_shared(#current,#shared,#(#pn),*);
            let (#pre,#post,#frame)=Protocol #expr::#witness(#before,#shared.fragment(),#current.fragment(),IMap::empty(),IMap::empty(),#(#pn),*);
            ::vstd::resource::tsm_collections::option_owned_frame(#combined.#option,#frame.#option,#pre.#option,#bound);
            Fragment #expr::unit().op_unit();
            assert(#current.fragment()==Fragment #expr::#factory(Some(#updated)).#setter(#width));
            *#slot=Tracked(Some(#current));
        }
        pub proof fn #name(tracked &self,#(#params,)*tracked #owner:&mut #option #types,tracked #have_owner:&#map #types)
            requires old(#owner).instance_id()==self.id(),#have_owner.instance_id()==self.id(),#have_owner.key()==old(#owner).value(),#have_owner.value()==#value,
            ensures final(#owner).instance_id()==self.id(),final(#owner).value()=={let #bound=old(#owner).value();#updated},
        {
            ::vstd::prelude::use_type_invariant(&*#owner);::vstd::prelude::use_type_invariant(#have_owner);
            self.metadata.agrees(&#owner.metadata);self.metadata.agrees(&#have_owner.metadata);
            Self::#raw_name(&mut #owner.raw,#have_owner.borrow_token(),self.#constant(),#(#pn),*);
        }
    }))
}

fn variable_deposit(
    sm: &SM,
    tr: &Transition,
    cx: &roles::Context<'_>,
) -> Result<Option<TokenStream>, Error> {
    struct Ops {
        update: Option<(verus_syn::Ident, verus_syn::Expr)>,
        special: Vec<(verus_syn::Ident, SpecialOp)>,
    }
    fn collect(s: &TransitionStmt, o: &mut Ops) -> bool {
        match s {
            TransitionStmt::Block(_, c) => c.iter().all(|s| collect(s, o)),
            TransitionStmt::Update(_, f, e) if o.update.is_none() => {
                o.update = Some((f.clone(), e.clone()));
                true
            }
            TransitionStmt::Split(_, s, c) => {
                if let SplitKind::Special(f, op, _, None) = &**s {
                    o.special.push((f.clone(), op.clone()));
                    c.iter().all(|s| collect(s, o))
                } else {
                    false
                }
            }
            _ => false,
        }
    }
    let mut ops = Ops {
        update: None,
        special: vec![],
    };
    if !collect(&tr.body, &mut ops) || ops.special.len() != 2 {
        return Ok(None);
    }
    let Some((variable, update)) = ops.update else {
        return Ok(None);
    };
    let (removed, remove) = &ops.special[0];
    let (storage, deposit) = &ops.special[1];
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    if !matches!(
        fields[&variable.to_string()].stype,
        ShardableType::Variable(..)
    ) || !matches!(
        fields[&removed.to_string()].stype,
        ShardableType::Option(..)
    ) || !remove.is_remove()
        || !matches!(deposit.stmt, MonoidStmtType::Deposit)
    {
        return Ok(None);
    }
    let ShardableType::StorageOption(permission) = &fields[&storage.to_string()].stype else {
        return Ok(None);
    };
    let (MonoidElt::OptionSome(Some(removed_value)), MonoidElt::OptionSome(Some(deposited_value))) =
        (&remove.elt, &deposit.elt)
    else {
        return Ok(None);
    };
    let mut names = reserved_names(sm);
    let mut fresh = |label: &str| {
        let mut n = format!("__tsm_dist_dep_{label}");
        while names.contains(&n) {
            n.push('_')
        }
        names.insert(n.clone());
        verus_syn::Ident::new(&n, proc_macro2::Span::mixed_site())
    };
    let slot = fresh("slot");
    let owner = fresh("owner");
    let consumed = fresh("consumed");
    let actual = fresh("actual");
    let width = fresh("width");
    let current = fresh("current");
    let physical = fresh("physical");
    let certificate = fresh("certificate");
    let raw_name = format_ident!("__distributed_{}_raw", tr.name);
    let name = &tr.name;
    let observed = format_ident!("{name}_observed");
    let local = format_ident!("{name}_local_requires");
    let constant = &cx.constants[0].name;
    let setter = format_ident!("with_{constant}");
    let getter = format_ident!("value_{variable}");
    let factory = format_ident!("field_{variable}");
    let removed_factory = format_ident!("field_{removed}");
    let types = cx.types;
    let expr = cx.expr;
    let token = cx.token;
    let params: Vec<_> = tr
        .params
        .iter()
        .map(|p| {
            let n = &p.name;
            let t = &p.ty;
            quote! {#n:#t}
        })
        .collect();
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    // This straight-line form reads source parameters, not an unowned pre-state field.
    for e in [&update, removed_value, deposited_value] {
        let mut e = e.clone();
        let mut errors = vec![];
        crate::field_access_visitor::visit_field_accesses(
            &mut e,
            |errors, f, _| {
                errors.push(Error::new(
                    f.name.span(),
                    "distributed deposit uses explicit native operands",
                ))
            },
            &mut errors,
            &fields,
        );
        if let Some(e) = errors.into_iter().next() {
            return Err(e);
        }
    }
    Ok(Some(quote! {
        proof fn #raw_name(tracked #slot:&mut Tracked<Option<#token>>,tracked #consumed:#token,tracked #actual:#permission,#width:int,#(#params),*)
            requires old(#slot)@ is Some,#consumed.loc()==old(#slot)@->Some_0.loc(),#actual==#deposited_value,
                old(#slot)@->Some_0.fragment()==Fragment #expr::#factory(old(#slot)@->Some_0.fragment().#getter()).#setter(#width),
                #consumed.fragment()==Fragment #expr::#removed_factory(Some(#removed_value)).#setter(#width),
            ensures final(#slot)@ is Some,final(#slot)@->Some_0.loc()==old(#slot)@->Some_0.loc(),
                final(#slot)@->Some_0.fragment()==Fragment #expr::#factory(#update).#setter(#width),
        {
            let tracked #current=#slot.borrow_mut().tracked_take();let tracked #current=#current.join(#consumed);
            let tracked #physical=::vstd::resource::tsm_helpers::singleton_map(0int,#actual);
            #current.fragment().op_unit();
            assert(Protocol #expr::#local(#current.fragment(),Fragment #expr::unit(),#physical,#(#pn),*));
            let tracked #certificate=Protocol #expr::#observed(#current,#physical,#(#pn),*);
            Fragment #expr::unit().op_unit();
            assert(#certificate.token.fragment()==Fragment #expr::#factory(#update).#setter(#width));
            *#slot=Tracked(Some(#certificate.token));
        }
        pub proof fn #name(tracked &self,#(#params,)*tracked #owner:&mut #variable #types,tracked #consumed:#removed #types,tracked #actual:#permission)
            requires old(#owner).instance_id()==self.id(),#consumed.instance_id()==self.id(),#consumed.value()==#removed_value,#actual==#deposited_value,
            ensures final(#owner).instance_id()==self.id(),final(#owner).value()==#update,
        {
            ::vstd::prelude::use_type_invariant(&*#owner);::vstd::prelude::use_type_invariant(&#consumed);
            self.metadata.agrees(&#owner.metadata);self.metadata.agrees(&#consumed.metadata);
            let tracked #consumed=#consumed.raw.get().tracked_unwrap();
            Self::#raw_name(&mut #owner.raw,#consumed,#actual,self.#constant(),#(#pn),*);
        }
    }))
}

fn birds_eye_reader(
    sm: &SM,
    tr: &Transition,
    cx: &roles::Context<'_>,
) -> Result<Option<TokenStream>, Error> {
    struct Ops {
        require: Vec<verus_syn::Expr>,
        special: Vec<(verus_syn::Ident, SpecialOp)>,
        hidden: Option<(Box<verus_syn::Pat>, verus_syn::Expr)>,
    }
    fn collect(s: &TransitionStmt, o: &mut Ops) -> bool {
        match s {
            TransitionStmt::Block(_, c) => c.iter().all(|s| collect(s, o)),
            TransitionStmt::Require(_, e) => {
                o.require.push(e.clone());
                true
            }
            TransitionStmt::Split(_, s, c) => {
                match &**s {
                    SplitKind::Special(f, op, _, None) => o.special.push((f.clone(), op.clone())),
                    SplitKind::Let(p, _, LetKind::BirdsEye, e) if o.hidden.is_none() => {
                        o.hidden = Some((p.clone(), e.clone()))
                    }
                    _ => return false,
                }
                c.iter().all(|s| collect(s, o))
            }
            _ => false,
        }
    }
    let mut o = Ops {
        require: vec![],
        special: vec![],
        hidden: None,
    };
    if !collect(&tr.body, &mut o) || o.special.len() != 2 {
        return Ok(None);
    }
    let Some((binding, selection)) = o.hidden else {
        return Ok(None);
    };
    let verus_syn::Pat::Ident(bound) = &*binding else {
        return Err(Error::new(
            tr.name.span(),
            "distributed stored-value selection binds one identifier",
        ));
    };
    let bound = &bound.ident;
    let (removed, remove) = &o.special[0];
    let (added, add) = &o.special[1];
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    if !remove.is_remove()
        || !add.is_add()
        || !matches!(
            fields[&removed.to_string()].stype,
            ShardableType::Multiset(..)
        )
        || !matches!(
            fields[&added.to_string()].stype,
            ShardableType::Multiset(..)
        )
    {
        return Ok(None);
    }
    let (MonoidElt::SingletonMultiset(removed_value), MonoidElt::SingletonMultiset(added_value)) =
        (&remove.elt, &add.elt)
    else {
        return Ok(None);
    };
    let variable = &sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::Variable(..)))
        .unwrap()
        .name;
    let ShardableType::Multiset(added_type) = &fields[&added.to_string()].stype else {
        unreachable!()
    };
    let mut names = reserved_names(sm);
    let mut fresh = |label: &str| {
        let mut n = format!("__tsm_dist_reader_{label}");
        while names.contains(&n) {
            n.push('_')
        }
        names.insert(n.clone());
        verus_syn::Ident::new(&n, proc_macro2::Span::mixed_site())
    };
    let owned = fresh("owned");
    let shared = fresh("shared");
    let flags = fresh("flags");
    let input = fresh("input");
    let width = fresh("width");
    let certificate = fresh("certificate");
    let result = fresh("result");
    let pre = fresh("pre");
    let post = fresh("post");
    let bag_element = fresh("bag_element");
    let raw_name = format_ident!("__distributed_{}_raw", tr.name);
    let name = &tr.name;
    let local = format_ident!("{name}_local_requires");
    let observed = format_ident!("{name}_local_with_shared");
    let witness = format_ident!("{name}_witness");
    let before = fresh("before");
    let current = fresh("current");
    let frame = fresh("frame");
    let strong = format_ident!("{name}_strong");
    let constant = &cx.constants[0].name;
    let setter = format_ident!("with_{constant}");
    let variable_factory = format_ident!("field_{variable}");
    let variable_getter = format_ident!("value_{variable}");
    let removed_factory = format_ident!("field_{removed}");
    let added_factory = format_ident!("field_{added}");
    let types = cx.types;
    let expr = cx.expr;
    let token = cx.token;
    let params: Vec<_> = tr
        .params
        .iter()
        .map(|p| {
            let n = &p.name;
            let t = &p.ty;
            quote! {#n:#t}
        })
        .collect();
    let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let lower = |e: &verus_syn::Expr, replacement: TokenStream| -> Result<TokenStream, Error> {
        let mut e = e.clone();
        let mut errors = vec![];
        crate::field_access_visitor::visit_field_accesses(
            &mut e,
            |errors, f, slot| {
                if f.name == *variable {
                    *slot = verus_syn::parse2(replacement.clone()).unwrap()
                } else {
                    errors.push(Error::new(
                        f.name.span(),
                        "distributed reader requires its supplied variable observation",
                    ))
                }
            },
            &mut errors,
            &fields,
        );
        if let Some(e) = errors.into_iter().next() {
            Err(e)
        } else {
            Ok(quote! {#e})
        }
    };
    let raw_require: Vec<_> = o
        .require
        .iter()
        .map(|e| lower(e, quote! {#shared.fragment().#variable_getter()}))
        .collect::<Result<_, _>>()?;
    let public_require: Vec<_> = o
        .require
        .iter()
        .map(|e| lower(e, quote! {#flags.value()}))
        .collect::<Result<_, _>>()?;
    use verus_syn::visit_mut::VisitMut;
    struct Pre(verus_syn::Ident);
    impl VisitMut for Pre {
        fn visit_expr_path_mut(&mut self, e: &mut verus_syn::ExprPath) {
            if e.path.is_ident("pre") {
                let n = &self.0;
                e.path = verus_syn::parse_quote!(#n)
            }
        }
    }
    let mut selected = selection.clone();
    Pre(pre.clone()).visit_expr_mut(&mut selected);
    let mut certificate_selection = selection.clone();
    struct Certificate(verus_syn::Ident);
    impl VisitMut for Certificate {
        fn visit_expr_mut(&mut self, e: &mut verus_syn::Expr) {
            if matches!(e,verus_syn::Expr::Path(p) if p.path.is_ident("pre")) {
                let n = &self.0;
                *e = verus_syn::parse_quote!(#n.before)
            } else {
                verus_syn::visit_mut::visit_expr_mut(self, e)
            }
        }
    }
    Certificate(certificate.clone()).visit_expr_mut(&mut certificate_selection);
    let mut bag_norm = vec![];
    for f in &sm.fields {
        if let ShardableType::Multiset(ty) = &f.stype {
            let n = &f.name;
            let expected = if n == added {
                quote! {Multiset::<#ty>::singleton(#added_value)}
            } else {
                quote! {Multiset::<#ty>::empty()}
            };
            bag_norm.push(quote!{
        assert forall|#bag_element:#ty| #[trigger] #certificate.token.fragment().#n.values.count(#bag_element)==(#expected).count(#bag_element) by{};
        assert(::vstd::prelude::ext_equal(#certificate.token.fragment().#n.values,#expected));
    })
        }
    }
    Ok(Some(quote! {
        proof fn #raw_name(tracked #owned:#token,tracked #shared:&#token,#width:int,#(#params),*)->(tracked #result:(Tracked<#token>,Ghost<#added_type>))
            requires #owned.loc()==#shared.loc(),#owned.fragment()==Fragment #expr::#removed_factory(Multiset::singleton(#removed_value)).#setter(#width),
                #shared.fragment()==Fragment #expr::#variable_factory(#shared.fragment().#variable_getter()).#setter(#width),#(#raw_require,)*
            ensures #result.0@.loc()==#owned.loc(),#result.0@.fragment()==Fragment #expr::#added_factory(Multiset::singleton(#result.1@)).#setter(#width),
                exists|#pre:State #types,#post:State #types|#pre.invariant()&&#post.invariant()&&#pre.#constant==#width&&State #expr::#strong(#pre,#post,#(#pn),*)&&#result.1@=={let #bound=#selected;#added_value},
        {
            broadcast use ::vstd::multiset::group_multiset_axioms;
            assert(Protocol #expr::#local(#owned.fragment(),#shared.fragment(),IMap::empty(),#(#pn),*));
            let #before=#owned.fragment();
            let tracked #current=Protocol #expr::#observed(#owned,#shared,#(#pn),*);
            let (#pre,#post,#frame)=Protocol #expr::#witness(#before,#shared.fragment(),#current.fragment(),IMap::empty(),IMap::empty(),#(#pn),*);
            let tracked #certificate=TransitionObservation{token:#current,withdrawn:IMap::<int,_>::tracked_empty(),before:#pre,after:#post,frame:#frame};
            let #bound=#certificate_selection;
            #(#bag_norm)*Fragment #expr::unit().op_unit();
            assert(#certificate.token.fragment()==Fragment #expr::#added_factory(Multiset::singleton(#added_value)).#setter(#width));
            assert(#certificate.before.#constant==#width);
            (Tracked(#certificate.token),Ghost(#added_value))
        }
        pub proof fn #name(tracked &self,#(#params,)*tracked #flags:&#variable #types,tracked #input:#removed #types)->(tracked #result:#added #types)
            requires #flags.instance_id()==self.id(),#input.instance_id()==self.id(),#input.element()==#removed_value,#(#public_require,)*
            ensures #result.instance_id()==self.id(),
                exists|#pre:State #types,#post:State #types|#pre.invariant()&&#post.invariant()&&#pre.#constant==self.#constant()&&State #expr::#strong(#pre,#post,#(#pn),*)&&#result.element()=={let #bound=#selected;#added_value},
        {
            ::vstd::prelude::use_type_invariant(#flags);::vstd::prelude::use_type_invariant(&#input);
            self.metadata.agrees(&#flags.metadata);self.metadata.agrees(&#input.metadata);
            let tracked #owned=#input.raw.get().tracked_unwrap();
            let tracked(Tracked(#owned),#result)=Self::#raw_name(#owned,#flags.borrow_token(),self.#constant(),#(#pn),*);
            <#added #types>::__from_token(#owned,self.metadata.clone(),#result@)
        }
    }))
}
