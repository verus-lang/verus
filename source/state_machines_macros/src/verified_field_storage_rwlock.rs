//! Physical optional storage with variable, optional and multiset owners.
use crate::ast::*;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use crate::verified_field_storage_roles as roles;
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote, ToTokens};
use std::collections::{HashMap, HashSet};
use verus_syn::Expr;
use verus_syn::{Error, Ident};

#[derive(Default)]
struct Operations {
    requirements: Vec<Expr>,
    assertions: Vec<Expr>,
    update: Option<(Ident, Expr)>,
    special: Vec<(Ident, SpecialOp)>,
    hidden: Option<(Box<verus_syn::Pat>, Expr)>,
}
fn collect(stmt: &TransitionStmt, out: &mut Operations) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                collect(child, out)?;
            }
        }
        TransitionStmt::Require(_, e) => out.requirements.push(e.clone()),
        TransitionStmt::Assert(_, e, _) => out.assertions.push(e.clone()),
        TransitionStmt::Update(_, field, e) => {
            if out.update.replace((field.clone(), e.clone())).is_some() {
                return Err(Error::new(
                    field.span(),
                    "mixed physical scope permits one variable update",
                ));
            }
        }
        TransitionStmt::Split(span, split, children) => {
            match &**split {
                SplitKind::Special(field, op, _, None) => out.special.push((field.clone(),op.clone())),
                SplitKind::Let(p, _, LetKind::BirdsEye, e) if out.hidden.is_none() => out.hidden=Some((p.clone(),e.clone())),
                _ => return Err(Error::new(*span,"mixed physical scope requires straight-line unbound operations and one physical selection")),
            }
            for child in children {
                collect(child, out)?;
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "unsupported mixed physical transition statement",
            ))
        }
    }
    Ok(())
}

pub fn needed(sm: &SM) -> bool {
    sm.fields.len() == 6
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
fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
    for token in tokens {
        match token {
            TokenTree::Ident(id) => {
                names.insert(id.to_string());
            }
            TokenTree::Group(g) => reserve(g.stream(), names),
            _ => {}
        }
    }
}
fn initial(
    stmt: &TransitionStmt,
    values: &mut HashMap<String, verus_syn::Expr>,
) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                initial(child, values)?;
            }
        }
        TransitionStmt::Initialize(_, field, value) => {
            values.insert(field.to_string(), value.clone());
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "mixed physical initializer requires explicit straight-line fields",
            ))
        }
    }
    Ok(())
}
pub fn output(sm: &SM, _selected: &HashSet<String>) -> Result<TokenStream, Error> {
    if !needed(sm) {
        return Err(Error::new(sm.name.span(), "mixed physical facade requires one variable, two optional roles, two multiset roles and optional storage"));
    }
    let mut generated_types: HashSet<String> = [
        "State",
        "Fragment",
        "Protocol",
        "Token",
        "Instance",
        "TransitionObservation",
    ]
    .into_iter()
    .map(|s| s.to_string())
    .collect();
    for field in sm.fields.iter().filter(|f| !f.stype.is_storage()) {
        if !generated_types.insert(field.name.to_string()) {
            return Err(Error::new(
                field.name.span(),
                "mixed physical field conflicts with a generated type",
            ));
        }
        if matches!(field.stype, ShardableType::Multiset(..))
            && !generated_types.insert(format!("{}_collection", field.name))
        {
            return Err(Error::new(
                field.name.span(),
                "mixed physical collection name collision",
            ));
        }
    }
    if let Some(g) = &sm.generics {
        for p in &g.params {
            let n = match p {
                verus_syn::GenericParam::Type(p) => Some(&p.ident),
                verus_syn::GenericParam::Const(p) => Some(&p.ident),
                _ => None,
            };
            if let Some(n) = n {
                if generated_types.contains(&n.to_string()) {
                    return Err(Error::new(
                        n.span(),
                        "mixed physical generic conflicts with a generated type",
                    ));
                }
            }
        }
    }
    let mut generated_methods: HashSet<String> =
        ["id", "clone", "invariant", "__protocol_location"]
            .into_iter()
            .map(|s| s.to_string())
            .collect();
    for transition in &sm.transitions {
        if !generated_methods.insert(transition.name.to_string())
            || !generated_methods.insert(format!("__mixed_physical_{}_raw", transition.name))
        {
            return Err(Error::new(
                transition.name.span(),
                "mixed physical transition conflicts with a generated method",
            ));
        }
    }
    let store = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::StorageOption(..)))
        .unwrap();
    let ShardableType::StorageOption(permission) = &store.stype else {
        unreachable!()
    };
    let (g, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&g);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let mut names: HashSet<_> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(sm.transitions.iter().map(|t| t.name.to_string()))
        .collect();
    if let Some(g) = &sm.generics {
        reserve(quote! {#g}, &mut names);
    }
    for field in &sm.fields {
        let ty = field.get_type();
        reserve(quote! {#ty}, &mut names);
    }
    let mut fresh = |label: &str| {
        let mut name = format!("__tsm_optional_multiset_{label}");
        while names.contains(&name) {
            name.push('_');
        }
        names.insert(name.clone());
        Ident::new(&name, Span::mixed_site())
    };
    let metadata = fresh("Metadata");
    let location = fresh("protocol_location");
    let marker = fresh("payload");
    let token = quote! {Token #types};
    let descriptor = quote! {::vstd::resource::tsm_context::Descriptor<#metadata #types>};
    let constants = vec![];
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
    let mut wrappers = Vec::new();
    for field in sm.fields.iter().filter(|f| !f.stype.is_storage()) {
        wrappers.push(roles::wrapper(field, &cx)?);
        if matches!(field.stype, ShardableType::Multiset(..)) {
            wrappers.push(crate::verified_field_storage_collections::wrapper(
                field,
                &cx,
                &reservation,
            )?);
        }
    }
    let mut methods = Vec::new();
    for tr in &sm.transitions {
        if tr.kind == TransitionKind::Property {
            let reader=sm.fields.iter().find(|f| matches!(&f.stype,ShardableType::Multiset(element) if element.to_token_stream().to_string()==permission.to_token_stream().to_string())).ok_or_else(||Error::new(tr.name.span(),"optional guard requires a matching actual reader payload"))?;
            methods.push(roles::guard_method(reader, tr, &cx)?);
            continue;
        }
        if tr.kind != TransitionKind::Init {
            methods.push(method(sm, tr, &cx)?);
            continue;
        }
        let mut values = HashMap::new();
        initial(&tr.body, &mut values)?;
        if values.len() != sm.fields.len() || tr.params.len() != 0 {
            return Err(Error::new(
                tr.name.span(),
                "initial mixed physical scope requires complete parameter-free initialization",
            ));
        }
        let storage_value = &values[&store.name.to_string()];
        let storage_native = store.get_type();
        let storage_anchor = fresh("initial_storage_value");
        let storage_value =
            quote! {((|#storage_anchor:#storage_native|#storage_anchor)(#storage_value))};
        let name = &tr.name;
        let owned = fresh("initial_owner");
        let context = fresh("descriptor");
        let owners: Vec<_> = sm.fields.iter().filter(|f| !f.stype.is_storage()).collect();
        let mut returns = Vec::new();
        let mut observations = Vec::new();
        let mut constructions = Vec::new();
        let mut takes = Vec::new();
        for (offset, field) in owners.iter().enumerate() {
            let index = verus_syn::Index::from(offset + 1);
            let field_name = &field.name;
            let value = &values[&field.name.to_string()];
            let native = field.get_type();
            let parameter = fresh(&format!("initial_value_{field_name}"));
            let value = quote! {((|#parameter:#native|#parameter)(#value))};
            let raw = fresh(&format!("initial_{field_name}"));
            let take = format_ident!("take_{field_name}");
            let getter = format_ident!("value_{field_name}");
            takes.push(quote! {let tracked(#raw,#owned)=Protocol #expr::#take(#owned);});
            match &field.stype {
                ShardableType::Variable(..) => {
                    returns.push(quote! {#field_name #types});
                    observations.push(quote!{out.#index@.instance_id()==out.0@.id(),out.#index@.value()==#value,});
                    constructions.push(
                        quote! {Tracked(<#field_name #types>::__from_token(#raw,#context.clone()))},
                    );
                }
                ShardableType::Option(..) => {
                    returns.push(quote! {Option<#field_name #types>});
                    observations.push(quote!{(out.#index@ is Some)==((#value) is Some),::vstd::prelude::imply(out.#index@ is Some,out.#index@->Some_0.instance_id()==out.0@.id()&&out.#index@->Some_0.value()==(#value)->Some_0),});
                    constructions.push(quote!{Tracked(if (#value) is Some{Some(<#field_name #types>::__from_token(#raw,#context.clone(),(#value)->Some_0))}else{None})});
                }
                ShardableType::Multiset(..) => {
                    let bulk = format_ident!("{field_name}_collection");
                    returns.push(quote! {#bulk #types});
                    observations.push(quote!{out.#index@.instance_id()==out.0@.id(),out.#index@.multiset()==#value,});
                    constructions.push(quote!{Tracked(<#bulk #types>::__from_token(#raw,#context.clone(),#value))});
                }
                _ => unreachable!(),
            }
            let _ = getter;
        }
        methods.push(quote!{
            pub proof fn #name()->(tracked out:(Tracked<Self>,#(Tracked<#returns>),*))
                requires (#storage_value) is None,
                ensures #(#observations)*
            {
                let tracked #owned=Protocol #expr::#name(::vstd::imap::IMap::tracked_empty());
                let tracked #context=::vstd::resource::tsm_context::Descriptor::alloc(#metadata{#location:#owned.loc(),#marker:core::marker::PhantomData});
                #(#takes)*
                (Tracked(Self{metadata:#context.clone()}),#(#constructions),*)
            }
        });
    }
    Ok(quote! {
        #(#attrs)*struct #metadata #decl #wc{ghost #location: ::vstd::resource::Loc,ghost #marker:core::marker::PhantomData<#permission>}
        #(#wrappers)*
        #(#attrs)*pub tracked struct Instance #decl #wc{metadata:#descriptor}
        impl #decl Instance #types #wc{
            pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}
            pub closed spec fn __protocol_location(&self)->::vstd::resource::Loc{self.metadata.value().#location}
            pub proof fn clone(tracked &self)->(tracked out:Self)
                ensures out.id()==self.id(),out.__protocol_location()==self.__protocol_location(),
            {Self{metadata:self.metadata.clone()}}
            #(#methods)*
        }
    })
}

fn method(sm: &SM, tr: &Transition, cx: &roles::Context<'_>) -> Result<TokenStream, Error> {
    let mut ops = Operations::default();
    collect(&tr.body, &mut ops)?;
    let variable = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::Variable(..)))
        .unwrap();
    let storage = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::StorageOption(..)))
        .unwrap();
    let ShardableType::StorageOption(permission) = &storage.stype else {
        unreachable!()
    };
    let sn = &storage.name;
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let mut removed = None;
    let mut added = None;
    let mut deposit = None;
    let mut withdraw = false;
    for (field, op) in &ops.special {
        let f = &fields[&field.to_string()];
        match op.stmt {
            MonoidStmtType::Remove if !f.stype.is_storage() && removed.is_none() => {
                removed = Some((f, op))
            }
            MonoidStmtType::Add(_) if !f.stype.is_storage() && added.is_none() => {
                added = Some((f, op))
            }
            MonoidStmtType::Deposit if f.name == storage.name && deposit.is_none() => {
                let MonoidElt::OptionSome(Some(value)) = &op.elt else {
                    return Err(Error::new(
                        field.span(),
                        "mixed deposit requires an actual optional singleton",
                    ));
                };
                deposit = Some(value);
            }
            MonoidStmtType::Withdraw if f.name == storage.name && !withdraw => withdraw = true,
            _ => {
                return Err(Error::new(
                    field.span(),
                    "mixed physical scope permits one logical Remove/Add and one physical transfer",
                ))
            }
        }
    }
    if deposit.is_some() && withdraw {
        return Err(Error::new(
            tr.name.span(),
            "mixed physical scope does not pair deposit with withdrawal",
        ));
    }
    if let Some((field, _)) = &ops.update {
        if *field != variable.name {
            return Err(Error::new(
                field.span(),
                "mixed physical scope updates its actual variable owner only",
            ));
        }
    }
    if ops.update.is_none() && removed.is_none() {
        return Err(Error::new(
            tr.name.span(),
            "mixed physical operation requires an actual consumed owner",
        ));
    }
    let mut names: HashSet<_> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(sm.transitions.iter().map(|t| t.name.to_string()))
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .collect();
    if let Some(g) = &sm.generics {
        reserve(quote! {#g}, &mut names);
    }
    for f in &sm.fields {
        let ty = f.get_type();
        reserve(quote! {#ty}, &mut names);
    }
    for e in ops.requirements.iter().chain(&ops.assertions) {
        reserve(quote! {#e}, &mut names);
    }
    if let Some((_, e)) = &ops.update {
        reserve(quote! {#e}, &mut names);
    }
    if let Some((p, e)) = &ops.hidden {
        reserve(quote! {#p #e}, &mut names);
    }
    for (_, op) in &ops.special {
        match &op.elt {
            MonoidElt::OptionSome(Some(e)) | MonoidElt::SingletonMultiset(e) => {
                reserve(quote! {#e}, &mut names)
            }
            _ => {}
        }
    }
    let mut fresh = |label: &str| {
        let mut n = format!("__tsm_mixed_physical_{label}");
        while names.contains(&n) {
            n.push('_');
        }
        names.insert(n.clone());
        Ident::new(&n, Span::mixed_site())
    };
    let owner = fresh("variable");
    let slot = fresh("slot");
    let consumed = fresh("consumed");
    let shared = fresh("shared");
    let owned = fresh("owned");
    let before = fresh("before");
    let pre = fresh("pre");
    let post = fresh("post");
    let frame = fresh("frame");
    let dep = fresh("deposit");
    let wd = fresh("withdrawn");
    let actual = fresh("actual");
    let selected = fresh("selected");
    let produced = fresh("produced");
    let remainder = fresh("remainder");
    let initial = fresh("initial");
    let raw_result = fresh("raw_result");
    let result = fresh("result");
    let vn = &variable.name;
    let vf = format_ident!("field_{vn}");
    let vg = format_ident!("value_{vn}");
    let vo = format_ident!("owns_{vn}");
    let types = cx.types;
    let expr = cx.expr;
    let token = cx.token;
    let native = variable.get_type();
    let lower = |e: &Expr, value: TokenStream| -> Result<TokenStream, Error> {
        let mut e = e.clone();
        let mut errors = vec![];
        crate::field_access_visitor::visit_field_accesses(
            &mut e,
            |errors, f, slot| {
                if f.name == *vn {
                    *slot = verus_syn::parse2(value.clone()).unwrap();
                } else {
                    errors.push(Error::new(
                        f.name.span(),
                        "mixed physical native clauses read only the supplied variable",
                    ));
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
    let mutating = ops.update.is_some();
    let pub_value = if mutating {
        quote! {old(#owner).value()}
    } else {
        quote! {#owner.value()}
    };
    let raw_value = if mutating {
        quote! {old(#slot)@->Some_0.fragment().#vg()}
    } else {
        quote! {#shared.fragment().#vg()}
    };
    let public_req: Vec<_> = ops
        .requirements
        .iter()
        .map(|e| lower(e, pub_value.clone()))
        .collect::<Result<_, _>>()?;
    let raw_req: Vec<_> = ops
        .requirements
        .iter()
        .map(|e| lower(e, raw_value.clone()))
        .collect::<Result<_, _>>()?;
    let update = ops
        .update
        .as_ref()
        .map(|(_, e)| lower(e, pub_value.clone()))
        .transpose()?;
    let raw_update = ops
        .update
        .as_ref()
        .map(|(_, e)| lower(e, raw_value.clone()))
        .transpose()?;
    let operand = |f: &Field, op: &SpecialOp| -> Result<(TokenStream, TokenStream), Error> {
        Ok(match (&f.stype, &op.elt) {
            (ShardableType::Option(_), MonoidElt::OptionSome(Some(e))) => {
                (quote! {Some(#e)}, quote! {#e})
            }
            (ShardableType::Multiset(t), MonoidElt::SingletonMultiset(e)) => (
                quote! {::vstd::multiset::Multiset::<#t>::singleton(#e)},
                quote! {#e},
            ),
            _ => {
                return Err(Error::new(
                    f.name.span(),
                    "mixed physical scope needs explicit optional/multiset singletons",
                ))
            }
        })
    };
    let removed_native = removed.map(|(f, o)| operand(f, o)).transpose()?;
    let mut raw_consume = quote! {};
    let mut raw_consume_req = quote! {};
    let mut public_consume = quote! {};
    let mut public_consume_req = quote! {};
    let mut consume_use = quote! {};
    let mut consume_arg = quote! {};
    let mut remove_hints = quote! {};
    if let Some((f, _)) = removed {
        let fnm = &f.name;
        let ff = format_ident!("field_{fnm}");
        let (value, element) = removed_native.as_ref().unwrap();
        let accessor = if matches!(f.stype, ShardableType::Option(..)) {
            quote! {value}
        } else {
            quote! {element}
        };
        raw_consume = quote! {tracked #consumed:#token,};
        raw_consume_req = quote! {#consumed.fragment()==Fragment #expr::#ff(#value),};
        public_consume = quote! {tracked #consumed:#fnm #types,};
        public_consume_req =
            quote! {#consumed.instance_id()==self.id(),#consumed.#accessor()==#element,};
        consume_use = quote! {::vstd::prelude::use_type_invariant(&#consumed);self.metadata.agrees(&#consumed.metadata);};
        consume_arg = quote! {#consumed.raw.get().tracked_unwrap(),};
        remove_hints = match &f.stype {
            ShardableType::Option(_) => {
                quote! {::vstd::resource::tsm_collections::option_owned_frame(#before.#fnm,#frame.#fnm,#pre.#fnm,#element);}
            }
            ShardableType::Multiset(t) => quote! {
                #before.#fnm.op_unit();
                assert(::vstd::resource::tsm_finite_multiset::FiniteMultisetRA::<#t>::op(#before.#fnm,#frame.#fnm)==::vstd::resource::tsm_finite_multiset::finite_multiset_frag(#pre.#fnm));
                ::vstd::resource::tsm_finite_multiset::finite_multiset_owned_frame(#before.#fnm,#frame.#fnm,#pre.#fnm,#element);
            },
            _ => unreachable!(),
        };
    }
    let physical_param = if deposit.is_some() {
        quote! {tracked #actual:#permission,}
    } else {
        quote! {}
    };
    let physical_req = deposit.map(|e| quote! {#actual==#e,}).unwrap_or_default();
    let dep_arg = if deposit.is_some() {
        quote! {#dep,}
    } else {
        quote! {}
    };
    let physical_arg = if deposit.is_some() {
        quote! {#actual,}
    } else {
        quote! {}
    };
    let pack = if deposit.is_some() {
        quote! {let tracked #dep=::vstd::resource::tsm_helpers::singleton_map(0int,#actual);}
    } else {
        quote! {}
    };
    let dep_value = deposit
        .map(|e| quote! {::vstd::imap::IMap::empty().insert(0int,#e)})
        .unwrap_or_else(|| quote! {::vstd::imap::IMap::empty()});
    let shared_fragment = if mutating {
        quote! {Fragment #expr::empty()}
    } else {
        quote! {#shared.fragment()}
    };
    let raw_signature = if mutating {
        quote! {tracked #slot:&mut Tracked<Option<#token>>,}
    } else {
        quote! {tracked #shared:&#token,}
    };
    let raw_input = if mutating {
        quote! {
            let tracked #owned=#slot.borrow_mut().tracked_take();
            #owned.fragment().op_unit();
        }
    } else {
        quote! {}
    };
    let raw_same = if mutating {
        removed
            .map(|_| quote! {#consumed.loc()==old(#slot)@->Some_0.loc(),})
            .unwrap_or_default()
    } else {
        quote! {#consumed.loc()==#shared.loc(),}
    };
    let raw_shape = if mutating {
        quote! {
            old(#slot)@ is Some,old(#slot)@->Some_0.fragment().#vo(),
            old(#slot)@->Some_0.fragment()==Fragment #expr::#vf(old(#slot)@->Some_0.fragment().#vg()),
        }
    } else {
        quote! {
            #shared.fragment().#vo(),#shared.fragment()==Fragment #expr::#vf(#shared.fragment().#vg()),
        }
    };
    let joining = if mutating && removed.is_some() {
        quote! {let tracked #owned=#owned.join(#consumed);}
    } else if !mutating {
        quote! {let tracked #owned=#consumed;}
    } else {
        quote! {}
    };
    let raw_location = if mutating {
        quote! {old(#slot)@->Some_0.loc()}
    } else {
        quote! {#shared.loc()}
    };
    let raw_post = if mutating {
        let value = raw_update.as_ref().unwrap();
        quote! {final(#slot)@ is Some,final(#slot)@->Some_0.loc()==#raw_location,
        final(#slot)@->Some_0.fragment()==Fragment #expr::#vf(#value),}
    } else {
        quote! {}
    };
    let public_post = update
        .as_ref()
        .map(|e| quote! {final(#owner).instance_id()==self.id(),final(#owner).value()==#e,})
        .unwrap_or_default();
    let flags_in = if mutating {
        quote! {tracked #owner:&mut #vn #types,}
    } else {
        quote! {tracked #owner:&#vn #types,}
    };
    let flags_id = if mutating {
        quote! {old(#owner).instance_id()==self.id()}
    } else {
        quote! {#owner.instance_id()==self.id()}
    };
    let flags_use = if mutating {
        quote! {::vstd::prelude::use_type_invariant(&*#owner);}
    } else {
        quote! {::vstd::prelude::use_type_invariant(#owner);}
    };
    let public_flags_arg = if mutating {
        quote! {&mut #owner.raw,}
    } else {
        quote! {#owner.borrow_token(),}
    };
    let name = &tr.name;
    let req = format_ident!("{name}_requires");
    let enabled = format_ident!("{name}_enabled");
    let owners = format_ident!("{name}_owners_enabled");
    let deposited = format_ident!("{name}_deposited");
    let strong = format_ident!("{name}_strong");
    let witness = format_ident!("{name}_witness");
    let shared_fn = format_ident!("{name}_with_shared");
    let raw_fn = format_ident!("__mixed_physical_{name}_raw");
    if sm.transitions.iter().any(|t| t.name == raw_fn) {
        return Err(Error::new(
            name.span(),
            "transition conflicts with mixed physical raw adapter",
        ));
    }
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
    let call = if mutating {
        quote! {Protocol #expr::#name(#owned,#dep_arg #(#pn),*)}
    } else {
        quote! {Protocol #expr::#shared_fn(#owned,#shared,#dep_arg #(#pn),*)}
    };
    let operation = if withdraw {
        quote! {let tracked(#owned,#wd)=#call;}
    } else {
        quote! {let tracked #owned=#call;let #wd=::vstd::imap::IMap::empty();}
    };
    let mut choose = quote! {};
    let mut role_return_type = quote! {};
    let mut role_return_req = quote! {};
    let mut role_native = quote! {};
    let mut role_value = quote! {};
    let mut role_type = quote! {};
    let mut hidden_role = false;
    if let Some((f, o)) = added {
        let fnm = &f.name;
        let ff = format_ident!("field_{fnm}");
        role_type = quote! {#fnm #types};
        hidden_role = ops.hidden.as_ref().is_some_and(|(p, _)| {
            let v = match &o.elt {
                MonoidElt::OptionSome(Some(e)) | MonoidElt::SingletonMultiset(e) => e,
                _ => return false,
            };
            p.to_token_stream().to_string() == v.to_token_stream().to_string()
        });
        if hidden_role {
            let (_, e) = ops.hidden.as_ref().unwrap();
            let mut e = e.clone();
            use verus_syn::visit_mut::VisitMut;
            struct Replace(Ident);
            impl VisitMut for Replace {
                fn visit_expr_path_mut(&mut self, e: &mut verus_syn::ExprPath) {
                    if e.path.is_ident("pre") {
                        let id = &self.0;
                        e.path = verus_syn::parse_quote!(#id);
                    }
                }
            }
            Replace(pre.clone()).visit_expr_mut(&mut e);
            choose = quote! {let #selected=#e;};
            role_value = quote! {#selected};
            role_native = match &f.stype {
                ShardableType::Option(_) => quote! {Some(#selected)},
                ShardableType::Multiset(t) => {
                    quote! {::vstd::multiset::Multiset::<#t>::singleton(#selected)}
                }
                _ => unreachable!(),
            };
        } else {
            let (n, v) = operand(f, o)?;
            role_native = n;
            role_value = v;
            choose = quote! {let #selected=#role_value;};
        }
        role_return_type = quote! {Tracked<#token>,Ghost<#permission>,};
        // The ghost selector's type may differ from the physical payload for
        // ordinary unit options/bags; use the added field's actual element.
        let element = match &f.stype {
            ShardableType::Option(t) | ShardableType::Multiset(t) => t,
            _ => unreachable!(),
        };
        role_return_type = quote! {Tracked<#token>,Ghost<#element>,};
        role_return_req = quote! {#result.0@.loc()==#raw_location,#result.0@.fragment()==Fragment #expr::#ff(match (){()=>#role_native}),};
        let _ = &role_value;
    }
    let raw_return_type = if added.is_some() && withdraw {
        quote! {->(tracked #result:(#role_return_type Tracked<#permission>))}
    } else if added.is_some() {
        quote! {->(tracked #result:(#role_return_type))}
    } else if withdraw {
        quote! {->(tracked #result:Tracked<#permission>)}
    } else {
        quote! {}
    };
    // The selector in the result contract is its actual ghost result.
    if let Some((f, _)) = added {
        let fnm = &f.name;
        let ff = format_ident!("field_{fnm}");
        let n = match &f.stype {
            ShardableType::Option(_) => quote! {Some(#result.1@)},
            ShardableType::Multiset(t) => {
                quote! {::vstd::multiset::Multiset::<#t>::singleton(#result.1@)}
            }
            _ => unreachable!(),
        };
        role_return_req = quote! {#result.0@.loc()==#raw_location,#result.0@.fragment()==Fragment #expr::#ff(#n),};
        if !hidden_role {
            role_return_req.extend(quote! {#result.1@==#role_value,});
        }
    }
    let mut bag_normalization = quote! {};
    for bag in sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Multiset(..)))
    {
        let n = &bag.name;
        let ShardableType::Multiset(t) = &bag.stype else {
            unreachable!()
        };
        let expected = if added.is_some_and(|(f, _)| f.name == bag.name) {
            role_native.clone()
        } else {
            quote! {::vstd::multiset::Multiset::<#t>::empty()}
        };
        let candidate = fresh(&format!("normalization_{n}"));
        bag_normalization.extend(quote!{
            assert forall|#candidate:#t| #[trigger] #owned.fragment().#n.values.count(#candidate)==(#expected).count(#candidate) by{};
            assert(::vstd::prelude::ext_equal(#owned.fragment().#n.values,#expected));
        });
    }
    let splitting = if let Some((f, _)) = added {
        let take = format_ident!("take_{}", f.name);
        quote! {let tracked(#produced,#owned)=Protocol #expr::#take(#owned);}
    } else {
        quote! {}
    };
    let restore = if mutating {
        quote! {*#slot=Tracked(Some(#owned));}
    } else {
        quote! {}
    };
    let extract = if withdraw {
        quote! {
            assert(#wd==::vstd::imap::IMap::empty().insert(0int,#pre.#sn->Some_0));
            let tracked #actual=::vstd::resource::tsm_helpers::take_singleton(#wd,0int);
        }
    } else {
        quote! {}
    };
    let return_expr = if added.is_some() && withdraw {
        quote! {(Tracked(#produced),Ghost(#selected),Tracked(#actual))}
    } else if added.is_some() {
        quote! {(Tracked(#produced),Ghost(#selected))}
    } else if withdraw {
        quote! {Tracked(#actual)}
    } else {
        quote! {}
    };
    let public_returns = if added.is_some() && withdraw {
        quote! {->(tracked #result:(Tracked<#role_type>,Tracked<#permission>))}
    } else if added.is_some() {
        quote! {->(tracked #result:#role_type)}
    } else if withdraw {
        quote! {->(tracked #result:#permission)}
    } else {
        quote! {}
    };
    let public_result_req = if added.is_some() {
        let accessor = if matches!(added.unwrap().0.stype, ShardableType::Option(..)) {
            quote! {value}
        } else {
            quote! {element}
        };
        let role_out = if withdraw {
            quote! {#result.0@}
        } else {
            quote! {#result}
        };
        let valreq = if !hidden_role {
            quote! {#role_out.#accessor()==#role_value,}
        } else {
            quote! {}
        };
        quote! {#role_out.instance_id()==self.id(),#valreq}
    } else {
        quote! {}
    };
    // Both mathematical descriptions refer to the same actual exchange witness;
    // the physical result itself is still taken exclusively from the tracked map.
    let mut raw_observation = quote! {};
    let mut public_observation = quote! {};
    if hidden_role || withdraw {
        let raw_payload = if withdraw {
            if added.is_some() {
                quote! {#result.2@}
            } else {
                quote! {#result@}
            }
        } else {
            quote! {#result.1@}
        };
        let public_payload = if withdraw {
            if added.is_some() {
                quote! {#result.1@}
            } else {
                quote! {#result}
            }
        } else {
            quote! {#result.element()}
        };
        raw_observation = quote! {exists|#pre:State #types,#post:State #types|
        #pre.invariant()&&#post.invariant()&&#pre.#vn==#raw_value
        &&State #expr::#strong(#pre,#post,#(#pn),*)
        &&#pre.#sn is Some&&#raw_payload==#pre.#sn->Some_0,};
        public_observation = quote! {exists|#pre:State #types,#post:State #types|
        #pre.invariant()&&#post.invariant()&&#pre.#vn==#pub_value
        &&State #expr::#strong(#pre,#post,#(#pn),*)
        &&#pre.#sn is Some&&#public_payload==#pre.#sn->Some_0,};
    }
    let raw_call = quote! {Self::#raw_fn(#(#pn,)*#public_flags_arg #consume_arg #physical_arg)};
    let public_body = if let Some((f, _)) = added {
        let fnm = &f.name;
        if withdraw {
            quote! {let tracked(#produced,#selected,#actual)=#raw_call;(Tracked(<#fnm #types>::__from_token(#produced.get(),self.metadata.clone(),#selected@)),#actual)}
        } else {
            quote! {let tracked(#produced,#selected)=#raw_call;<#fnm #types>::__from_token(#produced.get(),self.metadata.clone(),#selected@)}
        }
    } else if withdraw {
        quote! {#raw_call.get()}
    } else {
        raw_call
    };
    let flags_complete = quote! {assert(#pre.#vn==#raw_value);};
    let guard_source = if mutating {
        quote! {assert(#pre.#vn==#before.#vg());}
    } else {
        quote! {assert(#pre.#vn==#shared.fragment().#vg());}
    };
    let _ = (
        native,
        initial,
        raw_result,
        remainder,
        role_native,
        flags_complete,
    );
    Ok(quote! {
        proof fn #raw_fn(#(#params,)*#raw_signature #raw_consume #physical_param)#raw_return_type
            requires #raw_shape #raw_same #raw_consume_req #physical_req #(#raw_req,)*
            ensures #raw_post #role_return_req #raw_observation
        {
            #raw_input #joining
            let #before=#owned.fragment();#pack
            assert(Protocol #expr::#req(#before,#shared_fragment,#dep_value,#(#pn),*)) by{
                assert forall|#frame:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#shared_fragment),#frame)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#pn),*)&&#dep_value==State #expr::#deposited(#pre,#(#pn),*)&&State #expr::#owners(#pre,#before,#shared_fragment,#(#pn),*) by{
                    #guard_source #remove_hints
                }
            }
            #operation
            let(#pre,#post,#frame)=Protocol #expr::#witness(#before,#shared_fragment,#owned.fragment(),#dep_value,#wd,#(#pn),*);
            #guard_source
            #choose #bag_normalization #splitting #extract #restore #return_expr
        }
        pub proof fn #name(tracked &self,#(#params,)*#flags_in #public_consume #physical_param)#public_returns
            requires #flags_id,#(#public_req,)*#public_consume_req #physical_req
            ensures #public_post #public_result_req #public_observation
        {
            #flags_use self.metadata.agrees(&#owner.metadata);#consume_use
            #public_body
        }
    })
}
