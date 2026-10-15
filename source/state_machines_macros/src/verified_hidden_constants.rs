//! Actual agreement observations for scalar fields proved syntactically unchanged.
//! The user's State and transition bodies are preserved; no reachability invariant
//! is inferred from an initializer or supplied by a chosen completion.
use crate::ast::*;
use crate::parse_token_stream::SMBundle;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, ImplItem, Item, Visibility};

pub fn needed(sm: &SM) -> bool {
    sm.fields
        .iter()
        .any(|f| matches!(f.stype, ShardableType::NotTokenized(_)))
}

fn check_writes(stmt: &TransitionStmt, hidden: &HashSet<String>) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Update(_, field, _) | TransitionStmt::SubUpdate(_, field, _, _)
            if hidden.contains(&field.to_string()) =>
        {
            Err(Error::new(
                field.span(),
                "hidden agreement observation requires a never-updated not_tokenized field",
            ))
        }
        TransitionStmt::Block(_, children) | TransitionStmt::Split(_, _, children) => {
            for child in children {
                check_writes(child, hidden)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
    for token in tokens {
        match token {
            proc_macro2::TokenTree::Ident(ident) => {
                names.insert(ident.to_string().trim_start_matches("r#").to_string());
            }
            proc_macro2::TokenTree::Group(group) => reserve(group.stream(), names),
            _ => {}
        }
    }
}

fn reserve_statement(stmt: &TransitionStmt, names: &mut HashSet<String>) {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                reserve_statement(child, names);
            }
        }
        TransitionStmt::Initialize(_, field, e) | TransitionStmt::Update(_, field, e) => {
            reserve(quote! {#field #e}, names)
        }
        TransitionStmt::Require(_, e) | TransitionStmt::PostCondition(_, e) => {
            reserve(quote! {#e}, names)
        }
        TransitionStmt::Assert(_, e, proof) => {
            reserve(quote! {#e}, names);
            if let Some(proof) = &proof.proof {
                reserve(quote! {#proof}, names);
            }
        }
        TransitionStmt::SubUpdate(_, field, indices, e) => {
            reserve(quote! {#field #e}, names);
            for index in indices {
                match index {
                    SubIdx::Field(f) => reserve(quote! {#f}, names),
                    SubIdx::Idx(e) => reserve(quote! {#e}, names),
                }
            }
        }
        TransitionStmt::Split(_, kind, children) => {
            match &**kind {
                SplitKind::If(e) => reserve(quote! {#e}, names),
                SplitKind::Match(e, arms) => {
                    reserve(quote! {#e}, names);
                    for arm in arms {
                        let pat = &arm.pat;
                        reserve(quote! {#pat}, names);
                        if let Some((_, guard)) = &arm.guard {
                            reserve(quote! {#guard}, names);
                        }
                    }
                }
                SplitKind::Let(pat, ty, _, e) => reserve(quote! {#pat #ty #e}, names),
                SplitKind::Special(field, op, proof, pat) => {
                    reserve(quote! {#field #pat}, names);
                    if let Some(proof) = &proof.proof {
                        reserve(quote! {#proof}, names);
                    }
                    match &op.elt {
                        MonoidElt::OptionSome(e) => reserve(quote! {#e}, names),
                        MonoidElt::SingletonMultiset(e)
                        | MonoidElt::SingletonSet(e)
                        | MonoidElt::General(e) => reserve(quote! {#e}, names),
                        MonoidElt::SingletonKV(k, v) => reserve(quote! {#k #v}, names),
                        _ => {}
                    }
                }
            }
            for child in children {
                reserve_statement(child, names);
            }
        }
    }
}

fn hide_api(
    output: TokenStream,
    hidden: &HashSet<String>,
    observations: &HashMap<String, verus_syn::Ident>,
    initializers: &HashSet<String>,
) -> Result<TokenStream, Error> {
    let mut module: verus_syn::ItemMod = verus_syn::parse2(output)?;
    let (_, items) = module.content.as_mut().unwrap();
    for item in items {
        let Item::Macro(item) = item else { continue };
        if !item
            .mac
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "verus")
        {
            continue;
        }
        let mut file: verus_syn::File = verus_syn::parse2(item.mac.tokens.clone())?;
        let mut takes = HashSet::new();
        for field in hidden {
            takes.insert(format!("take_{field}"));
            takes.insert(format!("take_{field}_with_constants"));
        }
        file.items.retain(|item| match item {
            Item::Struct(item) => !hidden.contains(&item.ident.to_string()),
            Item::Impl(item) => !matches!(&*item.self_ty,
                verus_syn::Type::Path(ty) if ty.path.segments.last()
                    .is_some_and(|owner| hidden.contains(&owner.ident.to_string()))),
            _ => true,
        });
        for item in &mut file.items {
            let Item::Impl(item) = item else { continue };
            let verus_syn::Type::Path(ty) = &*item.self_ty else {
                continue;
            };
            let Some(owner) = ty.path.segments.last() else {
                continue;
            };
            for method in &mut item.items {
                let ImplItem::Fn(method) = method else {
                    continue;
                };
                let name = method.sig.ident.to_string();
                if owner.ident == "Instance" {
                    use verus_syn::visit_mut::VisitMut;
                    struct Rename<'a> {
                        observations: &'a HashMap<String, verus_syn::Ident>,
                        clone_result: bool,
                        initializer_result: bool,
                    }
                    impl VisitMut for Rename<'_> {
                        fn visit_expr_method_call_mut(
                            &mut self,
                            call: &mut verus_syn::ExprMethodCall,
                        ) {
                            // Only generated Instance receivers use this observation API.
                            // Calls on user transition arguments keep their original method names.
                            fn instance_receiver(
                                e: &verus_syn::Expr,
                                clone_result: bool,
                                initializer_result: bool,
                            ) -> bool {
                                match e {
                                    verus_syn::Expr::Path(p) => {
                                        p.path.is_ident("self")
                                            || (clone_result && p.path.is_ident("out"))
                                    }
                                    verus_syn::Expr::View(v) if initializer_result => {
                                        match &*v.expr {
                                            verus_syn::Expr::Field(f) => {
                                                matches!(f.member, verus_syn::Member::Unnamed(ref i) if i.index == 0)
                                                    && matches!(&*f.base, verus_syn::Expr::Path(p) if p.path.is_ident("out"))
                                            }
                                            _ => false,
                                        }
                                    }
                                    _ => false,
                                }
                            }
                            if instance_receiver(
                                &call.receiver,
                                self.clone_result,
                                self.initializer_result,
                            ) {
                                if let Some(name) = self.observations.get(&call.method.to_string())
                                {
                                    call.method = name.clone();
                                }
                            }
                            verus_syn::visit_mut::visit_expr_method_call_mut(self, call);
                        }
                    }
                    let mut rename = Rename {
                        observations,
                        clone_result: name == "clone",
                        initializer_result: initializers.contains(&name),
                    };
                    rename.visit_signature_mut(&mut method.sig);
                    rename.visit_block_mut(&mut method.block);
                    if let Some(observation) = observations.get(&name) {
                        method.sig.ident = observation.clone();
                        method.attrs.push(verus_syn::parse_quote!(#[doc(hidden)]));
                    }
                } else if owner.ident == "Protocol" && takes.contains(&name) {
                    method.vis = Visibility::Inherited;
                    method.sig.publish = verus_syn::Publish::Default;
                }
            }
        }
        item.mac.tokens = quote! {#file};
        return Ok(quote! {#module});
    }
    Err(Error::new(
        module.ident.span(),
        "hidden observation machine module not found",
    ))
}

pub fn output(mut bundle: SMBundle) -> Result<TokenStream, Error> {
    if let Some(field) = bundle
        .sm
        .fields
        .iter()
        .find(|field| field.name.to_string().starts_with("r#"))
    {
        return Err(Error::new(
            field.name.span(),
            "hidden agreement field facade does not support raw field names",
        ));
    }
    if let Some(tr) = bundle
        .sm
        .transitions
        .iter()
        .find(|tr| tr.name.to_string().starts_with("r#"))
    {
        return Err(Error::new(
            tr.name.span(),
            "hidden agreement field facade does not support raw transition names",
        ));
    }
    if !bundle
        .sm
        .fields
        .iter()
        .any(|f| matches!(f.stype, ShardableType::Variable(_)))
        || bundle.sm.fields.iter().any(|f| {
            !matches!(
                f.stype,
                ShardableType::Variable(_)
                    | ShardableType::Constant(_)
                    | ShardableType::NotTokenized(_)
            )
        })
    {
        return Err(Error::new(
            bundle.name.span(),
            "hidden unchanging observations currently require a scalar variable/constant model",
        ));
    }
    let hidden: HashSet<_> = bundle
        .sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::NotTokenized(_)))
        .map(|f| f.name.to_string())
        .collect();
    let mut occupied = HashSet::new();
    let fields = &bundle.sm.fields_named_ast;
    let generics = &bundle.sm.generics;
    reserve(quote! {#fields #generics}, &mut occupied);
    for tr in &bundle.sm.transitions {
        let name = &tr.name;
        reserve(quote! {#name}, &mut occupied);
        reserve_statement(&tr.body, &mut occupied);
        for parameter in &tr.params {
            let name = &parameter.name;
            let ty = &parameter.ty;
            reserve(quote! {#name #ty}, &mut occupied);
        }
    }
    for f in &bundle.normal_fns {
        reserve(quote! {#f}, &mut occupied);
    }
    for inv in &bundle.extras.invariants {
        let f = &inv.func;
        reserve(quote! {#f}, &mut occupied);
    }
    for lemma in &bundle.extras.lemmas {
        let f = &lemma.func;
        reserve(quote! {#f}, &mut occupied);
    }
    // Reserve all caller syntax before introducing hidden observation names.
    let mut observations = HashMap::new();
    let mut hidden_order: Vec<_> = hidden.iter().collect();
    hidden_order.sort();
    for field in hidden_order {
        let mut name = format!("__tsm_hidden_observation_{field}");
        while occupied.contains(&name) {
            name.push('_');
        }
        occupied.insert(name.clone());
        observations.insert(
            field.clone(),
            verus_syn::Ident::new(&name, proc_macro2::Span::mixed_site()),
        );
    }
    for tr in &bundle.sm.transitions {
        check_writes(&tr.body, &hidden)?;
    }
    // This is an internal resource representation, not a source-model edit.
    // Every noninitializer transition has been checked to retain these fields.
    for field in &mut bundle.sm.fields {
        if let ShardableType::NotTokenized(ty) = &field.stype {
            field.stype = ShardableType::Constant(ty.clone());
        }
    }
    let initializers = bundle
        .sm
        .transitions
        .iter()
        .filter(|t| t.kind == TransitionKind::Init)
        .map(|t| t.name.to_string())
        .collect();
    let api = crate::verified_field_tokens::output(&bundle.sm)?;
    let raw = crate::verified_general::output(bundle)?;
    let output = crate::verified_field_tokens::append(raw, api)?;
    hide_api(output, &hidden, &observations, &initializers)
}
