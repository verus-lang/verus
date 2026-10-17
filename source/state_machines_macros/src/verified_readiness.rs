//! Optional checked readiness over locally observed inputs. The existing
//! all-completion API remains available when a transition is not opted in.
use crate::ast::*;
use crate::parse_token_stream::{parse_result_to_smir, ParseResult, SMBundle};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;
use verus_syn::{punctuated::Punctuated, Error, Ident, Token, Type};

pub fn construct(mut parsed: ParseResult) -> Result<TokenStream, Error> {
    let mut selected = HashSet::new();
    let mut field_optin=false;
    let mut raw_optout=false;
    let mut generic=false;
    let mut names = vec![];
    let mut remaining = vec![];
    for attr in parsed.attrs {
        let attribute_name = if attr.path().leading_colon.is_none() && attr.path().segments.len() == 1 {
            attr.path().segments[0].ident.to_string().trim_start_matches("r#").to_string()
        } else {
            String::new()
        };
        if attribute_name == "verified_field_tokens" {
            if field_optin {return Err(Error::new(attr.path().segments[0].ident.span(),"duplicate field facade attribute"));}
            if !matches!(attr.meta,verus_syn::Meta::Path(_)){return Err(Error::new(attr.path().segments[0].ident.span(),"field facade attribute takes no arguments"));}
            if raw_optout {return Err(Error::new(attr.path().segments[0].ident.span(),"field facade and raw token attributes cannot be combined"));}
            field_optin=true;
        } else if attribute_name == "verified_generic_tokens" {
            if field_optin || raw_optout || generic {return Err(Error::new(attr.path().segments[0].ident.span(),"generic field tokens cannot be combined with another token attribute"));}
            if !matches!(attr.meta,verus_syn::Meta::Path(_)){return Err(Error::new(attr.path().segments[0].ident.span(),"generic field tokens attribute takes no arguments"));}
            generic=true;
            raw_optout=true;
        } else if attribute_name == "verified_raw_tokens" {
            if raw_optout {return Err(Error::new(attr.path().segments[0].ident.span(),"duplicate raw token attribute"));}
            if !matches!(attr.meta,verus_syn::Meta::Path(_)){return Err(Error::new(attr.path().segments[0].ident.span(),"raw token attribute takes no arguments"));}
            if field_optin {return Err(Error::new(attr.path().segments[0].ident.span(),"field facade and raw token attributes cannot be combined"));}
            raw_optout=true;
        } else if attr.path().is_ident("verified_local_ready") {
            let list = attr.parse_args_with(Punctuated::<Ident, Token![,]>::parse_terminated)?;
            for name in list {
                if !selected.insert(name.to_string()) {
                    return Err(Error::new(name.span(), "duplicate local-ready transition"));
                }
                names.push(name);
            }
        } else {
            remaining.push(attr);
        }
    }
    // Nominal field APIs are the default. The explicit raw marker selects
    // exactly the existing lower-level checked resource path. Unsupported
    // nominal profiles still return their original facade diagnostics.
    let typed = !raw_optout;
    parsed.attrs = remaining;
    let mut bundle = parse_result_to_smir(parsed, true)?;
    crate::lemmas::check_lemmas(&bundle)?;
    if typed && crate::verified_field_nondet::needed(&bundle.sm) {
        if !selected.is_empty() {
            return Err(Error::new(bundle.name.span(), "mutable unowned observations do not combine with physical readiness"));
        }
        validate_api_names(&bundle,&selected)?;
        let api=crate::verified_field_nondet::output(&bundle.sm)?;
        let output=crate::verified_general::output(bundle)?;
        return crate::verified_field_tokens::append(output,api);
    }
    if typed && crate::verified_hidden_constants::needed(&bundle.sm) {
        if !selected.is_empty() {
            return Err(Error::new(bundle.name.span(), "hidden unchanging observations do not yet combine with selected physical readiness"));
        }
        return crate::verified_hidden_constants::output(bundle);
    }
    if selected.is_empty() {
        if typed && crate::verified_storage_owned_imap::needed(&bundle.sm) {
            validate_api_names(&bundle,&selected)?;
            let api=crate::verified_storage_owned_imap::output(&bundle)?;
            let output=crate::verified_model::output(bundle)?;
            return crate::verified_field_tokens::append(output,api);
        }
        if typed && crate::verified_field_storage_refutable::needed(&bundle.sm) {
            validate_api_names(&bundle,&selected)?;
            let api=crate::verified_field_storage_refutable::output(&bundle.sm)?;
            let output=crate::verified_general::output(bundle)?;
            return crate::verified_field_tokens::append(output,api);
        }
        if typed && crate::verified_field_storage_bindings::needed(&bundle.sm) {
            validate_api_names(&bundle,&selected)?;
            let api=crate::verified_field_storage_bindings::output(&bundle.sm)?;
            let output=crate::verified_general::output(bundle)?;
            return crate::verified_field_tokens::append(output,api);
        }

        if typed && crate::verified_field_storage_map_pair::needed(&bundle.sm) {
            validate_api_names(&bundle,&selected)?;
            let api=crate::verified_field_storage_map_pair::output(&bundle.sm,&selected)?;
            let output=crate::verified_general::output(bundle)?;
            return crate::verified_field_tokens::append(output,api);
        }
        if typed && bundle.sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::StorageMap(..))).count() == 1
            && bundle.sm.fields.iter().filter(|f| matches!(f.stype, ShardableType::StorageOption(_))).count() == 1
            && bundle.sm.fields.iter().all(|f| matches!(f.stype,
                ShardableType::StorageMap(..) | ShardableType::StorageOption(_)
                | ShardableType::Constant(_) | ShardableType::Variable(_)
                | ShardableType::Count | ShardableType::Bool | ShardableType::PersistentBool
                | ShardableType::Option(_) | ShardableType::PersistentOption(_)
                | ShardableType::Set(_) | ShardableType::PersistentSet(_)
                | ShardableType::Multiset(_) | ShardableType::PersistentMap(..))) {
            validate_api_names(&bundle, &selected)?;
            let api = crate::verified_field_storage_wide::output(&bundle.sm, &selected)?;
            let output = crate::verified_general::output(bundle)?;
            return crate::verified_field_tokens::append(output, api);
        }
        if generic {
            if !names.is_empty() {
                return Err(Error::new(bundle.name.span(), "generic field tokens do not combine with selected physical readiness"));
            }
            // Initial requirements over a storage map become named open spec
            // functions (as for the field facades), which keeps the raw
            // initializer's execution proof stable; clients see equal terms.
            if bundle.sm.fields.iter().any(|field| matches!(field.stype, ShardableType::StorageMap(..))) {
                crate::verified_field_storage_map::normalize_initial_requirements(&mut bundle)?;
            }
            let api=crate::verified_generic_tokens::output(&bundle)?;
            let output=crate::verified_general::output(bundle)?;
            return crate::verified_generic_tokens::append_tokens(output,api);
        }
        let api=if typed {Some(crate::verified_field_tokens::output(&bundle.sm)?)}else{None};
        let output=if typed && bundle.sm.fields.len()==1 && matches!(bundle.sm.fields[0].stype,ShardableType::Count) {
            crate::verified_general::output(bundle)?
        }else{crate::verified_tokens::output(bundle)?};
        return if let Some(api)=api {crate::verified_field_tokens::append(output,api)}else{Ok(output)};
    }
    for name in names {
        let Some(tr) = bundle.sm.transitions.iter().find(|tr| tr.name == name) else {
            return Err(Error::new(name.span(), "unknown local-ready transition"));
        };
        if tr.kind != TransitionKind::Transition {
            return Err(Error::new(
                name.span(),
                "local-ready requires a mutating transition",
            ));
        }
    }
    if typed && bundle.sm.fields.iter().any(|field| matches!(field.stype, ShardableType::StorageMap(..))) {
        crate::verified_field_storage_map::normalize_initial_requirements(&mut bundle)?;
    }
    if typed {
        if !bundle.sm.fields.iter().any(|field| field.stype.is_storage()) {
            return Err(Error::new(bundle.name.span(),"field facade cannot yet combine with selected physical readiness"));
        }
        let variables = bundle.sm.fields.iter()
            .filter(|field| matches!(field.stype, ShardableType::Variable(_))).count();
        let api = if crate::verified_field_storage_general_bulk::needed(&bundle.sm) {crate::verified_field_storage_general_bulk::output(&bundle.sm,&selected)?} else if crate::verified_field_storage_distributed_rwlock::needed(&bundle.sm) {crate::verified_field_storage_distributed_rwlock::output(&bundle.sm,&selected)?} else if crate::verified_field_storage_map_pair::needed(&bundle.sm) {crate::verified_field_storage_map_pair::output(&bundle.sm,&selected)?} else if crate::verified_field_storage_rwlock::needed(&bundle.sm) {crate::verified_field_storage_rwlock::output(&bundle.sm,&selected)?} else if crate::verified_field_storage_logical_map::needed(&bundle.sm) { crate::verified_field_storage_logical_map::output(&bundle.sm, &selected)? } else if bundle.sm.fields.iter().filter(|field|field.stype.is_storage()).count()>1 {crate::verified_field_storage_multiple::output(&bundle.sm,&selected)?} else if variables > 1 && bundle.sm.fields.iter().any(|field| matches!(field.stype,ShardableType::Count|ShardableType::Set(_)|ShardableType::Option(_))) {
            crate::verified_field_storage_heterogeneous::output(&bundle.sm,&selected)?
        } else if bundle.sm.fields.iter().any(|field| matches!(field.stype,ShardableType::Multiset(_))) && bundle.sm.fields.iter().any(|field| matches!(field.stype,ShardableType::Bool)) {
            crate::verified_field_storage_borrows::output(&bundle.sm,&selected)?
        } else if bundle.sm.fields.iter().any(|field| matches!(field.stype,ShardableType::Multiset(_))) {
            if crate::verified_field_storage_counting::needed(&bundle.sm){crate::verified_field_storage_counting::output(&bundle.sm,&selected)?}else{crate::verified_field_storage_readers::output(&bundle.sm,&selected)?}
        } else if bundle.sm.fields.iter().any(|field| matches!(field.stype, ShardableType::StorageMap(..))) {
            crate::verified_field_storage_map::output(&bundle.sm, &selected)?
        } else if variables > 1 {
            crate::verified_field_storage_grouped::output(&bundle.sm, &selected)?
        } else {
            crate::verified_field_storage::output(&bundle.sm, &selected)?
        };
        validate_api_names(&bundle, &selected)?;
        let output = crate::verified_general::output_with_ready(bundle, &selected)?;
        return crate::verified_field_tokens::append(output, api);
    }
    validate_api_names(&bundle, &selected)?;
    crate::verified_general::output_with_ready(bundle, &selected)
}

fn validate_api_names(bundle: &SMBundle, selected: &HashSet<String>) -> Result<(), Error> {
    let sm = &bundle.sm;
    let mut state = HashSet::from(["invariant".to_string(), "__storage".to_string()]);
    let mut protocol = HashSet::from(["__observed".to_string()]);
    for f in &bundle.normal_fns {
        state.insert(f.sig.ident.to_string());
    }
    for inv in &bundle.extras.invariants {
        state.insert(inv.func.sig.ident.to_string());
    }
    for lemma in &bundle.extras.lemmas {
        state.insert(lemma.func.sig.ident.to_string());
    }
    let constants = sm
        .fields
        .iter()
        .any(|f| matches!(f.stype, ShardableType::Constant(_)));
    for field in &sm.fields {
        if field.stype.is_storage() || matches!(field.stype, ShardableType::NotTokenized(_)) {
            continue;
        }
        protocol.insert(format!("take_{}", field.name));
        if constants && !matches!(field.stype, ShardableType::Constant(_)) {
            protocol.insert(format!("take_{}_with_constants", field.name));
        }
        if matches!(field.stype, ShardableType::Count) {
            protocol.insert(format!("split_{}", field.name));
        }
    }
    for tr in &sm.transitions {
        protocol.insert(tr.name.to_string());
        if tr.kind != TransitionKind::Init {
            for suffix in [
                "_owned_post",
                "_requires",
                "_outputs",
                "_witness",
                "_frame",
                "_with_shared",
            ] {
                protocol.insert(format!("{}{suffix}", tr.name));
            }
        } else {
            state.insert(tr.name.to_string());
        }
        for suffix in [
            "_strong",
            "_enabled",
            "_safety",
            "_execute",
            "_owners_enabled",
            "_deposited",
            "_guarded",
        ] {
            state.insert(format!("{}{suffix}", tr.name));
        }
        for field in &sm.fields {
            state.insert(format!("{}_{}_effect", tr.name, field.name));
            state.insert(format!("{}_{}_effect_owned", tr.name, field.name));
            protocol.insert(format!("{}_{}_effect_frame", tr.name, field.name));
        }
    }
    for tr in sm
        .transitions
        .iter()
        .filter(|tr| selected.contains(&tr.name.to_string()))
    {
        for suffix in [
            "_local_requires",
            "_local_ready",
            "_local",
            "_local_with_shared",
            "_observed",
        ] {
            if !protocol.insert(format!("{}{suffix}", tr.name)) {
                return Err(Error::new(
                    tr.name.span(),
                    "local-ready API name conflicts with an existing generated method",
                ));
            }
        }
        for suffix in ["_declared_requires", "_local_deposited"] {
            if !state.insert(format!("{}{suffix}", tr.name)) {
                return Err(Error::new(
                    tr.name.span(),
                    "local-ready State predicate conflicts with an existing method",
                ));
            }
        }
    }
    Ok(())
}

// General collection operands create a substantial sequential ownership term.
// Retain a named specification call at each frame/ready boundary instead of
// duplicating that term through verifier inline expansion. This changes no
// precondition: the explicit assertions below instantiate the same predicate.
pub(crate) fn inline_ownership(sm: &SM, tr: &Transition) -> bool {
    fn general_collection(stmt: &TransitionStmt, sm: &SM) -> bool {
        match stmt {
            TransitionStmt::Block(_, children) => children.iter().any(|child| general_collection(child, sm)),
            TransitionStmt::Split(_, split, children) => {
                let here = match &**split {
                    SplitKind::Special(field, op, _, _) => matches!(op.elt, MonoidElt::General(_))
                        && sm.fields.iter().any(|f| f.name == *field
                            && matches!(f.stype, ShardableType::Map(..) | ShardableType::IMap(..) | ShardableType::Multiset(_))),
                    _ => false,
                };
                here || children.iter().any(|child| general_collection(child, sm))
            }
            _ => false,
        }
    }
    !general_collection(&tr.body, sm)
}

fn contains_require(s: &TransitionStmt) -> bool {
    match s {
        TransitionStmt::Require(..) => true,
        TransitionStmt::Block(_, xs) | TransitionStmt::Split(_, _, xs) => {
            xs.iter().any(contains_require)
        }
        _ => false,
    }
}

fn declared_requires(s: &TransitionStmt) -> Result<TokenStream, Error> {
    if !contains_require(s) {
        return Ok(quote! {true});
    }
    match s {
        TransitionStmt::Require(_, expr) => Ok(quote! {#expr}),
        TransitionStmt::Block(_, xs) => {
            let xs = xs
                .iter()
                .map(declared_requires)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(quote! {true #(&& (#xs))*})
        }
        TransitionStmt::Split(span, kind, xs) => {
            let bodies = xs
                .iter()
                .map(declared_requires)
                .collect::<Result<Vec<_>, _>>()?;
            match &**kind {
                SplitKind::Let(pat, ty, LetKind::Normal, expr) => {
                    let ty = ty.as_ref().map(|ty| quote! {: #ty});
                    let body = &bodies[0];
                    Ok(quote! {{let #pat #ty = #expr; #body}})
                }
                SplitKind::If(expr) => {
                    let yes = &bodies[0];
                    let no = &bodies[1];
                    Ok(quote! {if #expr {#yes} else {#no}})
                }
                SplitKind::Match(expr, arms) => {
                    let arms: Vec<_> = arms
                        .iter()
                        .zip(bodies)
                        .map(|(arm, body)| {
                            let pat = &arm.pat;
                            let guard = arm.guard.as_ref().map(|(_, expr)| quote! {if #expr});
                            quote! {#pat #guard => {#body}}
                        })
                        .collect();
                    Ok(quote! {match #expr {#(#arms),*}})
                }
                SplitKind::Special(_, _, _, None) => Ok(quote! {true #(&& (#bodies))*}),
                _ => Err(Error::new(
                    *span,
                    "local-ready cannot observe a hidden or special-bound require",
                )),
            }
        }
        _ => Ok(quote! {true}),
    }
}

pub fn declared_api(
    tr: &Transition,
    st: &TokenStream,
    params: &[TokenStream],
) -> Result<TokenStream, Error> {
    let declared = format_ident!("{}_declared_requires", tr.name);
    let expression = declared_requires(&tr.body)?;
    Ok(
        quote! {#[verifier::inline] pub open spec fn #declared(pre:#st,#(#params),*)->bool {#expression}},
    )
}

pub struct Context<'a> {
    pub sm: &'a SM,
    pub tr: &'a Transition,
    pub st: &'a TokenStream,
    pub se: &'a TokenStream,
    pub ft: &'a TokenStream,
    pub tt: &'a TokenStream,
    pub result: &'a TokenStream,
    pub result_expr: &'a TokenStream,
    pub params: &'a [TokenStream],
    pub pn: &'a [&'a Ident],
    pub owned: &'a [TokenStream],
    pub observed: &'a [TokenStream],
    pub reads: &'a [&'a Ident],
    pub key: &'a Type,
    pub val: &'a Type,
    pub deposits: bool,
    pub withdraws: bool,
    pub paired: bool,
}

fn fresh(sm:&SM,tr:&Transition,stem:&str)->Ident {
    fn reserve(tokens:TokenStream,names:&mut HashSet<String>){for token in tokens{match token{
        proc_macro2::TokenTree::Ident(n)=>{names.insert(n.to_string());},
        proc_macro2::TokenTree::Group(g)=>reserve(g.stream(),names),_=>{},
    }}}
    fn visit(stmt:&TransitionStmt,names:&mut HashSet<String>){match stmt{
        TransitionStmt::Block(_,children)=>for child in children{visit(child,names)},
        TransitionStmt::Initialize(_,_,e)|TransitionStmt::Update(_,_,e)|TransitionStmt::Require(_,e)|TransitionStmt::PostCondition(_,e)=>reserve(quote!{#e},names),
        TransitionStmt::Assert(_,e,proof)=>{reserve(quote!{#e},names);if let Some(block)=&proof.proof{reserve(quote!{#block},names);}},
        TransitionStmt::SubUpdate(_,_,indices,e)=>{reserve(quote!{#e},names);for index in indices{if let SubIdx::Idx(e)=index{reserve(quote!{#e},names);}}},
        TransitionStmt::Split(_,split,children)=>{
            match &**split{
                SplitKind::If(e)=>reserve(quote!{#e},names),
                SplitKind::Match(e,arms)=>{reserve(quote!{#e},names);for arm in arms{let pat=&arm.pat;reserve(quote!{#pat},names);if let Some((_,guard))=&arm.guard{reserve(quote!{#guard},names);}}},
                SplitKind::Let(pat,ty,_,e)=>reserve(quote!{#pat #ty #e},names),
                SplitKind::Special(_,op,proof,pat)=>{
                    reserve(quote!{#pat},names);
                    if let Some(block)=&proof.proof{reserve(quote!{#block},names);}
                    match &op.elt{
                        MonoidElt::OptionSome(Some(e))|MonoidElt::SingletonMultiset(e)|MonoidElt::SingletonSet(e)|MonoidElt::General(e)=>reserve(quote!{#e},names),
                        MonoidElt::SingletonKV(key,value)=>reserve(quote!{#key #value},names),_=>{},
                    }
                },
            }
            for child in children{visit(child,names)}
        },
    }}
    let mut unavailable:HashSet<_>=tr.params.iter().map(|p|p.name.to_string()).chain(sm.fields.iter().map(|f|f.name.to_string())).collect();
    if let Some(g)=&sm.generics{reserve(quote!{#g},&mut unavailable);}
    visit(&tr.body,&mut unavailable);
    for suffix in 0usize..{let candidate=format!("__tsm_{stem}_{suffix}");if !unavailable.contains(&candidate){return Ident::new(&candidate,proc_macro2::Span::mixed_site());}}
    unreachable!()
}

// A singleton exclusive Set owner implies actual membership in every compatible
// completion. Explicit key instantiation and pointwise composition avoid relying
// on solver triggers to lift a Remove ownership requirement through the frame.
fn singleton_set_remove_hints(tr:&Transition,observation:&Ident,completion:&Ident,
    completion_frame:&Ident,ft:&TokenStream,se:&TokenStream,owners:&Ident,pn:&[&Ident])
    ->Vec<TokenStream>
{
    use std::collections::HashSet;
    fn collect(stmt:&TransitionStmt,changed:&mut HashSet<String>,bound:&mut HashSet<String>,
        result:&mut Vec<(Ident,verus_syn::Expr)>) {
        match stmt {
            TransitionStmt::Block(_,children)=>for child in children {collect(child,changed,bound,result)},
            TransitionStmt::Update(_,field,_)|TransitionStmt::Initialize(_,field,_)=>{changed.insert(field.to_string());},
            TransitionStmt::Split(_,split,children)=>match &**split {
                SplitKind::Special(field,operation,_,pattern)=>{
                    if matches!(operation.stmt,MonoidStmtType::Remove)&&!changed.contains("*")&&!changed.contains(&field.to_string()) {
                        if let MonoidElt::SingletonSet(key)=&operation.elt {
                            struct Names<'a>(&'a mut HashSet<String>);
                            impl<'ast> verus_syn::visit::Visit<'ast> for Names<'_> {
                                fn visit_ident(&mut self,name:&'ast Ident) {self.0.insert(name.to_string());}
                            }
                            use verus_syn::visit::Visit;
                            let mut names=HashSet::new();Names(&mut names).visit_expr(key);
                            if names.is_disjoint(bound) {result.push((field.clone(),key.clone()));}
                        }
                    }
                    if matches!(operation.stmt,MonoidStmtType::Remove|MonoidStmtType::Add(_)) {changed.insert(field.to_string());}
                    if pattern.is_some() {return;}
                    for child in children {collect(child,changed,bound,result)}
                },
                SplitKind::Let(pattern,_,_,_)=>{
                    struct Names<'a>(&'a mut HashSet<String>);
                    impl<'ast> verus_syn::visit::Visit<'ast> for Names<'_> {
                        fn visit_ident(&mut self,name:&'ast Ident) {self.0.insert(name.to_string());}
                    }
                    use verus_syn::visit::Visit;
                    Names(bound).visit_pat(pattern);
                    for child in children {collect(child,changed,bound,result)}
                },
                // Hints are unconditional. Branch-dependent resource membership
                // must continue to be proved by the existing general theorem.
                _=>{changed.insert("*".to_string());},
            },
            _=>{},
        }
    }
    let mut removals=Vec::new();collect(&tr.body,&mut HashSet::new(),&mut HashSet::new(),&mut removals);
    removals.into_iter().map(|(field,mut key)| {
        // Replace only the state root; source parameter and binder names retain
        // their spelling. The completion agrees with every ordinary read.
        struct PreRoot<'a>(&'a Ident);
        impl verus_syn::visit_mut::VisitMut for PreRoot<'_> {
            fn visit_expr_path_mut(&mut self,node:&mut verus_syn::ExprPath) {
                if node.path.is_ident("pre") {let name=self.0;node.path=verus_syn::parse_quote!{#name};}
            }
        }
        use verus_syn::visit_mut::VisitMut;
        PreRoot(observation).visit_expr_mut(&mut key);
        fn fresh_key_name(tr:&Transition,stem:&str,key:&verus_syn::Expr)->Ident {
            fn reserve(tokens:TokenStream,names:&mut HashSet<String>) {
                for token in tokens {match token {
                    proc_macro2::TokenTree::Ident(name)=>{names.insert(name.to_string());},
                    proc_macro2::TokenTree::Group(group)=>reserve(group.stream(),names),_=>{},
                }}
            }
            let mut unavailable:HashSet<String>=tr.params.iter().map(|p|p.name.to_string()).collect();
            reserve(quote!{#key},&mut unavailable);
            for suffix in 0usize.. {
                let candidate=format!("__tsm_{stem}_{suffix}");
                if !unavailable.contains(&candidate){return Ident::new(&candidate,proc_macro2::Span::mixed_site());}
            }
            unreachable!()
        }
        let frame=fresh_key_name(tr,&format!("set_inclusion_frame_{field}"),&key);
        let membership_key=fresh_key_name(tr,"set_inclusion_key",&key);
        quote! {
            assert(#se::#owners(#observation,owned,h,#(#pn),*));
            assert(ISet::empty().insert(#key).contains(#key));
            assert forall|#membership_key|ISet::empty().insert(#key).contains(#membership_key)
                implies #[trigger] owned.#field.at(#membership_key)==Some(ExclusiveRA::Exclusive(())) by {};
            assert(owned.#field.at(#key)==Some(ExclusiveRA::Exclusive(())));
            <#ft>::associative(owned,h,#completion_frame);
            let #frame=::vstd::resource::tsm_collections::SetFragment::op(h.#field,#completion_frame.#field);
            assert(Option::<ExclusiveRA<()>>::op(owned.#field.at(#key),#frame.at(#key))==Self::embed(#completion).#field.at(#key));
            assert(Self::embed(#completion).#field.at(#key)==if #completion.#field.contains(#key){Some(ExclusiveRA::Exclusive(()))}else{None});
            assert(#frame.at(#key) is None);
            assert(#completion.#field.contains(#key));
        }
    }).collect()
}
// Only unconditional first removals are eligible. Every emitted hint is checked
// from the declared CURRENT local ownership and the actual completion equality.
fn singleton_map_remove_hints(sm:&SM,tr:&Transition,observation:&Ident,completion:&Ident,
    completion_frame:&Ident,ft:&TokenStream,se:&TokenStream,owners:&Ident,pn:&[&Ident])->Vec<TokenStream>{
    fn collect(stmt:&TransitionStmt,changed:&mut HashSet<String>,bound:&mut HashSet<String>,result:&mut Vec<(Ident,verus_syn::Expr,verus_syn::Expr)>){
        match stmt{
            TransitionStmt::Block(_,children)=>for child in children{collect(child,changed,bound,result)},
            TransitionStmt::Update(_,field,_)|TransitionStmt::Initialize(_,field,_)=>{changed.insert(field.to_string());},
            TransitionStmt::Split(_,split,children)=>match &**split{
                SplitKind::Special(field,operation,_,pattern)=>{
                    if operation.is_remove()&&!changed.contains("*")&&!changed.contains(&field.to_string()){
                        if let MonoidElt::SingletonKV(key,Some(value))=&operation.elt{
                            struct Names<'a>(&'a mut HashSet<String>);
                            impl<'ast> verus_syn::visit::Visit<'ast> for Names<'_>{fn visit_ident(&mut self,name:&'ast Ident){self.0.insert(name.to_string());}}
                            use verus_syn::visit::Visit;
                            let mut names=HashSet::new();Names(&mut names).visit_expr(key);Names(&mut names).visit_expr(value);
                            if names.is_disjoint(bound){result.push((field.clone(),key.clone(),*value.clone()));}
                        }
                    }
                    if operation.is_remove()||operation.is_add(){changed.insert(field.to_string());}
                    if pattern.is_some(){return;}
                    for child in children{collect(child,changed,bound,result)}
                },
                SplitKind::Let(pattern,_,_,_)=>{
                    struct Names<'a>(&'a mut HashSet<String>);
                    impl<'ast> verus_syn::visit::Visit<'ast> for Names<'_>{fn visit_ident(&mut self,name:&'ast Ident){self.0.insert(name.to_string());}}
                    use verus_syn::visit::Visit;Names(bound).visit_pat(pattern);
                    for child in children{collect(child,changed,bound,result)}
                },
                _=>{changed.insert("*".to_string());},
            },
            _=>{},
        }
    }
    let mut removals=vec![];collect(&tr.body,&mut HashSet::new(),&mut HashSet::new(),&mut removals);
    removals.into_iter().filter_map(|(field,mut key,mut value)|{
        let actual=sm.fields.iter().find(|f|f.name==field)?;
        let finite=match actual.stype{ShardableType::Map(..)=>true,ShardableType::IMap(..)=>false,_=>return None};
        struct PreRoot<'a>(&'a Ident);
        impl verus_syn::visit_mut::VisitMut for PreRoot<'_>{fn visit_expr_path_mut(&mut self,node:&mut verus_syn::ExprPath){if node.path.is_ident("pre"){let name=self.0;node.path=verus_syn::parse_quote!{#name};}}}
        use verus_syn::visit_mut::VisitMut;PreRoot(observation).visit_expr_mut(&mut key);PreRoot(observation).visit_expr_mut(&mut value);
        fn reserve(tokens:TokenStream,names:&mut HashSet<String>){for token in tokens{match token{proc_macro2::TokenTree::Ident(n)=>{names.insert(n.to_string());},proc_macro2::TokenTree::Group(g)=>reserve(g.stream(),names),_=>{}}}}
        let mut names:HashSet<_>=tr.params.iter().map(|p|p.name.to_string()).collect();reserve(quote!{#key #value},&mut names);if let Some(g)=&sm.generics{reserve(quote!{#g},&mut names);}
        let base=format!("__tsm_map_inclusion_frame_{field}");let mut candidate=base;while names.contains(&candidate){candidate.push('_');}let frame=Ident::new(&candidate,proc_macro2::Span::mixed_site());
        let native=if finite{quote!{#completion.#field.to_imap()}}else{quote!{#completion.#field}};
        Some(quote!{
            assert(#se::#owners(#observation,owned,h,#(#pn),*));
            assert(owned.#field.at(#key)==Some(ExclusiveRA::Exclusive(#value)));
            <#ft>::associative(owned,h,#completion_frame);
            let #frame=::vstd::resource::tsm_collections::MapFragment::op(h.#field,#completion_frame.#field);
            ::vstd::resource::tsm_collections::map_owned_frame(owned.#field,#frame,#native,#key,#value);
        })
    }).collect()
}

pub fn api(c: Context<'_>) -> Result<TokenStream, Error> {
    let Context {
        sm,
        tr,
        st,
        se,
        ft,
        tt,
        result,
        result_expr,
        params,
        pn,
        owned,
        observed,
        reads,
        key,
        val,
        deposits,
        withdraws,
        paired,
    } = c;
    let n = &tr.name;
    let local_req = format_ident!("{}_local_requires", n);
    let ready = format_ident!("{}_local_ready", n);
    let local = format_ident!("{}_local", n);
    let local_shared = format_ident!("{}_local_with_shared", n);
    let observed_op = format_ident!("{}_observed", n);
    let req = format_ident!("{}_requires", n);
    let enabled = format_ident!("{}_enabled", n);
    let owners = format_ident!("{}_owners_enabled", n);
    let declared = format_ident!("{}_declared_requires", n);
    let deposited = format_ident!("{}_deposited", n);
    let local_deposited = format_ident!("{}_local_deposited", n);
    let output = format_ident!("{}_outputs", n);
    let witness = format_ident!("{}_witness", n);
    let strong = format_ident!("{}_strong", n);
    let owned_post = format_ident!("{}_owned_post", n);
    let shared_op = format_ident!("{}_with_shared", n);

    let local_state = fresh(sm,tr, "local_state");
    let observation = fresh(sm,tr, "observed_state");
    let completion_frame = fresh(sm,tr, "completion_frame");
    let full_state = fresh(sm,tr, "completion_state");
    let certificate = fresh(sm,tr, "certificate");
    let initial = fresh(sm,tr, "initial_fragment");
    let physical_deposit = fresh(sm,tr, "physical_deposit");
    let next = fresh(sm,tr, "next_token");
    let returned_map = fresh(sm,tr, "withdrawn_map");
    let before = fresh(sm,tr, "before_state");
    let after = fresh(sm,tr, "after_state");
    let witness_frame = fresh(sm,tr, "witness_frame");
    let map = quote! {IMap<#key, #val>};
    let dep_param = if deposits {
        quote! {tracked deposit:#map,}
    } else {
        quote! {}
    };
    let dep_arg = if deposits {
        quote! {deposit,}
    } else {
        quote! {}
    };
    let dep_value = if deposits {
        quote! {deposit}
    } else {
        quote! {IMap::<#key,#val>::empty()}
    };
    let ret = if withdraws {
        quote! {tracked out:(#tt,#map)}
    } else {
        quote! {tracked out:#tt}
    };
    let call = if withdraws {
        quote! {let tracked (#next,#returned_map)=Self::#local(owned,#dep_arg #(#pn),*);}
    } else {
        quote! {let tracked #next=Self::#local(owned,#dep_arg #(#pn),*);let tracked #returned_map:#map=IMap::tracked_empty();}
    };
    let out = if withdraws {
        quote! {out.0}
    } else {
        quote! {out}
    };
    let wd = if withdraws {
        quote! {out.1}
    } else {
        quote! {IMap::empty()}
    };
    let wd_shape = if withdraws {
        quote! {}
    } else {
        quote! {,#certificate.withdrawn==IMap::empty()}
    };
    let physical = if paired {
        quote! {#dep_value==#se::#deposited(#certificate.before,#(#pn),*),
        #certificate.before.__storage().dom().disjoint(#dep_value.dom()),
        #certificate.after.__storage().submap_of(#certificate.before.__storage().union_prefer_right(#dep_value)),}
    } else {
        quote! {#dep_value==#certificate.after.__storage().remove_keys(#certificate.before.__storage().dom()),}
    };
    let set_hints=singleton_set_remove_hints(tr,&observation,&full_state,&completion_frame,ft,se,&owners,pn);
    let map_hints=singleton_map_remove_hints(sm,tr,&observation,&full_state,&completion_frame,ft,se,&owners,pn);
    Ok(quote! {
        /// Local observations suffice only because the following theorem checks every completion.
        #[verifier::inline]
        pub open spec fn #local_req(owned:#ft,h:#ft,deposit:#map,#(#params),*)->bool {
            true #(&& #owned)* #(&& #observed)* && {
                let #local_state=Self::__observed(<#ft>::op(owned,h));
                #se::#declared(#local_state,#(#pn),*) && #se::#owners(#local_state,owned,h,#(#pn),*)
                    && deposit==#se::#local_deposited(#local_state,#(#pn),*)
            }
        }
        pub proof fn #ready(owned:#ft,h:#ft,deposit:#map,#(#params),*)
            requires Self::#local_req(owned,h,deposit,#(#pn),*)
            ensures Self::#req(owned,h,deposit,#(#pn),*)
        {
            let #observation=Self::__observed(<#ft>::op(owned,h));
            assert forall|#completion_frame:#ft,#full_state:#st|#full_state.invariant()
                &&<#ft>::op(<#ft>::op(owned,h),#completion_frame)==Self::embed(#full_state)
                implies #se::#enabled(#full_state,#(#pn),*)
                    &&#se::#deposited(#full_state,#(#pn),*)==deposit
                    &&#se::#owners(#full_state,owned,h,#(#pn),*) by {
                #(assert(#full_state.#reads==#observation.#reads);)*
                assert(#se::#declared(#full_state,#(#pn),*));
                assert(#se::#owners(#full_state,owned,h,#(#pn),*));
                #(#set_hints)*
                #(#map_hints)*
                assert(::vstd::prelude::ext_equal(#se::#local_deposited(#full_state,#(#pn),*),#se::#deposited(#full_state,#(#pn),*)));
            }
        }
        pub proof fn #local_shared(tracked owned:#tt,tracked shared:&#tt,#dep_param #(#params),*)->(#ret)
            requires owned.loc()==shared.loc(),Self::#local_req(owned.fragment(),shared.fragment(),#dep_value,#(#pn),*)
            ensures #out.loc()==owned.loc(),Self::#output(owned.fragment(),shared.fragment(),#out.fragment(),#dep_value,#wd,#(#pn),*)
        {
            Self::#ready(owned.fragment(),shared.fragment(),#dep_value,#(#pn),*);
            Self::#shared_op(owned,shared,#dep_arg #(#pn),*)
        }
        pub proof fn #local(tracked owned:#tt,#dep_param #(#params),*)->(#ret)
            requires Self::#local_req(owned.fragment(),<#ft>::unit(),#dep_value,#(#pn),*)
            ensures #out.loc()==owned.loc(),Self::#output(owned.fragment(),<#ft>::unit(),#out.fragment(),#dep_value,#wd,#(#pn),*)
        {
            Self::#ready(owned.fragment(),<#ft>::unit(),#dep_value,#(#pn),*);
            Self::#n(owned,#dep_arg #(#pn),*)
        }
        /// Returned states describe a compatible completion, not a distinguished hidden history.
        pub proof fn #observed_op(tracked owned:#tt,#dep_param #(#params),*)->(tracked #certificate:#result)
            requires Self::#local_req(owned.fragment(),<#ft>::unit(),#dep_value,#(#pn),*)
            ensures #certificate.token.loc()==owned.loc(),#certificate.before.invariant(),#certificate.after.invariant(),
                <#ft>::op(<#ft>::op(owned.fragment(),<#ft>::unit()),#certificate.frame)==Self::embed(#certificate.before),
                #se::#strong(#certificate.before,#certificate.after,#(#pn),*),
                #certificate.token.fragment()==Self::#owned_post(owned.fragment(),#certificate.before,#certificate.after,#(#pn),*),
                <#ft>::op(<#ft>::op(#certificate.token.fragment(),<#ft>::unit()),#certificate.frame)==Self::embed(#certificate.after),
                #physical
                #certificate.withdrawn==#certificate.before.__storage().union_prefer_right(#dep_value).remove_keys(#certificate.after.__storage().dom()),
                Self::#output(owned.fragment(),<#ft>::unit(),#certificate.token.fragment(),#dep_value,#certificate.withdrawn,#(#pn),*)
                #wd_shape
        {
            let ghost #initial=owned.fragment();
            let ghost #physical_deposit=#dep_value;
            #call
            let (#before,#after,#witness_frame)=Self::#witness(#initial,<#ft>::unit(),#next.fragment(),#physical_deposit,#returned_map,#(#pn),*);
            #result_expr{token:#next,withdrawn:#returned_map,before:#before,after:#after,frame:#witness_frame}
        }
    })
}
