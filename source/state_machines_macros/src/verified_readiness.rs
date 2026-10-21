//! Interface selection for `verified_tokenized_state_machine!`, and optional
//! checked readiness over locally observed inputs for the raw interface. The
//! existing all-completion API remains available when a transition is not
//! opted in.
use crate::ast::*;
use crate::parse_token_stream::{parse_result_to_smir, ParseResult, SMBundle};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;
use verus_syn::{punctuated::Punctuated, Error, Ident, Token};

/// Selects the client interface. The default is the generic field-token
/// interface (`verified_generic_tokens`, which may also be written explicitly):
/// the trusted macro's token types and `Instance` methods, each proved by a
/// call to the raw operation. `#[verified_raw_tokens]` selects the raw
/// resource interface, optionally with `#[verified_local_ready(..)]` raw
/// operations whose preconditions are stated over the owned fragments. On the
/// generic interface `#[verified_local_ready(..)]` is accepted (its names are
/// checked) and has no further effect.
pub fn construct(mut parsed: ParseResult) -> Result<TokenStream, Error> {
    let mut selected = HashSet::new();
    let mut raw = false;
    let mut generic = false;
    let mut names = vec![];
    let mut remaining = vec![];
    for attr in parsed.attrs {
        let attribute_name = if attr.path().leading_colon.is_none() && attr.path().segments.len() == 1 {
            attr.path().segments[0].ident.to_string().trim_start_matches("r#").to_string()
        } else {
            String::new()
        };
        if attribute_name == "verified_field_tokens" {
            return Err(Error::new(
                attr.path().segments[0].ident.span(),
                "`#[verified_field_tokens]` was removed: per-field tokens (the generic interface) are the default; delete the attribute",
            ));
        } else if attribute_name == "verified_generic_tokens" {
            if generic {return Err(Error::new(attr.path().segments[0].ident.span(),"duplicate generic field tokens attribute"));}
            if raw {return Err(Error::new(attr.path().segments[0].ident.span(),"generic field tokens and raw token attributes cannot be combined"));}
            if !matches!(attr.meta,verus_syn::Meta::Path(_)){return Err(Error::new(attr.path().segments[0].ident.span(),"generic field tokens attribute takes no arguments"));}
            generic=true;
        } else if attribute_name == "verified_raw_tokens" {
            if raw {return Err(Error::new(attr.path().segments[0].ident.span(),"duplicate raw token attribute"));}
            if generic {return Err(Error::new(attr.path().segments[0].ident.span(),"generic field tokens and raw token attributes cannot be combined"));}
            if !matches!(attr.meta,verus_syn::Meta::Path(_)){return Err(Error::new(attr.path().segments[0].ident.span(),"raw token attribute takes no arguments"));}
            raw=true;
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
    parsed.attrs = remaining;
    let mut bundle = parse_result_to_smir(parsed, true)?;
    crate::lemmas::check_lemmas(&bundle)?;
    for name in &names {
        let Some(tr) = bundle.sm.transitions.iter().find(|tr| tr.name == *name) else {
            return Err(Error::new(name.span(), "unknown local-ready transition"));
        };
        if tr.kind != TransitionKind::Transition {
            return Err(Error::new(
                name.span(),
                "local-ready requires a mutating transition",
            ));
        }
    }
    if !raw {
        // `#[verified_local_ready(..)]` has no effect here beyond the check
        // above: every generic operation already has a token-level
        // precondition, and its generated readiness lemma covers every
        // completion.
        // Initial requirements over a storage map become named open spec
        // functions, which keeps the raw initializer's execution proof
        // stable; clients see equal terms.
        if bundle.sm.fields.iter().any(|field| matches!(field.stype, ShardableType::StorageMap(..))) {
            crate::verified_generic_tokens::normalize_initial_requirements(&mut bundle)?;
        }
        let api=crate::verified_generic_tokens::output(&bundle)?;
        // The generic interface is written against the general emitter's
        // interface, so every machine goes there directly. This is the
        // end point of `verified_tokens::output_raw`'s fallback as well,
        // and the general emitter carries the raw backend's lifted limits
        // (labels, several deposits/withdrawals/guards per path, ...).
        let output=crate::verified_general::output(bundle)?;
        return crate::verified_generic_tokens::append_tokens(output,api);
    }
    if selected.is_empty() {
        return crate::verified_tokens::output_raw(bundle);
    }
    check_local_ready_names(&bundle, &selected)?;
    crate::verified_general::output_with_ready(bundle, &selected)
}

/// Rejects local-ready item names that collide with other generated items.
fn check_local_ready_names(bundle: &SMBundle, selected: &HashSet<String>) -> Result<(), Error> {
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

/// The transition's `require` conditions as one expression, keeping its `let`s, `if`s and
/// `match`es.
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

/// The `<tr>_declared_requires` spec fn: the transition's own requirements on `pre`.
pub fn declared_requires_spec(
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

/// What `local_ready_api` uses of the machine and of one local-ready transition (`st`/`se`:
/// state type/expression, `ft`: fragment type, `tt`: token type, `pn`: parameter names).
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
    pub storage: &'a crate::verified_storage_tagged::Tagged,
    pub deposits: bool,
    pub withdraws: bool,
    pub paired: bool,
}

/// A `__tsm_<stem>_<n>` name that no parameter, field, generic or body identifier of `tr`
/// uses.
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
    completion_frame:&Ident,ft:&TokenStream,se:&TokenStream,owners:&Ident,pn:&[&Ident],
    skip:&HashSet<String>)->Vec<TokenStream>
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
    removals.retain(|(field,_)|!skip.contains(&field.to_string()));
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
    completion_frame:&Ident,ft:&TokenStream,se:&TokenStream,owners:&Ident,pn:&[&Ident],
    skip:&HashSet<String>)->Vec<TokenStream>{
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
    removals.retain(|(field,_,_)|!skip.contains(&field.to_string()));
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

/// A step of a transition's body, for `local_sequence_hints`.
enum LocalStep<'a> {
    /// A `remove` or `have` of a map, set or multiset field (exclusive or
    /// persistent), with the pattern it binds.
    Observe(&'a Field, &'a SpecialOp, Option<&'a verus_syn::Pat>),
    /// An `add` of such a field: later statements on it are not followed.
    Add(&'a Field),
    /// A `let` (pattern, type, value).
    Let(&'a verus_syn::Pat, Option<&'a verus_syn::Type>, &'a verus_syn::Expr),
    /// The first branch of an `if`/`match`, see `local_steps`.
    Branch(LocalBranch<'a>),
    /// The next branch (`else`, or the next arm).
    Next,
    /// The end of the last branch.
    Join,
}

/// The case split of a `LocalStep::Branch`.
#[derive(Clone, Copy)]
enum LocalBranch<'a> {
    If(&'a verus_syn::Expr),
    Match(&'a verus_syn::Expr, &'a [Arm]),
}

/// The steps of `tr`'s body. An `if`/`match` ends the statements it follows:
/// it is `Branch`, each branch's steps (followed by the statements after the
/// join, which are repeated per branch), separated by `Next`, then `Join`. A
/// path ends at a pattern binding a field of another kind, or after a
/// refutable pattern.
fn local_steps<'a>(sm: &'a SM, tr: &'a Transition) -> Vec<LocalStep<'a>> {
    // `todo`: the statements still to do on this path, the next one last.
    fn walk<'a>(sm: &'a SM, mut todo: Vec<&'a TransitionStmt>, out: &mut Vec<LocalStep<'a>>) {
        while let Some(stmt) = todo.pop() {
            let TransitionStmt::Split(_, split, children) = stmt else {
                if let TransitionStmt::Block(_, children) = stmt {
                    todo.extend(children.iter().rev());
                }
                continue;
            };
            match &**split {
                SplitKind::Special(name, operation, _, pattern) => {
                    let field = sm.fields.iter().find(|f| f.name == *name).filter(|f| {
                        matches!(
                            f.stype,
                            ShardableType::Map(..)
                                | ShardableType::IMap(..)
                                | ShardableType::Set(_)
                                | ShardableType::ISet(_)
                                | ShardableType::Multiset(_)
                                | ShardableType::PersistentMap(..)
                                | ShardableType::PersistentIMap(..)
                                | ShardableType::PersistentSet(_)
                                | ShardableType::PersistentISet(_)
                        )
                    });
                    let pattern = pattern.as_deref();
                    match field {
                        Some(field) if operation.is_remove() || operation.is_have() => {
                            out.push(LocalStep::Observe(field, operation, pattern));
                        }
                        Some(field) => out.push(LocalStep::Add(field)),
                        None if pattern.is_some() => return,
                        None => {}
                    }
                    if pattern.is_some_and(|p| !crate::util::is_definitely_irrefutable(p)) {
                        return;
                    }
                }
                SplitKind::Let(pattern, ty, _, expression) => {
                    if !crate::util::is_definitely_irrefutable(pattern) {
                        return;
                    }
                    out.push(LocalStep::Let(pattern, ty.as_deref(), expression));
                }
                SplitKind::If(condition) => {
                    out.push(LocalStep::Branch(LocalBranch::If(condition)));
                    branches(sm, &todo, children, out);
                    return;
                }
                SplitKind::Match(scrutinee, arms) => {
                    out.push(LocalStep::Branch(LocalBranch::Match(scrutinee, arms)));
                    branches(sm, &todo, children, out);
                    return;
                }
            }
            todo.extend(children.iter().rev());
        }
    }
    fn branches<'a>(
        sm: &'a SM,
        todo: &[&'a TransitionStmt],
        children: &'a [TransitionStmt],
        out: &mut Vec<LocalStep<'a>>,
    ) {
        for (index, child) in children.iter().enumerate() {
            if index > 0 {
                out.push(LocalStep::Next);
            }
            let mut todo = todo.to_vec();
            todo.push(child);
            walk(sm, todo, out);
        }
        out.push(LocalStep::Join);
    }
    let mut out = vec![];
    walk(sm, vec![&tr.body], &mut out);
    out
}

/// A `LocalStep::Branch` being replayed: the hints before it, the tracked
/// fields' fragments and states and the fields not followed at its start, and
/// the hints of its branches done so far.
struct LocalCase<'a> {
    branch: LocalBranch<'a>,
    outer: Vec<TokenStream>,
    tracked: Vec<(String, TokenStream, TokenStream, Ident)>,
    ended: HashSet<String>,
    done: Vec<Vec<TokenStream>>,
}

/// The case split replaying the branches' `hints` (`local_sequence_hints`):
/// the condition, scrutinee and guards are read at the completion.
fn local_case_split(
    branch: LocalBranch<'_>,
    hints: Vec<Vec<TokenStream>>,
    at_completion: &dyn Fn(&verus_syn::Expr) -> verus_syn::Expr,
) -> TokenStream {
    match branch {
        LocalBranch::If(condition) => {
            let condition = at_completion(condition);
            let (yes, no) = (&hints[0], &hints[1]);
            quote! {if #condition {#(#yes)*} else {#(#no)*}}
        }
        LocalBranch::Match(scrutinee, arms) => {
            let scrutinee = at_completion(scrutinee);
            let arms = arms.iter().zip(&hints).map(|(arm, hints)| {
                let pattern = &arm.pat;
                let guard = arm.guard.as_ref().map(|(_, guard)| {
                    let guard = at_completion(guard);
                    quote! {if #guard}
                });
                quote! {#pattern #guard => {#(#hints)*}}
            });
            quote! {match #scrutinee {#(#arms),*}}
        }
    }
}

/// The paths through `steps` (`local_steps`), without branch markers.
fn local_paths<'s, 'a>(steps: &'s [LocalStep<'a>]) -> Vec<Vec<&'s LocalStep<'a>>> {
    let Some(start) = steps.iter().position(|step| matches!(step, LocalStep::Branch(_))) else {
        return vec![steps.iter().collect()];
    };
    let prefix = &steps[..start];
    let mut sections = vec![];
    let (mut depth, mut from) = (0usize, start + 1);
    for (index, step) in steps.iter().enumerate().skip(start + 1) {
        match step {
            LocalStep::Branch(_) => depth += 1,
            LocalStep::Next if depth == 0 => {
                sections.push(&steps[from..index]);
                from = index + 1;
            }
            LocalStep::Join if depth == 0 => {
                sections.push(&steps[from..index]);
                break;
            }
            LocalStep::Join => depth -= 1,
            _ => {}
        }
    }
    let mut paths = vec![];
    for section in sections {
        for path in local_paths(section) {
            paths.push(prefix.iter().chain(path).collect());
        }
    }
    paths
}

/// Readiness facts for the `remove`s and `have`s of map, set and multiset
/// fields, when one of them goes beyond what the singleton hints cover (a
/// field's first `remove`, of a singleton): a map or set `have` or general
/// `remove`, or any `remove`/`have` after a `remove` of the same field.
///
/// The ownership condition observes each operand in the owned fragment that
/// the field's earlier statements leave (joined with `h` for a `have`), and
/// the enabling condition in the state those statements leave. Neither
/// follows from the inclusion of the operands in `op(owned, h)` alone. The
/// proof rebuilds both, statement by statement: starting from `owned` and the
/// completion's field, a statement's frame lemma lifts its operand from the
/// fragment it observes to the current state (that fragment composes with
/// `h`, for a `remove`, and the completion frame to the state's embedding),
/// and a `remove` yields the next fragment (the ownership compiler's) and the
/// next state (the transition's update). `let`s and pattern bindings are
/// bound as in the transition. An `if`/`match` is a case split on its
/// condition or scrutinee (with the arms' patterns and guards), each branch
/// replaying its statements and those after the join from the fragments and
/// states before the split. Stated inside the completion quantifier, with
/// operands read at the completion. Returns the hints and the fields they
/// cover (all fields of the steps, if any; their singleton hints are omitted).
fn local_sequence_hints(
    sm: &SM,
    tr: &Transition,
    completion: &Ident,
    completion_frame: &Ident,
    ft: &TokenStream,
) -> Result<(Vec<TokenStream>, HashSet<String>), Error> {
    use crate::verified_monoids::{
        component_type, map_view, set_view, updated_component, EffectOp,
    };
    let steps = local_steps(sm, tr);
    let paths = local_paths(&steps);
    // Whether the field's statements on a path need these hints.
    let needs = |path: &Vec<&LocalStep>, field: &Field| {
        let mut operations = vec![];
        for step in path {
            match step {
                LocalStep::Observe(f, operation, _) if f.name == field.name => {
                    operations.push(*operation)
                }
                LocalStep::Add(f) if f.name == field.name => break,
                _ => {}
            }
        }
        let after_remove = operations
            .iter()
            .position(|o| o.is_remove())
            .is_some_and(|i| i + 1 < operations.len());
        let beyond_singleton = !matches!(field.stype, ShardableType::Multiset(_))
            && operations.iter().any(|o| {
                o.is_have() || matches!(o.elt, MonoidElt::General(_))
            });
        after_remove || beyond_singleton
    };
    let observed = || {
        steps.iter().filter_map(|step| match step {
            LocalStep::Observe(field, ..) => Some(*field),
            _ => None,
        })
    };
    if !paths.iter().any(|path| observed().any(|field| needs(path, field))) {
        return Ok((vec![], HashSet::new()));
    }
    let covered = observed().map(|field| field.name.to_string()).collect();
    let c = quote! {::vstd::resource::tsm_collections};
    let m = quote! {::vstd::resource::tsm_finite_multiset};
    let z = completion_frame;
    let span = proc_macro2::Span::mixed_site();
    let key = format_ident!("__tsm_local_key", span = span);
    let at_completion = |e: &verus_syn::Expr| -> verus_syn::Expr {
        struct PreRoot<'a>(&'a Ident);
        impl verus_syn::visit_mut::VisitMut for PreRoot<'_> {
            fn visit_expr_path_mut(&mut self, node: &mut verus_syn::ExprPath) {
                if node.path.is_ident("pre") {
                    let name = self.0;
                    node.path = verus_syn::parse_quote! {#name};
                }
            }
        }
        use verus_syn::visit_mut::VisitMut;
        let mut e = e.clone();
        PreRoot(completion).visit_expr_mut(&mut e);
        e
    };
    // Per field: its current owned fragment and state, and the frame of a
    // `remove` (`op(h, z)`). A field is not followed after an `add`.
    let mut tracked: Vec<(String, TokenStream, TokenStream, Ident)> = vec![];
    let mut ended: HashSet<String> = HashSet::new();
    let mut hints = vec![quote! {<#ft>::associative(owned,h,#z);}];
    // The enclosing branches, innermost last (`LocalCase`), and while a path
    // is not followed further, 1 + the depth of the branches entered since.
    let mut cases: Vec<LocalCase> = vec![];
    let mut skipping = 0usize;
    for (index, step) in steps.iter().enumerate() {
        if skipping > 0 {
            match step {
                LocalStep::Branch(_) => skipping += 1,
                LocalStep::Next | LocalStep::Join if skipping > 1 => {
                    if matches!(step, LocalStep::Join) {
                        skipping -= 1;
                    }
                }
                LocalStep::Next | LocalStep::Join => skipping = 0,
                _ => {}
            }
            if skipping > 0 {
                continue;
            }
        }
        let (field, operation, pattern) = match step {
            LocalStep::Branch(branch) => {
                cases.push(LocalCase {
                    branch: *branch,
                    outer: std::mem::take(&mut hints),
                    tracked: tracked.clone(),
                    ended: ended.clone(),
                    done: vec![],
                });
                continue;
            }
            LocalStep::Next | LocalStep::Join => {
                let case = cases.last_mut().unwrap();
                case.done.push(std::mem::take(&mut hints));
                tracked = case.tracked.clone();
                ended = case.ended.clone();
                if matches!(step, LocalStep::Join) {
                    let case = cases.pop().unwrap();
                    hints = case.outer;
                    hints.push(local_case_split(case.branch, case.done, &at_completion));
                }
                continue;
            }
            LocalStep::Let(pattern, ty, expression) => {
                let ty = ty.map(|ty| quote! {:#ty});
                let expression = at_completion(expression);
                hints.push(quote! {let #pattern #ty = #expression;});
                continue;
            }
            LocalStep::Add(field) => {
                ended.insert(field.name.to_string());
                continue;
            }
            LocalStep::Observe(field, operation, pattern) => (*field, *operation, *pattern),
        };
        let n = &field.name;
        if ended.contains(&n.to_string()) {
            if pattern.is_some() {
                // This path is not followed further.
                skipping = 1;
            }
            continue;
        }
        let ct = component_type(&field.stype);
        let setter = format_ident!("__tsm_set_{}", n);
        if !tracked.iter().any(|(name, ..)| name == &n.to_string()) {
            let frame = fresh(sm, tr, &format!("local_frame_{n}"));
            hints.push(quote! {let #frame=<#ct>::op(h.#n,#z.#n);});
            tracked.push((n.to_string(), quote! {owned}, quote! {#completion.#n}, frame));
        }
        let entry = tracked.iter().position(|(name, ..)| name == &n.to_string()).unwrap();
        let (_, current, state, frame) = tracked[entry].clone();
        let elt = match &operation.elt {
            MonoidElt::SingletonKV(k, v) => MonoidElt::SingletonKV(
                at_completion(k),
                v.as_ref().map(|v| Box::new(at_completion(v))),
            ),
            MonoidElt::SingletonSet(e) => MonoidElt::SingletonSet(at_completion(e)),
            MonoidElt::SingletonMultiset(e) => MonoidElt::SingletonMultiset(at_completion(e)),
            MonoidElt::General(e) => MonoidElt::General(at_completion(e)),
            other => other.clone(),
        };
        let operation = SpecialOp { stmt: operation.stmt, elt };
        let remove = operation.is_remove();
        let multiset = matches!(field.stype, ShardableType::Multiset(_));
        let map = matches!(
            field.stype,
            ShardableType::Map(..)
                | ShardableType::IMap(..)
                | ShardableType::PersistentMap(..)
                | ShardableType::PersistentIMap(..)
        );
        let finite = matches!(
            field.stype,
            ShardableType::Map(..)
                | ShardableType::Set(_)
                | ShardableType::PersistentMap(..)
                | ShardableType::PersistentSet(_)
        );
        // A field's state and an operand as the fragments' (infinite) domains.
        let native = |e: &TokenStream| {
            if map {
                map_view(&field.stype, e.clone())
            } else if multiset {
                e.clone()
            } else {
                set_view(&field.stype, e.clone())
            }
        };
        let observer = if remove { current.clone() } else { quote! {<#ft>::op(#current,h)} };
        let value = crate::verified_ownership::observed_value(field, &operation, &observer, span)?;
        let st = native(&state);
        // The observed fragment and the rest of the state's embedding.
        let (part, rest) = if remove {
            (quote! {#current.#n}, quote! {#frame})
        } else {
            hints.push(quote! {<#ct>::associative(#current.#n,h.#n,#z.#n);});
            (quote! {<#ct>::op(#current.#n,h.#n)}, quote! {#z.#n})
        };
        let lemma = match (&field.stype, remove) {
            (ShardableType::Map(..) | ShardableType::IMap(..), true) => {
                quote! {#c::map_remove_many_frame}
            }
            (ShardableType::Map(..) | ShardableType::IMap(..), false) => {
                quote! {#c::map_have_many_frame}
            }
            (ShardableType::PersistentMap(..) | ShardableType::PersistentIMap(..), _) => {
                quote! {#c::persistent_map_have_many_frame}
            }
            (ShardableType::Set(_) | ShardableType::ISet(_), true) => {
                quote! {#c::set_remove_many_frame}
            }
            (ShardableType::Set(_) | ShardableType::ISet(_), false) => {
                quote! {#c::set_have_many_frame}
            }
            (ShardableType::PersistentSet(_) | ShardableType::PersistentISet(_), _) => {
                quote! {#c::persistent_set_have_many_frame}
            }
            (_, true) => quote! {#m::finite_multiset_remove_many_frame},
            (_, false) => quote! {#m::finite_multiset_owned_subset},
        };
        if multiset && !remove {
            hints.push(quote! {#lemma(#part,#rest,#st); assert((#value).subset_of(#st));});
        } else {
            hints.push(quote! {#lemma(#part,#rest,#st,#value);});
        }
        // The statement's enabling condition on the current state, from the
        // operand's inclusion in the state's native view.
        hints.push(match &operation.elt {
            MonoidElt::General(e) if finite && map => quote! {
                assert forall|#key| #![trigger (#e).dom().contains(#key)] #![trigger (#state).dom().contains(#key)]
                    (#e).dom().contains(#key) implies (#state).dom().contains(#key) && (#state)[#key]==(#e)[#key] by {
                    assert((#value).dom().contains(#key));
                    assert((#st).dom().contains(#key));
                }
                assert((#e).submap_of(#state));
            },
            MonoidElt::General(e) if finite => quote! {
                assert forall|#key| (#e).contains(#key) implies #[trigger] (#state).contains(#key) by {
                    assert((#value).contains(#key));
                }
                assert((#e).subset_of(#state));
            },
            MonoidElt::SingletonKV(k, v) => {
                let v = v.as_ref().map(|v| quote! {assert((#state)[#k]==#v);});
                let native_key = finite.then(|| quote! {assert((#st).dom().contains(#k));});
                quote! {
                    assert((#value).dom().contains(#k));
                    #native_key
                    assert((#state).dom().contains(#k));
                    #v
                }
            }
            MonoidElt::SingletonSet(e) => {
                quote! {assert((#value).contains(#e)); assert((#state).contains(#e));}
            }
            MonoidElt::SingletonMultiset(e) => {
                quote! {assert((#value).count(#e)==1); assert((#state).count(#e)>=1);}
            }
            _ => quote! {},
        });
        if remove {
            // The fragment and the state the removal leaves.
            let next = fresh(sm, tr, &format!("local_owned_{n}_{index}"));
            let next_state = fresh(sm, tr, &format!("local_state_{n}_{index}"));
            let component =
                updated_component(&field.stype, EffectOp::Remove, quote! {(#current).#n}, value.clone());
            let (updated, native_updated) = match &operation.elt {
                MonoidElt::General(e) if map => {
                    (quote! {(#state).remove_keys(#e.dom())}, quote! {(#st).remove_keys((#value).dom())})
                }
                MonoidElt::SingletonKV(k, _) => {
                    (quote! {(#state).remove(#k)}, quote! {(#st).remove_keys((#value).dom())})
                }
                MonoidElt::General(e) if multiset => {
                    (quote! {(#state).sub(#e)}, quote! {(#st).sub(#value)})
                }
                MonoidElt::SingletonMultiset(e) => {
                    (quote! {(#state).remove(#e)}, quote! {(#st).sub(#value)})
                }
                MonoidElt::General(e) => {
                    (quote! {(#state).difference(#e)}, quote! {(#st).difference(#value)})
                }
                MonoidElt::SingletonSet(e) => {
                    (quote! {(#state).remove(#e)}, quote! {(#st).difference(#value)})
                }
                _ => unreachable!(),
            };
            let native_next = native(&quote! {#next_state});
            hints.push(quote! {
                let #next=<#ft>::#setter(#current,#component);
                let #next_state=#updated;
                assert(::vstd::prelude::ext_equal(#native_next,#native_updated));
            });
            tracked[entry].1 = quote! {#next};
            tracked[entry].2 = quote! {#next_state};
        }
        if let Some(pattern) = pattern {
            let bound = crate::verified_ownership::bound_value(field, &operation, value, span)?;
            hints.push(quote! {let #pattern = #bound;});
        }
    }
    Ok((hints, covered))
}

/// Whether `stmt` has a storage operation under a `let`, `if` or `match`
/// (which `<tr>_deposited` and `<tr>_local_deposited` then keep).
fn scoped_deposits(stmt: &TransitionStmt) -> bool {
    fn storage(stmt: &TransitionStmt) -> bool {
        match stmt {
            TransitionStmt::Block(_, children) => children.iter().any(storage),
            TransitionStmt::Split(_, split, children) => {
                matches!(&**split, SplitKind::Special(_, operation, ..) if operation.stmt.is_for_storage())
                    || children.iter().any(storage)
            }
            _ => false,
        }
    }
    match stmt {
        TransitionStmt::Block(_, children) => children.iter().any(scoped_deposits),
        TransitionStmt::Split(_, split, children) => {
            let scope = matches!(&**split, SplitKind::Let(..) | SplitKind::If(_) | SplitKind::Match(..));
            (scope && children.iter().any(storage)) || children.iter().any(scoped_deposits)
        }
        _ => false,
    }
}

/// The local-ready items of a transition: `_local_requires`, `_local_ready`, `_local`,
/// `_local_with_shared` and `_observed`.
pub fn local_ready_api(c: Context<'_>) -> Result<TokenStream, Error> {
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
        storage,
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
    let map = storage.ty();
    let unit = storage.unit();
    let tracked_unit = storage.tracked_unit();
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
        unit.clone()
    };
    let ret = if withdraws {
        quote! {tracked out:(#tt,#map)}
    } else {
        quote! {tracked out:#tt}
    };
    let call = if withdraws {
        quote! {let tracked (#next,#returned_map)=Self::#local(owned,#dep_arg #(#pn),*);}
    } else {
        quote! {let tracked #next=Self::#local(owned,#dep_arg #(#pn),*);let tracked #returned_map:#map=#tracked_unit;}
    };
    let out = if withdraws {
        quote! {out.0}
    } else {
        quote! {out}
    };
    let wd = if withdraws {
        quote! {out.1}
    } else {
        unit.clone()
    };
    let wd_shape = if withdraws {
        quote! {}
    } else {
        quote! {,#certificate.withdrawn==#unit}
    };
    let before_s = quote! {#certificate.before.__storage()};
    let after_s = quote! {#certificate.after.__storage()};
    let physical = if paired {
        let disjoint = storage.disjoint(before_s.clone(), dep_value.clone());
        let within = storage.le(after_s.clone(), storage.op(before_s.clone(), dep_value.clone()));
        quote! {#dep_value==#se::#deposited(#certificate.before,#(#pn),*),
        #disjoint,
        #within,}
    } else {
        let delta = storage.minus(after_s.clone(), before_s.clone());
        quote! {#dep_value==#delta,}
    };
    let withdrawn_value = storage.minus(storage.op(before_s.clone(), dep_value.clone()), after_s.clone());
    // A step that withdraws nothing and has one storage operation per path:
    // its outputs do not state the withdrawn storage (only that it is the
    // unit), so the certificate derives it from the storage growing.
    let monotone_withdrawn = if !withdraws && !paired {
        let (b, a) = (quote! {#before.__storage()}, quote! {#after.__storage()});
        let grow = storage.prove_le(
            &format_ident!("__tsm_storage_index", span = proc_macro2::Span::mixed_site()),
            b.clone(),
            a.clone(),
        );
        quote! {
            #grow
            ::vstd::resource::tsm_storage::storage_withdrawn_none(#b,#a,#physical_deposit);
        }
    } else {
        quote! {}
    };
    let deposit_index = format_ident!("__tsm_deposit_index", span = proc_macro2::Span::mixed_site());
    let (local_deposit, full_deposit) = (
        quote! {#se::#local_deposited(#full_state,#(#pn),*)},
        quote! {#se::#deposited(#full_state,#(#pn),*)},
    );
    let deposit_eq = if scoped_deposits(&tr.body) {
        // Both deposit functions are inline: name them, as Verus cannot
        // choose a trigger in their `let`/`if`/`match` bodies.
        let (local_name, full_name) = (fresh(sm, tr, "local_deposit"), fresh(sm, tr, "deposit"));
        let eq = storage.prove_eq(&deposit_index, quote! {#local_name}, quote! {#full_name});
        quote! {let #local_name = #local_deposit; let #full_name = #full_deposit; #eq}
    } else {
        storage.prove_eq(&deposit_index, local_deposit, full_deposit)
    };
    let (sequence_hints,sequenced)=local_sequence_hints(sm,tr,&full_state,&completion_frame,ft)?;
    let set_hints=singleton_set_remove_hints(tr,&observation,&full_state,&completion_frame,ft,se,&owners,pn,&sequenced);
    let map_hints=singleton_map_remove_hints(sm,tr,&observation,&full_state,&completion_frame,ft,se,&owners,pn,&sequenced);
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
                #(#sequence_hints)*
                #deposit_eq
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
                #certificate.withdrawn==#withdrawn_value,
                Self::#output(owned.fragment(),<#ft>::unit(),#certificate.token.fragment(),#dep_value,#certificate.withdrawn,#(#pn),*)
                #wd_shape
        {
            let ghost #initial=owned.fragment();
            let ghost #physical_deposit=#dep_value;
            #call
            let (#before,#after,#witness_frame)=Self::#witness(#initial,<#ft>::unit(),#next.fragment(),#physical_deposit,#returned_map,#(#pn),*);
            #monotone_withdrawn
            #result_expr{token:#next,withdrawn:#returned_map,before:#before,after:#after,frame:#witness_frame}
        }
    })
}
