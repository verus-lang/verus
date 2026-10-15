//! Checked singleton-reader facade over actual StorageTokens.
use crate::ast::*;
use crate::field_access_visitor::visit_field_accesses;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use crate::verified_field_storage_roles as roles;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

#[derive(Default)]
struct Operations {
    initial: HashMap<String, Expr>,
    requirements: Vec<Expr>,
    assertions: Vec<Expr>,
    update: Option<(Ident, Expr)>,
    specials: Vec<(Ident, SpecialOp)>,
}
fn flatten(stmt: &TransitionStmt, out: &mut Operations) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, xs) => {
            for x in xs {
                flatten(x, out)?;
            }
        }
        TransitionStmt::Initialize(_, n, e) => {
            if out.initial.insert(n.to_string(), e.clone()).is_some() {
                return Err(Error::new(
                    n.span(),
                    "duplicate reader-facade initialization",
                ));
            }
        }
        TransitionStmt::Update(_, n, e) => {
            if out.update.replace((n.clone(), e.clone())).is_some() {
                return Err(Error::new(
                    n.span(),
                    "reader facade requires exactly one ordinary update",
                ));
            }
        }
        TransitionStmt::Require(_, e) => out.requirements.push(e.clone()),
        TransitionStmt::Assert(_, e, _) => out.assertions.push(e.clone()),
        TransitionStmt::Split(span, split, xs) => {
            let SplitKind::Special(n, op, _, None) = &**split else {
                return Err(Error::new(
                    *span,
                    "reader facade requires straight-line unbound singleton operations",
                ));
            };
            out.specials.push((n.clone(), op.clone()));
            for x in xs {
                flatten(x, out)?;
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "reader facade requires straight-line initialization or transitions",
            ))
        }
    }
    Ok(())
}
fn fresh(sm: &SM, tr: &Transition, stem: &str) -> Ident {
    let mut names: HashSet<_> = sm.fields.iter().map(|f| f.name.to_string()).collect();
    names.extend(tr.params.iter().map(|p| p.name.to_string()));
    // Rewritten pre-field reads may occur under user quantifiers/closures.
    // Reserve their binders as well as free identifiers before introducing refs.
    fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
        for token in tokens {
            match token {
                proc_macro2::TokenTree::Ident(name) => {
                    names.insert(name.to_string());
                }
                proc_macro2::TokenTree::Group(group) => reserve(group.stream(), names),
                _ => {}
            }
        }
    }
    let mut operations = Operations::default();
    if flatten(&tr.body, &mut operations).is_ok() {
        for expression in operations
            .initial
            .values()
            .chain(operations.requirements.iter())
            .chain(operations.assertions.iter())
            .chain(operations.update.iter().map(|(_, expression)| expression))
        {
            reserve(quote! {#expression}, &mut names);
        }
        for (_, operation) in &operations.specials {
            match &operation.elt {
                MonoidElt::SingletonMultiset(expression)
                | MonoidElt::OptionSome(Some(expression)) => {
                    reserve(quote! {#expression}, &mut names)
                }
                _ => {}
            }
        }
    }
    let mut name = format!("__tsm_reader_{stem}");
    while names.contains(&name) {
        name.push('_');
    }
    Ident::new(&name, Span::mixed_site())
}
fn lower(
    input: &Expr,
    fields: &HashMap<String, Field>,
    variable: &Field,
    value: TokenStream,
) -> Result<TokenStream, Error> {
    let mut expression = input.clone();
    let mut errors = Vec::new();
    visit_field_accesses(
        &mut expression,
        |errors, field, node| {
            if field.name == variable.name {
                *node = Expr::Verbatim(value.clone());
            } else {
                errors.push(Error::new(
                    field.name.span(),
                    "reader facade requires expressions observed by the supplied ordinary owner",
                ));
            }
        },
        &mut errors,
        fields,
    );
    if let Some(e) = errors.into_iter().next() {
        return Err(e);
    }
    Ok(quote! {#expression})
}
pub fn output(sm: &SM, selected: &HashSet<String>) -> Result<TokenStream, Error> {
    let variables: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Variable(_)))
        .collect();
    let readers: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Multiset(_)))
        .collect();
    let stores: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::StorageOption(_)))
        .collect();
    if sm.fields.len() != 3 || variables.len() != 1 || readers.len() != 1 || stores.len() != 1 {
        return Err(Error::new(sm.name.span(),"singleton reader facade currently requires one Variable, one Multiset and one StorageOption"));
    }
    let variable = variables[0];
    let reader = readers[0];
    let store = stores[0];
    let ShardableType::Multiset(element) = &reader.stype else {
        unreachable!()
    };
    let ShardableType::StorageOption(permission) = &store.stype else {
        unreachable!()
    };
    if element.to_token_stream().to_string() != permission.to_token_stream().to_string() {
        return Err(Error::new(
            store.name.span(),
            "reader and optional storage payload types must match",
        ));
    }
    let mut api_names = HashSet::from([
        "id".to_string(),
        "clone".to_string(),
        "invariant".to_string(),
        "__reader_singleton_normalize".to_string(),
    ]);
    for tr in &sm.transitions {
        if !api_names.insert(tr.name.to_string()) {
            return Err(Error::new(
                tr.name.span(),
                "reader facade generated Instance method name collision",
            ));
        }
        if tr.kind == TransitionKind::Transition
            && !api_names.insert(format!("__reader_{}_raw", tr.name))
        {
            return Err(Error::new(
                tr.name.span(),
                "reader facade generated raw helper name collision",
            ));
        }
    }
    let generated_collection = format!("{}_collection", reader.name);
    for f in &sm.fields {
        if f.name == "Instance"
            || f.name == "__ReaderMetadata"
            || f.name == generated_collection.as_str()
        {
            return Err(Error::new(
                f.name.span(),
                "reader facade generated nominal type name collision",
            ));
        }
    }
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let token = quote! {Token #types};
    let descriptor = quote! {::vstd::resource::tsm_context::Descriptor<__ReaderMetadata>};
    let location = format_ident!("protocol_location");
    let cx = roles::Context {
        decl: &decl,
        types: &types,
        expr: &expr,
        where_clause: &wc,
        attrs: &attrs,
        token: &token,
        descriptor: &descriptor,
        protocol_location: &location,
        constants: &[],
    };
    let var = &variable.name;
    let bag = &reader.name;
    let storage = &store.name;
    let var_factory = format_ident!("field_{var}");
    let var_getter = format_ident!("value_{var}");
    let bag_factory = format_ident!("field_{bag}");
    let collection = format_ident!("{bag}_collection");
    let take_law = format_ident!("take_{var}_law");
    let wrappers = [roles::wrapper(variable, &cx)?, roles::wrapper(reader, &cx)?];
    let mut methods = Vec::new();
    let mut init_count = 0;
    for tr in &sm.transitions {
        let name = &tr.name;
        if tr.kind == TransitionKind::Property {
            methods.push(roles::guard_method(reader, tr, &cx)?);
            continue;
        }
        let mut op = Operations::default();
        flatten(&tr.body, &mut op)?;
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
        if tr.kind == TransitionKind::Init {
            init_count += 1;
            if op.update.is_some()
                || !op.specials.is_empty()
                || !op.assertions.is_empty()
                || op.initial.len() != 3
            {
                return Err(Error::new(name.span(),"reader initializer requires exact ordinary/empty-reader/empty-storage initialization"));
            }
            let value = op
                .initial
                .get(&var.to_string())
                .ok_or_else(|| Error::new(name.span(), "missing ordinary initializer"))?;
            let initialbag = op.initial.get(&bag.to_string()).unwrap();
            let initialstore = op.initial.get(&storage.to_string()).unwrap();
            if !matches!(
                initialbag
                    .to_token_stream()
                    .to_string()
                    .replace(' ', "")
                    .as_str(),
                "Multiset::empty()" | "::vstd::multiset::Multiset::empty()"
            ) || !matches!(
                initialstore
                    .to_token_stream()
                    .to_string()
                    .replace(' ', "")
                    .as_str(),
                "Option::None" | "None"
            ) {
                return Err(Error::new(
                    name.span(),
                    "reader facade initializer currently requires empty reader and None storage",
                ));
            }
            let req = &op.requirements;
            let actual = fresh(sm, tr, "initial_permission");
            let owned = fresh(sm, tr, "initial_owned");
            let md = fresh(sm, tr, "initial_metadata");
            let init_result = fresh(sm, tr, "initial_result");
            let rawvar = fresh(sm, tr, "initial_variable");
            let rawbag = fresh(sm, tr, "initial_reader");
            let context = fresh(sm, tr, "initial_context");
            methods.push(quote!{
    pub proof fn #name(#(#params,)*tracked #actual:Option<#permission>)->(tracked #init_result:(Tracked<Self>,Tracked<#var #types>,Tracked<#collection #types>))
      requires #(#req,)*#actual==None,
      ensures #init_result.1@.instance_id()==#init_result.0@.id(),#init_result.1@.value()==#value,#init_result.2@.instance_id()==#init_result.0@.id(),#init_result.2@.multiset()==::vstd::multiset::Multiset::empty(),
    {
     let tracked #owned=Protocol #expr::#name(IMap::tracked_empty(),#(#pn),*);
     assert(#owned.fragment()==Fragment #expr::#var_factory(#value));
     let tracked #md=::vstd::resource::tsm_context::Descriptor::alloc(__ReaderMetadata{protocol_location:#owned.loc()});
     #owned.fragment().#take_law();
     let tracked(#rawvar,#rawbag)=#owned.split(Fragment #expr::#var_factory(#value),Fragment #expr::#bag_factory(::vstd::multiset::Multiset::empty()));
     #rawbag.fragment().op_unit();
     let tracked(#context,#rawbag)=#rawbag.split(Fragment #expr::empty(),Fragment #expr::#bag_factory(::vstd::multiset::Multiset::empty()));
     let tracked #rawvar=<#var #types>::__from_token(#rawvar,#md.clone());
     let tracked #rawbag=#collection #expr{raw:#rawbag,metadata:#md.clone()};
     (Tracked(Self{metadata:#md,context:Tracked(Some(#context))}),Tracked(#rawvar),Tracked(#rawbag))
    }
   });
            continue;
        }
        if tr.kind != TransitionKind::Transition
            || !selected.contains(&name.to_string())
            || !op.initial.is_empty()
        {
            return Err(Error::new(name.span(),"reader facade requires selected checked local readiness for every mutating transition"));
        }
        let [parameter] = tr.params.as_slice() else {
            return Err(Error::new(
                name.span(),
                "reader facade transitions currently require one element parameter",
            ));
        };
        if parameter.ty.to_token_stream().to_string() != element.to_token_stream().to_string() {
            return Err(Error::new(
                parameter.name.span(),
                "reader facade element parameter type mismatch",
            ));
        }
        let (updated, value) = op.update.as_ref().ok_or_else(|| {
            Error::new(
                name.span(),
                "reader facade requires an ordinary field update",
            )
        })?;
        if updated != var {
            return Err(Error::new(
                updated.span(),
                "reader facade ordinary update field mismatch",
            ));
        }
        let x = &parameter.name;
        let mut have = false;
        let mut add = false;
        let mut remove = false;
        let mut deposit = false;
        let mut withdraw = false;
        for (field, special) in &op.specials {
            let seen = match (&special.stmt, &special.elt) {
                (MonoidStmtType::Have, MonoidElt::SingletonMultiset(e))
                    if field == bag && e.to_token_stream().to_string() == x.to_string() =>
                {
                    &mut have
                }
                (MonoidStmtType::Add(false), MonoidElt::SingletonMultiset(e))
                    if field == bag && e.to_token_stream().to_string() == x.to_string() =>
                {
                    &mut add
                }
                (MonoidStmtType::Remove, MonoidElt::SingletonMultiset(e))
                    if field == bag && e.to_token_stream().to_string() == x.to_string() =>
                {
                    &mut remove
                }
                (MonoidStmtType::Deposit, MonoidElt::OptionSome(Some(e)))
                    if field == storage && e.to_token_stream().to_string() == x.to_string() =>
                {
                    &mut deposit
                }
                (MonoidStmtType::Withdraw, MonoidElt::OptionSome(Some(e)))
                    if field == storage && e.to_token_stream().to_string() == x.to_string() =>
                {
                    &mut withdraw
                }
                _ => {
                    return Err(Error::new(
                        field.span(),
                        "reader facade requires matching singleton element operations",
                    ))
                }
            };
            if *seen {
                return Err(Error::new(
                    field.span(),
                    "reader facade allows at most one operation of each kind",
                ));
            }
            *seen = true;
        }
        if (have && remove) || (add && remove) || (deposit && withdraw) || (add && withdraw) {
            return Err(Error::new(name.span(),"reader facade currently separates shared addition from consuming removal and physical withdrawal"));
        }
        let raw = format_ident!("__reader_{name}_raw");
        let publicvar = fresh(sm, tr, "variable");
        let publicreader = fresh(sm, tr, "reader");
        let slot = fresh(sm, tr, "slot");
        let consumed = fresh(sm, tr, "consumed");
        let shared = fresh(sm, tr, "shared");
        let actual = fresh(sm, tr, "actual");
        let owned = fresh(sm, tr, "owned");
        let initial = fresh(sm, tr, "initial");
        let before = fresh(sm, tr, "before");
        let after = fresh(sm, tr, "after");
        let withdrawn = fresh(sm, tr, "withdrawn");
        let dep = fresh(sm, tr, "deposit");
        let result = fresh(sm, tr, "result");
        let context = fresh(sm, tr, "context");
        let choice = fresh(sm, tr, "choice");
        let pair = fresh(sm, tr, "pair");
        let h = fresh(sm, tr, "shared_fragment");
        let selectedpart = fresh(sm, tr, "selected");
        let oldvalue = quote! {old(#slot)@->Some_0.fragment().#var_getter()};
        let rawvalue = lower(value, &fields, variable, quote! {#initial.#var_getter()})?;
        let publicvalue = lower(value, &fields, variable, quote! {old(#publicvar).value()})?;
        let rawrequirements: Vec<_> = op
            .requirements
            .iter()
            .map(|e| lower(e, &fields, variable, oldvalue.clone()))
            .collect::<Result<_, _>>()?;
        let requirements: Vec<_> = op
            .requirements
            .iter()
            .map(|e| lower(e, &fields, variable, quote! {old(#publicvar).value()}))
            .collect::<Result<_, _>>()?;
        let assertions: Vec<_> = op
            .assertions
            .iter()
            .map(|e| lower(e, &fields, variable, quote! {old(#publicvar).value()}))
            .collect::<Result<_, _>>()?;
        let rawassertions: Vec<_> = op
            .assertions
            .iter()
            .map(|e| lower(e, &fields, variable, oldvalue.clone()))
            .collect::<Result<_, _>>()?;
        let rawpost = lower(value, &fields, variable, oldvalue.clone())?;
        let rawreaderparam = if have {
            quote! {tracked #shared:&#token,}
        } else if remove {
            quote! {tracked #consumed:#token,}
        } else {
            quote! {}
        };
        let publicreaderparam = if have {
            quote! {tracked #publicreader:&#bag #types,}
        } else if remove {
            quote! {tracked #publicreader:#bag #types,}
        } else {
            quote! {}
        };
        let rawreaderreq = if have {
            quote! {#shared.loc()==old(#slot)@->Some_0.loc(),#shared.fragment()==Fragment #expr::#bag_factory(::vstd::multiset::Multiset::singleton(#x)),}
        } else if remove {
            quote! {#consumed.loc()==old(#slot)@->Some_0.loc(),#consumed.fragment()==Fragment #expr::#bag_factory(::vstd::multiset::Multiset::singleton(#x)),}
        } else {
            quote! {}
        };
        let publicreaderreq = if have || remove {
            quote! {#publicreader.instance_id()==self.id(),#publicreader.element()==#x,}
        } else {
            quote! {}
        };
        let readerpreparation = if have || remove {
            quote! {::vstd::prelude::use_type_invariant(&#publicreader);self.metadata.agrees(&#publicreader.metadata);}
        } else {
            quote! {}
        };
        let readerarg = if have {
            quote! {#publicreader.borrow_token(),}
        } else if remove {
            quote! {#publicreader.raw.get().tracked_unwrap(),}
        } else {
            quote! {}
        };
        let physicalparam = if deposit {
            quote! {tracked #actual:#permission,}
        } else {
            quote! {}
        };
        let physicalreq = if deposit {
            quote! {#actual==#x,}
        } else {
            quote! {}
        };
        let actualarg = if deposit {
            quote! {#actual,}
        } else {
            quote! {}
        };
        let pack = if deposit {
            quote! {let tracked #dep=::vstd::resource::tsm_helpers::singleton_map(0int,#actual);}
        } else {
            quote! {}
        };
        let join = if remove {
            quote! {let tracked #owned=#owned.join(#consumed);}
        } else {
            quote! {}
        };
        let observed = format_ident!("{name}_observed");
        let ready = format_ident!("{name}_local_ready");
        let frame = format_ident!("{name}_frame");
        let outputs = format_ident!("{name}_outputs");
        let witness = format_ident!("{name}_witness");
        let call = if have {
            quote! {
             let #h=#shared.fragment();Protocol #expr::#ready(#initial,#h,IMap::empty(),#x);Protocol #expr::#frame(#initial,#h,IMap::empty(),#x);
             let tracked #context=#shared.observe();let tracked #dep=IMap::<int,#permission>::tracked_empty();
             let #choice=ISet::new(|#pair:(Fragment #types,IMap<int,#permission>)|Protocol #expr::#outputs(#initial,#h,#pair.0,IMap::empty(),#pair.1,#x));
             let tracked(#owned,#withdrawn)=#owned.exchange_nondeterministic_with_observation(&#context,#dep,#choice);
             let (#before,#after,_)=Protocol #expr::#witness(#initial,#h,#owned.fragment(),IMap::empty(),#withdrawn,#x);
            }
        } else {
            let dep_arg = if deposit {
                quote! {#dep,}
            } else {
                quote! {}
            };
            quote! {let tracked TransitionObservation #expr{token:#owned,withdrawn:#withdrawn,before:#before,after:#after,..}=Protocol #expr::#observed(#owned,#dep_arg #x);}
        };
        let rawreturn = if add {
            quote! {->(tracked #result:#token)}
        } else if withdraw {
            quote! {->(tracked #result:#permission)}
        } else {
            quote! {}
        };
        let publicreturn = if add {
            quote! {->(tracked #result:#bag #types)}
        } else if withdraw {
            quote! {->(tracked #result:#permission)}
        } else {
            quote! {}
        };
        let rawresult = if add {
            quote! {#result.loc()==old(#slot)@->Some_0.loc(),#result.fragment()==Fragment #expr::#bag_factory(::vstd::multiset::Multiset::singleton(#x)),}
        } else if withdraw {
            quote! {#result==#x,}
        } else {
            quote! {}
        };
        let publicresult = if add {
            quote! {#result.instance_id()==self.id(),#result.element()==#x,}
        } else if withdraw {
            quote! {#result==#x,}
        } else {
            quote! {}
        };
        let split = if add {
            quote! {
             #owned.fragment().#take_law();let #selectedpart=Fragment #expr::#var_factory(#rawvalue);let #context=Fragment #expr::#bag_factory(::vstd::multiset::Multiset::singleton(#x));
             assert(Fragment #expr::op(#selectedpart,#context)==#owned.fragment());let tracked(#owned,#result)=#owned.split(#selectedpart,#context);
            }
        } else if withdraw {
            quote! {assert(#withdrawn==IMap::empty().insert(0int,#x));let tracked #result=::vstd::resource::tsm_helpers::take_singleton(#withdrawn,0int);}
        } else {
            quote! {}
        };
        let rawtail = if add || withdraw {
            quote! {#result}
        } else {
            quote! {}
        };
        let publiccall = quote! {Self::#raw(#x,&mut #publicvar.raw,#readerarg #actualarg)};
        let publicbody = if add {
            quote! {let tracked #result=#publiccall;<#bag #types>::__from_token(#result,self.metadata.clone(),#x)}
        } else {
            publiccall
        };
        methods.push(quote!{
   proof fn #raw(#(#params,)*tracked #slot:&mut Tracked<Option<#token>>,#rawreaderparam #physicalparam)#rawreturn
    requires old(#slot)@ is Some,old(#slot)@->Some_0.fragment()==Fragment #expr::#var_factory(#oldvalue),#(#rawrequirements,)*#rawreaderreq #physicalreq
    ensures final(#slot)@ is Some,final(#slot)@->Some_0.loc()==old(#slot)@->Some_0.loc(),final(#slot)@->Some_0.fragment()==Fragment #expr::#var_factory(#rawpost),#(#rawassertions,)*#rawresult
   {
    let tracked #owned=#slot.borrow_mut().tracked_take();#join let #initial=#owned.fragment();#pack
    Self::__reader_singleton_normalize(#x);#call #split
    *#slot=Tracked(Some(#owned));#rawtail
   }
   pub proof fn #name(tracked &self,#(#params,)*tracked #publicvar:&mut #var #types,#publicreaderparam #physicalparam)#publicreturn
    requires old(#publicvar).instance_id()==self.id(),#(#requirements,)*#publicreaderreq #physicalreq
    ensures final(#publicvar).instance_id()==self.id(),final(#publicvar).value()==#publicvalue,#(#assertions,)*#publicresult
   {
    ::vstd::prelude::use_type_invariant(&*#publicvar);self.metadata.agrees(&#publicvar.metadata);#readerpreparation #publicbody
   }
  });
    }
    if init_count == 0 {
        return Err(Error::new(
            sm.name.span(),
            "reader facade requires an initializer",
        ));
    }
    Ok(quote! {
     struct __ReaderMetadata{ghost protocol_location: ::vstd::resource::Loc}
     #(#wrappers)*
     #(#attrs)*#[allow(non_camel_case_types)]pub tracked struct #collection #decl #wc{raw:#token,metadata:#descriptor}
     impl #decl #collection #types #wc{
      #[verifier::type_invariant]spec fn invariant(self)->bool{self.raw.loc()==self.metadata.value().protocol_location&&self.raw.fragment()==Fragment #expr::#bag_factory(::vstd::multiset::Multiset::empty())}
      pub closed spec fn instance_id(&self)->::vstd::resource::Loc{self.metadata.id()}
      pub closed spec fn multiset(&self)->::vstd::multiset::Multiset<#element>{::vstd::multiset::Multiset::empty()}
     }
     #(#attrs)*pub tracked struct Instance #decl #wc{metadata:#descriptor,context:Tracked<Option<#token>>}
     impl #decl Instance #types #wc{
      #[verifier::type_invariant]spec fn invariant(self)->bool{!(self.context@ is Some)||self.context@->Some_0.loc()==self.metadata.value().protocol_location&&self.context@->Some_0.fragment()==Fragment #expr::empty()}
      pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}
      pub proof fn clone(tracked &self)->(tracked out:Self)ensures out.id()==self.id(){Self{metadata:self.metadata.clone(),context:Tracked(None)}}
      proof fn __reader_singleton_normalize(x:#element)
       ensures ::vstd::multiset::Multiset::<#element>::empty().insert(x)==::vstd::multiset::Multiset::singleton(x),::vstd::multiset::Multiset::<#element>::empty().add(::vstd::multiset::Multiset::empty().insert(x))==::vstd::multiset::Multiset::singleton(x),::vstd::multiset::Multiset::<#element>::singleton(x).sub(::vstd::multiset::Multiset::empty().insert(x))==::vstd::multiset::Multiset::empty(),
      {
       let inserted=::vstd::multiset::Multiset::<#element>::empty().insert(x);let singleton=::vstd::multiset::Multiset::<#element>::singleton(x);
       assert(::vstd::prelude::ext_equal(inserted,singleton));assert(::vstd::prelude::ext_equal(::vstd::multiset::Multiset::<#element>::empty().add(inserted),singleton));assert(::vstd::prelude::ext_equal(singleton.sub(inserted),::vstd::multiset::Multiset::empty()));
      }
      #(#methods)*
     }
    })
}
