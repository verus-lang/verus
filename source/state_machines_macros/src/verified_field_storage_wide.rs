//! Native mixed-storage role facade for the complete heterogeneous models.
//! Private work in progress: routed only in the isolated private workspace.
use crate::ast::*;
use crate::field_access_visitor::visit_field_accesses;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use crate::verified_field_storage_roles as roles;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

#[derive(Default)]
pub(crate) struct Ops {
    pub(crate) initial: HashMap<String, Expr>,
    pub(crate) updates: HashMap<String, Expr>,
    pub(crate) requires: Vec<Expr>,
    pub(crate) asserts: Vec<Expr>,
    pub(crate) special: Vec<(Ident, SpecialOp)>,
    pub(crate) bindings: Vec<(Ident, Expr)>,
    pub(crate) withdrawals: HashMap<String, Ident>,
    pub(crate) have_bindings: HashMap<String,Ident>,
}
fn collect(stmt: &TransitionStmt, out: &mut Ops) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, xs) => {
            for x in xs {
                collect(x, out)?
            }
        }
        TransitionStmt::Initialize(_, n, e) => {
            if out.initial.insert(n.to_string(), e.clone()).is_some() {
                return Err(Error::new(
                    n.span(),
                    "heterogeneous initialization requires one value per field",
                ));
            }
        }
        TransitionStmt::Update(_, n, e) => {
            if out.updates.insert(n.to_string(), e.clone()).is_some() {
                return Err(Error::new(
                    n.span(),
                    "heterogeneous transition requires one write per variable",
                ));
            }
        }
        TransitionStmt::Require(_, e) => out.requires.push(e.clone()),
        TransitionStmt::Assert(_, e, _) => out.asserts.push(e.clone()),
        TransitionStmt::Split(span, k, xs) => {
            match &**k {
                SplitKind::Let(p, _, LetKind::BirdsEye, e) => {
                    let verus_syn::Pat::Ident(p) = &**p else {
                        return Err(Error::new(
                            *span,
                            "heterogeneous selected binding requires one identifier",
                        ));
                    };
                    out.bindings.push((p.ident.clone(), e.clone()));
                }
                SplitKind::Special(n, op, _, None) => out.special.push((n.clone(), op.clone())),
                SplitKind::Special(n, op, _, Some(pattern))
                    if matches!(op.stmt, MonoidStmtType::Have) =>
                {
                    let verus_syn::Pat::Ident(binding)=&**pattern else {
                        return Err(Error::new(*span,"bound Have requires one identifier"));
                    };
                    if out.have_bindings.insert(n.to_string(),binding.ident.clone()).is_some(){
                        return Err(Error::new(n.span(),"duplicate bound Have on one field"));
                    }
                    out.special.push((n.clone(),op.clone()));
                }
                SplitKind::Special(n, op, _, Some(pattern))
                    if matches!(op.stmt, MonoidStmtType::Withdraw) =>
                {
                    let verus_syn::Pat::Ident(binding) = &**pattern else {
                        return Err(Error::new(
                            *span,
                            "bound optional withdrawal requires one identifier",
                        ));
                    };
                    if out
                        .withdrawals
                        .insert(n.to_string(), binding.ident.clone())
                        .is_some()
                    {
                        return Err(Error::new(n.span(), "duplicate withdrawal binding"));
                    }
                    out.special.push((n.clone(), op.clone()));
                }
                _ => {
                    return Err(Error::new(
                        *span,
                        "heterogeneous facade requires straight-line unbound singleton operations",
                    ))
                }
            }
            for x in xs {
                collect(x, out)?
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "unsupported heterogeneous facade statement",
            ))
        }
    }
    Ok(())
}
fn names(tokens: TokenStream, out: &mut HashSet<String>) {
    for token in tokens {
        match token {
            proc_macro2::TokenTree::Ident(n) => {
                out.insert(n.to_string());
            }
            proc_macro2::TokenTree::Group(g) => names(g.stream(), out),
            _ => {}
        }
    }
}
pub(crate) fn fresh(sm: &SM, tr: &Transition, label: &str) -> Ident {
    let mut unavailable: HashSet<String> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .collect();
    let generics = &sm.generics;
    names(quote! {#generics}, &mut unavailable);
    let original_fields=&sm.fields_named_ast;
    names(quote! {#original_fields}, &mut unavailable);
    let mut ops = Ops::default();
    let _ = collect(&tr.body, &mut ops);
    for e in ops
        .initial
        .values()
        .chain(ops.updates.values())
        .chain(ops.requires.iter())
        .chain(ops.asserts.iter())
        .chain(ops.bindings.iter().map(|(_, e)| e))
    {
        names(quote! {#e}, &mut unavailable)
    }
    for (b, _) in ops.bindings {
        unavailable.insert(b.to_string());
    }
    for binding in ops.withdrawals.values().chain(ops.have_bindings.values()) {
        unavailable.insert(binding.to_string());
    }
    for (_, op) in ops.special {
        match op.elt {
            MonoidElt::General(e)
            | MonoidElt::SingletonSet(e)
            | MonoidElt::SingletonMultiset(e) => names(quote! {#e}, &mut unavailable),
            MonoidElt::OptionSome(Some(e)) => names(quote! {#e}, &mut unavailable),
            MonoidElt::SingletonKV(key,value) => names(quote!{#key #value},&mut unavailable),
            _ => {}
        }
    }
    let unavailable: HashSet<String> = unavailable
        .into_iter()
        .map(|name| name.strip_prefix("r#").unwrap_or(&name).to_owned())
        .collect();
    for suffix in 0usize.. {
        let candidate = format!("__tsm_roles_{label}_{suffix}");
        if !unavailable.contains(&candidate) {
            return Ident::new(&candidate, Span::mixed_site());
        }
    }
    unreachable!()
}
pub(crate) fn footprint(
    e: &Expr,
    fields: &HashMap<String, Field>,
    used: &mut HashSet<String>,
) -> Result<(), Error> {
    let mut e = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut e,
        |_, f, _| {
            used.insert(f.name.to_string());
        },
        &mut errors,
        fields,
    );
    if let Some(e) = errors.into_iter().next() {
        return Err(e);
    }
    Ok(())
}
pub(crate) fn lower(
    e: &Expr,
    fields: &HashMap<String, Field>,
    values: &HashMap<String, TokenStream>,
) -> Result<TokenStream, Error> {
    let mut e = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut e,
        |errors, f, node| {
            if let Some(value) = values.get(&f.name.to_string()) {
                *node = Expr::Verbatim(value.clone());
            } else {
                errors.push(Error::new(
                    f.name.span(),
                    "heterogeneous expression requires a supplied actual role observation",
                ));
            }
        },
        &mut errors,
        fields,
    );
    if let Some(e) = errors.into_iter().next() {
        return Err(e);
    }
    Ok(quote! {#e})
}
pub fn output(sm: &SM, selected: &HashSet<String>) -> Result<TokenStream, Error> {
    output_mode(sm,selected,false)
}
/// Private component gate; emits the real complete schema and initializer only.
pub fn initializer_output(sm:&SM)->Result<TokenStream,Error>{output_mode(sm,&HashSet::new(),true)}
fn output_mode(sm:&SM,_selected:&HashSet<String>,initializer_only:bool)->Result<TokenStream,Error>{
    let storage: Vec<_> = sm.fields.iter().filter(|f| f.stype.is_storage()).collect();
    if storage.len()!=2 || !storage.iter().any(|field|matches!(field.stype,ShardableType::StorageMap(..)))
        || !storage.iter().any(|field|matches!(field.stype,ShardableType::StorageOption(_))) {
        return Err(Error::new(sm.name.span(),"wide physical roles require one finite Map and one Option store"));
    }
    let carrier_args=sm.generics.as_ref().map(|g|get_generic_args(&g.params));
    let carrier_fragment=carrier_args.as_ref().map(|args|quote!{Fragment<#args>}).unwrap_or_else(||quote!{Fragment});
    let carrier=crate::verified_storage_carrier::Carrier::build(sm,carrier_fragment)?.ok_or_else(||
        Error::new(sm.name.span(),"wide physical roles require checked tagged carrier"))?;
    let constants: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(_)))
        .collect();
    let ordinary: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| !f.stype.is_storage() && !matches!(f.stype, ShardableType::Constant(_)))
        .collect();
    let (g, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&g);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let token = quote! {Token #types};
    let metadata_name=fresh(sm,&sm.transitions[0],"native_metadata");
    let metadata = quote! {#metadata_name #types};
    let descriptor = quote! {::vstd::resource::tsm_context::Descriptor<#metadata>};
    let location = format_ident!("protocol_location");
    let marker = args
        .as_ref()
        .map(|a| quote! {ghost marker:core::marker::PhantomData<(#a,)>,});
    let markerv = args
        .as_ref()
        .map(|_| quote! {marker:core::marker::PhantomData,});
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
    let mut wrappers = vec![];
    for f in &ordinary {
        wrappers.push(roles::wide_wrapper(f, &cx)?);
        if !initializer_only&&matches!(f.stype,ShardableType::Option(_)|ShardableType::Bool|ShardableType::Variable(_)){
            let n=&f.name;let unique=crate::verified_field_storage_unique::method(sm,f,&cx)?;
            wrappers.push(quote!{impl #decl #n #types #wc{#unique}});
        }
        if !initializer_only&&matches!(f.stype,ShardableType::Variable(_)|ShardableType::PersistentOption(_)|ShardableType::PersistentMap(..)){
            let n=&f.name;let agree=crate::verified_field_storage_unique::agree(sm,f,&cx)?;
            wrappers.push(quote!{impl #decl #n #types #wc{#agree}});
        }
        if matches!(f.stype,ShardableType::Count){
            let n=&f.name;
            let split=roles::count_split_method(f,&cx)?;
            let join=roles::count_join_method(f,&cx)?;
            wrappers.push(quote!{impl #decl #n #types #wc{#split #join}});
        }
        if matches!(f.stype,ShardableType::Set(_)|ShardableType::Multiset(_)){
            wrappers.push(crate::verified_field_storage_collections::wrapper(f,&cx,&quote!{#original_fields})?);
            if let ShardableType::Set(element)=&f.stype {
                let collection=format_ident!("{}_collection",f.name);
                let original_alias=format_ident!("{}_set",f.name);
                let parameter=fresh(sm,&sm.transitions[0],&format!("legacy_set_element_{}",f.name));
                wrappers.push(quote!{
                    pub type #original_alias #decl #wc = #collection #types;
                    impl #decl #collection #types #wc {
                        pub open spec fn contains(&self,#parameter:#element)->bool {
                            self.set().contains(#parameter)
                        }
                    }
                });
            }
            if !initializer_only {
                let singleton=&f.name;let collection=format_ident!("{singleton}_collection");
                let (access,description)=if matches!(f.stype,ShardableType::Set(_)){
                    (format_ident!("set"),quote!{::vstd::set::Set::empty().insert(single.element())})
                }else{
                    (format_ident!("multiset"),quote!{::vstd::multiset::Multiset::singleton(single.element())})
                };
                wrappers.push(quote!{
                    impl #decl #collection #types #wc {
                        pub proof fn from_singleton(tracked single:#singleton #types)->(tracked out:Self)
                            ensures out.instance_id()==single.instance_id(),
                                out.#access()==#description,
                        {
                            ::vstd::prelude::use_type_invariant(&single);
                            let elements=#description;
                            let tracked metadata=single.metadata;
                            let tracked token=single.raw.get().tracked_unwrap();
                            Self::__from_token(token,metadata,elements)
                        }
                    }
                });
            }
        }
        if matches!(f.stype,ShardableType::PersistentSet(_)){
            wrappers.push(crate::verified_field_storage_persistent_sets::wrapper(f,&cx,&quote!{#original_fields})?);
        }
        if matches!(f.stype,ShardableType::PersistentMap(..)){
            wrappers.push(crate::verified_field_storage_maps::wrapper(f,&cx,&quote!{#original_fields})?);
        }
        if matches!(f.stype,ShardableType::PersistentBool|ShardableType::PersistentOption(_)
            |ShardableType::PersistentSet(_)|ShardableType::PersistentMap(..)){
            let n=&f.name;
            let clone=roles::persistent_clone_method(f,&cx)?;
            wrappers.push(quote!{impl #decl #n #types #wc{#clone}});
        }
    }

    let constant_facts=initial_constant_facts(sm)?;
    let mut methods = vec![];
    if !initializer_only {
        methods.push(crate::verified_field_storage_wide_transitions::empty_lift_helper(sm).1);
    }
    for tr in &sm.transitions {
        let mut ops = Ops::default();
        collect(&tr.body, &mut ops)?;
        if tr.kind == TransitionKind::Init {
            methods.push(wide_initializer(sm,tr,&ops,&cx,&carrier)?);
        } else if initializer_only {
            continue;
        } else if tr.kind == TransitionKind::Property {
            continue;
        } else {
            methods.push(crate::verified_field_storage_wide_transitions::methods(sm,tr,&ops,&cx,&carrier)?);
        }
    }
    if !initializer_only {methods.push(crate::verified_field_storage_properties::methods(sm,&cx)?);}
    let info_id = fresh(sm, &sm.transitions[0], "info_instance_id");
    let info_marker = args
        .as_ref()
        .map(|a| quote! {pub ghost marker:core::marker::PhantomData<(#a,)>,});
    Ok(
        quote! {#(#attrs)*pub ghost struct InstanceInfo #decl #wc{pub #info_id: ::vstd::resource::Loc,#(pub #cn:#ct,)*#info_marker}impl #decl InstanceInfo #types #wc{pub open spec fn id(&self)->::vstd::resource::Loc{self.#info_id}#(pub open spec fn #cn(&self)->#ct{self.#cn})*}#(#attrs)*struct #metadata_name #decl #wc{ghost protocol_location: ::vstd::resource::Loc,#(ghost #cn:#ct,)*#marker}#(#wrappers)*#(#attrs)*pub tracked struct Instance #decl #wc{metadata:#descriptor,context:Tracked<Option<#token>>}impl #decl Instance #types #wc{#[verifier::type_invariant]spec fn invariant(self)->bool{self.__initial_constants()&&::vstd::prelude::imply(self.context@ is Some,self.context@->Some_0.loc()==self.metadata.value().protocol_location&&self.context@->Some_0.fragment()==Fragment #expr::empty()#(.#setters(self.metadata.value().#cn))*)}pub open spec fn __initial_constants(&self)->bool{true #(&&(#constant_facts))*}pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}#(pub closed spec fn #cn(&self)->#ct{self.metadata.value().#cn})*pub open spec fn info(&self)->InstanceInfo #types{InstanceInfo #expr{#info_id:self.id(),#(#cn:self.#cn(),)*#markerv}}pub proof fn clone(tracked &self)->(tracked out:Self)ensures out.id()==self.id(),out.info()==self.info(),#(out.#cn()==self.#cn(),)*{::vstd::prelude::use_type_invariant(self);Self{metadata:self.metadata.clone(),context:Tracked(None)}}#(#methods)*}},
    )
}
/// Finite collection roles preserve the original field representation. The
/// scalar/singleton distinction follows the original monoid operand syntax.
pub(crate) fn role_type(field:&Field,operand:Option<&MonoidElt>)->Ident{
    match (&field.stype,operand){
        (ShardableType::Set(_)|ShardableType::PersistentSet(_)|ShardableType::Multiset(_)
            |ShardableType::PersistentMap(..),None|Some(MonoidElt::General(_)))=>
            format_ident!("{}_collection",field.name),
        _=>field.name.clone(),
    }
}
pub(crate) fn role_observation(field:&Field,operand:Option<&MonoidElt>,owner:TokenStream)->TokenStream{
    match &field.stype{
        ShardableType::Count=>quote!{#owner.count()},
        ShardableType::Set(_)|ShardableType::PersistentSet(_) =>
            if operand.is_none()||matches!(operand,Some(MonoidElt::General(_))){quote!{#owner.set()}}
            else{quote!{::vstd::set::Set::empty().insert(#owner.element())}},
        ShardableType::Multiset(_)=>
            if operand.is_none()||matches!(operand,Some(MonoidElt::General(_))){quote!{#owner.multiset()}}
            else{quote!{::vstd::multiset::Multiset::singleton(#owner.element())}},
        ShardableType::PersistentMap(..)=>
            if operand.is_none()||matches!(operand,Some(MonoidElt::General(_))){quote!{#owner.map()}}
            else{quote!{::vstd::map::Map::empty().insert(#owner.key(),#owner.value())}},
        ShardableType::Option(_)|ShardableType::PersistentOption(_)=>quote!{Some(#owner.value())},
        _=>quote!{#owner.value()},
    }
}

/// Initialize all original logical fields by selecting and splitting real
/// fragments from the initialized physical protocol; physical arguments are
/// packed through the checked per-field tagged helpers.
fn wide_initializer(sm:&SM,tr:&Transition,ops:&Ops,cx:&roles::Context<'_>,carrier:&crate::verified_storage_carrier::Carrier)
    ->Result<TokenStream,Error>{
    let types=cx.types;let expr=cx.expr;
    let metadata_name=fresh(sm,&sm.transitions[0],"native_metadata");
    let key=&carrier.key;let val=&carrier.value;
    let name=&tr.name;let strong=format_ident!("{name}_strong");
    let params:Vec<_>=tr.params.iter().map(|p|{let n=&p.name;let t=&p.ty;quote!{#n:#t}}).collect();
    let pn:Vec<_>=tr.params.iter().map(|p|&p.name).collect();
    let cn:Vec<_>=cx.constants.iter().map(|f|&f.name).collect();
    let cv:Vec<_>=cn.iter().map(|n|&ops.initial[&n.to_string()]).collect();
    let setters:Vec<_>=cn.iter().map(|n|format_ident!("with_{n}")).collect();
    let remaining=fresh(sm,tr,"initial_remaining");let descriptor=fresh(sm,tr,"initial_metadata");
    let deposited=fresh(sm,tr,"initial_deposited");let state=fresh(sm,tr,"initial_state");
    let mut inputs=vec![];let mut pre=vec![];let mut pack=vec![];
    for field in sm.fields.iter().filter(|f|f.stype.is_storage()){
        let n=&field.name;let value=&ops.initial[&n.to_string()];
        let actual=fresh(sm,tr,&format!("initial_actual_{n}"));
        let packed=fresh(sm,tr,&format!("initial_packed_{n}"));
        let pack_fn=format_ident!("__pack_{n}");let ty=field.get_type();
        inputs.push(quote!{tracked #actual:#ty});pre.push(quote!{#actual==#value});
        pack.push(quote!{let tracked #packed=<#key>::#pack_fn(#actual);#deposited.tracked_union_prefer_right(#packed);});
    }
    let mut outputs=vec![];let mut values=vec![];let mut post=vec![];let mut splits=vec![];
    for (index,field) in sm.fields.iter().filter(|f|!f.stype.is_storage()&&!matches!(f.stype,ShardableType::Constant(_))).enumerate(){
        let n=&field.name;let value=&ops.initial[&n.to_string()];let ix=verus_syn::Index::from(index+1);
        let optional=matches!(field.stype,ShardableType::Option(_)|ShardableType::PersistentOption(_)|ShardableType::Bool|ShardableType::PersistentBool);
        let (present,args,observation)=match &field.stype{
            ShardableType::Bool|ShardableType::PersistentBool=>{
                let Expr::Lit(verus_syn::ExprLit{lit:verus_syn::Lit::Bool(literal),..})=value else{
                    return Err(Error::new(n.span(),"wide Bool initializer requires literal bool"));
                };
                (literal.value,quote!{},quote!{value})
            },
            ShardableType::Option(_)|ShardableType::PersistentOption(_)=>{
                let mut v=value;loop{match v{Expr::Paren(p)=>v=&p.expr,Expr::Group(g)=>v=&g.expr,_=>break}}
                if matches!(v,Expr::Path(path)if path.path.is_ident("None")){(false,quote!{},quote!{value})}
                else{
                    let Expr::Call(call)=v else{return Err(Error::new(n.span(),"wide Option initializer requires Some or None"));};
                    if call.args.len()!=1||!matches!(&*call.func,Expr::Path(path)if path.path.segments.last().is_some_and(|s|s.ident=="Some")){
                        return Err(Error::new(n.span(),"wide Option initializer requires Some or None"));
                    }
                    let element=&call.args[0];(true,quote!{,#element},quote!{value})
                }
            },
            ShardableType::Set(_)|ShardableType::PersistentSet(_)=>(true,quote!{,#value},quote!{set}),
            ShardableType::Multiset(_)=>(true,quote!{,#value},quote!{multiset}),
            ShardableType::PersistentMap(..)=>(true,quote!{,#value},quote!{map}),
            ShardableType::Count=>(true,quote!{},quote!{count}),
            ShardableType::Variable(_)=>(true,quote!{},quote!{value}),
            _=>return Err(Error::new(n.span(),"unsupported wide initial role")),
        };
        let role=role_type(field,None);let select=format_ident!("select_{n}");let without=format_ident!("without_{n}");
        let law=format_ident!("take_{n}_law");let part=fresh(sm,tr,&format!("initial_part_{n}"));
        let rest=fresh(sm,tr,&format!("initial_rest_{n}"));let owner=fresh(sm,tr,&format!("initial_owner_{n}"));
        outputs.push(if optional{quote!{Tracked<Option<#role #types>>}}else{quote!{Tracked<#role #types>}});
        if present{
            splits.push(quote!{#remaining.fragment().#law();let #part=#remaining.fragment().#select()#(.#setters(#cv))*;
                let #rest=#remaining.fragment().#without();assert(Fragment #expr::op(#part,#rest)==#remaining.fragment());
                let tracked(#owner,#remaining)=#remaining.split(#part,#rest);
                let tracked #owner=<#role #types>::__from_token(#owner,#descriptor.clone()#args);});
            if optional{
                values.push(quote!{Tracked(Some(#owner))});post.push(quote!{out.#ix@ is Some});
                post.push(quote!{out.#ix@->Some_0.instance_id()==out.0@.id()});
                if matches!(field.stype,ShardableType::Option(_)|ShardableType::PersistentOption(_)){
                    post.push(quote!{Some(out.#ix@->Some_0.value())==#value});
                }else{post.push(quote!{out.#ix@->Some_0.value()==#value});}
            }else{
                values.push(quote!{Tracked(#owner)});post.push(quote!{out.#ix@.instance_id()==out.0@.id()});
                post.push(quote!{out.#ix@.#observation()==#value});
            }
        }else{values.push(quote!{Tracked(None)});post.push(quote!{out.#ix@ is None});}
    }
    let marker=if sm.generics.is_some(){quote!{marker:core::marker::PhantomData,}}else{quote!{}};
    let requires=&ops.requires;
    Ok(quote!{
        pub proof fn #name(#(#params,)*#(#inputs),*)->(tracked out:(Tracked<Self>,#(#outputs),*))
            requires #(#pre,)*#(#requires,)*
            ensures #(#post,)*#(out.0@.#cn()==#cv,)*
        {
            let tracked mut #deposited=IMap::<#key,#val>::tracked_empty();#(#pack)*
            assert forall|#state:State #types|State #expr::#strong(#state,#(#pn),*) implies #deposited==#state.__storage() by{};
            let tracked #remaining=Protocol #expr::#name(#deposited,#(#pn),*);
            let tracked #descriptor=::vstd::resource::tsm_context::Descriptor::alloc(#metadata_name #expr{
                protocol_location:#remaining.loc(),#(#cn:#cv,)*#marker});
            #(#splits)*
            (Tracked(Self{metadata:#descriptor.clone(),context:Tracked(Some(#remaining))}),#(#values),*)
        }
    })
}

/// Cache only initializer requirements whose parameters are direct immutable
/// constants. The value grants no protocol rights; initialization proves it,
/// metadata cloning preserves it, and mutable logical/physical operations
/// still require actual role ownership.
fn initial_constant_facts(sm:&SM)->Result<Vec<TokenStream>,Error>{
    let initializers:Vec<_>=sm.transitions.iter().filter(|tr|tr.kind==TransitionKind::Init).collect();
    if initializers.len()!=1{return Err(Error::new(sm.name.span(),"wide metadata requires one original initializer"));}
    let tr=initializers[0];let mut ops=Ops::default();collect(&tr.body,&mut ops)?;
    let parameters:HashSet<_>=tr.params.iter().map(|p|p.name.to_string()).collect();
    let mut constants=HashMap::new();
    for field in sm.fields.iter().filter(|f|matches!(f.stype,ShardableType::Constant(_))){
        let mut value=&ops.initial[&field.name.to_string()];
        loop{match value{Expr::Paren(p)=>value=&p.expr,Expr::Group(g)=>value=&g.expr,_=>break}}
        if let Expr::Path(path)=value{
            if let Some(param)=path.path.get_ident().filter(|n|parameters.contains(&n.to_string())){
                let n=&field.name;constants.insert(param.to_string(),quote!{self.#n()});
            }
        }
    }
    struct Lower<'a>{parameters:&'a HashSet<String>,constants:&'a HashMap<String,TokenStream>,unsupported:bool}
    impl verus_syn::visit_mut::VisitMut for Lower<'_>{
        fn visit_expr_mut(&mut self,expr:&mut Expr){
            if let Expr::Path(path)=expr{
                if let Some(name)=path.path.get_ident(){
                    if let Some(value)=self.constants.get(&name.to_string()){
                        *expr=Expr::Verbatim(value.clone());return;
                    }else if self.parameters.contains(&name.to_string()){self.unsupported=true;}
                }
            }
            // Bound names are intentionally excluded from immutable caching;
            // their original obligations remain in the initializer API.
            if matches!(expr,Expr::Closure(_)){self.unsupported=true;return;}
            verus_syn::visit_mut::visit_expr_mut(self,expr);
        }
    }
    use verus_syn::visit_mut::VisitMut;
    let mut result=vec![];
    for condition in ops.requires{
        let mut condition=condition;
        let mut lower=Lower{parameters:&parameters,constants:&constants,unsupported:false};
        lower.visit_expr_mut(&mut condition);
        if !lower.unsupported{result.push(quote!{#condition});}
    }
    Ok(result)
}

