//! Complete logical set-to-persistent-set transfers with actual Variable authority.
use crate::ast::*;
use crate::field_access_visitor::visit_field_accesses;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

pub fn supports(sm: &SM) -> bool {
    sm.fields.len() == 4
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::Constant(_)))
            .count()
            == 1
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::Variable(_)))
            .count()
            == 1
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::ISet(_)))
            .count()
            == 1
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::PersistentISet(_)))
            .count()
            == 1
}
#[derive(Default)]
struct Flat {
    ops: Vec<(Ident, SpecialOp)>,
    req: Vec<Expr>,
    assert: Vec<Expr>,
    update: Vec<(Ident, Expr)>,
}
fn collect(s: &TransitionStmt, f: &mut Flat) -> Result<(), Error> {
    match s {
        TransitionStmt::Block(_, ss) => {
            for s in ss {
                collect(s, f)?;
            }
        }
        TransitionStmt::Require(_, e) => f.req.push(e.clone()),
        TransitionStmt::Assert(_, e, _) => f.assert.push(e.clone()),
        TransitionStmt::Update(_, n, e) => f.update.push((n.clone(), e.clone())),
        TransitionStmt::Split(span, k, ss) => {
            let SplitKind::Special(n, op, _, None) = &**k else {
                return Err(Error::new(
                    *span,
                    "set transfer facade requires unbound operations",
                ));
            };
            f.ops.push((n.clone(), op.clone()));
            for s in ss {
                collect(s, f)?;
            }
        }
        _ => {
            return Err(Error::new(
                *s.get_span(),
                "set transfer facade requires straight-line operations",
            ))
        }
    }
    Ok(())
}
fn reserve(t: TokenStream, n: &mut HashSet<String>) {
    for t in t {
        match t {
            TokenTree::Ident(i) => {
                n.insert(i.to_string().trim_start_matches("r#").to_string());
            }
            TokenTree::Group(g) => reserve(g.stream(), n),
            _ => {}
        }
    }
}
fn names(sm: &SM) -> HashSet<String> {
    let mut n = HashSet::new();
    let fields = &sm.fields_named_ast;
    let generics = &sm.generics;
    reserve(quote! {#fields #generics}, &mut n);
    for tr in &sm.transitions {
        n.insert(tr.name.to_string().trim_start_matches("r#").to_string());
        for p in &tr.params {
            let name = &p.name;
            let ty = &p.ty;
            reserve(quote! {#name #ty}, &mut n);
        }
        crate::verified_field_storage_map_pair::reserve_stmt(&tr.body, &mut n);
    }
    n
}
fn fresh(n: &mut HashSet<String>, label: &str) -> Ident {
    let mut s = format!("__tsm_top_sort_{label}");
    while n.contains(&s) {
        s.push('_');
    }
    n.insert(s.clone());
    Ident::new(&s, Span::mixed_site())
}
fn lower(sm: &SM, e: &Expr, map: &HashMap<String, TokenStream>) -> Result<Expr, Error> {
    let fields = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let mut e = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut e,
        |errors, field, node| {
            if let Some(t) = map.get(&field.name.to_string()) {
                *node = verus_syn::parse2(t.clone()).unwrap();
            } else {
                errors.push(Error::new(
                    field.name.span(),
                    "set transfer reads an unsupplied field",
                ));
            }
        },
        &mut errors,
        &fields,
    );
    if let Some(e) = errors.into_iter().next() {
        Err(e)
    } else {
        Ok(e)
    }
}
pub fn aliases(sm: &SM) -> Result<TokenStream, Error> {
    let (g, _) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&g);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let mut out = vec![];
    for f in sm.fields.iter().filter(|f| {
        matches!(
            f.stype,
            ShardableType::ISet(_) | ShardableType::PersistentISet(_)
        )
    }) {
        let alias = format_ident!("{}_set", f.name);
        let bulk = format_ident!("{}_collection", f.name);
        let key = match &f.stype {
            ShardableType::ISet(k) | ShardableType::PersistentISet(k) => k,
            _ => unreachable!(),
        };
        if sm.fields.iter().any(|f| {
            f.name.to_string().trim_start_matches("r#")
                == alias.to_string().trim_start_matches("r#")
        }) {
            return Err(Error::new(
                alias.span(),
                "set alias conflicts with an original field",
            ));
        }
        if let Some(g) = &sm.generics {
            for p in &g.params {
                let id = match p {
                    verus_syn::GenericParam::Type(t) => Some(&t.ident),
                    verus_syn::GenericParam::Const(t) => Some(&t.ident),
                    _ => None,
                };
                if id.is_some_and(|id| {
                    id.to_string().trim_start_matches("r#")
                        == alias.to_string().trim_start_matches("r#")
                }) {
                    return Err(Error::new(
                        alias.span(),
                        "set alias conflicts with an original generic parameter",
                    ));
                }
            }
        }
        out.push(quote! {#[allow(non_camel_case_types)]pub type #alias #decl #wc=#bulk #types;});
    }
    Ok(quote! {#(#out)*})
}

pub fn method(sm: &SM, tr: &Transition) -> Result<TokenStream, Error> {
    let mut f = Flat::default();
    collect(&tr.body, &mut f)?;
    if !f.req.is_empty() {
        return Err(Error::new(
            tr.name.span(),
            "set transfer facade does not yet lower explicit requirements",
        ));
    }
    if tr.kind != TransitionKind::Property && !f.assert.is_empty() {
        return Err(Error::new(
            tr.name.span(),
            "set transfer facade does not yet lower transition assertions",
        ));
    }
    let var = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::Variable(_)))
        .unwrap();
    let constant = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::Constant(_)))
        .unwrap();
    let ordinary = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::ISet(_)))
        .unwrap();
    let persistent = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::PersistentISet(_)))
        .unwrap();
    let (vn, cn, on, pn) = (&var.name, &constant.name, &ordinary.name, &persistent.name);
    let (g, _) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&g);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let key = match &ordinary.stype {
        ShardableType::ISet(k) => k,
        _ => unreachable!(),
    };
    let variable_type = var.get_type();
    let bulk = format_ident!("{}_collection", pn);
    let vfactory = format_ident!("field_{vn}");
    let pfactory = format_ident!("field_{pn}");
    let ofactory = format_ident!("field_{on}");
    let vgetter = format_ident!("value_{vn}");
    let vowns = format_ident!("owns_{vn}");
    let takev = format_ident!("take_{vn}");
    let takep = format_ident!("take_{pn}");
    let name = &tr.name;
    let req = format_ident!("{name}_requires");
    let enabled = format_ident!("{name}_enabled");
    let owners = format_ident!("{name}_owners_enabled");
    let strong = format_ident!("{name}_strong");
    let safety = format_ident!("{name}_safety");
    let post_owned = format_ident!("{name}_owned_post");
    let adapter = format_ident!("__field_{name}_with_observation");
    let params: Vec<_> = tr
        .params
        .iter()
        .map(|p| {
            let n = &p.name;
            let t = &p.ty;
            quote! {#n:#t}
        })
        .collect();
    let args: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let mut n = names(sm);
    let input = fresh(&mut n, "unvisited");
    let observed = fresh(&mut n, "visited");
    let variable = fresh(&mut n, "variable");
    let slot = fresh(&mut n, "slot");
    let helper = fresh(
        &mut n,
        &format!("raw_{}", name.to_string().trim_start_matches("r#")),
    );
    let native = fresh(&mut n, "native");
    let owned = fresh(&mut n, "owned");
    let shared = fresh(&mut n, "shared");
    let before = fresh(&mut n, "before");
    let next = fresh(&mut n, "next");
    let outer = fresh(&mut n, "outer");
    let pre = fresh(&mut n, "pre");
    let post = fresh(&mut n, "post");
    let frame = fresh(&mut n, "lower_frame");
    let point = fresh(&mut n, "point");
    let tmp = fresh(&mut n, "temporary");
    let out = fresh(&mut n, "out");
    let remain = fresh(&mut n, "remaining");
    let middle = fresh(&mut n, "middle");
    let included = fresh(&mut n, "included_transitive");
    let left = fresh(&mut n, "included_left");
    let mid = fresh(&mut n, "included_middle");
    let right = fresh(&mut n, "included_right");
    let lf = fresh(&mut n, "included_left_frame");
    let rf = fresh(&mut n, "included_right_frame");
    let target = fresh(&mut n, "shared_target");
    let upper_state = fresh(&mut n, "upper_state");
    let upper_outer = fresh(&mut n, "upper_outer");
    let context_frame = fresh(&mut n, "context_frame");
    let source_frame = fresh(&mut n, "source_frame");
    let inclusion_helper = quote! {
        proof fn #included(#left:Fragment #types,#mid:Fragment #types,#right:Fragment #types)
            requires ::vstd::resource::tsm::fragment_included::<Protocol #types>(#left,#mid),::vstd::resource::tsm::fragment_included::<Protocol #types>(#mid,#right),
            ensures ::vstd::resource::tsm::fragment_included::<Protocol #types>(#left,#right),
        {let #lf=choose|#lf:Fragment #types|Fragment #expr::op(#left,#lf)==#mid;let #rf=choose|#rf:Fragment #types|Fragment #expr::op(#mid,#rf)==#right;Fragment #expr::associative(#left,#lf,#rf);assert(Fragment #expr::op(#left,Fragment #expr::op(#lf,#rf))==#right);}
    };
    let mut public = HashMap::new();
    public.insert(cn.to_string(), quote! {self.#cn()});
    public.insert(
        vn.to_string(),
        if tr.kind == TransitionKind::Property {
            quote! {#variable.value()}
        } else {
            quote! {old(#variable).value()}
        },
    );
    let mut local = HashMap::new();
    local.insert(cn.to_string(), quote! {self.#cn()});
    local.insert(vn.to_string(), quote! {#native});
    let have = f
        .ops
        .iter()
        .find(|(field, op)| *field == *pn && matches!(op.stmt, MonoidStmtType::Have))
        .ok_or_else(|| Error::new(name.span(), "set transfer needs a borrowed persistent set"))?;
    let MonoidElt::General(have) = &have.1.elt else {
        return Err(Error::new(
            name.span(),
            "set transfer requires a general persistent Have",
        ));
    };
    let have_public = lower(sm, have, &public)?;
    let have_local = lower(sm, have, &local)?;
    let observed_facts = quote! {
        if #observed.has_resource(){
            let #frame=Self::__lower_completion(#before,#shared.fragment(),#outer,#observed.raw@->Some_0.fragment(),#pre);
            assert forall|#point:#key|#[trigger]#observed.set().contains(#point) implies #pre.#pn.contains(#point) by{
                ::vstd::resource::tsm_collections::persistent_set_owned_frame(#observed.raw@->Some_0.fragment().#pn,#frame.#pn,#pre.#pn,#point);
            }
        }else{assert(#observed.set()==ISet::empty());}
        assert((#have_local).subset_of(#pre.#pn));
        assert forall|#point:#key|#[trigger](#have_local).contains(#point) implies Fragment #expr::op(#before,#shared.fragment()).#pn.at(#point)==Some(::vstd::resource::agree::AgreementRA::Agree(())) by{
            if #observed.has_resource(){
                let #frame=choose|#frame:Fragment #types|Fragment #expr::op(#observed.raw@->Some_0.fragment(),#frame)==#shared.fragment();
                assert(#observed.raw@->Some_0.fragment().#pn.at(#point)==Some(::vstd::resource::agree::AgreementRA::Agree(())));
                assert(Fragment #expr::op(Fragment #expr::op(#before,#shared.fragment()),#outer).#pn.at(#point)==Protocol #expr::embed(#pre).#pn.at(#point));
                assert(Fragment #expr::op(#before,#shared.fragment()).#pn.at(#point)==Some(::vstd::resource::agree::AgreementRA::Agree(())));
            }
        }
    };
    if tr.kind == TransitionKind::Property {
        if f.ops.len() != 1 || !f.update.is_empty() {
            return Err(Error::new(
                name.span(),
                "set read property only accepts a borrowed persistent Have",
            ));
        }
        let returns: Vec<_> = f
            .assert
            .iter()
            .map(|e| lower(sm, e, &public))
            .collect::<Result<_, _>>()?;
        return Ok(quote! {
            #inclusion_helper
            pub proof fn #name(tracked &self,#(#params,)*tracked #observed:&#bulk #types,tracked #variable:&#vn #types)
                requires #observed.instance_id()==self.id(),#variable.instance_id()==self.id(),(forall|#point:#key|!#[trigger](#have_public).contains(#point) || #observed.contains(#point)),
                ensures #(#returns,)*
            {
                ::vstd::prelude::use_type_invariant(self);::vstd::prelude::use_type_invariant(#observed);::vstd::prelude::use_type_invariant(#variable);
                assert((#have_public).subset_of(#observed.set()));let #native=#variable.value();let tracked #shared=self.context.observe().join(&#variable.borrow_token().observe());let #middle=#shared.fragment();
                let tracked #shared=if #observed.has_resource(){#shared.join(&#observed.borrow_token().observe())}else{Fragment #expr::op_unit(#middle);assert(Fragment #expr::op(#middle,Fragment #expr::unit())==#middle);#shared};
                Self::#included(#variable.raw.fragment(),#middle,#shared.fragment());
                #shared.validate();let(#pre,#outer)=choose|#pre:State #types,#outer:Fragment #types|#pre.invariant()&&Fragment #expr::op(#shared.fragment(),#outer)==Protocol #expr::embed(#pre);
                let #before=Fragment #expr::unit();Fragment #expr::op_unit(#shared.fragment());Fragment #expr::commutative(#before,#shared.fragment());
                let #frame=Self::__lower_completion(#before,#shared.fragment(),#outer,#variable.raw.fragment(),#pre);
                ::vstd::resource::tsm_collections::option_owned_frame(#variable.raw.fragment().#vn,#frame.#vn,Some(#pre.#vn),#native);
                #observed_facts
                assert(#pre.#cn==self.#cn());assert(State #expr::#enabled(#pre,#(#args),*));State #expr::#safety(#pre,#(#args),*);
            }
        });
    }
    let remove = f
        .ops
        .iter()
        .find(|(field, op)| *field == *on && matches!(op.stmt, MonoidStmtType::Remove))
        .ok_or_else(|| {
            Error::new(
                name.span(),
                "set transfer needs consumed ordinary ownership",
            )
        })?;
    let add = f
        .ops
        .iter()
        .find(|(field, op)| *field == *pn && matches!(op.stmt, MonoidStmtType::Add(_)))
        .ok_or_else(|| {
            Error::new(
                name.span(),
                "set transfer needs produced persistent ownership",
            )
        })?;
    if f.ops.len() != 3 || f.update.len() != 1 || f.update[0].0 != *vn {
        return Err(Error::new(
            name.span(),
            "set transfer requires one paired set transfer and one Variable update",
        ));
    }
    let (MonoidElt::SingletonSet(remove), MonoidElt::SingletonSet(add)) =
        (&remove.1.elt, &add.1.elt)
    else {
        return Err(Error::new(
            name.span(),
            "set transfer requires singleton Remove/Add",
        ));
    };
    let removed_public = lower(sm, remove, &public)?;
    let removed_local = lower(sm, remove, &local)?;
    let added_public = lower(sm, add, &public)?;
    let added_local = lower(sm, add, &local)?;
    let updated_public = lower(sm, &f.update[0].1, &public)?;
    let updated_local = lower(sm, &f.update[0].1, &local)?;
    Ok(quote! {
        proof fn #helper(tracked &self,#(#params,)*#native:#variable_type,tracked #input:#on #types,tracked #observed:&#bulk #types,tracked #slot:&mut Token #types)->(tracked #out:#pn #types)
            requires #input.instance_id()==self.id(),#observed.instance_id()==self.id(),old(#slot).loc()==self.id(),old(#slot).fragment().#vowns(),old(#slot).fragment().#vgetter()==#native,old(#slot).fragment()==Fragment #expr::#vfactory(old(#slot).fragment().#vgetter()),
                #input.element()==#removed_local,(#have_local).subset_of(#observed.set()),
            ensures final(#slot).loc()==self.id(),final(#slot).fragment().#vgetter()==#updated_local,final(#slot).fragment().#vowns(),final(#slot).fragment()==Fragment #expr::#vfactory(final(#slot).fragment().#vgetter()),#out.instance_id()==self.id(),#out.element()==#added_local,
        {
            ::vstd::prelude::use_type_invariant(self);::vstd::prelude::use_type_invariant(&#input);::vstd::prelude::use_type_invariant(#observed);
            Fragment #expr::op_unit(Fragment #expr::unit());assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());let tracked #owned=self.context.duplicate();let tracked #owned=#owned.join(#input.raw);
            let tracked mut #tmp=#slot.empty();::vstd::modes::tracked_swap(#slot,&mut #tmp);let tracked #owned=#owned.join(#tmp);
            let tracked #shared=if #observed.has_resource(){self.context.observe().join(&#observed.borrow_token().observe())}else{self.context.observe()};
            #shared.validate();
            let (#upper_state,#upper_outer)=choose|#upper_state:State #types,#upper_outer:Fragment #types|#upper_state.invariant()&&Fragment #expr::op(#shared.fragment(),#upper_outer)==Protocol #expr::embed(#upper_state);
            let #context_frame=choose|#context_frame:Fragment #types|Fragment #expr::op(self.context.fragment(),#context_frame)==#shared.fragment();
            assert(#shared.fragment().#cn==self.context.fragment().#cn);
            let #target=if #observed.has_resource(){Fragment #expr::op(self.context.fragment(),#observed.raw@->Some_0.fragment())}else{self.context.fragment()};
            assert forall|#point:#key|#[trigger]Fragment #expr::op(#target,#shared.fragment()).#pn.at(#point)==#shared.fragment().#pn.at(#point) by{
                if #observed.has_resource(){
                    let #source_frame=choose|#source_frame:Fragment #types|Fragment #expr::op(#observed.raw@->Some_0.fragment(),#source_frame)==#shared.fragment();
                    if #observed.set().contains(#point){
                        assert(#observed.raw@->Some_0.fragment().#pn.at(#point)==Some(::vstd::resource::agree::AgreementRA::Agree(())));
                        assert(Fragment #expr::op(#shared.fragment(),#upper_outer).#pn.at(#point)==Protocol #expr::embed(#upper_state).#pn.at(#point));
                        assert(#shared.fragment().#pn.at(#point)==Some(::vstd::resource::agree::AgreementRA::Agree(())));
                    }
                }
            }
            ::vstd::resource::tsm_collections::Pointwise::extensionality(Fragment #expr::op(#target,#shared.fragment()).#pn,#shared.fragment().#pn);
            Fragment #expr::op_unit(#shared.fragment());Fragment #expr::commutative(Fragment #expr::unit(),#shared.fragment());
            assert(Fragment #expr::op(#target,#shared.fragment())==#shared.fragment());
            let tracked #shared=#shared.weaken(#target);
            if #observed.has_resource(){Fragment #expr::commutative(self.context.fragment(),#observed.raw@->Some_0.fragment());assert(::vstd::resource::tsm::fragment_included::<Protocol #types>(#observed.raw@->Some_0.fragment(),#shared.fragment()));}
            let #before=#owned.fragment();
            assert(Protocol #expr::#req(#before,#shared.fragment(),#(#args),*)) by{
                assert forall|#outer:Fragment #types,#pre:State #types|#pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#shared.fragment()),#outer)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#shared.fragment(),#(#args),*) by{
                    Fragment #expr::associative(#before,#shared.fragment(),#outer);
                    ::vstd::resource::tsm_collections::option_owned_frame(#before.#vn,Fragment #expr::op(#shared.fragment(),#outer).#vn,Some(#pre.#vn),#native);
                    ::vstd::resource::tsm_collections::set_owned_frame(#before.#on,Fragment #expr::op(#shared.fragment(),#outer).#on,#pre.#on,#removed_local);
                    #observed_facts
                    assert(#pre.#cn==self.#cn());assert(State #expr::#enabled(#pre,#(#args),*));assert(State #expr::#owners(#pre,#before,#shared.fragment(),#(#args),*));
                }
            }
            let tracked #next=Protocol #expr::#adapter(#owned,&#shared,#(#args),*);
            let(#outer,#pre,#post)=choose|#outer:Fragment #types,#pre:State #types,#post:State #types|#pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#shared.fragment()),#outer)==Protocol #expr::embed(#pre)&&State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()&&#next.fragment()==Protocol #expr::#post_owned(#before,#pre,#post,#(#args),*);
            let tracked (#remain,#next)=Protocol #expr::#takep(#next);
            ::vstd::resource::tsm_collections::Pointwise::extensionality(#remain.fragment().#pn,Fragment #expr::#pfactory(::vstd::iset::ISet::empty().insert(#added_local)).#pn);
            assert(#remain.fragment()==Fragment #expr::#pfactory(::vstd::iset::ISet::empty().insert(#added_local)));
            let tracked(mut #tmp,#next)=Protocol #expr::#takev(#next);::vstd::modes::tracked_swap(#slot,&mut #tmp);
            <#pn #types>::__from_token(#remain,#added_local)
        }
        pub proof fn #name(tracked &self,#(#params,)*tracked #input:#on #types,tracked #observed:&#bulk #types,tracked #variable:&mut #vn #types)->(tracked #out:#pn #types)
            requires #input.instance_id()==self.id(),#observed.instance_id()==self.id(),old(#variable).instance_id()==self.id(),#input.element()==#removed_public,(#have_public).subset_of(#observed.set()),
            ensures final(#variable).instance_id()==self.id(),final(#variable).value()==#updated_public,#out.instance_id()==self.id(),#out.element()==#added_public,
        {::vstd::prelude::use_type_invariant(&*#variable);let #native=#variable.value();Self::#helper(self,#(#args,)*#native,#input,#observed,&mut #variable.raw)}
    })
}
