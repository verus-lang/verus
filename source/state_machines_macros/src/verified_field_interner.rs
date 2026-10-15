//! Native variable authority and persistent entry operations over actual owners.
use crate::ast::*;
use crate::verified_field_logical::{generics, Generics};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident, Pat, Type};

pub fn supports(sm: &SM) -> bool {
    sm.fields.len() == 2
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::Variable(..)))
            .count()
            == 1
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::PersistentIMap(..)))
            .count()
            == 1
}

enum Step {
    Require(Expr),
    Let(Box<Pat>, Option<Box<Type>>, Expr),
    Op(Ident, SpecialOp, Option<Box<Pat>>),
    Assert(Expr),
    Update(Ident, Expr),
}
fn collect(stmt: &TransitionStmt, out: &mut Vec<Step>) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                collect(child, out)?;
            }
        }
        TransitionStmt::Require(_, e) => out.push(Step::Require(e.clone())),
        TransitionStmt::Assert(_, e, _) => out.push(Step::Assert(e.clone())),
        TransitionStmt::Update(_, field, e) => out.push(Step::Update(field.clone(), e.clone())),
        TransitionStmt::Split(_, kind, children) => {
            match &**kind {
                SplitKind::Let(pat, ty, LetKind::Normal, e) => {
                    out.push(Step::Let(pat.clone(), ty.clone(), e.clone()))
                }
                SplitKind::Special(field, op, _, pat) => {
                    out.push(Step::Op(field.clone(), op.clone(), pat.clone()))
                }
                _ => {
                    return Err(Error::new(
                        *stmt.get_span(),
                        "variable/persistent entry facade requires straight-line scoped operations",
                    ))
                }
            }
            for child in children {
                collect(child, out)?;
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "unsupported variable/persistent entry facade statement",
            ))
        }
    }
    Ok(())
}

pub fn method(sm: &SM, tr: &Transition) -> Result<TokenStream, Error> {
    let mut steps = Vec::new();
    collect(&tr.body, &mut steps)?;
    let auth = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::Variable(..)))
        .unwrap();
    let map = sm
        .fields
        .iter()
        .find(|f| matches!(f.stype, ShardableType::PersistentIMap(..)))
        .unwrap();
    let a = &auth.name;
    let m = &map.name;
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let mut reserved: HashSet<String> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .chain(sm.transitions.iter().map(|t| t.name.to_string()))
        .collect();
    fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
        for t in tokens {
            match t {
                TokenTree::Ident(id) => {
                    names.insert(id.to_string());
                }
                TokenTree::Group(g) => reserve(g.stream(), names),
                _ => {}
            }
        }
    }
    if let Some(g) = &sm.generics {
        reserve(quote! {#g}, &mut reserved);
    }
    for step in &steps {
        match step {
            Step::Require(e) | Step::Assert(e) | Step::Update(_, e) => {
                reserve(quote! {#e}, &mut reserved)
            }
            Step::Let(p, t, e) => {
                reserve(quote! {#p #t #e}, &mut reserved);
            }
            Step::Op(_, op, p) => {
                if let Some(p) = p {
                    reserve(quote! {#p}, &mut reserved);
                }
                match &op.elt {
                    MonoidElt::SingletonKV(k, v) => {
                        reserve(quote! {#k}, &mut reserved);
                        if let Some(v) = v {
                            reserve(quote! {#v}, &mut reserved);
                        }
                    }
                    _ => {
                        return Err(Error::new(
                            tr.name.span(),
                            "variable/persistent entry facade requires singleton entries",
                        ))
                    }
                }
            }
        }
    }
    let mut fresh = |label: &str| {
        let mut n = format!("__tsm_variable_persistent_{label}");
        while reserved.contains(&n) {
            n.push('_');
        }
        reserved.insert(n.clone());
        Ident::new(&n, Span::mixed_site())
    };
    let input = fresh("authority");
    let raw = fresh("raw");
    let oldraw = fresh("old_raw");
    let before = fresh("before");
    let after = fresh("after");
    let z = fresh("frame");
    let pre = fresh("pre");
    let post = fresh("post");
    let frame1 = fresh("frame1");
    let frame2 = fresh("frame2");
    let frame3 = fresh("frame3");
    let entry1 = fresh("entry1");
    let entry2 = fresh("entry2");
    let lower = |e: &Expr, value: TokenStream| -> Result<Expr, Error> {
        let mut e = e.clone();
        let mut errors = vec![];
        crate::field_access_visitor::visit_field_accesses(
            &mut e,
            |errors, field, slot| {
                if field.name == *a {
                    *slot = verus_syn::parse2(value.clone()).unwrap();
                } else {
                    errors.push(Error::new(
                        field.name.span(),
                        "native persistent entries expose only current authority reads",
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
    };
    let scoped = |expression: &Expr, value: TokenStream| -> Result<TokenStream, Error> {
        let e = lower(expression, value.clone())?;
        let mut lets = Vec::new();
        for step in &steps {
            if let Step::Let(p, ty, e) = step {
                let e = lower(e, value.clone())?;
                let annotation = ty.as_ref().map(|t| quote! {:#t});
                lets.push(quote! {let #p #annotation = #e;});
            }
        }
        Ok(quote! {{#(#lets)* #e}})
    };
    let requirement = |value: TokenStream| -> Result<TokenStream, Error> {
        let mut tail = quote! {true};
        for step in steps.iter().rev() {
            match step {
                Step::Require(e) => {
                    let e = lower(e, value.clone())?;
                    tail = quote! {(#e) && (#tail)};
                }
                Step::Let(p, ty, e) => {
                    let e = lower(e, value.clone())?;
                    let annotation = ty.as_ref().map(|t| quote! {:#t});
                    tail = quote! {{let #p #annotation = #e; #tail}};
                }
                _ => {}
            }
        }
        Ok(tail)
    };
    let Generics { types, expr, .. } = generics(sm);
    let name = &tr.name;
    let req = format_ident!("{}_requires", name);
    let with_shared = format_ident!("{}_with_shared", name);
    let enabled = format_ident!("{}_enabled", name);
    let owners = format_ident!("{}_owners_enabled", name);
    let strong = format_ident!("{}_strong", name);
    let owned_post = format_ident!("{}_owned_post", name);
    let execute = format_ident!("{}_execute", name);
    let helper = format_ident!("__variable_persistent_{}_raw", name);
    if sm.transitions.iter().any(|other| other.name == helper) {
        return Err(Error::new(
            tr.name.span(),
            "transition conflicts with generated variable/persistent raw adapter",
        ));
    }
    let factory_a = format_ident!("field_{}", a);
    let owns_a = format_ident!("owns_{}", a);
    let getter_a = format_ident!("value_{}", a);
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
    let operations: Vec<_> = steps
        .iter()
        .filter_map(|s| {
            if let Step::Op(f, o, p) = s {
                Some((f, o, p))
            } else {
                None
            }
        })
        .collect();
    let updates: Vec<_> = steps
        .iter()
        .filter_map(|s| {
            if let Step::Update(f, e) = s {
                Some((f, e))
            } else {
                None
            }
        })
        .collect();
    let assertions: Vec<_> = steps
        .iter()
        .filter_map(|s| {
            if let Step::Assert(e) = s {
                Some(e)
            } else {
                None
            }
        })
        .collect();
    if operations.is_empty() && updates.len() == 1 && *updates[0].0 == *a && assertions.is_empty() {
        let native_req = requirement(quote! {old(#input).value()})?;
        let raw_req = requirement(quote! {old(#raw).fragment().#getter_a()})?;
        let update = scoped(updates[0].1, quote! {old(#input).value()})?;
        let raw_update = scoped(updates[0].1, quote! {old(#raw).fragment().#getter_a()})?;
        return Ok(quote! {
            proof fn #helper(#(#params,)*tracked #raw:&mut Token #types)
                requires old(#raw).fragment().#owns_a(),
                    old(#raw).fragment()==Fragment #expr::#factory_a(old(#raw).fragment().#getter_a()),
                    #raw_req,
                ensures final(#raw).loc()==old(#raw).loc(),
                    final(#raw).fragment()==Fragment #expr::#factory_a(#raw_update),
                    final(#raw).fragment().#owns_a(),
            {
                let #before=#raw.fragment();
                let tracked mut #oldraw=#raw.empty();
                ::vstd::modes::tracked_swap(#raw,&mut #oldraw);
                assert(Protocol #expr::#req(#before,Fragment #expr::empty(),#(#args),*)) by {
                    assert forall|#z:Fragment #types,#pre:State #types|
                        #pre.invariant() && Fragment #expr::op(Fragment #expr::op(#before,Fragment #expr::empty()),#z)==Protocol #expr::embed(#pre)
                        implies State #expr::#enabled(#pre,#(#args),*) && State #expr::#owners(#pre,#before,Fragment #expr::empty(),#(#args),*) by {
                        assert(#pre.#a==#before.#getter_a());
                    }
                }
                let tracked #after=Protocol #expr::#name(#oldraw,#(#args),*);
                let (#z,#pre,#post)=choose|#z:Fragment #types,#pre:State #types,#post:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,Fragment #expr::empty()),#z)==Protocol #expr::embed(#pre)
                    && State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()
                    && #after.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
                    && Fragment #expr::op(Fragment #expr::op(#after.fragment(),Fragment #expr::empty()),#z)==Protocol #expr::embed(#post);
                assert(#pre.#a==#before.#getter_a());
                *#raw=#after;
            }
            pub proof fn #name(tracked &self,#(#params,)*tracked #input:&mut #a #types)
                requires old(#input).instance_id()==self.id(),#native_req,
                ensures final(#input).instance_id()==self.id(),final(#input).value()==#update,
            {
                ::vstd::prelude::use_type_invariant(self);
                ::vstd::prelude::use_type_invariant(&*#input);
                assert(#input.raw.fragment().#getter_a()==#input.value());
                assert(#input.value()==old(#input).value());
                Self::#helper(#(#args,)*&mut #input.raw);
            }
        });
    }
    if operations.len() == 1
        && operations[0].1.is_add()
        && updates.is_empty()
        && assertions.is_empty()
    {
        let (field, op, pat) = operations[0];
        if *field != *m || pat.is_some() {
            return Err(Error::new(name.span(), "persistent Add must be unbound"));
        }
        let MonoidElt::SingletonKV(key, Some(value)) = &op.elt else {
            unreachable!()
        };
        let native_req = requirement(quote! {#input.value()})?;
        let key_native = scoped(key, quote! {#input.value()})?;
        let val_native = scoped(value, quote! {#input.value()})?;
        return Ok(quote! {
            pub proof fn #name(tracked &self,#(#params,)*tracked #input:&#a #types)->(tracked out:#m #types)
                requires #input.instance_id()==self.id(),#native_req,
                ensures out.instance_id()==self.id(),out.key()==#key_native,out.value()==#val_native,
            {
                ::vstd::prelude::use_type_invariant(self);
                ::vstd::prelude::use_type_invariant(#input);
                Fragment #expr::op_unit(Fragment #expr::unit());
                let tracked #oldraw=self.context.duplicate();
                let #before=#oldraw.fragment();
                assert(#before==Fragment #expr::empty());
                assert(Protocol #expr::#req(#before,#input.raw.fragment(),#(#args),*)) by {
                    assert forall|#z:Fragment #types,#pre:State #types|
                        #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#input.raw.fragment()),#z)==Protocol #expr::embed(#pre)
                        implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#input.raw.fragment(),#(#args),*) by {
                        assert(#pre.#a==#input.value());
                    }
                }
                let tracked #after=Protocol #expr::#with_shared(#oldraw,&#input.raw,#(#args),*);
                let (#z,#pre,#post)=choose|#z:Fragment #types,#pre:State #types,#post:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#input.raw.fragment()),#z)==Protocol #expr::embed(#pre)
                    && State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()
                    && #after.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
                    && Fragment #expr::op(Fragment #expr::op(#after.fragment(),#input.raw.fragment()),#z)==Protocol #expr::embed(#post);
                assert(#pre.#a==#input.value());
                ::vstd::resource::tsm_collections::persistent_map_join(
                    ::vstd::imap::IMap::empty(),::vstd::imap::IMap::empty().insert(#key_native,#val_native));
                ::vstd::resource::tsm_collections::Pointwise::extensionality(
                    #after.fragment().#m,
                    ::vstd::resource::tsm_collections::persistent_map_frag(
                        ::vstd::imap::IMap::empty().insert(#key_native,#val_native)));
                #m #expr::__from_token(#after,#key_native,#val_native)
            }
        });
    }
    if tr.kind != TransitionKind::Property
        || !updates.is_empty()
        || operations.is_empty()
        || operations.len() > 2
        || operations.iter().any(|(f, o, _)| **f != *m || !o.is_have())
    {
        return Err(Error::new(name.span(),"variable/persistent entry facade supports one authority update, one Add, or up to two readonly Have entries"));
    }
    let mut uses_auth = false;
    for step in &steps {
        let expressions: Vec<&Expr> = match step {
            Step::Require(e) | Step::Assert(e) | Step::Update(_, e) | Step::Let(_, _, e) => vec![e],
            Step::Op(_, op, _) => match &op.elt {
                MonoidElt::SingletonKV(k, Some(v)) => vec![k, v],
                MonoidElt::SingletonKV(k, None) => vec![k],
                _ => unreachable!(),
            },
        };
        for expression in expressions {
            let mut expression = expression.clone();
            let mut errors = vec![];
            crate::field_access_visitor::visit_field_accesses(
                &mut expression,
                |_, field, _| {
                    if field.name == *a {
                        uses_auth = true;
                    }
                },
                &mut errors,
                &fields,
            );
            if let Some(error) = errors.into_iter().next() {
                return Err(error);
            }
        }
    }
    if uses_auth && operations.len() != 1 {
        return Err(Error::new(
            name.span(),
            "authority properties currently require one entry",
        ));
    }
    let entries = [&entry1, &entry2];
    let mut entry_req = Vec::new();
    let mut bindings = Vec::new();
    let mut lifts = Vec::new();
    for (index, (_, op, pat)) in operations.iter().enumerate() {
        let ent = entries[index];
        let MonoidElt::SingletonKV(key, value) = &op.elt else {
            unreachable!()
        };
        let key = lower(key, quote! {#input.value()})?;
        entry_req.push(quote! {#ent.instance_id()==self.id(),#ent.key()==#key,});
        if let Some(value) = value {
            let value = lower(value, quote! {#input.value()})?;
            entry_req.push(quote! {#ent.value()==#value,});
        } else if let Some(p) = pat {
            bindings.push(quote! {let #p=#ent.value();});
        } else {
            return Err(Error::new(
                name.span(),
                "Have value needs explicit operand or bound value",
            ));
        }
        let frame = if uses_auth {
            &frame3
        } else if index == 0 {
            &frame2
        } else {
            &frame3
        };
        lifts.push(quote! {
            ::vstd::resource::tsm_collections::persistent_map_owned_frame(
                #ent.raw.fragment().#m,#frame.#m,#pre.#m,#ent.key(),#ent.value());
        });
    }
    let native_req = requirement(quote! {#input.value()})?;
    let native_req = quote! {{#(#bindings)* #native_req}};
    let assertion: Vec<_> = assertions
        .iter()
        .map(|e| lower(e, quote! {#input.value()}))
        .collect::<Result<_, _>>()?;
    let assertion_contract = quote! {{#(#bindings)* true #(&& (#assertion))*}};
    let authority_param = if uses_auth {
        quote! {tracked #input:&#a #types,}
    } else {
        quote! {}
    };
    let authority_req = if uses_auth {
        quote! {#input.instance_id()==self.id(),}
    } else {
        quote! {}
    };
    let typeinv = if uses_auth {
        quote! {::vstd::prelude::use_type_invariant(#input);}
    } else {
        quote! {}
    };
    let params_entry: Vec<_> = entries
        .iter()
        .take(operations.len())
        .map(|e| quote! {tracked #e:&#m #types})
        .collect();
    let compatible = if uses_auth {
        quote! {self.context.compatible_3(&#input.raw,&#entry1.raw)}
    } else if operations.len() == 2 {
        quote! {self.context.compatible_3(&#entry1.raw,&#entry2.raw)}
    } else {
        quote! {self.context.compatible_3(&#entry1.raw,&#entry1.raw)}
    };
    let auth_equal = if uses_auth {
        quote! {assert(#pre.#a==#input.value());}
    } else {
        quote! {}
    };
    let entry_invs: Vec<_> = entries
        .iter()
        .take(operations.len())
        .map(|e| quote! {::vstd::prelude::use_type_invariant(#e);})
        .collect();
    Ok(quote! {
        pub proof fn #name(tracked &self,#(#params,)*#authority_param #(#params_entry),*)
            requires #authority_req #(#entry_req)*#native_req,
            ensures #assertion_contract,
        {
            ::vstd::prelude::use_type_invariant(self);#typeinv #(#entry_invs)*
            let (#pre,#frame1,#frame2,#frame3)=#compatible;
            #auth_equal #(#lifts)* #(#bindings)*
            let #post=State #expr::#execute(#pre,#(#args),*);
        }
    })
}
