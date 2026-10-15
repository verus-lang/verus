//! Checked current optional owners, including neutral native operands.
use crate::ast::*;
use crate::verified_field_logical::{fresh, generics};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use verus_syn::{Error, Expr, Ident};
#[derive(Default)]
struct Flat {
    ops: Vec<(Ident, SpecialOp)>,
    requires: Vec<Expr>,
    assertions: Vec<Expr>,
}
fn collect(s: &TransitionStmt, f: &mut Flat) -> Result<(), Error> {
    match s {
        TransitionStmt::Block(_, xs) => {
            for x in xs {
                collect(x, f)?;
            }
        }
        TransitionStmt::Require(_, e) => f.requires.push(e.clone()),
        TransitionStmt::Assert(_, e, _) => f.assertions.push(e.clone()),
        TransitionStmt::Split(_, k, xs) => {
            if let SplitKind::Special(n, op, _, None) = &**k {
                f.ops.push((n.clone(), op.clone()));
                for x in xs {
                    collect(x, f)?;
                }
            } else {
                return Err(Error::new(
                    *s.get_span(),
                    "optional field facade needs explicit straight-line operands",
                ));
            }
        }
        _ => {
            return Err(Error::new(
                *s.get_span(),
                "optional field facade does not yet combine ordinary writes",
            ))
        }
    }
    Ok(())
}
pub fn supports(sm: &SM, tr: &Transition) -> bool {
    let mut f = Flat::default();
    if collect(&tr.body, &mut f).is_err() {
        return false;
    }
    !f.ops.is_empty()
        && f.ops.len() <= 2
        && f.ops.iter().all(|(n, op)| {
            let field = sm.fields.iter().find(|f| f.name == *n).unwrap();
            matches!(
                field.stype,
                ShardableType::Bool
                    | ShardableType::PersistentBool
                    | ShardableType::Option(..)
                    | ShardableType::PersistentOption(..)
            ) && matches!(
                op.stmt,
                MonoidStmtType::Have | MonoidStmtType::Add(_) | MonoidStmtType::Remove
            )
        })
        && f.ops.iter().filter(|(_, op)| op.is_have()).count() <= 1
}
fn operand(field: &Field, op: &SpecialOp) -> Result<(TokenStream, bool), Error> {
    Ok(match (&field.stype, &op.elt) {
        (ShardableType::Bool | ShardableType::PersistentBool, MonoidElt::True) => {
            (quote! {true}, false)
        }
        (ShardableType::Bool | ShardableType::PersistentBool, MonoidElt::General(e)) => {
            (quote! {#e}, true)
        }
        (
            ShardableType::Option(..) | ShardableType::PersistentOption(..),
            MonoidElt::OptionSome(Some(e)),
        ) => (quote! {Some(#e)}, false),
        (
            ShardableType::Option(..) | ShardableType::PersistentOption(..),
            MonoidElt::General(e),
        ) => (quote! {#e}, true),
        _ => {
            return Err(Error::new(
                field.name.span(),
                "optional native operand is not supported",
            ))
        }
    })
}
pub fn method(sm: &SM, tr: &Transition) -> Result<TokenStream, Error> {
    let mut flat = Flat::default();
    collect(&tr.body, &mut flat)?;
    // Only explicit parameter expressions are published by this slice. Native
    // State reads and bound patterns require the later mixed-field compiler.
    let fields: std::collections::HashMap<_, _> = sm
        .fields
        .iter()
        .map(|field| (field.name.to_string(), field.clone()))
        .collect();
    let check = |expression: &Expr| -> Result<(), Error> {
        let mut expression = expression.clone();
        let mut errors = Vec::new();
        crate::field_access_visitor::visit_field_accesses(
            &mut expression,
            |errors, field, _| {
                errors.push(Error::new(
                    field.name.span(),
                    "optional native facade currently requires explicit parameter expressions",
                ))
            },
            &mut errors,
            &fields,
        );
        if let Some(error) = errors.into_iter().next() {
            Err(error)
        } else {
            Ok(())
        }
    };
    for expression in flat.requires.iter().chain(&flat.assertions) {
        check(expression)?;
    }
    for (name, operation) in &flat.ops {
        match &operation.elt {
            MonoidElt::General(expression) | MonoidElt::OptionSome(Some(expression)) => {
                check(expression)?
            }
            MonoidElt::True => (),
            _ => {
                return Err(Error::new(
                    name.span(),
                    "unsupported optional native operand",
                ))
            }
        }
    }
    let g = generics(sm);
    let types = &g.types;
    let expr = &g.expr;
    let name = &tr.name;
    let req = format_ident!("{}_requires", name);
    let enabled = format_ident!("{}_enabled", name);
    let owners = format_ident!("{}_owners_enabled", name);
    let strong = format_ident!("{}_strong", name);
    let owned_post = format_ident!("{}_owned_post", name);
    let adapter = format_ident!("__field_{}_with_observation", name);
    let out = fresh(sm, &tr.params, "optional_out");
    let typed = fresh(sm, &tr.params, "optional_typed");
    let owned = fresh(sm, &tr.params, "optional_owned");
    let observed = fresh(sm, &tr.params, "optional_observed");
    let before = fresh(sm, &tr.params, "optional_before");
    let outer = fresh(sm, &tr.params, "optional_outer");
    let pre = fresh(sm, &tr.params, "optional_pre");
    let post = fresh(sm, &tr.params, "optional_post");
    let next = fresh(sm, &tr.params, "optional_next");
    let mut inputs = Vec::new();
    let mut bounds = Vec::new();
    let mut setup = Vec::new();
    let mut transfer = Vec::new();
    let mut facts = Vec::new();
    let mut returns = Vec::new();
    let mut output_type = quote! {()};
    let mut result = quote! {()};
    let mut seen = std::collections::HashSet::new();
    for (index, (field_name, op)) in flat.ops.iter().enumerate() {
        if !seen.insert(field_name.to_string()) {
            return Err(Error::new(
                field_name.span(),
                "optional native slice needs one operation per field",
            ));
        }
        let field = sm.fields.iter().find(|f| f.name == *field_name).unwrap();
        let ty = field.get_type();
        let (native_untyped, general) = operand(field, op)?;
        let native = quote! {((|#typed:#ty|#typed)(#native_untyped))};
        let value = fresh(sm, &tr.params, &format!("operand_{index}"));
        let is_bool = matches!(
            field.stype,
            ShardableType::Bool | ShardableType::PersistentBool
        );
        let active = if is_bool {
            quote! {#value}
        } else {
            quote! {#value is Some}
        };
        let payload = if is_bool {
            quote! {true}
        } else {
            quote! {#value->Some_0}
        };
        setup.push(quote! {let #value:#ty=#native;});
        match op.stmt {
            MonoidStmtType::Add(_) => {
                if !returns.is_empty() {
                    return Err(Error::new(
                        field_name.span(),
                        "optional native slice returns one added owner",
                    ));
                }
                let raw = fresh(sm, &tr.params, "optional_result");
                let rest = fresh(sm, &tr.params, "optional_rest");
                let take = format_ident!("take_{field_name}");
                let rhs = if is_bool {
                    quote! {true}
                } else {
                    quote! {(#native)->Some_0}
                };
                if general {
                    output_type = quote! {Option<#field_name #types>};
                    let cond = if is_bool {
                        quote! {#native}
                    } else {
                        quote! {(#native) is Some}
                    };
                    returns.push(quote! {(#out is Some)==(#cond)});
                    returns.push(quote!{::vstd::prelude::imply(#out is Some,#out->Some_0.instance_id()==self.id()&&#out->Some_0.value()==#rhs)});
                    result = quote! {{let tracked (#raw,#rest)=Protocol #expr::#take(#next);if #active{Some(<#field_name #types>::__from_token(#raw))}else{None}}};
                } else {
                    output_type = quote! {#field_name #types};
                    returns.push(quote! {#out.instance_id()==self.id()});
                    returns.push(quote! {#out.value()==#rhs});
                    result = quote! {{let tracked (#raw,#rest)=Protocol #expr::#take(#next);<#field_name #types>::__from_token(#raw)}};
                }
            }
            MonoidStmtType::Have | MonoidStmtType::Remove => {
                if op.is_remove() && field.stype.is_persistent() {
                    return Err(Error::new(
                        field_name.span(),
                        "persistent owners cannot be consumed",
                    ));
                }
                let input = fresh(sm, &tr.params, &format!("optional_input_{index}"));
                let clause = if general {
                    if op.is_have() {
                        inputs.push(quote! {tracked #input:&Option<#field_name #types>});
                    } else {
                        inputs.push(quote! {tracked #input:Option<#field_name #types>});
                    }
                    let cond = if is_bool {
                        quote! {#native}
                    } else {
                        quote! {(#native) is Some}
                    };
                    let val = if is_bool {
                        quote! {true}
                    } else {
                        quote! {(#native)->Some_0}
                    };
                    let payload_matches = if is_bool {
                        quote! {true}
                    } else {
                        quote! {#input->Some_0.value()==#val}
                    };
                    bounds.push(quote!{::vstd::prelude::imply(#cond,#input is Some&&#input->Some_0.instance_id()==self.id()&&#payload_matches)});
                    if op.is_remove() {
                        bounds.push(quote! {::vstd::prelude::imply(! (#cond),#input is None)});
                    }
                    quote! {#input.tracked_borrow()}
                } else {
                    if op.is_have() {
                        inputs.push(quote! {tracked #input:&#field_name #types});
                    } else {
                        inputs.push(quote! {tracked #input:#field_name #types});
                    }
                    let val = if is_bool {
                        quote! {true}
                    } else {
                        quote! {(#native)->Some_0}
                    };
                    let payload_matches = if is_bool {
                        quote! {true}
                    } else {
                        quote! {#input.value()==#val}
                    };
                    bounds.push(quote! {#input.instance_id()==self.id()&&#payload_matches});
                    quote! {&#input}
                };
                let item = fresh(sm, &tr.params, &format!("optional_item_{index}"));
                let lower = fresh(sm, &tr.params, &format!("optional_lower_{index}"));
                let helper = match field.stype {
                    ShardableType::Bool => quote! {::vstd::resource::tsm_bool::bool_owned_frame},
                    ShardableType::PersistentBool => {
                        quote! {::vstd::resource::tsm_persistent::persistent_bool_owned_frame}
                    }
                    ShardableType::Option(..) => {
                        quote! {::vstd::resource::tsm_collections::option_owned_frame}
                    }
                    _ => quote! {::vstd::resource::tsm_collections::persistent_option_owned_frame},
                };
                if op.is_have() {
                    transfer.push(quote!{let tracked #observed=if #active{let tracked #item=#clause;::vstd::prelude::use_type_invariant(#item);let tracked source=#item.raw.observe();#observed.join(&source)}else{#observed};});
                    let extra = if is_bool {
                        quote! {}
                    } else {
                        quote! {,#payload}
                    };
                    let source = if general {
                        quote! {#input->Some_0.raw.fragment()}
                    } else {
                        quote! {#input.raw.fragment()}
                    };
                    facts.push(quote!{if #active{let #lower=Self::__lower_completion(#before,#observed.fragment(),#outer,#source,#pre);#helper((#source).#field_name,#lower.#field_name,#pre.#field_name #extra);}});
                } else {
                    if general {
                        transfer.push(quote!{let tracked #owned=if #active{let tracked item=#input.tracked_unwrap();::vstd::prelude::use_type_invariant(&item);#owned.join(item.raw)}else{#owned};});
                    } else {
                        transfer.push(quote!{::vstd::prelude::use_type_invariant(&#input);let tracked #owned=#owned.join(#input.raw);});
                    }
                    let extra = if is_bool {
                        quote! {}
                    } else {
                        quote! {,#payload}
                    };
                    facts.push(quote!{if #active{Fragment #expr::associative(#before,#observed.fragment(),#outer);#helper(#before.#field_name,Fragment #expr::op(#observed.fragment(),#outer).#field_name,#pre.#field_name #extra);}});
                }
            }
            _ => {
                return Err(Error::new(
                    field_name.span(),
                    "unsupported optional operation",
                ))
            }
        }
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
    let args: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
    let requirements = &flat.requires;
    let assertions = &flat.assertions;
    Ok(quote! {
    pub proof fn #name(tracked &self,#(#params,)*#(#inputs),*)->(tracked #out:#output_type)
     requires #(#bounds,)*#(#requirements,)* ensures #(#returns,)*#(#assertions,)*
    {
     ::vstd::prelude::use_type_invariant(self);Fragment #expr::op_unit(Fragment #expr::unit());
     assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());
     let tracked #owned=self.context.duplicate();let tracked #observed=self.context.observe();#(#setup)*#(#transfer)*let #before=#owned.fragment();
     assert(Protocol #expr::#req(#before,#observed.fragment(),#(#args),*)) by{
      assert forall|#outer:Fragment #types,#pre:State #types|#pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
       implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#observed.fragment(),#(#args),*) by{#(#facts)*}
     }
     let tracked #next=Protocol #expr::#adapter(#owned,&#observed,#(#args),*);
     let (#outer,#pre,#post)=choose|#outer:Fragment #types,#pre:State #types,#post:State #types|#pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
      &&State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()&&#next.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
      &&Fragment #expr::op(Fragment #expr::op(#next.fragment(),#observed.fragment()),#outer)==Protocol #expr::embed(#post);
     #result
    }
    })
}
