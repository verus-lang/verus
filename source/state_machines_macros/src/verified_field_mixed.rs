//! Private checked variable-authority and optional-owner transitions.
use crate::ast::*;
use crate::verified_field_logical::generics;
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident, Pat};

#[derive(Default)]
struct Flat {
    operations: Vec<(Ident, SpecialOp, bool)>,
    requirements: Vec<Expr>,
    assertions: Vec<Expr>,
    updates: Vec<(Ident, Expr)>,
}

fn collect(statement: &TransitionStmt, flat: &mut Flat) -> Result<(), Error> {
    match statement {
        TransitionStmt::Block(_, children) => {
            for child in children {
                collect(child, flat)?;
            }
        }
        TransitionStmt::Require(_, expression) => flat.requirements.push(expression.clone()),
        TransitionStmt::Assert(_, expression, _) => flat.assertions.push(expression.clone()),
        TransitionStmt::Update(_, field, expression) => {
            flat.updates.push((field.clone(), expression.clone()))
        }
        TransitionStmt::Split(_, split, children) => {
            if let SplitKind::Special(field, operation, _, pattern) = &**split {
                let wild = match pattern {
                    None => false,
                    Some(pattern) if matches!(&**pattern, Pat::Wild(_)) => true,
                    _ => {
                        return Err(Error::new(
                            field.span(),
                            "mixed facade binding is not supported",
                        ))
                    }
                };
                flat.operations
                    .push((field.clone(), operation.clone(), wild));
                for child in children {
                    collect(child, flat)?;
                }
            } else {
                return Err(Error::new(
                    *statement.get_span(),
                    "mixed facade control is not supported",
                ));
            }
        }
        _ => {
            return Err(Error::new(
                *statement.get_span(),
                "mixed facade statement is not supported",
            ))
        }
    }
    Ok(())
}

fn expressions(flat: &Flat) -> Vec<&Expr> {
    let mut result: Vec<_> = flat.requirements.iter().chain(&flat.assertions).collect();
    result.extend(flat.updates.iter().map(|(_, expression)| expression));
    for (_, operation, _) in &flat.operations {
        match &operation.elt {
            MonoidElt::General(expression) | MonoidElt::OptionSome(Some(expression)) => {
                result.push(expression)
            }
            _ => (),
        }
    }
    result
}

// Substituted pre-field reads can be nested below user closures/quantifiers.
// Reserve every recursive expression identifier, including binding names.
fn fresh(sm: &SM, params: &[TransitionParam], label: &str) -> Ident {
    fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
        for token in tokens {
            match token {
                TokenTree::Ident(name) => {
                    names.insert(name.to_string());
                }
                TokenTree::Group(group) => reserve(group.stream(), names),
                _ => (),
            }
        }
    }
    let mut unavailable: HashSet<_> = sm
        .fields
        .iter()
        .map(|field| field.name.to_string())
        .chain(params.iter().map(|parameter| parameter.name.to_string()))
        .chain(
            sm.transitions
                .iter()
                .map(|transition| transition.name.to_string()),
        )
        .collect();
    for transition in &sm.transitions {
        let mut flat = Flat::default();
        if collect(&transition.body, &mut flat).is_ok() {
            for expression in expressions(&flat) {
                reserve(quote! {#expression}, &mut unavailable);
            }
        }
    }
    let mut name = format!("__tsm_logical_{label}");
    while unavailable.contains(&name) {
        name.push('_');
    }
    Ident::new(&name, Span::mixed_site())
}

fn variable_fields(sm: &SM, flat: &Flat) -> Result<Vec<Field>, Error> {
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|field| (field.name.to_string(), field.clone()))
        .collect();
    let mut used: HashSet<_> = flat
        .updates
        .iter()
        .map(|(name, _)| name.to_string())
        .collect();
    for expression in expressions(flat) {
        let mut expression = expression.clone();
        let mut errors = Vec::new();
        crate::field_access_visitor::visit_field_accesses(
            &mut expression,
            |errors, field, _| {
                if matches!(field.stype, ShardableType::Variable(_)) {
                    used.insert(field.name.to_string());
                } else {
                    errors.push(Error::new(
                        field.name.span(),
                        "mixed facade native reads currently require variable fields",
                    ));
                }
            },
            &mut errors,
            &fields,
        );
        if let Some(error) = errors.into_iter().next() {
            return Err(error);
        }
    }
    let result: Vec<_> = sm
        .fields
        .iter()
        .filter(|field| used.contains(&field.name.to_string()))
        .cloned()
        .collect();
    if result
        .iter()
        .any(|field| !matches!(field.stype, ShardableType::Variable(_)))
    {
        return Err(Error::new(
            sm.name.span(),
            "mixed facade can only update variable fields",
        ));
    }
    Ok(result)
}

pub fn supports(sm: &SM, transition: &Transition) -> bool {
    let mut flat = Flat::default();
    if collect(&transition.body, &mut flat).is_err() || flat.operations.len() != 1 {
        return false;
    }
    let (name, operation, _) = &flat.operations[0];
    let field = sm.fields.iter().find(|field| field.name == *name).unwrap();
    matches!(field.stype, ShardableType::Bool | ShardableType::Option(_))
        && matches!(
            operation.stmt,
            MonoidStmtType::Have | MonoidStmtType::Add(_) | MonoidStmtType::Remove
        )
        && variable_fields(sm, &flat).is_ok_and(|variables| !variables.is_empty())
}

fn rewrite(
    sm: &SM,
    expression: &Expr,
    replacements: &HashMap<String, TokenStream>,
) -> Result<Expr, Error> {
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|field| (field.name.to_string(), field.clone()))
        .collect();
    let mut expression = expression.clone();
    let mut errors = Vec::new();
    crate::field_access_visitor::visit_field_accesses(
        &mut expression,
        |errors, field, node| {
            if let Some(value) = replacements.get(&field.name.to_string()) {
                *node = verus_syn::parse2(value.clone()).unwrap();
            } else {
                errors.push(Error::new(
                    field.name.span(),
                    "unobserved mixed facade native read",
                ));
            }
        },
        &mut errors,
        &fields,
    );
    if let Some(error) = errors.into_iter().next() {
        Err(error)
    } else {
        Ok(expression)
    }
}

pub fn method(sm: &SM, transition: &Transition) -> Result<TokenStream, Error> {
    let mut flat = Flat::default();
    collect(&transition.body, &mut flat)?;
    let variables = variable_fields(sm, &flat)?;
    let mut changed = HashSet::new();
    for (name, _) in &flat.updates {
        if !changed.insert(name.to_string()) {
            return Err(Error::new(
                name.span(),
                "mixed facade supports one update per variable field",
            ));
        }
    }
    let generics = generics(sm);
    let types = &generics.types;
    let expr = &generics.expr;
    let mut public_inputs = Vec::new();
    let mut helper_inputs = Vec::new();
    let mut arguments = Vec::new();
    let mut public_bounds = Vec::new();
    let mut helper_bounds = Vec::new();
    let mut public_returns = Vec::new();
    let mut helper_returns = Vec::new();
    let mut public_values = HashMap::new();
    let mut helper_values = HashMap::new();
    let mut local_values = HashMap::new();
    let mut setup = Vec::new();
    let mut transfer = Vec::new();
    let mut facts = Vec::new();
    let mut observed_facts = Vec::new();
    let mut restore = Vec::new();
    let mut observed_lowers: Vec<TokenStream> = Vec::new();
    let inclusion_helper = fresh(
        sm,
        &transition.params,
        &format!("mixed_inclusion_{}", transition.name),
    );
    let owned = fresh(sm, &transition.params, "mixed_owned");
    let observed = fresh(sm, &transition.params, "mixed_observed");
    let before = fresh(sm, &transition.params, "mixed_before");
    let outer = fresh(sm, &transition.params, "mixed_outer");
    let pre = fresh(sm, &transition.params, "mixed_pre");
    let post = fresh(sm, &transition.params, "mixed_post");
    let next = fresh(sm, &transition.params, "mixed_next");
    let out = fresh(sm, &transition.params, "mixed_out");
    for variable in &variables {
        let field = &variable.name;
        let reference = fresh(sm, &transition.params, &format!("mixed_reference_{field}"));
        let raw = fresh(sm, &transition.params, &format!("mixed_raw_{field}"));
        let native = fresh(sm, &transition.params, &format!("mixed_native_{field}"));
        let temporary = fresh(sm, &transition.params, &format!("mixed_temporary_{field}"));
        let factory = format_ident!("field_{field}");
        let getter = format_ident!("value_{field}");
        let owns = format_ident!("owns_{field}");
        let take = format_ident!("take_{field}");
        let ty = variable.get_type();
        let mutable = changed.contains(&field.to_string());
        if mutable {
            public_inputs.push(quote! {tracked #reference:&mut #field #types});
            helper_inputs.push(quote! {tracked #raw:&mut Token #types});
            arguments.push(quote! {&mut #reference.raw});
            public_values.insert(field.to_string(), quote! {old(#reference).value()});
            helper_values.insert(field.to_string(), quote! {old(#raw).fragment().#getter()});
            public_bounds.push(quote! {old(#reference).instance_id()==self.id()});
            helper_bounds.push(quote! {old(#raw).loc()==self.id()});
            helper_bounds.push(quote! {old(#raw).fragment().#owns()});
            helper_bounds.push(quote!{old(#raw).fragment()==Fragment #expr::#factory(old(#raw).fragment().#getter())});
            public_returns.push(quote! {final(#reference).instance_id()==self.id()});
            helper_returns.push(quote! {final(#raw).loc()==self.id()});
            helper_returns.push(quote!{final(#raw).fragment()==Fragment #expr::#factory(final(#raw).fragment().#getter())});
            transfer.push(quote! {
                let tracked mut #temporary=#raw.empty();
                ::vstd::modes::tracked_swap(#raw,&mut #temporary);
                let tracked #owned=#owned.join(#temporary);
            });
            restore.push(quote! {
                let tracked (mut #temporary,#next)=Protocol #expr::#take(#next);
                ::vstd::modes::tracked_swap(#raw,&mut #temporary);
            });
            facts.push(quote! {
                Fragment #expr::associative(#before,#observed.fragment(),#outer);
                ::vstd::resource::tsm_collections::option_owned_frame(
                    #before.#field,Fragment #expr::op(#observed.fragment(),#outer).#field,
                    Some(#pre.#field),#native);
            });
        } else {
            public_inputs.push(quote! {tracked #reference:&#field #types});
            helper_inputs.push(quote! {tracked #raw:&Token #types});
            arguments.push(quote! {&#reference.raw});
            public_values.insert(field.to_string(), quote! {#reference.value()});
            helper_values.insert(field.to_string(), quote! {#raw.fragment().#getter()});
            public_bounds.push(quote! {#reference.instance_id()==self.id()});
            helper_bounds.push(quote! {#raw.loc()==self.id()});
            helper_bounds.push(quote! {#raw.fragment().#owns()});
            helper_bounds.push(
                quote! {#raw.fragment()==Fragment #expr::#factory(#raw.fragment().#getter())},
            );
            let previous = fresh(sm, &transition.params, &format!("mixed_previous_{field}"));
            let inclusion_steps: Vec<_> = observed_lowers.iter().map(|lower|
                quote!{Self::#inclusion_helper(#lower,#previous,#observed.fragment());}).collect();
            transfer.push(quote! {
                let tracked #temporary=#raw.observe();
                let #previous=#observed.fragment();
                let tracked #observed=#observed.join(&#temporary);
                #(#inclusion_steps)*
            });
            observed_lowers.push(quote! {#raw.fragment()});
            let state = fresh(
                sm,
                &transition.params,
                &format!("mixed_observed_state_{field}"),
            );
            let frame = fresh(
                sm,
                &transition.params,
                &format!("mixed_observed_frame_{field}"),
            );
            let remainder = fresh(
                sm,
                &transition.params,
                &format!("mixed_observed_remainder_{field}"),
            );
            observed_facts.push(quote! {
                #observed.validate();
                let (#state,#frame)=choose|#state:State #types,#frame:Fragment #types|
                    #state.invariant()&&Fragment #expr::op(#observed.fragment(),#frame)==Protocol #expr::embed(#state);
                let #remainder=choose|#remainder:Fragment #types|
                    Fragment #expr::op(#raw.fragment(),#remainder)==#observed.fragment();
                Fragment #expr::associative(#raw.fragment(),#remainder,#frame);
                ::vstd::resource::tsm_collections::option_owned_frame(
                    #raw.fragment().#field,Fragment #expr::op(#remainder,#frame).#field,
                    Some(#state.#field),#native);
                assert(#observed.fragment().#field==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(#native)));
            });
            let lower = fresh(sm, &transition.params, &format!("mixed_lower_{field}"));
            facts.push(quote!{
                let #lower=Self::__lower_completion(#before,#observed.fragment(),#outer,#raw.fragment(),#pre);
                ::vstd::resource::tsm_collections::option_owned_frame(
                    #raw.fragment().#field,#lower.#field,Some(#pre.#field),#native);
            });
        }
        local_values.insert(field.to_string(), quote! {#native});
        setup.push(quote! {let #native:#ty=#raw.fragment().#getter();});
    }
    for (name, expression) in &flat.updates {
        let reference = fresh(sm, &transition.params, &format!("mixed_reference_{name}"));
        let raw = fresh(sm, &transition.params, &format!("mixed_raw_{name}"));
        let getter = format_ident!("value_{name}");
        let public_expression = rewrite(sm, expression, &public_values)?;
        let helper_expression = rewrite(sm, expression, &helper_values)?;
        public_returns.push(quote! {final(#reference).value()==#public_expression});
        helper_returns.push(quote! {final(#raw).fragment().#getter()==#helper_expression});
    }
    let (field_name, operation, wild) = &flat.operations[0];
    let field = sm
        .fields
        .iter()
        .find(|field| field.name == *field_name)
        .unwrap();
    let boolean = matches!(field.stype, ShardableType::Bool);
    let input = fresh(sm, &transition.params, "mixed_input");
    let value = fresh(sm, &transition.params, "mixed_operand");
    let typed = fresh(sm, &transition.params, "mixed_typed");
    let ty = field.get_type();
    let element = match &operation.elt {
        MonoidElt::True => quote! {true},
        MonoidElt::General(expression) => {
            let expression = rewrite(sm, expression, &local_values)?;
            quote! {#expression}
        }
        MonoidElt::OptionSome(Some(expression)) => {
            let expression = rewrite(sm, expression, &local_values)?;
            quote! {((|#typed:#ty|#typed)(Some(#expression)))}
        }
        MonoidElt::OptionSome(None) if *wild && !operation.is_add() => {
            quote! {Some(#input.value())}
        }
        _ => {
            return Err(Error::new(
                field_name.span(),
                "unsupported mixed optional operand",
            ))
        }
    };
    let general = matches!(operation.elt, MonoidElt::General(_));
    setup.push(quote! {let #value:#ty=((|#typed:#ty|#typed)(#element));});
    let active = if boolean {
        quote! {#value}
    } else {
        quote! {#value is Some}
    };
    let payload = if boolean {
        quote! {true}
    } else {
        quote! {#value->Some_0}
    };
    // Contract operands use original input/native observations, before mutation.
    let contract_operand = |values: &HashMap<String, TokenStream>| -> Result<TokenStream, Error> {
        Ok(match &operation.elt {
            MonoidElt::True => quote! {true},
            MonoidElt::General(expression) => {
                let expression = rewrite(sm, expression, values)?;
                quote! {((|#typed:#ty|#typed)(#expression))}
            }
            MonoidElt::OptionSome(Some(expression)) => {
                let expression = rewrite(sm, expression, values)?;
                quote! {((|#typed:#ty|#typed)(Some(#expression)))}
            }
            MonoidElt::OptionSome(None) if *wild => quote! {Some(#input.value())},
            _ => {
                return Err(Error::new(
                    field_name.span(),
                    "unsupported mixed contract operand",
                ))
            }
        })
    };
    let public_operand = contract_operand(&public_values)?;
    let helper_operand = contract_operand(&helper_values)?;
    let mut native_returns = Vec::new();
    let mut helper_native_returns = Vec::new();
    let mut output = quote! {()};
    let mut result = quote! {()};
    match operation.stmt {
        MonoidStmtType::Add(_) => {
            let take = format_ident!("take_{field_name}");
            let raw = fresh(sm, &transition.params, "mixed_result");
            let rest = fresh(sm, &transition.params, "mixed_rest");
            if general {
                output = quote! {Option<#field_name #types>};
                let cond = if boolean {
                    quote! {#public_operand}
                } else {
                    quote! {(#public_operand) is Some}
                };
                let rhs = if boolean {
                    quote! {true}
                } else {
                    quote! {(#public_operand)->Some_0}
                };
                native_returns.push(quote! {(#out is Some)==(#cond)});
                native_returns.push(quote!{::vstd::prelude::imply(#out is Some,#out->Some_0.instance_id()==self.id()&&#out->Some_0.value()==#rhs)});
                let helper_cond = if boolean {
                    quote! {#helper_operand}
                } else {
                    quote! {(#helper_operand) is Some}
                };
                let helper_rhs = if boolean {
                    quote! {true}
                } else {
                    quote! {(#helper_operand)->Some_0}
                };
                helper_native_returns.push(quote! {(#out is Some)==(#helper_cond)});
                helper_native_returns.push(quote!{::vstd::prelude::imply(#out is Some,#out->Some_0.instance_id()==self.id()&&#out->Some_0.value()==#helper_rhs)});
                result = quote! {{let tracked (#raw,#rest)=Protocol #expr::#take(#next);if #active{Some(<#field_name #types>::__from_token(#raw))}else{None}}};
            } else {
                output = quote! {#field_name #types};
                let rhs = if boolean {
                    quote! {true}
                } else {
                    quote! {(#public_operand)->Some_0}
                };
                native_returns.push(quote! {#out.instance_id()==self.id(),#out.value()==#rhs});
                let helper_rhs = if boolean {
                    quote! {true}
                } else {
                    quote! {(#helper_operand)->Some_0}
                };
                helper_native_returns
                    .push(quote! {#out.instance_id()==self.id(),#out.value()==#helper_rhs});
                result = quote! {{let tracked (#raw,#rest)=Protocol #expr::#take(#next);<#field_name #types>::__from_token(#raw)}};
            }
        }
        MonoidStmtType::Have | MonoidStmtType::Remove => {
            let input_type = if general {
                quote! {Option<#field_name #types>}
            } else {
                quote! {#field_name #types}
            };
            if operation.is_have() {
                public_inputs.push(quote! {tracked #input:&#input_type});
                helper_inputs.push(quote! {tracked #input:&#input_type});
            } else {
                public_inputs.push(quote! {tracked #input:#input_type});
                helper_inputs.push(quote! {tracked #input:#input_type});
            }
            arguments.push(quote! {#input});
            let predicate = |operand: &TokenStream| {
                let same = if general {
                    quote! {#input is Some&&#input->Some_0.instance_id()==self.id()}
                } else {
                    quote! {#input.instance_id()==self.id()}
                };
                let payload_matches = if boolean || *wild {
                    quote! {true}
                } else if general {
                    quote! {#input->Some_0.value()==(#operand)->Some_0}
                } else {
                    quote! {#input.value()==(#operand)->Some_0}
                };
                if general {
                    let cond = if boolean {
                        quote! {#operand}
                    } else {
                        quote! {(#operand) is Some}
                    };
                    let neutral = if operation.is_remove() {
                        quote! {&&::vstd::prelude::imply(!(#cond),#input is None)}
                    } else {
                        quote! {}
                    };
                    quote! {::vstd::prelude::imply(#cond,#same&&#payload_matches)#neutral}
                } else {
                    quote! {#same&&#payload_matches}
                }
            };
            public_bounds.push(predicate(&public_operand));
            helper_bounds.push(predicate(&helper_operand));
            let item = fresh(sm, &transition.params, "mixed_item");
            let source = fresh(sm, &transition.params, "mixed_source");
            if operation.is_have() {
                let borrow = if general {
                    quote! {#input.tracked_borrow()}
                } else {
                    quote! {#input}
                };
                let previous = fresh(sm, &transition.params, "mixed_previous_optional");
                let combined = fresh(sm, &transition.params, "mixed_combined_optional");
                let inclusion_steps:Vec<_>=observed_lowers.iter().map(|lower|
                    quote!{Self::#inclusion_helper(#lower,#previous,#combined.fragment());}).collect();
                transfer.push(quote! {
                    let tracked #observed=if #active{
                        let tracked #item=#borrow;
                        ::vstd::prelude::use_type_invariant(#item);
                        let tracked #source=#item.raw.observe();
                        let #previous=#observed.fragment();
                        let tracked #combined=#observed.join(&#source);
                        #(#inclusion_steps)*
                        #combined
                    }else{#observed};
                });
                let source_fragment = if general {
                    quote! {#input->Some_0.raw.fragment()}
                } else {
                    quote! {#input.raw.fragment()}
                };
                let lower = fresh(sm, &transition.params, "mixed_optional_lower");
                let helper = if boolean {
                    quote! {::vstd::resource::tsm_bool::bool_owned_frame}
                } else {
                    quote! {::vstd::resource::tsm_collections::option_owned_frame}
                };
                let extra = if boolean {
                    quote! {}
                } else {
                    quote! {,#payload}
                };
                facts.push(quote!{if #active{
                    let #lower=Self::__lower_completion(#before,#observed.fragment(),#outer,#source_fragment,#pre);
                    #helper((#source_fragment).#field_name,#lower.#field_name,#pre.#field_name #extra);
                }});
            } else {
                if general {
                    transfer.push(quote!{
                    let tracked #owned=if #active{
                        let tracked #item=#input.tracked_unwrap();::vstd::prelude::use_type_invariant(&#item);#owned.join(#item.raw)
                    }else{#owned};
                });
                } else {
                    transfer.push(quote!{::vstd::prelude::use_type_invariant(&#input);let tracked #owned=#owned.join(#input.raw);});
                }
                let helper = if boolean {
                    quote! {::vstd::resource::tsm_bool::bool_owned_frame}
                } else {
                    quote! {::vstd::resource::tsm_collections::option_owned_frame}
                };
                let extra = if boolean {
                    quote! {}
                } else {
                    quote! {,#payload}
                };
                facts.push(quote!{if #active{
                    Fragment #expr::associative(#before,#observed.fragment(),#outer);
                    #helper(#before.#field_name,Fragment #expr::op(#observed.fragment(),#outer).#field_name,#pre.#field_name #extra);
                }});
            }
        }
        _ => {
            return Err(Error::new(
                field_name.span(),
                "unsupported mixed optional operation",
            ))
        }
    }
    let name = &transition.name;
    let helper = fresh(sm, &transition.params, &format!("mixed_helper_{name}"));
    let req = format_ident!("{name}_requires");
    let enabled = format_ident!("{name}_enabled");
    let owners = format_ident!("{name}_owners_enabled");
    let strong = format_ident!("{name}_strong");
    let owned_post = format_ident!("{name}_owned_post");
    let adapter = format_ident!("__field_{name}_with_observation");
    let params: Vec<_> = transition
        .params
        .iter()
        .map(|parameter| {
            let name = &parameter.name;
            let ty = &parameter.ty;
            quote! {#name:#ty}
        })
        .collect();
    let args: Vec<_> = transition
        .params
        .iter()
        .map(|parameter| &parameter.name)
        .collect();
    let public_requirements: Vec<_> = flat
        .requirements
        .iter()
        .map(|expression| rewrite(sm, expression, &public_values))
        .collect::<Result<_, _>>()?;
    let helper_requirements: Vec<_> = flat
        .requirements
        .iter()
        .map(|expression| rewrite(sm, expression, &helper_values))
        .collect::<Result<_, _>>()?;
    let public_assertions: Vec<_> = flat
        .assertions
        .iter()
        .map(|expression| rewrite(sm, expression, &public_values))
        .collect::<Result<_, _>>()?;
    let helper_assertions: Vec<_> = flat
        .assertions
        .iter()
        .map(|expression| rewrite(sm, expression, &helper_values))
        .collect::<Result<_, _>>()?;
    let invariant_uses: Vec<_> = variables
        .iter()
        .map(|variable| {
            let reference = fresh(
                sm,
                &transition.params,
                &format!("mixed_reference_{}", variable.name),
            );
            quote! {::vstd::prelude::use_type_invariant(&*#reference);}
        })
        .collect();
    Ok(quote! {
        proof fn #inclusion_helper(lower:Fragment #types,middle:Fragment #types,upper:Fragment #types)
            requires ::vstd::resource::tsm::fragment_included::<Protocol #types>(lower,middle),
                ::vstd::resource::tsm::fragment_included::<Protocol #types>(middle,upper),
            ensures ::vstd::resource::tsm::fragment_included::<Protocol #types>(lower,upper),
        {
            let left=choose|left:Fragment #types|Fragment #expr::op(lower,left)==middle;
            let right=choose|right:Fragment #types|Fragment #expr::op(middle,right)==upper;
            Fragment #expr::associative(lower,left,right);
            assert(Fragment #expr::op(lower,Fragment #expr::op(left,right))==upper);
        }
        proof fn #helper(tracked &self,#(#params,)*#(#helper_inputs),*)->(tracked #out:#output)
            requires #(#helper_bounds,)*#(#helper_requirements,)*
            ensures #(#helper_returns,)*#(#helper_assertions,)*#(#helper_native_returns,)*
        {
            ::vstd::prelude::use_type_invariant(self);
            Fragment #expr::op_unit(Fragment #expr::unit());
            assert(Fragment #expr::op(self.context.fragment(),self.context.fragment())==self.context.fragment());
            let tracked #owned=self.context.duplicate();
            let tracked #observed=self.context.observe();
            #(#setup)*#(#transfer)*#(#observed_facts)*
            let #before=#owned.fragment();
            assert(Protocol #expr::#req(#before,#observed.fragment(),#(#args),*)) by {
                assert forall|#outer:Fragment #types,#pre:State #types|
                    #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                    implies State #expr::#enabled(#pre,#(#args),*)&&State #expr::#owners(#pre,#before,#observed.fragment(),#(#args),*) by{#(#facts)*}
            }
            let tracked #next=Protocol #expr::#adapter(#owned,&#observed,#(#args),*);
            let (#outer,#pre,#post)=choose|#outer:Fragment #types,#pre:State #types,#post:State #types|
                #pre.invariant()&&Fragment #expr::op(Fragment #expr::op(#before,#observed.fragment()),#outer)==Protocol #expr::embed(#pre)
                &&State #expr::#strong(#pre,#post,#(#args),*)&&#post.invariant()
                &&#next.fragment()==Protocol #expr::#owned_post(#before,#pre,#post,#(#args),*)
                &&Fragment #expr::op(Fragment #expr::op(#next.fragment(),#observed.fragment()),#outer)==Protocol #expr::embed(#post);
            #(#restore)*
            #result
        }
        pub proof fn #name(tracked &self,#(#params,)*#(#public_inputs),*)->(tracked #out:#output)
            requires #(#public_bounds,)*#(#public_requirements,)*
            ensures #(#public_returns,)*#(#public_assertions,)*#(#native_returns,)*
        {
            #(#invariant_uses)*
            Self::#helper(self,#(#args,)*#(#arguments),*)
        }
    })
}
