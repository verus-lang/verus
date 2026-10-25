//! The raw operations of the general emitter (`verified_general`): each transition's
//! `Protocol::t` with its requirement, outputs, witness, frame lemma and shared variant
//! (guards, initializers, storage exchanges and plain updates), and the local-ready API
//! of its steps.
use crate::ast::*;
use crate::hygiene::Binders;
use crate::verified_general::{
    Ctx, Footprint, Items, Names, guard_map_haves, guard_option_haves, guarded_storage,
};
use crate::verified_monoids as monoids;
use crate::verified_storage_tagged::Tagged;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;
use verus_syn::{Error, Ident};

/// The pieces of a non-init step's raw operations.
struct Step {
    /// That the owned fragment owns the variables the step changes.
    owned_req: Vec<TokenStream>,
    /// That the owned and shared fragments observe the fields the step reads.
    observed_req: Vec<TokenStream>,
    /// The body of `t_owned_post`, the owned fragment after the step.
    post_fragment: TokenStream,
    /// The statement calculus's chain of the frame lemma (`verified_chain::frame_chain`).
    frame_chain: TokenStream,
}

/// A `property!` or `readonly!` with a `guard`: `State::t_guarded`, the storage it
/// guards, and the raw operation borrowing the token and returning a reference into the
/// storage, with its requirement and frame lemma (and the local-ready API).
pub(crate) fn guard_items(
    ctx: &Ctx,
    tr: &Transition,
    names: &Names,
    read: &HashSet<String>,
    items: &mut Items,
) -> Result<(), Error> {
    let Ctx { sm, fields, st, se, pe, ft, pt, tt, .. } = ctx;
    let Names { name, pn, params, enabled, safety, run, req, frame, owners, b, .. } = names;
    let Binders { f, z, token, out, guard_key, .. } = b;
    let layout = ctx.storage.unwrap();
    let sty = layout.ty();
    let guarded = format_ident!("{}_guarded", name);
    let expression = guarded_storage(&tr.body, fields, layout)?;
    let map_haves = guard_map_haves(&tr.body, fields);
    let option_haves = guard_option_haves(&tr.body, fields);
    let observed_base = guard_observation(ctx, f, &map_haves, &option_haves);
    // The values the `have`s observe in `f` are the state's: the statement
    // calculus's chain (with the unit as the borrowed fragment) states them.
    let guard_links = if map_haves.is_empty() && option_haves.is_empty() {
        quote! {}
    } else {
        let chain = crate::verified_chain::chain(
            sm,
            tr,
            ft,
            &quote! {Self::__tsm_cfg_split},
            quote! {#f},
            quote! {<#ft>::unit()},
            z,
            &format_ident!("pre"),
        )?;
        quote! {
            assert(#se::#owners(pre,#f,<#ft>::unit(),#(#pn),*));
            #chain
        }
    };
    // The guard's storage fact, by a case split on each key's field.
    let guard_cases = layout.prove_le_by_cases(
        guard_key,
        quote! {Self::#guarded(#f,#(#pn),*)},
        quote! {Self::storage(pre)},
    );
    let guard_le = layout.le(quote! {Self::#guarded(#f,#(#pn),*)}, quote! {Self::storage(pre)});
    items
        .relations
        .push(quote! {pub open spec fn #guarded(pre:#st,#(#params),*)->#sty{#expression}});
    let mut observed_req = observed_requirements(ctx, read, quote! {#f});
    for (field, persistent, _) in option_haves.iter().filter(|(_, _, conditional)| !conditional) {
        observed_req.push(if *persistent {
            quote! {#f.#field is Some && #f.#field->Some_0 is Agree}
        } else {
            quote! {#f.#field is Some && #f.#field->Some_0 is Exclusive}
        });
    }
    let observe_equal: Vec<_> = sm
        .fields
        .iter()
        .filter(|field| read.contains(&field.name.to_string()))
        .map(|field| {
            let name = &field.name;
            quote! {pre.#name==Self::__observed(#f).#name}
        })
        .collect();
    items.operations.push(quote!{
        pub open spec fn #guarded(#f:#ft,#(#params),*)->#sty{#se::#guarded(#observed_base,#(#pn),*)}
        pub open spec fn #req(#f:#ft,#(#params),*)->bool {
            true #(&& #observed_req)* &&
            forall|#z:#ft,pre:#st|::vstd::prelude::imply(pre.invariant()&&<#ft>::op(#f,#z)==Self::embed(pre),
                #se::#owners(pre,#f,<#ft>::unit(),#(#pn),*)&&#se::#enabled(pre,#(#pn),*))
        }
        pub proof fn #frame(#f:#ft,#(#params),*)
            requires Self::#req(#f,#(#pn),*)
            ensures ::vstd::resource::tsm_storage::frame_guard::<#pt>(#f,Self::#guarded(#f,#(#pn),*))
        {
            // `frame_guard` is opaque; this is its proof (its users take it as an atom).
            reveal(::vstd::resource::tsm_storage::frame_guard);
            assert forall|#z:#ft,pre:#st|Self::invariant(pre)&&<#ft>::op(#f,#z)==Self::embed(pre)
                implies #guard_le by {
                <#ft>::op_unit(#f);
                assert(#se::#enabled(pre,#(#pn),*));
                let post=#se::#run(pre,#(#pn),*);
                assert(true #(&& #observe_equal)*);
                #guard_links
                assert(#se::#guarded(pre,#(#pn),*)==Self::#guarded(#f,#(#pn),*));
                // The guard's storage fact (with its user proof) comes from safety.
                #se::#safety(pre,#(#pn),*);
                #guard_cases
            }
        }
        pub proof fn #name(tracked #token:&#tt,#(#params),*)->(tracked #out:&#sty)
            requires Self::#req(#token.fragment(),#(#pn),*)
            ensures *#out==Self::#guarded(#token.fragment(),#(#pn),*)
        {Self::#frame(#token.fragment(),#(#pn),*);#token.guard(Self::#guarded(#token.fragment(),#(#pn),*))}
    });
    if ctx.is_local_ready(tr) {
        let declared_requires = crate::verified_readiness::declared_requires_spec(tr, st, params)?;
        let api = crate::verified_readiness::local_ready_guard_api(
            crate::verified_readiness::GuardContext {
                sm,
                tr,
                st,
                se,
                pe,
                ft,
                tt,
                sty: &sty,
                params,
                pn,
                observed: &observed_req,
                reads: &ctx.reads(read),
                chain: ctx.chained.contains(&name.to_string()),
            },
        )?;
        items.local_ready.push((names.name.clone(), quote! {#declared_requires #api}));
    }
    Ok(())
}

/// The state a guard's fragment `f` observes: `__observed(f)`, with the values the
/// `have`s bind read from `f`.
fn guard_observation(
    ctx: &Ctx,
    f: &Ident,
    map_haves: &[(Ident, verus_syn::Expr, bool)],
    option_haves: &[(Ident, bool, bool)],
) -> TokenStream {
    let Ctx { fields, se, .. } = ctx;
    // Values bound by `have m >= [k => ..]` on exclusive map fields are
    // observed from the owned fragment at k, so the guarded value stays
    // a function of the fragment and is linked to `pre` by map_owned_frame.
    let mut observed_fields: Vec<(Ident, Vec<verus_syn::Expr>)> = vec![];
    for (field, key, _) in map_haves {
        match observed_fields.iter_mut().find(|(name, _)| name == field) {
            Some((_, keys)) => keys.push(key.clone()),
            None => observed_fields.push((field.clone(), vec![key.clone()])),
        }
    }
    // Likewise for values bound by `have o >= Some(..)` on option
    // fields (linked to `pre` by option_owned_frame) and persistent
    // option fields (by persistent_option_owned_frame).
    let option_updates: Vec<_> = option_haves
        .iter()
        .map(|(field, persistent, _)| {
            if *persistent {
                quote! {#field: Some(#f.#field->Some_0->Agree_0)}
            } else {
                quote! {#field: Some(#f.#field->Some_0->Exclusive_0)}
            }
        })
        .collect();
    if observed_fields.is_empty() && option_updates.is_empty() {
        return quote! {Self::__observed(#f)};
    }
    let updates: Vec<_> = option_updates
        .iter()
        .cloned()
        .chain(observed_fields.iter().map(|(field, keys)| {
            let inserts =
                keys.iter().map(|k| quote! {.insert(#k, #f.#field.at(#k)->Some_0->Exclusive_0)});
            let empty = match fields[&field.to_string()].stype {
                ShardableType::IMap(..) => quote! {::vstd::imap::IMap::empty()},
                _ => quote! {::vstd::map::Map::empty()},
            };
            quote! {#field: #empty #(#inserts)*}
        }))
        .collect();
    quote! {#se{#(#updates,)* ..Self::__observed(#f)}}
}

/// That `fragment` observes each field in `read`: owns the variables and agrees on the
/// constants.
fn observed_requirements(
    ctx: &Ctx,
    read: &HashSet<String>,
    fragment: TokenStream,
) -> Vec<TokenStream> {
    ctx.reads(read)
        .into_iter()
        .map(|name| match ctx.fields[&name.to_string()].stype {
            ShardableType::Variable(_) => {
                quote! {#fragment.#name is Some &&#fragment.#name->Some_0 is Exclusive}
            }
            ShardableType::Constant(_) => {
                quote! {#fragment.#name is Some &&#fragment.#name->Some_0 is Agree}
            }
            _ => unreachable!(),
        })
        .collect()
}

/// An init transition's raw operation, which allocates the token (with the initial
/// storage, on machines with storage).
pub(crate) fn init_operation(ctx: &Ctx, names: &Names) -> TokenStream {
    let Ctx { st, se, tt, te, .. } = ctx;
    let Names { name, pn, params, strong, enabled, run, b, .. } = names;
    let Binders { base, s, out, .. } = b;
    let base_req = quote! {#se::#enabled(#(#pn),*)};
    if let Some(layout) = ctx.storage {
        let sty = layout.ty();
        quote! {
            pub proof fn #name(tracked #base:#sty,#(#params),*)->(tracked #out:#tt)
                requires #base_req,forall|#s:#st|::vstd::prelude::imply(#se::#strong(#s,#(#pn),*),#base==#s.__storage())
                ensures exists|#s:#st|#se::#name(#s,#(#pn),*)&&#s.invariant()&&#out.fragment()==Self::embed(#s)
            {let #s=#se::#run(#(#pn),*);#te::alloc_state(#s,#base)}
        }
    } else {
        quote! {
            pub proof fn #name(#(#params),*)->(tracked #out:#tt)
                requires #base_req
                ensures exists|#s:#st| #se::#name(#s,#(#pn),*) &&#s.invariant()&&#out.fragment()==Self::embed(#s)
            {let #s=#se::#run(#(#pn),*);#te::alloc_state(#s)}
        }
    }
}

/// Adds a non-init step's raw operations (and its local-ready API) to `items`.
pub(crate) fn step_items(
    ctx: &Ctx,
    tr: &Transition,
    names: &Names,
    footprint: &Footprint,
    read: &HashSet<String>,
    deposit: Option<TokenStream>,
    items: &mut Items,
) -> Result<(), Error> {
    let step = step_parts(ctx, tr, names, footprint, read)?;
    items.operations.push(match ctx.storage {
        Some(layout) => storage_operations(ctx, names, &step, footprint, layout),
        None => plain_operations(ctx, names, &step),
    });
    if ctx.is_local_ready(tr) {
        if ctx.storage.is_none() {
            items.operations.push(plain_witness(ctx, names));
        }
        let api = step_local_ready(ctx, tr, names, &step, footprint, read, deposit)?;
        items.local_ready.push((names.name.clone(), api));
    }
    Ok(())
}

/// The requirements, the owned post-fragment and the frame chain of a non-init step.
fn step_parts(
    ctx: &Ctx,
    tr: &Transition,
    names: &Names,
    footprint: &Footprint,
    read: &HashSet<String>,
) -> Result<Step, Error> {
    let Ctx { sm, fields, ft, fe, marker_value, decls, .. } = ctx;
    let Names { pn, owned_post, b: Binders { owned, h, post_fragment, .. }, .. } = names;
    let changed = &footprint.changed;
    let updated_variables: Vec<_> = decls
        .names
        .iter()
        .copied()
        .filter(|name| {
            changed.contains(&name.to_string())
                && matches!(fields[&name.to_string()].stype, ShardableType::Variable(_))
        })
        .collect();
    let owned_req = updated_variables
        .iter()
        .map(|name| quote! {#owned.#name is Some &&#owned.#name->Some_0 is Exclusive})
        .collect();
    let observed_req = observed_requirements(ctx, read, quote! {<#ft>::op(#owned,#h)});
    // The owned fragment after the transition: the chain's fragment (with the
    // patterns' values from `pre`) for the monoid fields, and the post-state's
    // values of the updated variables.
    let post_walk = crate::verified_chain::owned_post_fragment(sm, tr, ft)?;
    let fields_after: Vec<_> = decls
        .names
        .iter()
        .map(|name| {
            if monoids::is_monoid_type(&fields[&name.to_string()].stype) {
                quote! {#name:#post_fragment.#name}
            } else if changed.contains(&name.to_string()) {
                quote! {#name:Some(ExclusiveRA::Exclusive(post.#name))}
            } else {
                quote! {#name:#owned.#name}
            }
        })
        .collect();
    let frame_chain = crate::verified_chain::frame_chain(
        sm,
        tr,
        ft,
        &quote! {Self::__tsm_cfg_split},
        &quote! {Self::__tsm_cfg_join},
        quote! {Self::#owned_post(#owned,pre,post,#(#pn),*)},
        &updated_variables,
    )?;
    Ok(Step {
        owned_req,
        observed_req,
        post_fragment: quote! {{let #post_fragment = #post_walk; #fe{#marker_value #(#fields_after),*}}},
        frame_chain,
    })
}

/// The local-ready API of a non-init step (`verified_readiness::local_ready_api`), with
/// the inlined `deposited` on machines with storage; over the plain token, it has no
/// deposits and withdrawals.
fn step_local_ready(
    ctx: &Ctx,
    tr: &Transition,
    names: &Names,
    step: &Step,
    footprint: &Footprint,
    read: &HashSet<String>,
    deposit: Option<TokenStream>,
) -> Result<TokenStream, Error> {
    let Ctx { sm, st, se, pe, ft, tt, result_ty, result_expr, .. } = ctx;
    let Names { name, pn, params, .. } = names;
    let declared_requires = crate::verified_readiness::declared_requires_spec(tr, st, params)?;
    let local_deposited = match (ctx.storage, deposit) {
        (Some(layout), Some(expression)) => {
            let sty = layout.ty();
            quote! {#[verifier::inline] pub open spec fn deposited(pre:#st,#(#params),*)->#sty{#expression}}
        }
        _ => quote! {},
    };
    let with_storage = ctx.storage.is_some();
    let api = crate::verified_readiness::local_ready_api(crate::verified_readiness::Context {
        sm,
        tr,
        st,
        se,
        pe,
        ft,
        tt,
        result: result_ty,
        result_expr,
        params,
        pn,
        owned: &step.owned_req,
        observed: &step.observed_req,
        reads: &ctx.reads(read),
        storage: ctx.storage,
        deposits: with_storage && footprint.deposits,
        withdraws: with_storage && footprint.withdraws,
        paired: with_storage && footprint.paired,
        chain: ctx.chained.contains(&name.to_string()),
    })?;
    Ok(quote! {#declared_requires #local_deposited #api})
}

/// The raw operations of a step on a machine without storage: its requirement, outputs
/// and frame lemma, and the update of the owned token (with a shared one).
fn plain_operations(ctx: &Ctx, names: &Names, step: &Step) -> TokenStream {
    let Ctx { st, se, ft, pt, tt, .. } = ctx;
    let Names {
        name,
        pn,
        params,
        strong,
        enabled,
        run,
        req,
        output,
        frame,
        owned_post,
        shared: with_shared,
        owners,
        b,
        ..
    } = names;
    let Binders { owned, h, z, new, shared, outputs, out, empty, .. } = b;
    let Step { owned_req, observed_req, post_fragment, frame_chain } = step;
    quote! {
        pub open spec fn #owned_post(#owned:#ft,pre:#st,post:#st,#(#params),*)->#ft {#post_fragment}
        pub open spec fn #req(#owned:#ft,#h:#ft,#(#params),*)->bool {
            true #(&& #owned_req)* #(&& #observed_req)* && forall|#z:#ft,pre:#st|::vstd::prelude::imply(#[trigger] ::vstd::resource::tsm::completes_with::<#pt>(<#ft>::op(#owned,#h),#z,pre),
                #se::#enabled(pre,#(#pn),*)&&#se::#owners(pre,#owned,#h,#(#pn),*))
        }
        pub open spec fn #output(#owned:#ft,#h:#ft,#new:#ft,#(#params),*)->bool {
            exists|#z:#ft,pre:#st,post:#st|pre.invariant()&&<#ft>::op(<#ft>::op(#owned,#h),#z)==Self::embed(pre)
            && #se::#strong(pre,post,#(#pn),*)&&post.invariant()&&#new==Self::#owned_post(#owned,pre,post,#(#pn),*)
            &&<#ft>::op(<#ft>::op(#new,#h),#z)==Self::embed(post)
        }
        pub proof fn #frame(#owned:#ft,#h:#ft,#(#params),*)
            requires Self::#req(#owned,#h,#(#pn),*)
            ensures ::vstd::resource::tsm::frame_update_nondeterministic::<#pt>(
                <#ft>::op(#owned,#h),ISet::new(|#new:#ft|Self::#output(#owned,#h,#new,#(#pn),*)).map(|#new:#ft|<#ft>::op(#new,#h)))
        {
            let #outputs=ISet::new(|#new:#ft|Self::#output(#owned,#h,#new,#(#pn),*));
            assert forall|#z:#ft,pre:#st|pre.invariant()&&<#ft>::op(<#ft>::op(#owned,#h),#z)==Self::embed(pre)
                implies ::vstd::resource::tsm::update_point::<#pt>(#owned,#h,#z,pre,#outputs) by {
                assert(::vstd::resource::tsm::completes_with::<#pt>(<#ft>::op(#owned,#h),#z,pre));
                assert(#se::#owners(pre,#owned,#h,#(#pn),*));
                let post=#se::#run(pre,#(#pn),*);
                #frame_chain
                let #new=Self::#owned_post(#owned,pre,post,#(#pn),*);
                <#ft>::associative(#new,#h,#z);
                assert(Self::#output(#owned,#h,#new,#(#pn),*));
                ::vstd::resource::tsm::update_point_intro::<#pt>(#owned,#h,#z,pre,#outputs,#new,post);
            }
            ::vstd::resource::tsm::frame_update_by_points::<#pt>(#owned,#h,#outputs);
        }
        pub proof fn #with_shared(tracked #owned:#tt,tracked #shared:&#tt,#(#params),*)->(tracked #out:#tt)
            requires #owned.loc()==#shared.loc(),Self::#req(#owned.fragment(),#shared.fragment(),#(#pn),*)
            ensures #out.loc()==#owned.loc(),Self::#output(#owned.fragment(),#shared.fragment(),#out.fragment(),#(#pn),*)
        {
            Self::#frame(#owned.fragment(),#shared.fragment(),#(#pn),*);
            let #outputs=ISet::new(|#new:#ft|Self::#output(#owned.fragment(),#shared.fragment(),#new,#(#pn),*));
            #owned.update_nondeterministic_with_shared(#shared,#outputs)
        }
        pub proof fn #name(tracked #owned:#tt,#(#params),*)->(tracked #out:#tt)
            requires Self::#req(#owned.fragment(),<#ft>::unit(),#(#pn),*)
            ensures #out.loc()==#owned.loc(),Self::#output(#owned.fragment(),<#ft>::unit(),#out.fragment(),#(#pn),*)
        {
            let tracked #empty=#owned.empty();
            Self::#with_shared(#owned,&#empty,#(#pn),*)
        }
    }
}

/// The witness of a plain step's outputs, for its local-ready API: a completion and the
/// pre- and post-states that produce the new fragment.
fn plain_witness(ctx: &Ctx, names: &Names) -> TokenStream {
    let Ctx { st, se, ft, .. } = ctx;
    let Names { pn, params, strong, output, owned_post, witness, b, .. } = names;
    let Binders { owned, h, z, new, result, .. } = b;
    let output_at = |frame: TokenStream, pre: TokenStream, post: TokenStream| {
        quote! {
            #pre.invariant()&&<#ft>::op(<#ft>::op(#owned,#h),#frame)==Self::embed(#pre)
            && #se::#strong(#pre,#post,#(#pn),*)&&#post.invariant()&&#new==Self::#owned_post(#owned,#pre,#post,#(#pn),*)
            &&<#ft>::op(<#ft>::op(#new,#h),#frame)==Self::embed(#post)
        }
    };
    let chosen = output_at(quote! {#z}, quote! {pre}, quote! {post});
    let witnessed = output_at(quote! {#result.2}, quote! {#result.0}, quote! {#result.1});
    quote! {
        pub proof fn #witness(#owned:#ft,#h:#ft,#new:#ft,#(#params),*)->(#result:(#st,#st,#ft))
            requires Self::#output(#owned,#h,#new,#(#pn),*)
            ensures #witnessed
        {
            let (#z,pre,post)=choose|#z:#ft,pre:#st,post:#st| #chosen;
            (pre,post,#z)
        }
    }
}

/// The operations of a transition on a machine with storage: its requirement, outputs,
/// witness and frame lemma, and its storage exchanges.
fn storage_operations(
    ctx: &Ctx,
    names: &Names,
    step: &Step,
    footprint: &Footprint,
    storage: &Tagged,
) -> TokenStream {
    let Ctx { st, se, ft, pt, tt, .. } = ctx;
    let Names {
        name,
        pn,
        params,
        strong,
        enabled,
        run,
        req,
        output,
        frame,
        owned_post,
        shared: with_shared,
        deposited,
        owners,
        witness,
        b,
        ..
    } = names;
    let Binders {
        owned,
        h,
        z,
        new,
        shared,
        outputs,
        out,
        result,
        deposit,
        withdrawn,
        pair,
        key,
        ..
    } = b;
    let Step { owned_req, observed_req, post_fragment, frame_chain } = step;
    let Footprint { deposits, withdraws, paired, .. } = *footprint;
    let map = storage.ty();
    let unit = storage.unit();
    let tracked_unit = storage.tracked_unit();
    let pre_storage = quote! {pre.__storage()};
    let post_storage = quote! {post.__storage()};
    let withdrawn_spec =
        storage.minus(storage.op(pre_storage.clone(), quote! {#deposit}), post_storage.clone());
    let output_at = format_ident!("__tsm_{}_output_at", name);
    let outputs_set = quote! {ISet::new(|#pair:(#ft,#map)|Self::#output(#owned,#h,#pair.0,#deposit,#pair.1,#(#pn),*))};
    let lifted = quote! {#outputs_set.map(|#pair:(#ft,#map)|(<#ft>::op(#pair.0,#h),#pair.1))};
    let ret = if withdraws {
        quote! {tracked #out:(#tt,#map)}
    } else {
        quote! {tracked #out:#tt}
    };
    let out_token = if withdraws {
        quote! {#out.0}
    } else {
        quote! {#out}
    };
    let deposit_param = if deposits {
        quote! {tracked #deposit:#map,}
    } else {
        quote! {}
    };
    let deposit_spec = if deposits {
        quote! {#deposit}
    } else {
        unit.clone()
    };
    let deposit_init = if deposits {
        quote! {}
    } else {
        quote! {let tracked #deposit:#map=#tracked_unit;}
    };
    let return_ens = if withdraws {
        quote! {Self::#output(#owned.fragment(),#shared.fragment(),#out.0.fragment(),#deposit_spec,#out.1,#(#pn),*)}
    } else {
        quote! {Self::#output(#owned.fragment(),#shared.fragment(),#out.fragment(),#deposit_spec,#unit,#(#pn),*)}
    };
    let plain_ens = if withdraws {
        quote! {Self::#output(#owned.fragment(),<#ft>::unit(),#out.0.fragment(),#deposit_spec,#out.1,#(#pn),*)}
    } else {
        quote! {Self::#output(#owned.fragment(),<#ft>::unit(),#out.fragment(),#deposit_spec,#unit,#(#pn),*)}
    };
    let return_value = if withdraws {
        quote! {(#out,#withdrawn)}
    } else {
        quote! {
            assert(#withdrawn==#unit);
            #out
        }
    };
    // A step that withdraws nothing and has one storage operation per path:
    // its outputs state `withdrawn == empty` only, and the frame leaves the
    // storage bookkeeping to `exchange_point_intro_monotone`.
    let monotone = !withdraws && !paired;
    let withdrawn_value = if monotone {
        quote! {}
    } else {
        quote! {&&#withdrawn==#withdrawn_spec}
    };
    let withdrawal_shape = if withdraws {
        quote! {true}
    } else {
        quote! {#withdrawn==#unit}
    };
    let st_pre = quote! {Self::storage(pre)};
    let st_post = quote! {Self::storage(post)};
    let whole = storage.op(st_pre.clone(), quote! {#deposit});
    let withdrawal_proof = if withdraws {
        quote! {}
    } else if paired {
        // The old storage and the deposit are covered by the new storage
        // (the executor's `covered` fact): nothing is withdrawn.
        quote! {
            assert(::vstd::prelude::ext_equal(#withdrawn,#unit)) by {
                assert forall|#key| !#withdrawn.contains_key(#key) by {};
            }
        }
    } else {
        quote! {::vstd::resource::tsm_storage::storage_withdrawn_none(#st_pre,#st_post,#deposit);}
    };
    let output_storage = if paired {
        let disjoint = storage.disjoint(pre_storage.clone(), quote! {#deposit});
        let within =
            storage.le(post_storage.clone(), storage.op(pre_storage.clone(), quote! {#deposit}));
        quote! {
            #deposit==#se::#deposited(pre,#(#pn),*)
                &&#disjoint
                &&#within
        }
    } else {
        let delta = storage.minus(post_storage.clone(), pre_storage.clone());
        quote! {#deposit==#delta}
    };
    let transfer_proof = if paired {
        let disjoint = storage.disjoint(st_pre.clone(), quote! {#deposit});
        let within = storage.le(st_post.clone(), whole.clone());
        quote! {
            assert(#deposit==#se::#deposited(pre,#(#pn),*));
            assert(#disjoint);
            assert(#within);
        }
    } else {
        quote! {}
    };
    let frame_withdrawn = if monotone {
        quote! {assert(Self::#output_at(#owned,#h,#new,#deposit,#unit,#(#pn,)* #z,pre,post));}
    } else {
        let difference = storage.minus(whole.clone(), st_post.clone());
        quote! {
            let #withdrawn=#difference;
            #withdrawal_proof
            assert(Self::#output_at(#owned,#h,#new,#deposit,#withdrawn,#(#pn,)* #z,pre,post));
        }
    };
    // The exchange's witnesses for one frame (`exchange_point`).
    let point_intro = if paired {
        quote! {::vstd::resource::tsm_storage::exchange_point_intro::<#pt>(#owned,#h,#z,pre,#deposit,#outputs,#new,post);}
    } else if monotone {
        quote! {::vstd::resource::tsm_storage::exchange_point_intro_monotone::<#pt>(#owned,#h,#z,pre,#deposit,#outputs,#new,post);}
    } else {
        quote! {::vstd::resource::tsm_storage::exchange_point_intro_delta::<#pt>(#owned,#h,#z,pre,#deposit,#outputs,#new,post);}
    };
    quote! {
            pub open spec fn #owned_post(#owned:#ft,pre:#st,post:#st,#(#params),*)->#ft {#post_fragment}
            pub open spec fn #req(#owned:#ft,#h:#ft,#deposit:#map,#(#params),*)->bool {
                true #(&& #owned_req)* #(&& #observed_req)* &&
                forall|#z:#ft,pre:#st|::vstd::prelude::imply(
                    #[trigger] ::vstd::resource::tsm::completes_with::<#pt>(<#ft>::op(#owned,#h),#z,pre),
                    #se::#enabled(pre,#(#pn),*)&&#deposit==#se::#deposited(pre,#(#pn),*)&&#se::#owners(pre,#owned,#h,#(#pn),*))
            }
            pub open spec fn #output_at(#owned:#ft,#h:#ft,#new:#ft,#deposit:#map,#withdrawn:#map,#(#params,)* #z:#ft,pre:#st,post:#st)->bool {
                pre.invariant()&&<#ft>::op(<#ft>::op(#owned,#h),#z)==Self::embed(pre)
                    &&#se::#strong(pre,post,#(#pn),*)&&post.invariant()&&#new==Self::#owned_post(#owned,pre,post,#(#pn),*)
                    &&<#ft>::op(<#ft>::op(#new,#h),#z)==Self::embed(post)
                    &&(#output_storage)
                    #withdrawn_value
            }
            pub open spec fn #output(#owned:#ft,#h:#ft,#new:#ft,#deposit:#map,#withdrawn:#map,#(#params),*)->bool {
                #withdrawal_shape && exists|#z:#ft,pre:#st,post:#st| #[trigger] Self::#output_at(#owned,#h,#new,#deposit,#withdrawn,#(#pn,)* #z,pre,post)
            }
            pub proof fn #witness(#owned:#ft,#h:#ft,#new:#ft,#deposit:#map,#withdrawn:#map,#(#params),*)
                ->(#result:(#st,#st,#ft))
                requires Self::#output(#owned,#h,#new,#deposit,#withdrawn,#(#pn),*)
                ensures Self::#output_at(#owned,#h,#new,#deposit,#withdrawn,#(#pn,)* #result.2,#result.0,#result.1)
            {
                let (#z,pre,post)=choose|#z:#ft,pre:#st,post:#st| #[trigger] Self::#output_at(#owned,#h,#new,#deposit,#withdrawn,#(#pn,)* #z,pre,post);
                (pre,post,#z)
            }
            pub proof fn #frame(#owned:#ft,#h:#ft,#deposit:#map,#(#params),*)
                requires Self::#req(#owned,#h,#deposit,#(#pn),*)
                ensures ::vstd::resource::tsm_storage::frame_exchange_nondeterministic::<#pt>(<#ft>::op(#owned,#h),#deposit,#lifted)
            {
                let #outputs=#outputs_set;
                assert forall|#z:#ft,pre:#st|Self::invariant(pre)&&<#ft>::op(<#ft>::op(#owned,#h),#z)==Self::embed(pre)
                    implies ::vstd::resource::tsm_storage::exchange_point::<#pt>(#owned,#h,#z,pre,#deposit,#outputs) by {
                        assert(::vstd::resource::tsm::completes_with::<#pt>(<#ft>::op(#owned,#h),#z,pre));
                        let post=#se::#run(pre,#(#pn),*);
                        #frame_chain
                        let #new=Self::#owned_post(#owned,pre,post,#(#pn),*);
                        <#ft>::associative(#new,#h,#z);
                        #transfer_proof
                        #frame_withdrawn
                        #point_intro
                    }
                ::vstd::resource::tsm_storage::frame_exchange_by_points::<#pt>(#owned,#h,#deposit,#outputs);
            }
    pub proof fn #with_shared(tracked #owned:#tt,tracked #shared:&#tt,#deposit_param #(#params),*)->(#ret)
                requires #owned.loc()==#shared.loc(),Self::#req(#owned.fragment(),#shared.fragment(),#deposit_spec,#(#pn),*)
                ensures #out_token.loc()==#owned.loc(),#return_ens
            {
                #deposit_init
                Self::#frame(#owned.fragment(),#shared.fragment(),#deposit,#(#pn),*);
                let #outputs=ISet::new(|#pair:(#ft,#map)|Self::#output(#owned.fragment(),#shared.fragment(),#pair.0,#deposit,#pair.1,#(#pn),*));
                let tracked (#out,#withdrawn)=#owned.exchange_nondeterministic_with_shared(#shared,#deposit,#outputs);
                #return_value
            }
            pub proof fn #name(tracked #owned:#tt,#deposit_param #(#params),*)->(#ret)
                requires Self::#req(#owned.fragment(),<#ft>::unit(),#deposit_spec,#(#pn),*)
                ensures #out_token.loc()==#owned.loc(),#plain_ens
            {
                #deposit_init
                <#ft>::op_unit(#owned.fragment());
                Self::#frame(#owned.fragment(),<#ft>::unit(),#deposit,#(#pn),*);
                let #outputs=ISet::new(|#pair:(#ft,#map)|Self::#output(#owned.fragment(),<#ft>::unit(),#pair.0,#deposit,#pair.1,#(#pn),*));
                ::vstd::resource::tsm_storage::storage_outputs_unit::<#pt>(#outputs);
                let tracked (#out,#withdrawn)=#owned.exchange_nondeterministic(#deposit,#outputs);
                #return_value
            }
        }
}
