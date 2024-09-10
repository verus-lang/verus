//! Output all the generated code specific to tokenized state machines.
//! We print declarations for:
//!
//!  * The Instance type
//!  * All the Token types for shardable fields
//!  * #[verifier::proof] methods for each transition (including init and readonly transitions)

use crate::ast::{
    Arm, Field, Lemma, LetKind, MonoidElt, MonoidStmtType, ShardableType, SpecialOp, SplitKind,
    Transition, TransitionKind, TransitionStmt, SM,
};
use crate::field_access_visitor::{find_all_accesses, visit_field_accesses};
use crate::parse_token_stream::SMBundle;
use crate::to_relation::{conjunct_opt, emit_match};
use crate::to_token_stream::{
    get_self_ty, get_self_ty_turbofish, impl_decl_stream, name_with_type_args,
    name_with_type_args_turbofish, shardable_type_to_type,
};
use crate::token_transition_checks::{check_ordering_remove_have_add, check_unsupported_updates};
use crate::util::{combine_errors_or_ok, is_definitely_irrefutable};
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use std::collections::HashMap;
use std::collections::HashSet;
use syn_verus::parse;
use syn_verus::parse::Error;
use syn_verus::spanned::Spanned;
use syn_verus::{Expr, Ident, Pat, Type};

// Misc. definitions for various identifiers we use
// Note that everything is going to be inside a module, so for example,
// the user will refer to the Instance type as `Name::Instance`.

fn inst_type_name(sm_name: &Ident) -> Ident {
    Ident::new("Instance", sm_name.span())
}

fn inst_type(sm: &SM) -> Type {
    name_with_type_args(&inst_type_name(&sm.name), sm)
}

fn field_token_type_name(field: &Field) -> Ident {
    let name = &field.name.to_string();
    Ident::new(&name, field.name.span())
}

fn field_token_data_type_name(field: &Field) -> Ident {
    let name = field.name.to_string() + "_token_data";
    Ident::new(&name, field.name.span())
}

fn field_token_type(sm: &SM, field: &Field) -> Type {
    name_with_type_args(&field_token_type_name(field), sm)
}

fn field_token_data_type(sm: &SM, field: &Field) -> Type {
    name_with_type_args(&field_token_data_type_name(field), sm)
}

fn field_token_type_turbofish(sm: &SM, field: &Field) -> Type {
    name_with_type_args_turbofish(&field_token_type_name(field), sm)
}

fn field_token_data_type_turbofish(sm: &SM, field: &Field) -> Type {
    name_with_type_args_turbofish(&field_token_data_type_name(field), sm)
}

fn field_token_field_name(field: &Field) -> Ident {
    // just call it value rather than repeat the field name
    // else, the user will be writing foo.foo everywhere
    Ident::new("value", field.name.span())
}

fn nondeterministic_read_spec_out_name(field: &Field) -> Ident {
    let name = "original_field_".to_string() + &field.name.to_string();
    Ident::new(&name, field.name.span())
}

fn stored_object_type(field: &Field) -> Type {
    match &field.stype {
        ShardableType::StorageOption(ty) => ty.clone(),
        ShardableType::StorageMap(_key, ty) => ty.clone(),
        ShardableType::Variable(_)
        | ShardableType::Constant(_)
        | ShardableType::NotTokenized(_)
        | ShardableType::Option(_)
        | ShardableType::Map(_, _)
        | ShardableType::PersistentOption(_)
        | ShardableType::PersistentMap(_, _)
        | ShardableType::PersistentSet(_)
        | ShardableType::PersistentCount
        | ShardableType::PersistentBool
        | ShardableType::Multiset(_)
        | ShardableType::Set(_)
        | ShardableType::Bool
        | ShardableType::Count => {
            panic!("stored_object_type");
        }
    }
}

fn exchange_name(tr: &Transition) -> Ident {
    tr.name.clone()
}

fn transition_arg_name(field: &Field) -> Ident {
    let name = "param_token_".to_string() + &field.name.to_string();
    Ident::new(&name, field.name.span())
}

fn option_relation_post_condition_name(field: &Field, strict: bool) -> Ident {
    if strict {
        Ident::new("option_agree_strict", field.name.span())
    } else {
        Ident::new("option_agree", field.name.span())
    }
}

fn set_relation_post_condition_name(field: &Field, strict: bool) -> Ident {
    if strict {
        Ident::new("set_agree_strict", field.name.span())
    } else {
        Ident::new("set_agree", field.name.span())
    }
}

fn bool_relation_post_condition_name(field: &Field, strict: bool) -> Ident {
    if strict {
        Ident::new("bool_agree_strict", field.name.span())
    } else {
        Ident::new("bool_agree", field.name.span())
    }
}

fn option_relation_post_condition_qualified_name(sm: &SM, field: &Field, strict: bool) -> Type {
    let ty = field_token_type_turbofish(sm, field);
    let name = option_relation_post_condition_name(field, strict);
    Type::Verbatim(quote! { #ty::#name })
}

fn set_relation_post_condition_qualified_name(sm: &SM, field: &Field, strict: bool) -> Type {
    let ty = field_token_type_turbofish(sm, field);
    let name = set_relation_post_condition_name(field, strict);
    Type::Verbatim(quote! { #ty::#name })
}

fn bool_relation_post_condition_qualified_name(sm: &SM, field: &Field, strict: bool) -> Type {
    let ty = field_token_type_turbofish(sm, field);
    let name = bool_relation_post_condition_name(field, strict);
    Type::Verbatim(quote! { #ty::#name })
}

fn map_relation_post_condition_name(field: &Field, strict: bool) -> Ident {
    if strict {
        Ident::new("map_agree_strict", field.name.span())
    } else {
        Ident::new("map_agree", field.name.span())
    }
}

fn map_relation_post_condition_qualified_name(sm: &SM, field: &Field, strict: bool) -> Type {
    let ty = field_token_type_turbofish(sm, field);
    let name = map_relation_post_condition_name(field, strict);
    Type::Verbatim(quote! { #ty::#name })
}

fn multiset_relation_post_condition_name(field: &Field, strict: bool) -> Ident {
    if strict {
        Ident::new("multiset_agree_strict", field.name.span())
    } else {
        Ident::new("multiset_agree", field.name.span())
    }
}

fn multiset_relation_post_condition_qualified_name(sm: &SM, field: &Field, strict: bool) -> Type {
    let ty = field_token_type_turbofish(sm, field);
    let name = multiset_relation_post_condition_name(field, strict);
    Type::Verbatim(quote! { #ty::#name })
}

/// Print declaration for the Instance type.
///
/// From the user's perspective, this should just be an opaque, unforgeable token type
/// that serves as an identifier for a protocol instance and contains the constants
/// for the instance.
///
/// Formally, this token should be derived in terms of a monoid derived from the state
/// machine state. (See `monoid-formalism.md`.) Since that formalism is not
/// implemented mechanically
/// in Verus, we instead make the state itself a field. This is kind of meaningless, but it
/// serves as a placeholder and does result in the necessary dependency edge between this
/// struct and the type struct. The fields are private, so they shouldn't matter to the user.
///
/// Another thing is that we need the `Instance` struct to have the correct Send/Sync traits.
/// (All the other token types will then inherit those traits. The Senc/Synd traits of
/// the Instance should depend on the Sync/Send traits of the storage types.
/// In particular, the Instance should be Sync+Send iff the storage types are all Sync+Send.
/// Otherwise, the Instance type should have neither.
/// Initially, this rule might seem a little extra-restrictive, but we need this restriction
/// because if it is possible for the instance to interact with another thread at all, it
/// could conceivably do arbitrary withdraw/deposits (thus 'sending' the storage objects
/// to the other thread) or arbitrary guards (thus 'syncing' the storage objects to the
/// other thread). Due to the flexibility of the guard protocol, this could theoretically
/// happen regardless of whether the instance/tokens are synced or sent to the other thread.
///
/// TODO make sure that the Instance/tokens don't inherit !Sync or !Send negative-instances
/// from the other fields where it doesn't matter. (Completeness issue)

fn instance_struct_stream(sm: &SM) -> TokenStream {
    let insttype = inst_type_name(&sm.name);
    let self_ty = get_self_ty(sm);
    let gen = &sm.generics;
    let attrs = &sm.attrs;

    let storage_types = get_storage_type_tuple(sm);

    return quote_vstd! { vstd =>
        #[cfg_attr(verus_keep_ghost, verifier::proof)]
        #[allow(non_camel_case_types)]
        #(#attrs)*
        pub struct #insttype #gen {
            // This is not marked external_body, but the fields are private, so the
            // user should not be able to do illegal things with this type from outside
            // the module created by the macro.
            // For example, this prevents the user from constructing an instance.
            // However, since it's not marked external_body,
            // Verus will still look at the fields when doing its type hierarchy analysis.

            #[cfg_attr(verus_keep_ghost, verifier::spec)] send_sync: #vstd::state_machine_internal::SyncSendIfSyncSend<#storage_types>,
            #[cfg_attr(verus_keep_ghost, verifier::spec)] state: #self_ty,
            #[cfg_attr(verus_keep_ghost, verifier::spec)] location: #vstd::prelude::int,
        }
    };
}

/// If the SM has storage types T1, T2, ...
/// this returns the tuple type (T1, T2, ...).
/// Uses the "inner" type (e.g., the X in Option<X>, not Option<X> itself)
fn get_storage_type_tuple(sm: &SM) -> Type {
    let types: Vec<Type> = sm
        .fields
        .iter()
        .filter_map(
            |field| if field.stype.is_storage() { Some(stored_object_type(field)) } else { None },
        )
        .collect();
    Type::Verbatim(quote! { (#(#types),*) })
}

/// Add a `clone()` method to the Instance type (or any other type which is cloneable).
/// This is safe, because the Instance object effectively just represents
///
///   * the fact that the protocol exists, and has been initialized
///   * any constants associated to the protocol
///
/// TODO it would be even better to add a Copy instance as well; however, this
/// currently runs into Verus limitations with deriving instances.
fn trusted_clone() -> TokenStream {
    return quote_vstd! { vstd =>
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #[verifier::proof]
        #[verifier::external_body] /* vattr */
        #[verifier::returns(proof)] /* vattr */
        pub fn clone(#[verifier::proof] &self) -> Self {
            ensures(|s: Self| #vstd::prelude::equal(*self, s));
            ::core::unimplemented!();
        }
    };
}

/// Create the struct for a Token.
/// Can create any combination of three fields: key, value, count.
/// The `count` field, when present, always has type `nat`;
/// for the other two, when present, the types are provided as arguments.
///
/// In general the 'key' field is used when something is unique
/// And the 'count' is for nats that are additive.
///
/// For example:
///   'option' only has a value
///   'map' strategy has a key and a value
///   'set' only has a key,
///   'count' only has a count field
///   'multiset' has key and count
///
/// The 'multiset' is kind of tricky but the idea is that a Multiset<V>
/// is basically a Map<V, nat>. So the V is treated as a 'key' here
/// and if you have multiple elements of the same value, that's represented
/// by having a higher counter.

fn token_struct_stream(
    sm: &SM,
    field: &Field,
    key_ty: Option<&Type>,
    value_ty: Option<&Type>,
    count: bool,
) -> TokenStream {
    let tokenname = field_token_type_name(field);
    let tokenname_data = field_token_data_type_name(field);
    let insttype = inst_type(sm);
    let token_data_ty = field_token_data_type(sm, field);
    let token_ty = field_token_type(sm, field);
    let gen = &sm.generics;
    let attrs = &sm.attrs;

    let impldecl = impl_decl_stream(&field_token_type(sm, field), &sm.generics);
    let mut impl_token_stream = collection_relation_fns_stream(sm, field);

    if field.stype.is_persistent() {
        impl_token_stream.extend(trusted_clone());
    }

    let key_field = match key_ty {
        Some(key_ty) => quote! { #[cfg_attr(verus_keep_ghost, verifier::spec)] pub key: #key_ty, },
        None => TokenStream::new(),
    };

    let value_field = match value_ty {
        Some(value_ty) => {
            quote! { #[cfg_attr(verus_keep_ghost, verifier::spec)] pub value: #value_ty, }
        }
        None => TokenStream::new(),
    };

    let count_field = if count {
        quote_vstd! { vstd => #[cfg_attr(verus_keep_ghost, verifier::spec)] pub count: #vstd::prelude::nat }
    } else {
        TokenStream::new()
    };

    return quote_vstd! { vstd =>
        #[cfg_attr(verus_keep_ghost, verifier::proof)]
        #[allow(non_camel_case_types)]
        #(#attrs)*
        pub struct #tokenname#gen {
            // These are private so they can't be accessed outside this module.
            // I would have marked it external_body, but I want to make sure
            // VIR knows about the dummy_instance field. It is important for
            // the type well-foundedness checks.

            #[cfg_attr(verus_keep_ghost, verifier::proof)] dummy_instance: #insttype,
            no_copy: #vstd::state_machine_internal::NoCopy,
        }

        #[cfg_attr(verus_keep_ghost, verifier::spec)]
        #[allow(non_camel_case_types)]
        #(#attrs)*
        pub struct #tokenname_data#gen {
            #[cfg_attr(verus_keep_ghost, verifier::spec)] pub instance: #insttype,
            #key_field
            #value_field
            #count_field
        }

        #impldecl {
            #[cfg(verus_keep_ghost_body)]
            #[verus::internal(verus_macro)]
            #[verus::internal(open)] /* vattr */
            #[verifier::external_body] /* vattr */
            #[verifier::spec]
            pub fn view(self) -> #token_data_ty { ::core::unimplemented!() }

            // Return an arbitrary token. It's not possible to do anything interesting
            // with this token because it doesn't have a specified instance.

            #[cfg(verus_keep_ghost_body)]
            #[verus::internal(verus_macro)]
            #[verifier::external_body] /* vattr */
            #[verifier::returns(proof)] /* vattr */
            #[verifier::proof]
            pub fn arbitrary() -> #token_ty { ::core::unimplemented!() }

            #impl_token_stream
        }
    };
}

/// For a given sharding(constant) field, add that constant
/// as a #[verifier::spec] fn on the Instance type. (The field is constant
/// for the entire instance.)

fn const_fn_stream(field: &Field) -> TokenStream {
    let fieldname = &field.name;
    let fieldtype = match &field.stype {
        ShardableType::Constant(ty) => ty,
        _ => panic!("const_fn_stream expected Constant"),
    };

    return quote! {
        #[cfg_attr(verus_keep_ghost, verifier::spec)]
        #[cfg_attr(verus_keep_ghost, verifier::external_body)]
        pub fn #fieldname(&self) -> #fieldtype { unimplemented!() }
    };
}

// Pull everything together.
//
//     struct Instance
//     token structs ...
//     impl Instance {
//         exchange fns ...
//     }
pub fn output_token_types_and_fns(
    token_stream: &mut TokenStream,
    bundle: &SMBundle,
    safety_condition_lemmas: &HashMap<String, Ident>,
) -> parse::Result<()> {
    let mut inst_impl_token_stream = TokenStream::new();

    token_stream.extend(instance_struct_stream(&bundle.sm));
    inst_impl_token_stream.extend(trusted_clone());

    for field in &bundle.sm.fields {
        match &field.stype {
            ShardableType::Constant(_) => {
                inst_impl_token_stream.extend(const_fn_stream(field));
            }
            ShardableType::Variable(ty) => {
                token_stream.extend(token_struct_stream(&bundle.sm, field, None, Some(ty), false));
            }
            ShardableType::NotTokenized(_) => {
                // don't need to add a struct in this case
            }
            ShardableType::Option(ty) | ShardableType::PersistentOption(ty) => {
                token_stream.extend(token_struct_stream(&bundle.sm, field, None, Some(ty), false));
            }
            ShardableType::Map(key, val) | ShardableType::PersistentMap(key, val) => {
                token_stream.extend(token_struct_stream(
                    &bundle.sm,
                    field,
                    Some(key),
                    Some(val),
                    false,
                ));
            }
            ShardableType::Multiset(ty) => {
                token_stream.extend(token_struct_stream(&bundle.sm, field, Some(ty), None, true));
            }
            ShardableType::Set(ty) | ShardableType::PersistentSet(ty) => {
                token_stream.extend(token_struct_stream(&bundle.sm, field, Some(ty), None, false));
            }
            ShardableType::StorageOption(_) | ShardableType::StorageMap(_, _) => {
                // storage types don't have tokens; the 'token type' is just the
                // the type of the field
            }
            ShardableType::Count | ShardableType::PersistentCount => {
                token_stream.extend(token_struct_stream(&bundle.sm, field, None, None, true));
            }
            ShardableType::Bool | ShardableType::PersistentBool => {
                token_stream.extend(token_struct_stream(&bundle.sm, field, None, None, false));
            }
        }
    }

    let mut errors = Vec::new();
    for tr in &bundle.sm.transitions {
        if tr.kind == TransitionKind::ReadonlyTransition {
            continue;
        }

        match exchange_stream(bundle, tr, safety_condition_lemmas) {
            Ok(stream) => {
                inst_impl_token_stream.extend(stream);
            }
            Err(err) => {
                errors.push(err);
            }
        }
    }
    combine_errors_or_ok(errors)?;

    let insttype = inst_type(&bundle.sm);
    let impldecl = impl_decl_stream(&insttype, &bundle.sm.generics);
    token_stream.extend(quote! {
        #impldecl {
            #inst_impl_token_stream
        }
    });

    Ok(())
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum InoutType {
    In,
    Out,
    InOut,
    BorrowIn,
    BorrowOut,
}

struct TokenParam {
    pub inout_type: InoutType,
    pub name: Ident,
    pub ty: Type,
    /// Is this param a collection (option, map, multiset) of tokens
    /// of the generated types? i.e., as opposed to just a single token,
    /// or opposed to a collection of external tokens.
    pub is_collection: bool,
}

/// Context object for the complex task of translating a single
/// transition into a token-exchange method.

struct Ctxt {
    // fields written in some normal 'update' or 'init' statements
    // (not including special ops)
    fields_written: HashSet<String>,

    // fields read (via `pre.field`) in some expression
    fields_read: HashSet<String>,

    // fields read in a birds_eye statement
    fields_read_birds_eye: HashSet<String>,

    // in/out params resulting from remove/have/add statements
    params: HashMap<String, Vec<TokenParam>>,

    requires: Vec<Expr>,
    ensures: Vec<Expr>,
    ident_to_field: HashMap<String, Field>,
    is_init: bool,
    sm: SM,

    fresh_num_counter: usize,
}

impl Ctxt {
    pub fn get_field_or_panic(&self, ident: &Ident) -> Field {
        match self.ident_to_field.get(&ident.to_string()) {
            Some(f) => f.clone(),
            None => panic!("should have already checked field updates are valid"),
        }
    }

    pub fn get_numbered_token_ident(&mut self, base_id: &Ident) -> Ident {
        let i = self.fresh_num_counter;
        self.fresh_num_counter += 1;
        Ident::new(&format!("param_token_{}_{}", i, base_id.to_string()), base_id.span())
    }

    /// Determines if we need to add an explicit lifetime parameter
    /// by checking if any of the out parameters is a borrow.
    pub fn get_explicit_lifetime(&self) -> bool {
        for (_p, v) in self.params.iter() {
            for tp in v {
                match tp.inout_type {
                    InoutType::BorrowOut => {
                        return true;
                    }
                    _ => {}
                }
            }
        }
        return false;
    }
}

enum Mode {
    Ghost,
    Tracked,
}

/// Primary method to build an exchange method for a given transition.
///
/// To build an exchange method, we need to collect 4 key pieces
/// of information:
///
///  * input arguments (may include spec & proof tokens)
///  * outputs (may include spec & proof tokens)
///  * pre-conditions (mostly follow from 'require' statements)
///  * post-conditions (mostly follow from 'update' and 'assert' statements)
///
/// When possible, we use &mut arguments (i.e., if a given token is
/// both an input and an output).

pub fn exchange_stream(
    bundle: &SMBundle,
    tr: &Transition,
    safety_condition_lemmas: &HashMap<String, Ident>,
) -> parse::Result<TokenStream> {
    let sm = &bundle.sm;

    let is_init = tr.kind == TransitionKind::Init;

    let mut ident_to_field = HashMap::new();

    // Initialize the `params` field of the `Ctxt` object. We'll fill this up
    // later; for now, just create an entry with an empty Vec for each relevant field.
    let mut params = HashMap::new();
    for field in &sm.fields {
        ident_to_field.insert(field.name.to_string(), field.clone());

        if !is_init {
            match &field.stype {
                ShardableType::Multiset(_)
                | ShardableType::Option(_)
                | ShardableType::Map(_, _)
                | ShardableType::PersistentOption(_)
                | ShardableType::PersistentMap(_, _)
                | ShardableType::Count
                | ShardableType::PersistentCount
                | ShardableType::Bool
                | ShardableType::PersistentBool
                | ShardableType::Set(_)
                | ShardableType::PersistentSet(_)
                | ShardableType::StorageOption(_)
                | ShardableType::StorageMap(_, _) => {
                    params.insert(field.name.to_string(), Vec::new());
                }
                ShardableType::Variable(_)
                | ShardableType::Constant(_)
                | ShardableType::NotTokenized(_) => {}
            }
        }
    }

    let mut ctxt = Ctxt {
        fields_read: HashSet::new(),
        fields_written: HashSet::new(),
        fields_read_birds_eye: HashSet::new(),
        params: params,
        requires: Vec::new(),
        ensures: Vec::new(),
        ident_to_field,
        is_init: is_init,
        sm: bundle.sm.clone(),
        fresh_num_counter: 0,
    };

    let mut tr = tr.clone();

    check_unsupported_updates(&tr.body)?;
    check_ordering_remove_have_add(sm, &tr.body)?;

    // Potentially remove steps that won't be useful.
    // We want to do this before `find_all_accesses` below, since this step may potentially
    // remove field accesses that we would like to ignore.
    // For example, suppose the user writes `update(foo, pre.bar)` where `foo` is
    // NotTokenized. In that case, we want to make sure that we _don't_ process
    // pre.bar as a requirement to have `bar` as an input token.
    tr.body = prune_irrelevant_ops(&ctxt, tr.body);

    // compute `ctxt.fields_written`, which is used to determine the output tokens
    determine_outputs(&mut ctxt, &tr.body)?;

    // Determine which fields are read (e.g., `pre.foo`) and in what context those
    // fields are read.

    let mut errors = Vec::new();
    let (fields_read, fields_read_birds_eye) =
        find_all_accesses(&mut tr.body, &mut errors, &ctxt.ident_to_field);
    combine_errors_or_ok(errors)?;

    ctxt.fields_read = fields_read;
    ctxt.fields_read_birds_eye = fields_read_birds_eye;

    // translate the expressions in the TransitionStmt so that
    // where they previously referred to fields like `pre.foo`,
    // they now refer to the field that comes from an input.
    // Also simplifies away SpecialOps.

    let mut errors = Vec::new();
    translate_transition(&mut ctxt, &mut tr.body, &mut errors)?;
    combine_errors_or_ok(errors)?;

    // translate the (new) TransitionStmt into expressions that
    // can be used as pre-conditions and post-conditions
    // This fills up `ctxt.requires` and `ctxt.ensures`.
    exchange_collect(&mut ctxt, &tr.body, Vec::new())?;

    // For our purposes here, a 'property' is just a special case of a normal transition,
    // but 'init' transitions need to be handled differently.
    // For the most part, there are two key differences between init and transition/readonly/property.
    //
    //   * An 'init' returns an arbitrary new Instance object, whereas a normal transition
    //     takes an Instance as input.
    //   * An 'init' will always return tokens for every field that has tokens,
    //     and take no tokens as input (except for external 'storage' tokens).
    //     A normal transition takes tokens as input only as is necessary.
    //
    // Generally speaking, the input parameters are going to look like:
    //    (instance as the 'self' argument)?    (present if not init)
    //    (spec transition params,)*            (parameters to the transition)
    //    (proof token params,)*                (if init, only includes storage tokens;
    //                                           otherwise, includes storage tokens AND
    //                                           tokens of this instance)

    let mut in_params: Vec<TokenStream> = Vec::new();
    let mut out_params: Vec<(TokenStream, TokenStream, Mode)> = Vec::new();

    // First, we create a parameter for the Instance, either an input or output parameter
    // as appropriate.

    if ctxt.is_init {
        let itn = inst_type(sm);
        out_params.push((quote! { instance }, quote! { #itn }, Mode::Tracked));
    } else {
        in_params.push(quote! { #[verifier::proof] &self });
    }

    // Take the transition parameters (the normal parameters defined in the transition)
    // and make them input parameters (spec-mode) to the corresponding exchange method.

    for param in &tr.params {
        let id = &param.name;
        let ty = &param.ty;
        in_params.push(quote! { #[verifier::spec] #id: #ty });
    }

    // We need some pre/post conditions that the input/output
    // tokens are all of the correct Instance.
    // We will fill these in as we go. (Note these might not contain all instance-related
    // conditions; for collection types, the pre- and post-conditions are more complicated
    // and in that case, some instance-related conditions might go in with the
    // `ctxt.requires` or `ctxt.ensures`).

    let mut inst_eq_reqs = Vec::new();
    let mut inst_eq_enss = Vec::new();

    // Whether or not to mark all borrows with a lifetime parameter 'a
    // We need to do this if there is any borrow in an out param
    // (which only happens for guards in 'readonly' transitions).
    let use_explicit_lifetime = ctxt.get_explicit_lifetime();

    for field in &sm.fields {
        // the 'init' case is different enough from the other two that we
        // handle it completely separately

        if ctxt.is_init {
            // For 'init', we start with a few special cases.
            // For a NotTokenized field, there's nothing to do. No token to output,
            // and no postcondition about it.

            match &field.stype {
                ShardableType::NotTokenized(..) => {
                    continue;
                }
                _ => {}
            }

            // Sanity check some assumptions that should hold for any well-formed
            // 'init' routine. In particular, there should be no occurrences of `pre.field`
            // and every field should be written.

            assert!(!use_explicit_lifetime);
            assert!(ctxt.fields_written.contains(&field.name.to_string()));
            assert!(!ctxt.fields_read.contains(&field.name.to_string()));
            assert!(!ctxt.fields_read_birds_eye.contains(&field.name.to_string()));

            // Next case is the Constant type. We don't need to output a new token for it,
            // we just need to add a postcondition like `instance.field() == value`.

            match &field.stype {
                ShardableType::Constant(_) => {
                    let e_opt = get_post_value_for_variable(&ctxt, &tr.body, field);
                    let e = e_opt.expect("get_post_value_for_variable");
                    let lhs = get_const_field_value(&ctxt, field, field.name.span());
                    ctxt.ensures.push(mk_eq(lhs.span(), &lhs, &e));
                    continue;
                }
                _ => {}
            }

            // Now everything else should fall into one of two buckets. We either need
            // to generate an input token or an output token.
            //
            // In most cases, we need to generate an output token param. This applies to
            // 'variable', naturally, but also 'option', 'multiset', etc.
            // And we need to generate a postconditions (an 'ensures') that the value of
            // the token is the value it was initialized to via the 'init' statement.
            //
            // For _storage_ type, we need to generate an _input_ token param.
            // The storage type comes externally from the system, so for example,
            // if the transition initializes the storage field to say, Some(x),
            // then the user needs to actually deposit 'x' in order to run
            // the initialization. Thus the Some(x) actually needs to come in
            // an input param.
            //
            // So in either case we:
            //  1. Determine type of the (input / output) token
            //  2. Determine the value the field is set to via the 'init' statement(s)
            //  3. Generate a (precondition / postcondition) that the token has
            //     the correct value.
            // Also note that in the non-storage (i.e., output) case, this includes
            // the conditions that the new tokens are all associated with the newly
            // generated Instance. But of course the input tokens have so such constraint.

            if let Some(init_input_token_type) = get_init_param_input_type(sm, &field) {
                // Storage case, input token & precondition:

                let arg_name = transition_arg_name(field);

                add_token_param_in_out(
                    &ctxt,
                    &mut in_params,
                    &mut out_params,
                    &mut inst_eq_enss,
                    &mut inst_eq_reqs,
                    &arg_name,
                    &init_input_token_type,
                    InoutType::In,
                    false, // (don't) apply_instance_condition
                    false, // (don't) use_explicit_lifetime
                );

                let e_opt = get_post_value_for_variable(&ctxt, &tr.body, field);
                let e = e_opt.expect("get_post_value_for_variable");

                add_initialization_input_conditions(
                    field,
                    &mut ctxt.requires,
                    e,
                    Expr::Verbatim(quote! { #arg_name }),
                );
            } else if let Some(init_output_token_type) = get_init_param_output_type(sm, &field) {
                // Everything else case, output token & postcondition:

                let arg_name = transition_arg_name(field);

                add_token_param_in_out(
                    &ctxt,
                    &mut in_params,
                    &mut out_params,
                    &mut inst_eq_enss,
                    &mut inst_eq_reqs,
                    &arg_name,
                    &init_output_token_type,
                    InoutType::Out,
                    false, // (don't) apply_instance_condition
                    false, // (don't) use_explicit_lifetime
                );

                let e_opt = get_post_value_for_variable(&ctxt, &tr.body, field);
                let e = e_opt.expect("get_post_value_for_variable");

                let inst = get_inst_value(&ctxt);
                add_initialization_output_conditions(
                    sm,
                    field,
                    &mut ctxt.ensures,
                    &mut inst_eq_enss,
                    e,
                    inst,
                    Expr::Verbatim(quote! { #arg_name }),
                );
            } else {
                panic!("unexpected case: {:#?}", field.stype);
            }
        } else {
            // The case for a 'transition' or 'property'.
            // (At this point, the distinction doesn't matter.)
            //
            // First, we handle fields that have "nondeterminstic reads"
            // which come from the `birds_eye` let-statements.
            // From the client's perspective, these values appear nondeterministically
            // when they make the call, so the client doesn't have to provide the
            // values, but rather, the exchange method provides them as outputs
            // (as spec values). These nondeterministic reads are the only way for the
            // client to interact with NotTokenized values.
            // Also, a nondeterministic read of the field is not inconsistent with
            // other tokens of that field, although in the 'variable' strategy case,
            // there is no reason to have both.
            //
            // Anyway, start by checking if a nondeterministic read occurs, and if so,
            // we add a spec-mode output param for the corresponding value.

            let nondeterministic_read =
                ctxt.fields_read_birds_eye.contains(&field.name.to_string())
                    && match field.stype {
                        ShardableType::Variable(_) => {
                            !ctxt.fields_written.contains(&field.name.to_string())
                                && !ctxt.fields_read.contains(&field.name.to_string())
                        }
                        ShardableType::Constant(_) => false,
                        _ => true,
                    };

            if nondeterministic_read {
                let ty = shardable_type_to_type(field.type_span, &field.stype);
                let name = nondeterministic_read_spec_out_name(field);
                out_params.push((quote! { #name }, quote! { #ty }, Mode::Ghost));
            }

            // Now, we handle the actual proof-mode tokens.

            match field.stype {
                ShardableType::Constant(_) => {
                    // We can't update a constant field in a non-init transition.
                    // This should have been checked already.
                    assert!(!ctxt.fields_written.contains(&field.name.to_string()));
                }
                ShardableType::NotTokenized(_) => {
                    // Do nothing.
                    // This field can only be accessed via nondeterministic
                    // read which was handled above.
                    // Nothing to do for writes (they simply aren't reflected in output tokens).
                }
                ShardableType::Variable(_) => {
                    // Variable case.
                    // We need to do something if it was either read or written.

                    let is_written = ctxt.fields_written.contains(&field.name.to_string());
                    let is_read = ctxt.fields_read.contains(&field.name.to_string());

                    if is_written || is_read {
                        assert!(!nondeterministic_read);

                        // If is_written=true, then it doesn't really matter what is_read is;
                        // we have to take the token as input either way.
                        // So there are really two cases here:
                        //  * is_written=true: InOut variable
                        //  * is_written=false (but in_read=true): BorrowIn variable

                        add_token_param_in_out(
                            &ctxt,
                            &mut in_params,
                            &mut out_params,
                            &mut inst_eq_enss,
                            &mut inst_eq_reqs,
                            &transition_arg_name(field),
                            &field_token_type(&sm, field),
                            if is_written { InoutType::InOut } else { InoutType::BorrowIn },
                            true,
                            use_explicit_lifetime,
                        );
                    }

                    if is_written {
                        // Post-condition that gives the value of the output token
                        // note: maybe instead of doing this here, we could translate the
                        // `Update` statements into `PostCondition` statements like we
                        // do for other kinds of tokens. Then we wouldn't have to have this here.

                        let e_opt = get_post_value_for_variable(&ctxt, &tr.body, field);
                        let e = e_opt.expect("get_post_value_for_variable");
                        let lhs = get_new_field_value(field);
                        ctxt.ensures.push(mk_eq(lhs.span(), &lhs, &e));
                    }
                }
                ShardableType::Option(_)
                | ShardableType::Map(_, _)
                | ShardableType::Set(_)
                | ShardableType::Multiset(_)
                | ShardableType::Count
                | ShardableType::Bool
                | ShardableType::PersistentOption(_)
                | ShardableType::PersistentSet(_)
                | ShardableType::PersistentMap(_, _)
                | ShardableType::PersistentCount
                | ShardableType::PersistentBool
                | ShardableType::StorageOption(_)
                | ShardableType::StorageMap(_, _) => {
                    // These sharding types all use the SpecialOps. The earlier translation
                    // phase has already processed those and established all the necessary
                    // pre-conditions and post-conditions, and it has also established
                    // the tokens we need to create, in `ctxt.params`.
                    // So we just need to look up it and actually add the params that it
                    // tells us to add.

                    assert!(!ctxt.fields_written.contains(&field.name.to_string()));
                    assert!(!ctxt.fields_read.contains(&field.name.to_string()));

                    for p in &ctxt.params[&field.name.to_string()] {
                        add_token_param_in_out(
                            &ctxt,
                            &mut in_params,
                            &mut out_params,
                            &mut inst_eq_enss,
                            &mut inst_eq_reqs,
                            &p.name,
                            &p.ty,
                            p.inout_type,
                            !field.stype.is_storage() && !p.is_collection,
                            use_explicit_lifetime,
                        );
                    }
                }
            };
        }
    }

    // Now we have all the parameters, and all the preconditions and postconditions
    // as expressions, so we just need to put it all together.

    let mut reqs = inst_eq_reqs;
    reqs.extend(ctxt.requires);

    let mut enss = inst_eq_enss;
    enss.extend(ctxt.ensures);

    let exch_name = exchange_name(&tr);

    let req_stream = if reqs.len() > 0 {
        quote_vstd! { vstd =>
            #vstd::prelude::requires(::builtin_macros::verus_proof_expr!([
                #(#reqs),*
            ]));
        }
    } else {
        TokenStream::new()
    };

    // Output types are a bit tricky
    // because of the lack of named output params.

    let (out_params_ret, ens_stream, ret_value_mode) = if out_params.len() == 0 {
        let ens_stream = if enss.len() > 0 {
            quote_vstd! { vstd =>
                #vstd::prelude::ensures(::builtin_macros::verus_proof_expr!([
                    #(#enss),*
                ]));
            }
        } else {
            TokenStream::new()
        };

        (TokenStream::new(), ens_stream, TokenStream::new())
    } else if out_params.len() == 1 {
        let param_name = &out_params[0].0;
        let param_ty = &out_params[0].1;
        let param_mode = &out_params[0].2;

        let ens_stream = if enss.len() > 0 {
            quote_vstd! { vstd =>
                #vstd::prelude::ensures(
                    |#param_name: #param_ty| ::builtin_macros::verus_proof_expr!([
                        #(#enss),*
                    ])
                );
            }
        } else {
            TokenStream::new()
        };

        let ret_value_mode = match param_mode {
            Mode::Tracked => quote! { #[verifier::returns(proof)] /* vattr */ },
            Mode::Ghost => TokenStream::new(),
        };

        (quote! { -> #param_ty }, ens_stream, ret_value_mode)
    } else {
        // If we have more than one output param (we aren't counting the &mut inputs here,
        // only stuff in the 'return type' position) then we have to package it all into
        // a tuple and unpack it in the 'ensures' clause.

        let param_tys: Vec<TokenStream> = out_params
            .iter()
            .map(|oa| {
                let ty = &oa.1;
                match oa.2 {
                    Mode::Ghost => {
                        quote_vstd! { vstd => #vstd::prelude::Ghost<#ty> }
                    }
                    Mode::Tracked => {
                        quote_vstd! { vstd => #vstd::prelude::Tracked<#ty> }
                    }
                }
            })
            .collect();
        let param_names: Vec<TokenStream> = out_params
            .iter()
            .map(|oa| {
                let name = &oa.0;
                quote! { #name }
            })
            .collect();
        let let_stmts: Vec<TokenStream> = out_params
            .iter()
            .map(|oa| {
                let name = &oa.0;
                quote! { let #name = #name.view(); }
            })
            .collect();

        let tup_typ = quote! { (#(#param_tys),*) };
        let tup_names = quote! { (#(#param_names),*) };

        let ens_stream = if enss.len() > 0 {
            quote_vstd! { vstd =>
                #vstd::prelude::ensures(
                    |tmp_tuple: #tup_typ| ::builtin_macros::verus_proof_expr!([{
                        let #tup_names = tmp_tuple;
                        #(#let_stmts)*
                        #((#enss))&&*
                    }])
                );
            }
        } else {
            TokenStream::new()
        };

        let ret_value_mode = quote! { #[verifier::returns(proof)] /* vattr */ };

        (quote! { -> #tup_typ }, ens_stream, ret_value_mode)
    };

    // Tie it all together

    let extra_deps = get_extra_deps(bundle, &tr, safety_condition_lemmas);

    let gen = if use_explicit_lifetime {
        quote! { <'a> }
    } else {
        TokenStream::new()
    };

    return Ok(quote! {
        #[cfg(verus_keep_ghost_body)]
        #[verus::internal(verus_macro)]
        #ret_value_mode
        #[verifier::external_body] /* vattr */
        #[verifier::proof]
        pub fn #exch_name#gen(#(#in_params),*) #out_params_ret {
            #req_stream
            #ens_stream
            #extra_deps
            ::core::unimplemented!();
        }
    });
}

fn get_init_param_input_type(_sm: &SM, field: &Field) -> Option<Type> {
    // Upon initialization, we may have to input stuff corresponding to storage.
    match &field.stype {
        ShardableType::Variable(_) => None,
        ShardableType::Constant(_) => None,
        ShardableType::NotTokenized(_) => None,
        ShardableType::Multiset(_) => None,
        ShardableType::Set(_) => None,
        ShardableType::Bool => None,
        ShardableType::Option(_) => None,
        ShardableType::Map(_, _) => None,
        ShardableType::PersistentOption(_) => None,
        ShardableType::PersistentSet(_) => None,
        ShardableType::PersistentMap(_, _) => None,
        ShardableType::PersistentCount => None,
        ShardableType::PersistentBool => None,
        ShardableType::Count => None,
        ShardableType::StorageOption(ty) => Some(Type::Verbatim(quote! {
            ::core::option::Option<#ty>
        })),
        ShardableType::StorageMap(key, val) => Some(Type::Verbatim(quote_vstd! { vstd =>
            #vstd::map::Map<#key, #val>
        })),
    }
}

fn add_initialization_input_conditions(
    field: &Field,
    requires: &mut Vec<Expr>,
    init_value: Expr,
    param_value: Expr,
) {
    match &field.stype {
        ShardableType::StorageOption(_) | ShardableType::StorageMap(_, _) => {
            requires.push(mk_eq(param_value.span(), &param_value, &init_value));
        }
        _ => {
            panic!("this should implement each case enabled by get_init_param_input_type");
        }
    }
}

fn get_init_param_output_type(sm: &SM, field: &Field) -> Option<Type> {
    match &field.stype {
        ShardableType::Variable(_) => Some(field_token_type(&sm, field)),
        ShardableType::Constant(_) => None, // constants handled separately
        ShardableType::NotTokenized(_) => None, // no tokens
        ShardableType::Count | ShardableType::PersistentCount => Some(field_token_type(&sm, field)),
        ShardableType::Multiset(_)
        | ShardableType::Option(_)
        | ShardableType::PersistentOption(_)
        | ShardableType::Bool
        | ShardableType::PersistentBool
        | ShardableType::Set(_)
        | ShardableType::PersistentSet(_)
        | ShardableType::Map(..)
        | ShardableType::PersistentMap(..) => Some(field_token_collection_type(sm, field)),

        ShardableType::StorageOption(_) => None, // no output tokens for storage
        ShardableType::StorageMap(_, _) => None,
    }
}

fn add_initialization_output_conditions(
    sm: &SM,
    field: &Field,
    ensures: &mut Vec<Expr>,
    inst_eq_enss: &mut Vec<Expr>,
    init_value: Expr,
    inst_value: Expr,
    param_value: Expr,
) {
    match &field.stype {
        ShardableType::Variable(_) => {
            inst_eq_enss.push(Expr::Verbatim(quote_vstd! { vstd =>
                #vstd::prelude::equal(#param_value.view().instance, #inst_value)
            }));
            let field_name = field_token_field_name(field);
            ensures.push(Expr::Verbatim(quote_vstd! { vstd =>
                #vstd::prelude::equal(#param_value.view().#field_name, #init_value)
            }));
        }
        ShardableType::Count | ShardableType::PersistentCount => {
            inst_eq_enss.push(Expr::Verbatim(quote_vstd! { vstd =>
                #vstd::prelude::equal(#param_value.view().instance, #inst_value)
            }));
            ensures.push(Expr::Verbatim(quote_vstd! { vstd =>
                #vstd::prelude::equal(#param_value.view().count, #init_value)
            }));
        }
        ShardableType::Option(_)
        | ShardableType::PersistentOption(_)
        | ShardableType::Bool
        | ShardableType::PersistentBool
        | ShardableType::Set(_)
        | ShardableType::PersistentSet(_)
        | ShardableType::Map(_, _)
        | ShardableType::PersistentMap(_, _)
        | ShardableType::Multiset(_) => {
            ensures.push(relation_for_collection_of_internal_tokens(
                sm,
                field,
                param_value,
                init_value,
                inst_value,
                true,
            ));
        }
        _ => {
            panic!("this should implement each case enabled by get_init_param_output_type");
        }
    }
}

fn relation_for_collection_of_internal_tokens(
    sm: &SM,
    field: &Field,
    param_value: Expr,
    given_value: Expr,
    inst_value: Expr,
    output: bool,
) -> Expr {
    // For output tokens, we allow the user to assume a slightly stronger condition about the data.
    // For input tokens, we require the user to prove a slightly weaker one.
    let strict = output;

    match &field.stype {
        ShardableType::Option(_) | ShardableType::PersistentOption(_) => {
            let fn_name = option_relation_post_condition_qualified_name(sm, field, strict);
            Expr::Verbatim(quote! {
                #fn_name(#param_value, #given_value, #inst_value)
            })
        }
        ShardableType::Set(_) | ShardableType::PersistentSet(_) => {
            let fn_name = set_relation_post_condition_qualified_name(sm, field, strict);
            Expr::Verbatim(quote! {
                #fn_name(#param_value, #given_value, #inst_value)
            })
        }
        ShardableType::Bool | ShardableType::PersistentBool => {
            let fn_name = bool_relation_post_condition_qualified_name(sm, field, strict);
            Expr::Verbatim(quote! {
                #fn_name(#param_value, #given_value, #inst_value)
            })
        }
        ShardableType::Map(_, _) | ShardableType::PersistentMap(_, _) => {
            let fn_name = map_relation_post_condition_qualified_name(sm, field, strict);
            Expr::Verbatim(quote! {
                #fn_name(#param_value, #given_value, #inst_value)
            })
        }
        ShardableType::Multiset(_) => {
            let fn_name = multiset_relation_post_condition_qualified_name(sm, field, strict);
            Expr::Verbatim(quote! {
                #fn_name(#param_value, #given_value, #inst_value)
            })
        }
        _ => {
            panic!("relation_for_collection_of_internal_tokens");
        }
    }
}

/// Add some helper functions that are useful to call from other
/// generated conditions (e.g., see `add_initialization_output_conditions`)
fn collection_relation_fns_stream(sm: &SM, field: &Field) -> TokenStream {
    match &field.stype {
        ShardableType::Option(ty) | ShardableType::PersistentOption(ty) => {
            let fn_name = option_relation_post_condition_name(field, false);
            let fn_name_strict = option_relation_post_condition_name(field, true);
            let token_ty = field_token_type(sm, field);
            let inst_ty = inst_type(sm);
            let option_token_ty = Type::Verbatim(quote! {
                ::core::option::Option<#token_ty>
            });
            let option_normal_ty = Type::Verbatim(quote! {
                ::core::option::Option<#ty>
            });

            // Predicate to check the option values agree:
            //
            // opt            token_opt
            // None           None
            // Some(x)        Some(Token { instance: instance, value: x })

            quote_vstd! { vstd =>
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::inline] /* vattr */
                #[verus::internal(open)] /* vattr */
                #[verifier::spec]
                pub fn #fn_name_strict(token_opt: #option_token_ty, opt: #option_normal_ty, instance: #inst_ty) -> bool {
                    Self::#fn_name(token_opt, opt, instance)
                    && #vstd::prelude::imply(opt.is_None(), token_opt.is_None())
                }

                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verus::internal(open)] /* vattr */
                #[verifier::spec]
                pub fn #fn_name(token_opt: #option_token_ty, opt: #option_normal_ty, instance: #inst_ty) -> bool {
                    #vstd::prelude::imply(
                        opt.is_Some(),
                        token_opt.is_Some()
                            && #vstd::prelude::equal(token_opt.get_Some_0().view().value, opt.get_Some_0())
                            && #vstd::prelude::equal(token_opt.get_Some_0().view().instance, instance)
                    )
                }
            }
        }
        ShardableType::Set(ty) | ShardableType::PersistentSet(ty) => {
            let fn_name_strict = set_relation_post_condition_name(field, true);
            let fn_name = set_relation_post_condition_name(field, false);
            let constructor_name = field_token_data_type_turbofish(sm, field);
            let token_ty = field_token_type(sm, field);
            let inst_ty = inst_type(sm);
            let set_token_ty = Type::Verbatim(quote_vstd! { vstd =>
                #vstd::map::Map<#ty, #token_ty>
            });
            let set_normal_ty = Type::Verbatim(quote_vstd! { vstd =>
                #vstd::set::Set<#ty>
            });

            // Predicate to check the set values agree:
            //
            // set            token_map
            // {x, y}         { x => { instance, x }, y => { instance, y } }

            quote_vstd! { vstd =>
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verus::internal(open)] /* vattr */
                #[verifier::spec]
                pub fn #fn_name(token_map: #set_token_ty, set: #set_normal_ty, instance: #inst_ty) -> bool {
                    #vstd::prelude::forall(|elem: #ty| {
                        #vstd::prelude::with_triggers(
                            (
                                ( token_map.dom().contains(elem), ),
                                ( token_map.index(elem), ),
                            ),
                            #vstd::prelude::imply(
                                set.contains(elem),
                                (#[verifier::trigger] token_map.dom().contains(elem))
                                && #vstd::prelude::equal(token_map.index(elem).view(),
                                    #constructor_name {
                                        instance: instance,
                                        key: elem,
                                    }
                                )
                            )
                        )
                    })
                }

                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::inline] /* vattr */
                #[verus::internal(open)] /* vattr */
                #[verifier::spec]
                pub fn #fn_name_strict(token_map: #set_token_ty, set: #set_normal_ty, instance: #inst_ty) -> bool {
                    #vstd::prelude::equal(token_map.dom(), set)
                      && Self::#fn_name(token_map, set, instance)
                }
            }
        }
        ShardableType::Bool | ShardableType::PersistentBool => {
            let fn_name = bool_relation_post_condition_name(field, false);
            let fn_name_strict = bool_relation_post_condition_name(field, true);
            let token_ty = field_token_type(sm, field);
            let inst_ty = inst_type(sm);
            let option_token_ty = Type::Verbatim(quote! {
                ::core::option::Option<#token_ty>
            });

            // Predicate to check the option values agree:
            //
            // b              token_opt
            // false          None
            // true           Some(Token { instance: instance })

            quote_vstd! { vstd =>
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verus::internal(open)] /* vattr */
                #[verifier::spec]
                pub fn #fn_name(token_opt: #option_token_ty, b: ::core::primitive::bool, instance: #inst_ty) -> bool {
                    #vstd::prelude::imply(b,
                        token_opt.is_Some()
                        && #vstd::prelude::equal(token_opt.get_Some_0().view().instance, instance)
                    )
                }

                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::inline] /* vattr */
                #[verus::internal(open)] /* vattr */
                #[verifier::spec]
                pub fn #fn_name_strict(token_opt: #option_token_ty, b: ::core::primitive::bool, instance: #inst_ty) -> bool {
                    Self::#fn_name(token_opt, b, instance)
                    && #vstd::prelude::imply(!b, token_opt.is_None())
                }
            }
        }
        ShardableType::Map(key, val) | ShardableType::PersistentMap(key, val) => {
            let fn_name = map_relation_post_condition_name(field, false);
            let fn_name_strict = map_relation_post_condition_name(field, true);
            let token_ty = field_token_type(sm, field);
            let inst_ty = inst_type(sm);
            let map_token_ty = Type::Verbatim(quote_vstd! { vstd =>
                #vstd::map::Map<#key, #token_ty>
            });
            let map_normal_ty = Type::Verbatim(quote_vstd! { vstd =>
                #vstd::map::Map<#key, #val>
            });

            // Predicate to check the map values agree:
            //
            // map:
            // map[k1 := v1]
            //    [k2 := v2]...
            //
            // token_map:
            // map[k1 := Token { instance: instance, value: v1 }]
            //    [k1 := Token { instance: instance, value: v2 }]...

            quote_vstd! { vstd =>
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verus::internal(open)] /* vattr */
                #[verifier::spec]
                pub fn #fn_name(token_map: #map_token_ty, m: #map_normal_ty, instance: #inst_ty) -> bool {
                    #vstd::prelude::forall(|key: #key|
                        #vstd::prelude::with_triggers(
                            (
                                ( token_map.dom().contains(key), ),
                                ( token_map.index(key), ),
                            ),
                            #vstd::prelude::imply(
                                token_map.dom().contains(key),
                                #vstd::prelude::equal(token_map.index(key).view().instance, instance)
                                    && #vstd::prelude::equal(token_map.index(key).view().key, key)
                                    && #vstd::prelude::equal(token_map.index(key).view().value, m.index(key))
                            )
                        )
                    )
                }

                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verus::internal(open)] /* vattr */
                #[verifier::spec]
                pub fn #fn_name_strict(token_map: #map_token_ty, m: #map_normal_ty, instance: #inst_ty) -> bool {
                    #vstd::prelude::equal(token_map.dom(), m.dom())
                    && Self::#fn_name(token_map, m, instance)
                }
            }
        }
        ShardableType::Multiset(ty) => {
            let fn_name = multiset_relation_post_condition_name(field, false);
            let fn_name_strict = multiset_relation_post_condition_name(field, true);
            let inst_ty = inst_type(sm);
            let token_ty = field_token_type(sm, field);
            let multiset_token_ty = Type::Verbatim(quote_vstd! { vstd =>
                #vstd::map::Map<#ty, #token_ty>
            });
            let multiset_normal_ty = Type::Verbatim(quote_vstd! { vstd =>
                #vstd::multiset::Multiset<#ty>
            });

            // Predicate to check the multiset values agree:
            //
            // m:
            // multiset{v1: n1, v2: n2, ...}
            //
            // tokens:
            // map{
            //    v1 => Token { instance: instance, key: v1, count: n1 }]
            //    v2 => Token { instance: instance, key: v2, count: n2 }]
            // }

            quote_vstd! { vstd =>
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verus::internal(open)] /* vattr */
                #[verifier::spec]
                pub fn #fn_name(tokens: #multiset_token_ty, m: #multiset_normal_ty, instance: #inst_ty) -> bool {
                    #vstd::prelude::forall(|x: #ty|
                        #vstd::prelude::imply(
                            m.count(x) > #vstd::prelude::spec_literal_nat("0"),
                            (#[verifier::trigger] tokens.dom().contains(x))
                            && #vstd::prelude::equal(tokens.index(x).view().instance, instance)
                            && tokens.index(x).view().count >= m.count(x)
                            && #vstd::prelude::equal(tokens.index(x).view().key, x)
                        )
                    )
                }

                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verus::internal(open)] /* vattr */
                #[verifier::spec]
                pub fn #fn_name_strict(tokens: #multiset_token_ty, m: #multiset_normal_ty, instance: #inst_ty) -> bool {
                    #vstd::prelude::forall(|x: #ty| {
                        #vstd::prelude::with_triggers(
                          (
                              ( tokens.dom().contains(x), ),
                              ( tokens.index(x), ),
                          ),
                          tokens.dom().contains(x)
                          && #vstd::prelude::equal(tokens.index(x).view().instance, instance)
                          && #vstd::prelude::equal(tokens.index(x).view().count, m.count(x))
                          && #vstd::prelude::equal(tokens.index(x).view().key, x)
                        )
                    })
                }

                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::proof]
                #[verifier::returns(proof)] /* vattr */
                #[verifier::external_body] /* vattr */
                pub fn join(#[verifier::proof] self, #[verifier::proof] other: Self) -> Self {
                    #vstd::prelude::requires(#vstd::prelude::equal(self.view().instance, other.view().instance) && #vstd::prelude::equal(self.view().key, other.view().key));
                    #vstd::prelude::ensures(|s: Self|
                        #vstd::prelude::equal(s.view().instance, self.view().instance)
                        && #vstd::prelude::equal(s.view().key, self.view().key)
                        && #vstd::prelude::equal(s.view().count, self.view().count + other.view().count)
                    );
                    ::core::unimplemented!();
                }

                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::external_body] /* vattr */
                #[verifier::returns(proof)] /* vattr */
                #[verifier::proof]
                pub fn split(#[verifier::proof] self, i: nat) -> (#vstd::prelude::Tracked<Self>, #vstd::prelude::Tracked<Self>) {
                    #vstd::prelude::requires(i <= self.view().count);
                    #vstd::prelude::ensures(|s: (#vstd::prelude::Tracked<Self>, #vstd::prelude::Tracked<Self>)| {
                        let x = s.0.view();
                        let y = s.1.view();
                        #vstd::prelude::equal(x.view().instance, self.view().instance)
                        && #vstd::prelude::equal(y.view().instance, self.view().instance)
                        && #vstd::prelude::equal(x.view().key, self.view().key)
                        && #vstd::prelude::equal(y.view().key, self.view().key)
                        && #vstd::prelude::equal(x.view().count, i)
                        && #vstd::prelude::equal(
                            #vstd::prelude::spec_cast_integer::<nat, int>(y.view().count),
                            self.view().count.spec_sub(i)
                        )
                    });
                    ::core::unimplemented!();
                }
            }
        }
        ShardableType::Count => {
            quote_vstd! { vstd =>
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::proof]
                #[verifier::returns(proof)] /* vattr */
                #[verifier::external_body] /* vattr */
                pub fn join(#[verifier::proof] self, #[verifier::proof] other: Self) -> Self {
                    #vstd::prelude::requires(#vstd::prelude::equal(self.view().instance, other.view().instance));
                    #vstd::prelude::ensures(|s: Self|
                        #vstd::prelude::equal(s.view().instance, self.view().instance)
                        && #vstd::prelude::equal(s.view().count, self.view().count + other.view().count)
                    );
                    ::core::unimplemented!();
                }

                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::external_body] /* vattr */
                #[verifier::returns(proof)] /* vattr */
                #[verifier::proof]
                pub fn split(#[verifier::proof] self, i: nat) -> (#vstd::prelude::Tracked<Self>, #vstd::prelude::Tracked<Self>) {
                    #vstd::prelude::requires(i <= self.view().count);
                    #vstd::prelude::ensures(|s: (#vstd::prelude::Tracked<Self>, #vstd::prelude::Tracked<Self>)| {
                        let x = s.0.view();
                        let y = s.1.view();
                        #vstd::prelude::equal(x.view().instance, self.view().instance)
                        && #vstd::prelude::equal(y.view().instance, self.view().instance)
                        && #vstd::prelude::equal(x.view().count, i)
                        && #vstd::prelude::equal(
                            #vstd::prelude::spec_cast_integer::<nat, int>(y.view().count),
                            self.view().count.spec_sub(i)
                        )
                    });
                    ::core::unimplemented!();
                }
            }
        }
        ShardableType::PersistentCount => {
            quote_vstd! { vstd =>
                #[cfg(verus_keep_ghost_body)]
                #[verus::internal(verus_macro)]
                #[verifier::external_body] /* vattr */
                #[verifier::returns(proof)] /* vattr */
                #[verifier::proof]
                pub fn weaken(#[verifier::proof] self, i: nat) -> Self {
                    #vstd::prelude::requires(i <= self.view().count);
                    #vstd::prelude::ensures(|s: Self|
                        #vstd::prelude::equal(s.view().instance, self.view().instance)
                        && #vstd::prelude::equal(s.view().count, i)
                    );
                    ::core::unimplemented!();
                }
            }
        }
        _ => TokenStream::new(),
    }
}

fn add_token_param_in_out(
    ctxt: &Ctxt,
    in_params: &mut Vec<TokenStream>,
    out_params: &mut Vec<(TokenStream, TokenStream, Mode)>,
    inst_eq_enss: &mut Vec<Expr>,
    inst_eq_reqs: &mut Vec<Expr>,

    param_name: &Ident,
    param_type: &Type,
    inout_type: InoutType,
    apply_instance_condition: bool,
    use_explicit_lifetime: bool,
) {
    // Explanation for the asserts about `use_explicit_lifetime`:
    //
    // Firstly, In, Out, and InOut can only occur in non-readonly
    // transitions, whereas guards can only occur in readonly transitions.
    // Therefore, In, Out, and InOut cases should all imply !use_explicit_lifetime
    //
    // Conversely, BorrowOut (which only occurs for guards) should imply
    // use_explicit_lifetime (this is how `use_explicit_lifetime` is computed).

    let (is_input, is_output) = match inout_type {
        InoutType::In => {
            assert!(!use_explicit_lifetime);
            in_params.push(quote! { #[verifier::proof] #param_name: #param_type });
            (true, false)
        }
        InoutType::Out => {
            assert!(!use_explicit_lifetime);
            out_params.push((quote! {#param_name}, quote! {#param_type}, Mode::Tracked));
            (false, true)
        }
        InoutType::InOut => {
            assert!(!use_explicit_lifetime);
            in_params.push(quote! { #[verifier::proof] #param_name: &mut #param_type });
            (true, true)
        }
        InoutType::BorrowIn => {
            if use_explicit_lifetime {
                in_params.push(quote! { #[verifier::proof] #param_name: &'a #param_type });
            } else {
                in_params.push(quote! { #[verifier::proof] #param_name: &#param_type });
            }
            (true, false)
        }
        InoutType::BorrowOut => {
            assert!(use_explicit_lifetime);
            out_params.push((quote! {#param_name}, quote! {&'a #param_type}, Mode::Tracked));
            (false, true)
        }
    };

    // Add a condition like `token.view().instance == instance`

    if apply_instance_condition {
        let inst = get_inst_value(&ctxt);
        if is_output {
            let lhs = Expr::Verbatim(quote! { #param_name.view().instance });
            inst_eq_enss.push(Expr::Verbatim(quote_vstd! { vstd =>
                #vstd::prelude::equal(#lhs, #inst)
            }));
        }
        if is_input {
            let lhs = if is_output {
                Expr::Verbatim(
                    quote_vstd! { vstd => #vstd::prelude::old(#param_name).view().instance },
                )
            } else {
                Expr::Verbatim(quote! { #param_name.view().instance })
            };
            inst_eq_reqs.push(Expr::Verbatim(quote_vstd! { vstd =>
                #vstd::prelude::equal(#lhs, #inst)
            }));
        }
    }
}

fn mk_and(span: Span, lhs: Expr, rhs: Expr) -> Expr {
    Expr::Verbatim(quote_spanned! { span =>
        ((#lhs) && (#rhs))
    })
}

fn mk_eq(span: Span, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::Verbatim(quote_spanned_vstd! { vstd, span =>
        #vstd::prelude::equal(#lhs, #rhs)
    })
}

pub fn get_extra_deps(
    bundle: &SMBundle,
    trans: &Transition,
    safety_condition_lemmas: &HashMap<String, Ident>,
) -> TokenStream {
    let ty = get_self_ty_turbofish(&bundle.sm);
    let deps: Vec<TokenStream> =
        get_all_lemmas_for_transition(bundle, trans, safety_condition_lemmas)
            .iter()
            .map(|ident| {
                quote_vstd! { vstd =>
                    #vstd::prelude::extra_dependency(#ty::#ident);
                }
            })
            .collect();
    quote! { #(#deps)* }
}

/// Gets the lemmas that prove validity of the given transition.
fn get_all_lemmas_for_transition(
    bundle: &SMBundle,
    trans: &Transition,
    safety_condition_lemmas: &HashMap<String, Ident>,
) -> Vec<Ident> {
    let mut v = Vec::new();

    if trans.kind.requires_invariant_lemma() {
        match get_main_lemma_for_transition_opt(&bundle.extras.lemmas, &trans.name) {
            Some(l) => v.push(l.func.sig.ident.clone()),
            None => {}
        }
    }

    match safety_condition_lemmas.get(&trans.name.to_string()) {
        Some(name) => v.push(name.clone()),
        None => {}
    }

    v
}

fn get_main_lemma_for_transition_opt<'a>(
    lemmas: &'a Vec<Lemma>,
    trans_name: &Ident,
) -> Option<&'a Lemma> {
    for l in lemmas {
        if l.purpose.transition.to_string() == trans_name.to_string() {
            return Some(l);
        }
    }

    None
}

// Find things that updated

fn determine_outputs(ctxt: &mut Ctxt, ts: &TransitionStmt) -> parse::Result<()> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            for child in v.iter() {
                determine_outputs(ctxt, child)?;
            }
            Ok(())
        }
        TransitionStmt::Split(_span, _split_kind, splits) => {
            for split in splits {
                determine_outputs(ctxt, split)?;
            }
            Ok(())
        }
        TransitionStmt::Require(_span, _req_e) => Ok(()),
        TransitionStmt::Assert(_span, _assert_e, _) => Ok(()),
        TransitionStmt::Initialize(_span, id, _e) => {
            ctxt.fields_written.insert(id.to_string());
            Ok(())
        }
        TransitionStmt::SubUpdate(..) => {
            panic!("sub-update not supported here");
        }
        TransitionStmt::Update(span, id, _e) => {
            let f = ctxt.get_field_or_panic(id);

            match f.stype {
                ShardableType::Variable(_) => {}
                ShardableType::Constant(_) => {
                    return Err(Error::new(*span, "cannot update a field marked constant"));
                }
                ShardableType::Multiset(_) => {
                    panic!("case should have been ruled out earlier");
                }
                _ => {}
            }

            ctxt.fields_written.insert(id.to_string());
            Ok(())
        }
        TransitionStmt::PostCondition(..) => {
            panic!("PostCondition statement shouldn't exist yet");
        }
    }
}

/// The function has several purposes:
///
///   1. Replace `pre.foo` subexpression with the corresponding value from the
///      input tokens, e.g., `token_foo.value`
///   2. Expand the definitions for any SpecialOps.
///
/// For point (1), we call `translate_expr` on each Rust Expr found in the transition AST.
///
/// For point (2), we translate all the SpecialOp into Require and PostCondition statements.
/// The Require statements, of course, will become pre-conditions on the exchange method,
/// while the PostCondition statements become post-conditions (and thus they can refer to
/// the out-params). Also, when processing the SpecialOps, we determine what params we need
/// to add to the exchange method (e.g., a 'remove' statement corresponds to an in-param,
/// an 'add' statement corresponds to an out-param, and so on). We collect that information
/// in `ctxt.params`.
///
/// Also note that the translation looks slightly different than the translation done in
/// `simplification.rs` which is used for the relations describing the atomic transitions.
/// The reason for that is that the translation of `simplification.rs` often creates
/// conditions that refer to the entire state (e.g., the safety conditions for 'add').
/// On the other hand, the conditions we produce here must refer to local state (although
/// they must also _imply_ the enabling conditions of the atomic transition relation).
/// Further, we do not create new 'Assert' statements here at all. If the user wants
/// the exchange postcondition to contain any additional predicates, they can always
/// add an 'assert' explicitly.

fn translate_transition(
    ctxt: &mut Ctxt,
    ts: &mut TransitionStmt,
    errors: &mut Vec<Error>,
) -> parse::Result<()> {
    let new_ts = match ts {
        TransitionStmt::Block(_span, v) => {
            for child in v.iter_mut() {
                translate_transition(ctxt, child, errors)?;
            }
            return Ok(());
        }
        TransitionStmt::Split(span, split_kind, splits) => {
            match split_kind {
                SplitKind::Special(id, op, _proof, pat_opt) => {
                    let field = ctxt.get_field_or_panic(id);
                    let condition_ts_opt =
                        translate_special_condition(ctxt, *span, &field, op, pat_opt, errors);
                    let assignment_opt = if pat_opt.is_some() {
                        // The relevant token param should be the last one in the params
                        // (having been added by the above call to
                        // `translate_special_condition`)
                        let param_vec = &ctxt.params[&field.name.to_string()];
                        let param = &param_vec[param_vec.len() - 1];

                        Some(translate_special_assignment(op, &param))
                    } else {
                        None
                    };

                    // Do this _after_ calling translate_special_condition so the params end up
                    // in the right order.
                    for split in splits.iter_mut() {
                        translate_transition(ctxt, split, errors)?;
                    }

                    let assignment_ts_opt = match assignment_opt {
                        None => {
                            assert!(splits.len() == 1 && splits[0].is_trivial());
                            assert!(pat_opt.is_none());
                            None
                        }
                        Some(assign_e) => {
                            assert!(splits.len() == 1);

                            let pat = pat_opt.as_ref().expect("expected pat");
                            if let Some((pat1, init1)) = assign_pat_or_arbitrary(pat, &assign_e) {
                                let kind = SplitKind::Let(pat1, None, LetKind::Normal, init1);
                                Some(TransitionStmt::Split(*span, kind, splits.clone()))
                            } else {
                                Some(splits[0].clone())
                            }
                        }
                    };

                    match (condition_ts_opt, assignment_ts_opt) {
                        (None, None) => {
                            panic!("no op should be completely trivial");
                        }
                        (Some(ts), None) => ts,
                        (None, Some(ts)) => ts,
                        (Some(ts1), Some(ts2)) => TransitionStmt::Block(*span, vec![ts1, ts2]),
                    }
                }
                _ => {
                    translate_split_kind(ctxt, split_kind, errors);
                    for split in splits.iter_mut() {
                        translate_transition(ctxt, split, errors)?;
                    }
                    return Ok(());
                }
            }
        }
        TransitionStmt::Require(_span, e) => {
            let req_e = translate_expr(ctxt, e, false, errors);
            *e = req_e;
            return Ok(());
        }
        TransitionStmt::Assert(_span, e, _) => {
            let assert_e = translate_expr(ctxt, e, false, errors);
            *e = assert_e;
            return Ok(());
        }

        TransitionStmt::SubUpdate(..) => {
            panic!("sub-update not supported here");
        }
        TransitionStmt::Initialize(_span, _id, e) | TransitionStmt::Update(_span, _id, e) => {
            let update_e = translate_expr(ctxt, e, false, errors);
            *e = update_e;
            return Ok(());
        }

        TransitionStmt::PostCondition(..) => {
            return Ok(());
        }
    };

    *ts = new_ts;

    Ok(())
}

fn translate_split_kind(ctxt: &mut Ctxt, sk: &mut SplitKind, errors: &mut Vec<Error>) {
    match sk {
        SplitKind::Let(_pat, _ty, lk, init_e) => {
            let birds_eye = *lk == LetKind::BirdsEye;
            let e = translate_expr(ctxt, init_e, birds_eye, errors);
            *init_e = e;
        }
        SplitKind::If(cond) => {
            let e = translate_expr(ctxt, cond, false, errors);
            *cond = e;
        }
        SplitKind::Match(match_e, arms) => {
            let e = translate_expr(ctxt, match_e, false, errors);
            *match_e = e;
            for arm in arms.iter_mut() {
                match &mut arm.guard {
                    None => {}
                    Some((_, g)) => {
                        let e = translate_expr(ctxt, g, false, errors);
                        *g = Box::new(e);
                    }
                }
            }
        }
        SplitKind::Special(..) => {
            panic!("handled separately");
        }
    }
}

fn field_token_collection_type(sm: &SM, field: &Field) -> Type {
    let ty = field_token_type(sm, field);
    match &field.stype {
        ShardableType::Option(_)
        | ShardableType::PersistentOption(_)
        | ShardableType::Bool
        | ShardableType::PersistentBool => Type::Verbatim(quote! { ::core::option::Option<#ty> }),

        ShardableType::Map(key, _) | ShardableType::PersistentMap(key, _) => {
            Type::Verbatim(quote_vstd! { vstd => #vstd::map::Map<#key, #ty> })
        }

        ShardableType::Set(t) | ShardableType::PersistentSet(t) => {
            Type::Verbatim(quote_vstd! { vstd => #vstd::map::Map<#t, #ty> })
        }

        ShardableType::Multiset(t) => {
            Type::Verbatim(quote_vstd! { vstd => #vstd::map::Map<#t, #ty> })
        }

        _ => {
            panic!("field_token_collection_type expected option/map/multiset/bool");
        }
    }
}

pub fn assign_pat_or_arbitrary(pat: &Pat, init_e: &Expr) -> Option<(Pat, Expr)> {
    let ids = crate::ident_visitor::pattern_get_bound_idents(&pat);
    if ids.len() == 0 {
        None
    } else if is_definitely_irrefutable(pat) {
        Some((pat.clone(), init_e.clone()))
    } else {
        let tup_pat;
        let tup_expr;
        if ids.len() > 1 {
            tup_pat = Pat::Verbatim(quote_spanned! { pat.span() =>
                (#(#ids),*)
            });
            tup_expr = Expr::Verbatim(quote_spanned! { pat.span() =>
                (#(#ids),*)
            });
        } else {
            let id = &ids[0];
            tup_pat = Pat::Verbatim(quote_spanned! { pat.span() =>
                #id
            });
            tup_expr = Expr::Verbatim(quote_spanned! { pat.span() =>
                #id
            });
        }

        let new_e = Expr::Verbatim(quote_spanned_vstd! { vstd, init_e.span() =>
            match (#init_e) { #pat => #tup_expr , #[allow(unreachable_patterns)] _ => #vstd::pervasive::arbitrary() }
        });
        Some((tup_pat, new_e))
    }
}

fn token_matches_elt(
    span: Span,
    token_is_ref: bool,
    token_name: &Ident,
    elt: &MonoidElt,
    pat_opt: &Option<Pat>,
    ctxt: &Ctxt,
    field: &Field,
    output: bool,
) -> Expr {
    match elt {
        MonoidElt::OptionSome(None) => {
            let pat = pat_opt.as_ref().expect("pat should exist for a pattern-binding case");
            if is_definitely_irrefutable(pat) {
                // TODO for cleaner output, avoid emitting anything here
                Expr::Verbatim(quote_spanned! { span => true })
            } else {
                Expr::Verbatim(quote_spanned! { span =>
                    match #token_name.view().value {
                        #pat => true,
                        #[allow(unreachable_patterns)]
                        _ => false,
                    }
                })
            }
        }
        MonoidElt::OptionSome(Some(e)) => {
            mk_eq(span, &Expr::Verbatim(quote_spanned! { span => #token_name.view().value}), &e)
        }
        MonoidElt::SingletonMultiset(e) => mk_and(
            span,
            mk_eq(span, &Expr::Verbatim(quote_spanned! { span => #token_name.view().key}), &e),
            Expr::Verbatim(quote_spanned! { span => #token_name.view().count == 1 }),
        ),
        MonoidElt::SingletonKV(key, None) => {
            let e1 = mk_eq(
                span,
                &Expr::Verbatim(quote_spanned! { span => #token_name.view().key}),
                &key,
            );

            let pat = pat_opt.as_ref().expect("pat should exist for a pattern-binding case");
            if is_definitely_irrefutable(pat) {
                e1
            } else {
                let e2 = Expr::Verbatim(quote_spanned! { span =>
                    match #token_name.view().value {
                        #pat => true,
                        #[allow(unreachable_patterns)]
                        _ => false,
                    }
                });
                mk_and(span, e1, e2)
            }
        }
        MonoidElt::SingletonKV(key, Some(val)) => mk_and(
            span,
            mk_eq(span, &Expr::Verbatim(quote_spanned! { span => #token_name.view().key}), &key),
            mk_eq(span, &Expr::Verbatim(quote_spanned! { span => #token_name.view().value}), &val),
        ),
        MonoidElt::SingletonSet(e) => {
            mk_eq(span, &Expr::Verbatim(quote_spanned! { span => #token_name.view().key }), &e)
        }
        MonoidElt::True => Expr::Verbatim(quote_spanned! { span => true }),
        MonoidElt::General(e) => match &field.stype {
            ShardableType::Count | ShardableType::PersistentCount => {
                mk_eq(span, &Expr::Verbatim(quote_spanned! { span => #token_name.view().count}), &e)
            }
            _ => {
                let token_value = if token_is_ref {
                    Expr::Verbatim(quote_spanned! { span => *#token_name })
                } else {
                    Expr::Verbatim(quote_spanned! { span => #token_name })
                };
                relation_for_collection_of_internal_tokens(
                    &ctxt.sm,
                    field,
                    token_value,
                    e.clone(),
                    get_inst_value(ctxt),
                    output,
                )
            }
        },
    }
}

fn translate_special_condition(
    ctxt: &mut Ctxt,
    span: Span,
    field: &Field,
    op: &SpecialOp,
    pat_opt: &Option<Pat>,
    errors: &mut Vec<Error>,
) -> Option<TransitionStmt> {
    match op {
        SpecialOp { stmt: MonoidStmtType::Have, elt } => {
            let elt = translate_elt(ctxt, elt, false, errors);

            let ident = ctxt.get_numbered_token_ident(&field.name);
            let is_collection = elt.is_general() && !field.stype.is_count();
            let ty = if is_collection {
                field_token_collection_type(&ctxt.sm, &field)
            } else {
                field_token_type(&ctxt.sm, &field)
            };

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::BorrowIn,
                name: ident.clone(),
                ty: ty,
                is_collection,
            });

            Some(TransitionStmt::Require(
                span,
                token_matches_elt(span, true, &ident, &elt, pat_opt, ctxt, &field, false),
            ))
        }

        SpecialOp { stmt: MonoidStmtType::Add(_), elt } => {
            let elt = translate_elt(ctxt, elt, false, errors);

            let ident = ctxt.get_numbered_token_ident(&field.name);
            let is_collection = elt.is_general() && !field.stype.is_count();
            let ty = if is_collection {
                field_token_collection_type(&ctxt.sm, &field)
            } else {
                field_token_type(&ctxt.sm, &field)
            };

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::Out,
                name: ident.clone(),
                ty: ty,
                is_collection,
            });

            Some(TransitionStmt::PostCondition(
                span,
                token_matches_elt(span, false, &ident, &elt, pat_opt, ctxt, &field, true),
            ))
        }

        SpecialOp { stmt: MonoidStmtType::Remove, elt } => {
            let elt = translate_elt(ctxt, elt, false, errors);

            let ident = ctxt.get_numbered_token_ident(&field.name);
            let is_collection = elt.is_general() && !field.stype.is_count();
            let ty = if is_collection {
                field_token_collection_type(&ctxt.sm, &field)
            } else {
                field_token_type(&ctxt.sm, &field)
            };

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::In,
                name: ident.clone(),
                ty: ty,
                is_collection,
            });

            Some(TransitionStmt::Require(
                span,
                token_matches_elt(span, false, &ident, &elt, pat_opt, ctxt, &field, false),
            ))
        }

        SpecialOp { stmt: MonoidStmtType::Guard, elt } => {
            // note: ignore 'key' expression for the KV case
            let e = translate_value_expr(ctxt, elt, false, errors)
                .expect("value must exist (can't bind in guard)");

            let ident = ctxt.get_numbered_token_ident(&field.name);
            let ty = if elt.is_general() {
                shardable_type_to_type(field.type_span, &field.stype)
            } else {
                stored_object_type(&field)
            };

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::BorrowOut,
                name: ident.clone(),
                ty: ty,
                is_collection: false,
            });

            Some(TransitionStmt::PostCondition(
                span,
                mk_eq(span, &Expr::Verbatim(quote! {*#ident}), &e),
            ))
        }

        SpecialOp { stmt: MonoidStmtType::Deposit, elt } => {
            let e = translate_value_expr(ctxt, elt, false, errors)
                .expect("value must exist (can't bind in guard)");

            let ident = ctxt.get_numbered_token_ident(&field.name);
            let ty = if elt.is_general() {
                shardable_type_to_type(field.type_span, &field.stype)
            } else {
                stored_object_type(&field)
            };

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::In,
                name: ident.clone(),
                ty: ty,
                is_collection: false,
            });

            Some(TransitionStmt::Require(span, mk_eq(span, &Expr::Verbatim(quote! {#ident}), &e)))
        }

        SpecialOp { stmt: MonoidStmtType::Withdraw, elt } => {
            let e_opt = translate_value_expr(ctxt, elt, false, errors);

            let ident = ctxt.get_numbered_token_ident(&field.name);
            let ty = if elt.is_general() {
                shardable_type_to_type(field.type_span, &field.stype)
            } else {
                stored_object_type(&field)
            };

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::Out,
                name: ident.clone(),
                ty: ty,
                is_collection: false,
            });

            if let Some(e) = e_opt {
                Some(TransitionStmt::PostCondition(
                    span,
                    mk_eq(span, &Expr::Verbatim(quote! {#ident}), &e),
                ))
            } else {
                let pat = pat_opt.as_ref().expect("for pat-binding case, pat is expected");
                if is_definitely_irrefutable(&pat) {
                    None
                } else {
                    Some(TransitionStmt::PostCondition(
                        span,
                        Expr::Verbatim(quote! {
                            match #ident {
                                #pat => true,
                                #[allow(unreachable_patterns)]
                                _ => false
                            }
                        }),
                    ))
                }
            }
        }
    }
}

fn translate_special_assignment(op: &SpecialOp, param: &TokenParam) -> Expr {
    let name = &param.name;

    match op.stmt {
        MonoidStmtType::Have => {
            assert!(param.inout_type == InoutType::BorrowIn);
            Expr::Verbatim(quote! { #name.view().value })
        }
        MonoidStmtType::Remove => {
            assert!(param.inout_type == InoutType::In);
            Expr::Verbatim(quote! { #name.view().value })
        }
        MonoidStmtType::Withdraw => {
            assert!(param.inout_type == InoutType::Out);
            Expr::Verbatim(quote! { #name })
        }

        MonoidStmtType::Add(_) | MonoidStmtType::Guard | MonoidStmtType::Deposit => {
            panic!("unexpected monoid type");
        }
    }
}

fn translate_elt(
    ctxt: &Ctxt,
    elt: &MonoidElt,
    birds_eye: bool,
    errors: &mut Vec<Error>,
) -> MonoidElt {
    match elt {
        MonoidElt::OptionSome(None) => MonoidElt::OptionSome(None),
        MonoidElt::OptionSome(Some(e)) => {
            let e = translate_expr(ctxt, e, birds_eye, errors);
            MonoidElt::OptionSome(Some(e))
        }
        MonoidElt::SingletonMultiset(e) => {
            let e = translate_expr(ctxt, e, birds_eye, errors);
            MonoidElt::SingletonMultiset(e)
        }
        MonoidElt::SingletonSet(e) => {
            let e = translate_expr(ctxt, e, birds_eye, errors);
            MonoidElt::SingletonSet(e)
        }
        MonoidElt::SingletonKV(e1, None) => {
            let e1 = translate_expr(ctxt, e1, birds_eye, errors);
            MonoidElt::SingletonKV(e1, None)
        }
        MonoidElt::SingletonKV(e1, Some(e2)) => {
            let e1 = translate_expr(ctxt, e1, birds_eye, errors);
            let e2 = translate_expr(ctxt, e2, birds_eye, errors);
            MonoidElt::SingletonKV(e1, Some(e2))
        }
        MonoidElt::True => MonoidElt::True,
        MonoidElt::General(e) => {
            let e = translate_expr(ctxt, e, birds_eye, errors);
            MonoidElt::General(e)
        }
    }
}

/// Gets the "value" expression from the MonoidElt
/// (whichever corresponds to the 'value' field of the token struct).
/// (For a map element, it's the value of the key-value pair;
/// for anything else, where there's only expression, it's that one.)
fn translate_value_expr(
    ctxt: &Ctxt,
    elt: &MonoidElt,
    birds_eye: bool,
    errors: &mut Vec<Error>,
) -> Option<Expr> {
    match elt {
        MonoidElt::OptionSome(Some(e))
        | MonoidElt::General(e)
        | MonoidElt::SingletonMultiset(e)
        | MonoidElt::SingletonSet(e)
        | MonoidElt::SingletonKV(_, Some(e)) => Some(translate_expr(ctxt, e, birds_eye, errors)),
        MonoidElt::OptionSome(None) | MonoidElt::SingletonKV(_, None) => None,
        MonoidElt::True => {
            // bool is not supported for storage types.
            // If this ends up getting called I'm not sure what the intent would be.
            panic!("translate_value_expr called for 'True'");
        }
    }
}

/// Perform translation on the Rust AST Exprs.
/// We need to find expressions like `pre.foo` that refer to individual fields and replace
/// them with some expression in terms of the parameters of the exchange function.
/// There are a few ways this can happen, depending on the context:
///
///  * Reading a 'Constant' field. In this case, we replace it with the constant value
///    from the instance object, e.g., `instance.foo()`.
///
///  * Reading a 'Variable' field. Replace it with the value from the input token
///    e.g., `token_foo.view().value` or `old(token_foo).view().value`.
///
///  * A nondeterministic read. In this case, we replace it with the value of one of the
///    _out_ parameters. Previous well-formedness checks (`check_birds_eye`) should ensure
///    that this will only happen in contexts that will ultimately appears in the
///    post-conditions, never pre-conditions.

#[must_use]
fn translate_expr(ctxt: &Ctxt, expr: &Expr, birds_eye: bool, errors: &mut Vec<Error>) -> Expr {
    let mut expr = expr.clone();
    visit_field_accesses(
        &mut expr,
        |errors, field, node| {
            if birds_eye {
                match &field.stype {
                    ShardableType::Variable(_ty) => {
                        // Handle it as a 'nondeterministic' value UNLESS
                        // we're already reading this token anyway.
                        if ctxt.fields_read.contains(&field.name.to_string())
                            || ctxt.fields_written.contains(&field.name.to_string())
                        {
                            *node = get_old_field_value(ctxt, &field, node.span());
                        } else {
                            *node = get_nondeterministic_out_value(ctxt, &field, node.span());
                        }
                    }
                    ShardableType::Constant(_ty) => {
                        // Always handle constants as normal, since we always have access to them.
                        *node = get_const_field_value(ctxt, &field, node.span());
                    }
                    _ => {
                        *node = get_nondeterministic_out_value(ctxt, &field, node.span());
                    }
                }
            } else {
                match &field.stype {
                    ShardableType::Variable(_ty) => {
                        *node = get_old_field_value(ctxt, &field, node.span());
                    }
                    ShardableType::Constant(_ty) => {
                        *node = get_const_field_value(ctxt, &field, node.span());
                    }
                    _ => {
                        let strat = field.stype.strategy_name();
                        errors.push(Error::new(
                            node.span(),
                            format!("A '{strat:}' field cannot be directly referenced here"),
                        )); // TODO be more specific
                    }
                }
            }
        },
        errors,
        &ctxt.ident_to_field,
    );
    expr
}

fn get_inst_value(ctxt: &Ctxt) -> Expr {
    if ctxt.is_init {
        Expr::Verbatim(quote! { instance })
    } else {
        Expr::Verbatim(quote! { (*self) })
    }
}

fn get_const_field_value(ctxt: &Ctxt, field: &Field, span: Span) -> Expr {
    let inst = get_inst_value(ctxt);
    let field_name = &field.name;
    Expr::Verbatim(quote_spanned! { span => #inst.#field_name() })
}

fn get_nondeterministic_out_value(_ctxt: &Ctxt, field: &Field, span: Span) -> Expr {
    let name = nondeterministic_read_spec_out_name(field);
    Expr::Verbatim(quote_spanned! { span => #name })
}

fn get_old_field_value(ctxt: &Ctxt, field: &Field, span: Span) -> Expr {
    let arg = transition_arg_name(&field);
    let field_name = field_token_field_name(&field);
    if ctxt.fields_written.contains(&field.name.to_string()) {
        Expr::Verbatim(
            quote_spanned_vstd! { vstd, span => #vstd::prelude::old(#arg).view().#field_name },
        )
    } else {
        Expr::Verbatim(quote_spanned! { span => #arg.view().#field_name })
    }
}

fn get_new_field_value(field: &Field) -> Expr {
    let arg = transition_arg_name(&field);
    let field = field_token_field_name(&field);
    Expr::Verbatim(quote! { #arg.view().#field })
}

// Collect requires and ensures. Updates `ctxt.requires` and `ctxt.ensures`
// of the &mut ctxt argument.
//
// This is somewhat tricky because of how we handle 'assert' statements.
// The pre-condition should have a condition that corresponds to the
// enabling conditions of the _weak_ translation relation, i.e., the caller
// of the exchange method should NOT need to prove any asserts.
//
// So if the transition is defined like,
//      assert(A);
//      require(B);
// then the precondition should be `A ==> B`.
//
// On the other hand, we also want to put the results of the 'assert'
// statements in the post-condition. (This is, in fact, the whole point
// of even having read-only transitions.)
//
// And of course, we have to consider some of these may be under conditionals.
// So as we walk the tree, we have to collect all these conditions that might
// be in the hypothesis of the condition we want to generate.

#[derive(Clone, Debug)]
enum PrequelElement {
    AssertCondition(Expr),
    Condition(Expr),
    Let(Pat, Option<Type>, Expr),
    Match(Expr, Vec<Arm>, usize),
}

fn exchange_collect(
    ctxt: &mut Ctxt,
    ts: &TransitionStmt,
    prequel: Vec<PrequelElement>,
) -> parse::Result<Vec<PrequelElement>> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            let mut p = prequel;
            for child in v.iter() {
                let p1 = exchange_collect(ctxt, child, p)?;
                p = p1;
            }
            Ok(p)
        }
        TransitionStmt::Split(_span, SplitKind::Let(pat, ty, _lk, init_e), es) => {
            assert!(es.len() == 1);
            let child = &es[0];

            let mut p = prequel.clone();
            p.push(PrequelElement::Let(pat.clone(), ty.clone(), init_e.clone()));
            let _ = exchange_collect(ctxt, child, p);

            let mut prequel = prequel;
            if let Some(e) = asserts_to_single_predicate(ts) {
                prequel.push(PrequelElement::AssertCondition(Expr::Verbatim(e)));
            }
            Ok(prequel)
        }
        TransitionStmt::Split(_span, SplitKind::If(cond_e), es) => {
            assert!(es.len() == 2);

            let cond = PrequelElement::Condition(cond_e.clone());
            let not_cond = PrequelElement::Condition(bool_not_expr(cond_e));

            let mut p1 = prequel.clone();
            p1.push(cond);
            let _ = exchange_collect(ctxt, &es[0], p1)?;

            let mut p2 = prequel.clone();
            p2.push(not_cond);
            let _ = exchange_collect(ctxt, &es[1], p2)?;

            let mut prequel = prequel;
            if let Some(e) = asserts_to_single_predicate(ts) {
                prequel.push(PrequelElement::AssertCondition(Expr::Verbatim(e)));
            }
            Ok(prequel)
        }
        TransitionStmt::Split(_span, SplitKind::Match(match_e, arms), es) => {
            assert!(arms.len() == es.len());
            for i in 0..arms.len() {
                let elem = PrequelElement::Match(match_e.clone(), arms.clone(), i);
                let mut p1 = prequel.clone();
                p1.push(elem);
                let _ = exchange_collect(ctxt, &es[i], p1)?;
            }
            let mut prequel = prequel;
            if let Some(e) = asserts_to_single_predicate(ts) {
                prequel.push(PrequelElement::AssertCondition(Expr::Verbatim(e)));
            }
            Ok(prequel)
        }
        TransitionStmt::Split(_span, SplitKind::Special(..), _) => {
            panic!("should have been removed in preprocessing");
        }
        TransitionStmt::Require(_span, req_e) => {
            ctxt.requires.push(with_prequel(&prequel, true, req_e.clone()));
            Ok(prequel)
        }
        TransitionStmt::Assert(_span, assert_e, _) => {
            ctxt.ensures.push(with_prequel(&prequel, false, assert_e.clone()));
            let mut prequel = prequel;
            prequel.push(PrequelElement::AssertCondition(assert_e.clone()));
            Ok(prequel)
        }
        TransitionStmt::PostCondition(_span, post_e) => {
            ctxt.ensures.push(with_prequel(&prequel, false, post_e.clone()));
            Ok(prequel)
        }
        TransitionStmt::Update(..) => Ok(prequel),
        TransitionStmt::SubUpdate(..) => Ok(prequel),
        TransitionStmt::Initialize(..) => Ok(prequel),
    }
}

fn bool_not_expr(e: &Expr) -> Expr {
    Expr::Verbatim(quote! { !(#e) })
}

fn with_prequel(pre: &Vec<PrequelElement>, include_assert_conditions: bool, e: Expr) -> Expr {
    let mut e = e;
    let span = e.span();
    for p in pre.iter().rev() {
        match p {
            PrequelElement::Let(pat, None, init_e) => {
                e = Expr::Verbatim(quote_spanned! { span => { let #pat = #init_e; #e } });
            }
            PrequelElement::Let(pat, Some(ty), init_e) => {
                e = Expr::Verbatim(quote_spanned! { span => { let #pat: #ty = #init_e; #e } });
            }
            PrequelElement::Condition(cond_e) => {
                e = Expr::Verbatim(
                    quote_spanned_vstd! { vstd, span => #vstd::prelude::imply(#cond_e, #e) },
                );
            }
            PrequelElement::Match(match_e, arms, idx) => {
                // Create something that looks like
                // match m {
                //    case1 => true,
                //    case2 => e,
                //    case3 => true,
                //    ...
                // }
                // That is, all the cases are just `true`, except the one case of interest.
                // Thus the match functions as an implication, i.e., "if the expression
                // matches this particular case, then ..."
                let mut arm_exprs = vec![Expr::Verbatim(quote! {true}); arms.len()];
                arm_exprs[*idx] = e;
                e = emit_match(span, match_e, arms, &arm_exprs);
            }
            PrequelElement::AssertCondition(cond_e) => {
                if include_assert_conditions {
                    e = Expr::Verbatim(
                        quote_spanned_vstd! { vstd, span => #vstd::prelude::imply(#cond_e, #e) },
                    );
                }
            }
        }
    }
    e
}

/// Prune out ops that update a NotTokenized field.
/// The resulting transition is, of course, not equivalent to the original in the
/// sense of its action on the global state, but for the purpose of the exchange method,
/// it doesn't matter. Updates to a NotTokenized field aren't observed by the exchange method.
/// (Also, if there's just any dead code for any other reason, that will also get pruned
/// as a byproduct.)

fn prune_irrelevant_ops(ctxt: &Ctxt, ts: TransitionStmt) -> TransitionStmt {
    let span = ts.get_span().clone();
    match prune_irrelevant_ops_rec(ctxt, ts) {
        Some(ts) => ts,
        None => TransitionStmt::Block(span, vec![]),
    }
}

fn prune_irrelevant_ops_rec(ctxt: &Ctxt, ts: TransitionStmt) -> Option<TransitionStmt> {
    match ts {
        TransitionStmt::Block(span, v) => {
            let res: Vec<TransitionStmt> =
                v.into_iter().filter_map(|t| prune_irrelevant_ops_rec(ctxt, t)).collect();
            if res.len() == 0 { None } else { Some(TransitionStmt::Block(span, res)) }
        }
        TransitionStmt::Split(span, split_kind, splits) => {
            let pruned_splits: Vec<Option<TransitionStmt>> =
                splits.into_iter().map(|split| prune_irrelevant_ops_rec(ctxt, split)).collect();

            let mut is_nontrivial = pruned_splits.iter().any(|s| s.is_some());
            match split_kind {
                SplitKind::Special(..) => {
                    is_nontrivial = true;
                }
                SplitKind::Let(..) | SplitKind::If(..) | SplitKind::Match(..) => {}
            }

            if !is_nontrivial {
                None
            } else {
                let splits = pruned_splits
                    .into_iter()
                    .map(|split| split.unwrap_or(TransitionStmt::Block(span, vec![])))
                    .collect();
                Some(TransitionStmt::Split(span, split_kind, splits))
            }
        }

        TransitionStmt::SubUpdate(..) => {
            panic!("sub-update not supported here");
        }

        TransitionStmt::Update(span, id, e) => {
            let f = ctxt.get_field_or_panic(&id);
            let is_not_tokenized = match &f.stype {
                ShardableType::NotTokenized(..) => true,
                _ => false,
            };
            if is_not_tokenized { None } else { Some(TransitionStmt::Update(span, id, e)) }
        }

        TransitionStmt::Initialize(span, id, e) => {
            let f = ctxt.get_field_or_panic(&id);
            let is_not_tokenized = match &f.stype {
                ShardableType::NotTokenized(..) => true,
                _ => false,
            };
            if is_not_tokenized { None } else { Some(TransitionStmt::Initialize(span, id, e)) }
        }

        TransitionStmt::Require(span, req_e) => Some(TransitionStmt::Require(span, req_e)),
        TransitionStmt::Assert(span, assert_e, proof) => {
            Some(TransitionStmt::Assert(span, assert_e, proof.clone()))
        }
        TransitionStmt::PostCondition(span, post_e) => {
            Some(TransitionStmt::PostCondition(span, post_e))
        }
    }
}

/// Get the expression E that a given field gets updated to.
/// This is used in the post-condition of the exchange method.
/// Since the 'update' might be inside a conditional, we may need to build
/// a conditional expression.
///
/// Returns 'None' if it doesn't find an 'update' for the given variable.
///
/// Also handles 'init' statements in the same way as 'update' statements,
/// so it can be used for initialization as well.
///
/// Ignores all special ops.

fn get_post_value_for_variable(ctxt: &Ctxt, ts: &TransitionStmt, field: &Field) -> Option<Expr> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            let mut opt = None;
            for child in v.iter() {
                let o = get_post_value_for_variable(ctxt, child, field);
                if o.is_some() {
                    // We should have already performed a check that the field
                    // is not updated more than once.
                    assert!(!opt.is_some());
                    opt = o;
                }
            }
            opt
        }
        TransitionStmt::Split(span, split_kind, es) => {
            let opts: Vec<Option<Expr>> =
                es.iter().map(|e| get_post_value_for_variable(ctxt, e, field)).collect();
            if opts.iter().any(|o| o.is_some()) {
                let cases: Vec<Expr> = opts
                    .into_iter()
                    .map(|o| match o {
                        None => get_old_field_value(ctxt, &field, field.name.span()),
                        Some(e) => e,
                    })
                    .collect();
                match split_kind {
                    SplitKind::If(cond_e) => {
                        assert!(cases.len() == 2);
                        let e1 = &cases[0];
                        let e2 = &cases[1];
                        Some(Expr::Verbatim(quote_spanned! { *span =>
                            if #cond_e { #e1 } else { #e2 }
                        }))
                    }
                    SplitKind::Match(match_e, arms) => {
                        Some(emit_match(*span, match_e, arms, &cases))
                    }
                    SplitKind::Let(pat, ty, _lk, init_e) => {
                        let ty_tokens = match ty {
                            None => TokenStream::new(),
                            Some(ty) => quote! { : #ty },
                        };
                        assert!(cases.len() == 1);
                        let child_e = &cases[0];
                        Some(Expr::Verbatim(quote! {
                            { let #pat #ty_tokens = #init_e; #child_e }
                        }))
                    }
                    SplitKind::Special(..) => {
                        panic!("should have been translated out");
                    }
                }
            } else {
                None
            }
        }
        TransitionStmt::SubUpdate(..) => {
            panic!("sub-update not supported here");
        }
        TransitionStmt::Initialize(_span, id, e) | TransitionStmt::Update(_span, id, e) => {
            if *id.to_string() == *field.name.to_string() { Some(e.clone()) } else { None }
        }
        TransitionStmt::Require(..)
        | TransitionStmt::Assert(..)
        | TransitionStmt::PostCondition(..) => None,
    }
}

fn asserts_to_single_predicate(ts: &TransitionStmt) -> Option<TokenStream> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            let mut o = None;
            for t in v {
                o = conjunct_opt(o, asserts_to_single_predicate(t));
            }
            o
        }
        TransitionStmt::Split(_span, SplitKind::Let(pat, ty, _, e), es) => {
            let ty_tokens = match ty {
                None => TokenStream::new(),
                Some(ty) => quote! { : #ty },
            };
            assert!(es.len() == 1);
            let child = &es[0];
            match asserts_to_single_predicate(child) {
                None => None,
                Some(r) => Some(quote! { { let #pat #ty_tokens = #e; #r } }),
            }
        }
        TransitionStmt::Split(_span, SplitKind::If(cond), es) => {
            assert!(es.len() == 2);
            let x1 = asserts_to_single_predicate(&es[0]);
            let x2 = asserts_to_single_predicate(&es[1]);
            match (x1, x2) {
                (None, None) => None,
                (Some(e1), None) => Some(quote_vstd! { vstd => #vstd::prelude::imply(#cond, #e1) }),
                (None, Some(e2)) => {
                    Some(quote_vstd! { vstd => #vstd::prelude::imply(!(#cond), #e2) })
                }
                (Some(e1), Some(e2)) => Some(quote! { if #cond { #e1 } else { #e2 } }),
            }
        }
        TransitionStmt::Split(span, SplitKind::Match(match_e, arms), es) => {
            let opts: Vec<Option<TokenStream>> =
                es.iter().map(|e| asserts_to_single_predicate(e)).collect();
            if opts.iter().any(|o| o.is_some()) {
                let cases = opts
                    .into_iter()
                    .map(|opt_t| Expr::Verbatim(opt_t.unwrap_or(quote! {true})))
                    .collect();
                let m = emit_match(*span, match_e, arms, &cases);
                Some(quote! {#m})
            } else {
                None
            }
        }
        TransitionStmt::Split(_span, SplitKind::Special(..), _es) => {
            panic!("Special should have been translated out");
        }
        TransitionStmt::Assert(_span, e, _) => Some(quote_spanned! { e.span() => (#e) }),
        TransitionStmt::PostCondition(..)
        | TransitionStmt::Require(..)
        | TransitionStmt::Initialize(..)
        | TransitionStmt::Update(..)
        | TransitionStmt::SubUpdate(..) => None,
    }
}
