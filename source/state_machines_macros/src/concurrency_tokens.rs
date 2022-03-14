//! Output all the generated code specific to concurrent state machines.
//! We print declarations for:
//!
//!  * The Instance type
//!  * All the Token types for shardable fields
//!  * #[proof] methods for each transition (including init and readonly transitions)

use crate::ast::{
    Field, Lemma, LetKind, ShardableType, SpecialOp, Transition, TransitionKind, TransitionStmt, SM,
};
use crate::checks::{check_ordering_remove_have_add, check_unsupported_updates_in_conditionals};
use crate::field_access_visitor::{find_all_accesses, visit_field_accesses};
use crate::parse_token_stream::SMBundle;
use crate::to_relation::asserts_to_single_predicate;
use crate::to_token_stream::{
    get_self_ty, get_self_ty_turbofish, impl_decl_stream, name_with_type_args,
    name_with_type_args_turbofish, shardable_type_to_type,
};
use crate::util::combine_errors_or_ok;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;
use std::collections::HashSet;
use syn::parse::Error;
use syn::spanned::Spanned;
use syn::{Expr, Ident, Type};

// Misc. definitions for various identifiers we use

// TODO names like {name}_Instance kind of suck, {name}::Instance
// would feel so much better, but this currently isn't possible unless {name}
// is a module... still, there's probably something better we can do though

fn inst_type_name(sm_name: &Ident) -> Ident {
    let name = sm_name.to_string() + "_Instance";
    Ident::new(&name, sm_name.span())
}

fn inst_type(sm: &SM) -> Type {
    name_with_type_args(&inst_type_name(&sm.name), sm)
}

fn field_token_type_name(sm_name: &Ident, field: &Field) -> Ident {
    let name = sm_name.to_string() + "_" + &field.name.to_string();
    Ident::new(&name, field.name.span())
}

fn field_token_type(sm: &SM, field: &Field) -> Type {
    name_with_type_args(&field_token_type_name(&sm.name, field), sm)
}

fn field_token_type_turbofish(sm: &SM, field: &Field) -> Type {
    name_with_type_args_turbofish(&field_token_type_name(&sm.name, field), sm)
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
        ShardableType::StorageOptional(ty) => ty.clone(),
        ShardableType::Variable(_)
        | ShardableType::Constant(_)
        | ShardableType::NotTokenized(_)
        | ShardableType::Optional(_)
        | ShardableType::Map(_, _)
        | ShardableType::Multiset(_) => {
            panic!("stored_object_type");
        }
    }
}

fn exchange_name(tr: &Transition) -> Ident {
    tr.name.clone()
}

fn transition_arg_name(field: &Field) -> Ident {
    let name = "token_".to_string() + &field.name.to_string();
    Ident::new(&name, field.name.span())
}

fn option_relation_post_condition_name(field: &Field) -> Ident {
    Ident::new("option_agree", field.name.span())
}

fn option_relation_post_condition_qualified_name(sm: &SM, field: &Field) -> Type {
    let ty = field_token_type_turbofish(sm, field);
    let name = option_relation_post_condition_name(field);
    Type::Verbatim(quote! { #ty::#name })
}

fn map_relation_post_condition_name(field: &Field) -> Ident {
    Ident::new("map_agree", field.name.span())
}

fn map_relation_post_condition_qualified_name(sm: &SM, field: &Field) -> Type {
    let ty = field_token_type_turbofish(sm, field);
    let name = map_relation_post_condition_name(field);
    Type::Verbatim(quote! { #ty::#name })
}

fn multiset_relation_post_condition_name(field: &Field) -> Ident {
    Ident::new("multiset_agree", field.name.span())
}

fn multiset_relation_post_condition_qualified_name(sm: &SM, field: &Field) -> Type {
    let ty = field_token_type_turbofish(sm, field);
    let name = multiset_relation_post_condition_name(field);
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

    let storage_types = get_storage_type_tuple(sm);

    return quote! {
        #[proof]
        #[allow(non_camel_case_types)]
        #[verifier(unforgeable)]
        pub struct #insttype #gen {
            #[spec] send_sync: crate::pervasive::SyncSendIfSyncSend<#storage_types>,
            #[spec] state: #self_ty,
            #[spec] location: ::builtin::int,
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

/// Add a `clone()` method to the Instance type.
/// This is safe, because the Instance object effectively just represents
///
///   * the fact that the protocol exists, and has been initialized
///   * any constants associated to the protocol
///
/// TODO it would be even better to add a Copy instance as well; however, this
/// currently runs into Verus limitations with deriving instances.
fn trusted_clone() -> TokenStream {
    return quote! {
        #[proof]
        #[verifier(external_body)]
        #[verifier(returns(proof))]
        pub fn clone(#[proof] &self) -> Self {
            ensures(|s: Self| ::builtin::equal(*self, s));
            unimplemented!();
        }
    };
}

/// Create the struct for a Token.
/// For map types, include the key type to create both a 'key' and 'value' field;
/// otherwise, just include the value type.
fn token_struct_stream(sm: &SM, field: &Field, key_ty: Option<&Type>, value_ty: &Type) -> TokenStream {
    let tokenname = field_token_type_name(&sm.name, field);
    let insttype = inst_type(sm);
    let gen = &sm.generics;

    let impldecl = impl_decl_stream(&field_token_type(sm, field), &sm.generics);
    let impl_token_stream = collection_relation_fns_stream(sm, field);

    let key_field = match key_ty {
        Some(key_ty) => quote!{ #[spec] pub key: #key_ty, },
        None => TokenStream::new(),
    };

    return quote! {
        #[proof]
        #[verifier(unforgeable)]
        #[allow(non_camel_case_types)]
        pub struct #tokenname#gen {
            #[spec] pub instance: #insttype,
            #key_field
            #[spec] pub value: #value_ty,
        }

        #impldecl {
            #impl_token_stream
        }
    };
}

/// For a given sharding(constant) field, add that constant
/// as a #[spec] fn on the Instance type. (The field is constant
/// for the entire instance.)
///
/// note: we could make these fields on the Instance type instead
/// (this is safe as long as the Instance type is an unforgeable proof type)
/// but currently we have the body of the Instance as private
fn const_fn_stream(field: &Field) -> TokenStream {
    let fieldname = field_token_field_name(field);
    let fieldtype = match &field.stype {
        ShardableType::Constant(ty) => ty,
        _ => panic!("const_fn_stream expected Constant"),
    };

    return quote! {
        ::builtin_macros::fndecl!(
            pub fn #fieldname(&self) -> #fieldtype
        );
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
) -> syn::parse::Result<()> {
    let mut inst_impl_token_stream = TokenStream::new();

    token_stream.extend(instance_struct_stream(&bundle.sm));
    inst_impl_token_stream.extend(trusted_clone());

    for field in &bundle.sm.fields {
        match &field.stype {
            ShardableType::Constant(_) => {
                inst_impl_token_stream.extend(const_fn_stream(field));
            }
            ShardableType::Variable(ty) => {
                token_stream.extend(token_struct_stream(&bundle.sm, field, None, ty));
            }
            ShardableType::NotTokenized(_) => {
                // don't need to add a struct in this case
            }
            ShardableType::Optional(ty) => {
                token_stream.extend(token_struct_stream(&bundle.sm, field, None, ty));
            }
            ShardableType::Map(key, val) => {
                token_stream.extend(token_struct_stream(&bundle.sm, field, Some(key), val));
            }
            ShardableType::Multiset(ty) => {
                token_stream.extend(token_struct_stream(&bundle.sm, field, None, ty));
            }
            ShardableType::StorageOptional(_) => {
                // storage types don't have tokens; the 'token type' is just the
                // the type of the field
            }
        }
    }

    let mut errors = Vec::new();
    for tr in &bundle.sm.transitions {
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

#[derive(Clone, Copy)]
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
}

/// Context object for the complex task of translating a single
/// transition into a token-exchange method.

struct Ctxt {
    // fields written in some normal 'update' or 'init' statements
    // (not including special ops)
    fields_written: HashSet<String>,

    // fields read (via `self.field`) in some expression
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
        Ident::new(&format!("token_{}_{}", i, base_id.to_string()), base_id.span())
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
) -> syn::parse::Result<TokenStream> {
    let sm = &bundle.sm;

    let is_init = tr.kind == TransitionKind::Init;

    let mut ident_to_field = HashMap::new();

    // Initialize the `params` field of the `Ctxt` object. We'll fill this up
    // later; for now, just create an entry with an empty Vec for each relevant field.
    let mut init_params = HashMap::new();
    for field in &sm.fields {
        ident_to_field.insert(field.name.to_string(), field.clone());

        if !is_init {
            match &field.stype {
                ShardableType::Multiset(_)
                | ShardableType::Optional(_)
                | ShardableType::StorageOptional(_) => {
                    init_params.insert(field.name.to_string(), Vec::new());
                }
                _ => {}
            }
        }
    }

    let mut ctxt = Ctxt {
        fields_read: HashSet::new(),
        fields_written: HashSet::new(),
        fields_read_birds_eye: HashSet::new(),
        params: init_params,
        requires: Vec::new(),
        ensures: Vec::new(),
        ident_to_field,
        is_init: is_init,
        sm: bundle.sm.clone(),
        fresh_num_counter: 0,
    };

    let mut tr = tr.clone();

    check_unsupported_updates_in_conditionals(&tr.body)?;
    check_ordering_remove_have_add(sm, &tr.body)?;

    // Potentially remove steps that won't be useful.
    // We want to do this before `find_all_accesses` below, since this step may potentially
    // remove field accesses that we would like to ignore.
    // For example, suppose the user writes `update(foo, self.bar)` where `foo` is
    // NotTokenized. In that case, we want to make sure that we _don't_ process
    // self.bar as a requirement to have `bar` as an input token.
    tr.body = prune_irrelevant_ops(&ctxt, tr.body);

    // compute `ctxt.fields_written`, which is used to determine the output tokens
    determine_outputs(&mut ctxt, &tr.body)?;

    // Determine which fields are read (e.g., `self.foo`) and in what context those
    // fields are read.

    let mut errors = Vec::new();
    let (fields_read, fields_read_birds_eye) =
        find_all_accesses(&mut tr.body, &mut errors, &ctxt.ident_to_field);
    combine_errors_or_ok(errors)?;

    ctxt.fields_read = fields_read;
    ctxt.fields_read_birds_eye = fields_read_birds_eye;

    // translate the expressions in the TransitionStmt so that
    // where they previously referred to fields like `self.foo`,
    // they now refer to the field that comes from an input.
    // Also simplifies away SpecialOps.

    let mut errors = Vec::new();
    translate_transition(&mut ctxt, &mut tr.body, &mut errors)?;
    combine_errors_or_ok(errors)?;

    // translate the (new) TransitionStmt into expressions that
    // can be used as pre-conditions and post-conditions
    // This fills up `ctxt.requires` and `ctxt.ensures`.
    exchange_collect(&mut ctxt, &tr.body, Vec::new())?;

    // For our purposes here, a 'readonly' is just a special case of a normal transition,
    // but 'init' transitions need to be handled differently.
    // For the most part, there are two key differences between init and transition/readonly.
    //
    //   * An 'init' returns an arbitrary new Instance object, whereas a normal transition
    //     takes an Instance as input.
    //   * An 'init' will always return tokens for every field, and take no tokens as input
    //     (except for external 'storage' tokens).
    //     A normal transition takes tokens as input as is necessary.
    //
    // Generally speaking, the input parameters are going to look like:
    //    (instance as the 'self' argument)?    (present if not init)
    //    (spec transition params,)*            (parameters to the transition)
    //    (proof token params,)*                (if init, only includes storage tokens;
    //                                           otherwise, includes storage tokens AND
    //                                           tokens of this instance)

    let mut in_args: Vec<TokenStream> = Vec::new();
    let mut out_args: Vec<(TokenStream, TokenStream)> = Vec::new();

    // First, we create a parameter for the Instance, either an input or output parameter
    // as appropriate.

    if ctxt.is_init {
        let itn = inst_type(sm);
        out_args.push((quote! { instance }, quote! { #itn }));
    } else {
        in_args.push(quote! { #[proof] &self });
    }

    // Take the transition parameters (the normal parameters defined in the transition)
    // and make them input parameters (spec-mode) to the corresponding exchange method.

    for param in &tr.params {
        let id = &param.name;
        let ty = &param.ty;
        in_args.push(quote! { #[spec] #id: #ty });
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
            // 'init' routine. In particular, there should be no occurrences to `self.field`
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
                    let lhs = get_const_field_value(&ctxt, field);
                    ctxt.ensures.push(mk_eq(&lhs, &e));
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
                    &mut in_args,
                    &mut out_args,
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
                    &mut in_args,
                    &mut out_args,
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
            }
        } else {
            // The case for a 'transition' or 'readonly' transition.
            // (At this point, the distinction doesn't matter.)
            //
            // First, we handle fields that have "nondeterminstic reads"
            // which come from the #[birds_eye] let statements.
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
                        _ => true,
                    };

            if nondeterministic_read {
                let ty = shardable_type_to_type(field.type_span, &field.stype);
                let name = nondeterministic_read_spec_out_name(field);
                out_args.push((quote! { #name }, quote! { crate::modes::Spec<#ty> }));
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
                            &mut in_args,
                            &mut out_args,
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
                        ctxt.ensures.push(mk_eq(&lhs, &e));
                    }
                }
                ShardableType::Multiset(_)
                | ShardableType::Map(_, _)
                | ShardableType::StorageOptional(_)
                | ShardableType::Optional(_) => {
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
                            &mut in_args,
                            &mut out_args,
                            &mut inst_eq_enss,
                            &mut inst_eq_reqs,
                            &p.name,
                            &p.ty,
                            p.inout_type,
                            !field.stype.is_storage(),
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
        quote! {
            ::builtin::requires([
                #(#reqs),*
            ]);
        }
    } else {
        TokenStream::new()
    };

    // Output types are a bit tricky
    // because of the lack of named output params.

    let (out_args_ret, ens_stream) = if out_args.len() == 0 {
        let ens_stream = if enss.len() > 0 {
            quote! {
                ::builtin::ensures([
                    #(#enss),*
                ]);
            }
        } else {
            TokenStream::new()
        };

        (TokenStream::new(), ens_stream)
    } else if out_args.len() == 1 {
        let arg_name = &out_args[0].0;
        let arg_ty = &out_args[0].1;

        let ens_stream = if enss.len() > 0 {
            quote! {
                ::builtin::ensures(
                    |#arg_name: #arg_ty| [
                        #(#enss),*
                    ]
                );
            }
        } else {
            TokenStream::new()
        };

        (quote! { -> #arg_ty }, ens_stream)
    } else {
        // If we have more than one output param (we aren't counting the &mut inputs here,
        // only stuff in the 'return type' position) then we have to package it all into
        // a tuple and unpack it in the 'ensures' clause.

        let arg_tys: Vec<TokenStream> = out_args.iter().map(|oa| oa.1.clone()).collect();
        let arg_names: Vec<TokenStream> = out_args.iter().map(|oa| oa.0.clone()).collect();
        let tup_typ = quote! { (#(#arg_tys),*) };
        let tup_names = quote! { (#(#arg_names),*) };

        let ens_stream = if enss.len() > 0 {
            quote! {
                ::builtin::ensures(
                    |tmp_tuple: #tup_typ| [{
                        let #tup_names = tmp_tuple;
                        #((#enss))&&*
                    }]
                );
            }
        } else {
            TokenStream::new()
        };

        (quote! { -> #tup_typ }, ens_stream)
    };

    let return_value_mode = if out_args.len() == 0 {
        TokenStream::new()
    } else {
        quote! { #[verifier(returns(proof))] }
    };

    // Tie it all together

    let extra_deps = get_extra_deps(bundle, &tr, safety_condition_lemmas);

    let gen = if use_explicit_lifetime {
        quote! { <'a> }
    } else {
        TokenStream::new()
    };

    return Ok(quote! {
        #[proof]
        #return_value_mode
        #[verifier(external_body)]
        pub fn #exch_name#gen(#(#in_args),*) #out_args_ret {
            #req_stream
            #ens_stream
            #extra_deps
            unimplemented!();
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
        ShardableType::Optional(_) => None,
        ShardableType::Map(_, _) => None,
        ShardableType::StorageOptional(ty) => Some(Type::Verbatim(quote! {
            crate::pervasive::option::Option<#ty>
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
        ShardableType::StorageOptional(_) => {
            requires.push(mk_eq(&param_value, &init_value));
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
        ShardableType::Multiset(_) => {
            let ty = field_token_type(&sm, field);
            Some(Type::Verbatim(quote! {
                crate::pervasive::multiset::Multiset<#ty>
            }))
        }
        ShardableType::Optional(_) => {
            let ty = field_token_type(&sm, field);
            Some(Type::Verbatim(quote! {
                crate::pervasive::option::Option<#ty>
            }))
        }
        ShardableType::Map(key, _val) => {
            let ty = field_token_type(&sm, field);
            Some(Type::Verbatim(quote! {
                crate::pervasive::option::Map<#key, #ty>
            }))
        }
        ShardableType::StorageOptional(_) => None, // no output token
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
            inst_eq_enss.push(Expr::Verbatim(quote! {
                ::builtin::equal(#param_value.instance, #inst_value)
            }));
            let field_name = field_token_field_name(field);
            ensures.push(Expr::Verbatim(quote! {
                ::builtin::equal(#param_value.#field_name, #init_value)
            }));
        }
        ShardableType::Optional(_) => {
            let fn_name = option_relation_post_condition_qualified_name(sm, field);
            ensures.push(Expr::Verbatim(quote! {
                #fn_name(#param_value, #init_value, #inst_value)
            }));
        }
        ShardableType::Map(_, _) => {
            let fn_name = map_relation_post_condition_qualified_name(sm, field);
            ensures.push(Expr::Verbatim(quote! {
                #fn_name(#param_value, #init_value, #inst_value)
            }));
        }
        ShardableType::Multiset(_) => {
            let fn_name = multiset_relation_post_condition_qualified_name(sm, field);
            ensures.push(Expr::Verbatim(quote! {
                #fn_name(#param_value, #init_value, #inst_value)
            }));
        }
        _ => {
            panic!("this should implement each case enabled by get_init_param_output_type");
        }
    }
}

/// Add some helper functions that are useful to call from other
/// generated conditions (e.g., see `add_initialization_output_conditions`)
fn collection_relation_fns_stream(sm: &SM, field: &Field) -> TokenStream {
    match &field.stype {
        ShardableType::Optional(ty) => {
            let fn_name = option_relation_post_condition_name(field);
            let token_ty = field_token_type(sm, field);
            let inst_ty = inst_type(sm);
            let option_token_ty = Type::Verbatim(quote! {
                crate::pervasive::option::Option<#token_ty>
            });
            let option_normal_ty = Type::Verbatim(quote! {
                crate::pervasive::option::Option<#ty>
            });

            // Predicate to check the option values agree:
            //
            // opt            token_opt
            // None           None
            // Some(x)        Some(Token { instance: instance, value: x })

            quote! {
                #[spec]
                #[verifier(publish)]
                pub fn #fn_name(token_opt: #option_token_ty, opt: #option_normal_ty, instance: #inst_ty) -> bool {
                    match token_opt {
                        crate::pervasive::option::Option::None => {
                            opt.is_None()
                        }
                        crate::pervasive::option::Option::Some(token) => {
                            ::builtin::equal(token.instance, instance)
                            && opt.is_Some()
                            && ::builtin::equal(token.value, opt.get_Some_0())
                        }
                    }
                }
            }
        }
        ShardableType::Map(key, val) => {
            let fn_name = map_relation_post_condition_name(field);
            let token_ty = field_token_type(sm, field);
            let inst_ty = inst_type(sm);
            let map_token_ty = Type::Verbatim(quote! {
                crate::pervasive::map::Map<#key, #token_ty>
            });
            let map_normal_ty = Type::Verbatim(quote! {
                crate::pervasive::map::Map<#key, #val>
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

            quote! {
                #[spec]
                #[verifier(publish)]
                pub fn #fn_name(token_map: #map_token_ty, m: #map_normal_ty, instance: #inst_ty) -> bool {
                    ::builtin::equal(token_map.dom(), m.dom())
                    && ::builtin::forall(|key: #key|
                        ::builtin::imply(
                            token_map.dom().contains(key),
                            ::builin::equal(token_map.index(key).instance, instance)
                                && ::builin::equal(token_map.index(key).key, key)
                                && ::builin::equal(token_map.index(key).value, m.index(key))
                        )
                    )
                }
            }
        }
        ShardableType::Multiset(ty) => {
            let fn_name = multiset_relation_post_condition_name(field);
            let constructor_name = field_token_type_turbofish(sm, field);
            let field_name = field_token_field_name(field);
            let inst_ty = inst_type(sm);
            let token_ty = field_token_type(sm, field);
            let multiset_token_ty = Type::Verbatim(quote! {
                crate::pervasive::multiset::Multiset<#token_ty>
            });
            let multiset_normal_ty = Type::Verbatim(quote! {
                crate::pervasive::multiset::Multiset<#ty>
            });

            // Predicate to check the multiset values agree:
            //
            // m:
            // multiset{v1, v2, ...}
            //
            // tokens:
            // multiset{
            //    Token { instance: instance, value: v1 }]
            //    Token { instance: instance, value: v2 }]
            // }

            quote! {
                #[spec]
                #[verifier(publish)]
                pub fn #fn_name(tokens: #multiset_token_ty, m: #multiset_normal_ty, instance: #inst_ty) -> bool {
                    ::builtin::forall(|x: #ty|
                        tokens.count(
                            #constructor_name {
                                instance: instance,
                                #field_name: x,
                            }) == m.count(x)
                    )
                    && ::builtin::forall(|t: #token_ty|
                        ::builtin::imply(
                            tokens.count(t) > 0,
                            ::builtin::equal(t.instance, instance)
                        )
                    )
                }
            }
        }
        _ => TokenStream::new(),
    }
}

fn add_token_param_in_out(
    ctxt: &Ctxt,
    in_args: &mut Vec<TokenStream>,
    out_args: &mut Vec<(TokenStream, TokenStream)>,
    inst_eq_enss: &mut Vec<Expr>,
    inst_eq_reqs: &mut Vec<Expr>,

    arg_name: &Ident,
    arg_type: &Type,
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
            in_args.push(quote! { #[proof] #arg_name: #arg_type });
            (true, false)
        }
        InoutType::Out => {
            assert!(!use_explicit_lifetime);
            out_args.push((quote! {#arg_name}, quote! {#arg_type}));
            (false, true)
        }
        InoutType::InOut => {
            assert!(!use_explicit_lifetime);
            in_args.push(quote! { #[proof] #arg_name: &mut #arg_type });
            (true, true)
        }
        InoutType::BorrowIn => {
            if use_explicit_lifetime {
                in_args.push(quote! { #[proof] #arg_name: &'a #arg_type });
            } else {
                in_args.push(quote! { #[proof] #arg_name: &#arg_type });
            }
            (true, false)
        }
        InoutType::BorrowOut => {
            assert!(use_explicit_lifetime);
            out_args.push((quote! {#arg_name}, quote! {&'a #arg_type}));
            (false, true)
        }
    };

    // Add a condition like `token.instance == instance`

    if apply_instance_condition {
        let inst = get_inst_value(&ctxt);
        if is_output {
            let lhs = Expr::Verbatim(quote! { #arg_name.instance });
            inst_eq_enss.push(Expr::Verbatim(quote! {
                ::builtin::equal(#lhs, #inst)
            }));
        }
        if is_input {
            let lhs = if is_output {
                Expr::Verbatim(quote! { ::builtin::old(#arg_name).instance })
            } else {
                Expr::Verbatim(quote! { #arg_name.instance })
            };
            inst_eq_reqs.push(Expr::Verbatim(quote! {
                ::builtin::equal(#lhs, #inst)
            }));
        }
    }
}

fn mk_and(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Verbatim(quote! {
        ((#lhs) && (#rhs))
    })
}


fn mk_eq(lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::Verbatim(quote! {
        ::builtin::equal(#lhs, #rhs)
    })
}

fn get_extra_deps(
    bundle: &SMBundle,
    trans: &Transition,
    safety_condition_lemmas: &HashMap<String, Ident>,
) -> TokenStream {
    let ty = get_self_ty_turbofish(&bundle.sm);
    let deps: Vec<TokenStream> =
        get_all_lemmas_for_transition(bundle, trans, safety_condition_lemmas)
            .iter()
            .map(|ident| {
                quote! {
                    ::builtin::extra_dependency(#ty::#ident);
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

    if trans.kind != TransitionKind::Readonly {
        let l = get_main_lemma_for_transition_or_panic(&bundle.extras.lemmas, &trans.name);
        v.push(l.func.sig.ident.clone());
    }

    match safety_condition_lemmas.get(&trans.name.to_string()) {
        Some(name) => v.push(name.clone()),
        None => {}
    }

    v
}

fn get_main_lemma_for_transition_or_panic<'a>(
    lemmas: &'a Vec<Lemma>,
    trans_name: &Ident,
) -> &'a Lemma {
    for l in lemmas {
        if l.purpose.transition.to_string() == trans_name.to_string() {
            return l;
        }
    }

    panic!("could not find lemma for: {}", trans_name.to_string());
}

// Find things that updated

fn determine_outputs(ctxt: &mut Ctxt, ts: &TransitionStmt) -> syn::parse::Result<()> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            for child in v.iter() {
                determine_outputs(ctxt, child)?;
            }
            Ok(())
        }
        TransitionStmt::Let(_span, _id, _lk, _init_e, child) => {
            determine_outputs(ctxt, child)?;
            Ok(())
        }
        TransitionStmt::If(_span, _cond_e, e1, e2) => {
            determine_outputs(ctxt, e1)?;
            determine_outputs(ctxt, e2)?;
            Ok(())
        }
        TransitionStmt::Require(_span, _req_e) => Ok(()),
        TransitionStmt::Assert(_span, _assert_e) => Ok(()),
        TransitionStmt::Initialize(_span, id, _e) => {
            ctxt.fields_written.insert(id.to_string());
            Ok(())
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
        TransitionStmt::Special(_span, _id, _op) => Ok(()),
        TransitionStmt::PostCondition(..) => {
            panic!("PostCondition statement shouldn't exist yet");
        }
    }
}

/// The function has several purposes:
///
///   1. Replace `self.foo` subexpression with the corresponding value from the
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
) -> syn::parse::Result<()> {
    let new_ts = match ts {
        TransitionStmt::Block(_span, v) => {
            for child in v.iter_mut() {
                translate_transition(ctxt, child, errors)?;
            }
            return Ok(());
        }
        TransitionStmt::Let(_span, _id, lk, e, child) => {
            let birds_eye = *lk == LetKind::BirdsEye;
            let init_e = translate_expr(ctxt, e, birds_eye, errors);
            *e = init_e;
            translate_transition(ctxt, child, errors)?;
            return Ok(());
        }
        TransitionStmt::If(_span, cond, e1, e2) => {
            let cond_e = translate_expr(ctxt, cond, false, errors);
            *cond = cond_e;
            translate_transition(ctxt, e1, errors)?;
            translate_transition(ctxt, e2, errors)?;
            return Ok(());
        }
        TransitionStmt::Require(_span, e) => {
            let req_e = translate_expr(ctxt, e, false, errors);
            *e = req_e;
            return Ok(());
        }
        TransitionStmt::Assert(_span, e) => {
            let assert_e = translate_expr(ctxt, e, false, errors);
            *e = assert_e;
            return Ok(());
        }

        TransitionStmt::Initialize(_span, _id, e) | TransitionStmt::Update(_span, _id, e) => {
            let update_e = translate_expr(ctxt, e, false, errors);
            *e = update_e;
            return Ok(());
        }

        TransitionStmt::Special(span, id, SpecialOp::HaveSome(e))
        | TransitionStmt::Special(span, id, SpecialOp::HaveElement(e)) => {
            let e = translate_expr(ctxt, e, false, errors);

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = field_token_type(&ctxt.sm, &field);
            let field_name = field_token_field_name(&field);

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::BorrowIn,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::Require(*span, mk_eq(&Expr::Verbatim(quote! {#ident.#field_name}), &e))
        }

        TransitionStmt::Special(span, id, SpecialOp::AddSome(e))
        | TransitionStmt::Special(span, id, SpecialOp::AddElement(e)) => {
            let e = translate_expr(ctxt, e, false, errors);

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = field_token_type(&ctxt.sm, &field);
            let field_name = field_token_field_name(&field);

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::Out,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::PostCondition(
                *span,
                mk_eq(&Expr::Verbatim(quote! {#ident.#field_name}), &e),
            )
        }

        TransitionStmt::Special(span, id, SpecialOp::RemoveSome(e))
        | TransitionStmt::Special(span, id, SpecialOp::RemoveElement(e)) => {
            let e = translate_expr(ctxt, e, false, errors);

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = field_token_type(&ctxt.sm, &field);
            let field_name = field_token_field_name(&field);

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::In,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::Require(*span, mk_eq(&Expr::Verbatim(quote! {#ident.#field_name}), &e))
        }

        TransitionStmt::Special(span, id, SpecialOp::HaveKV(key, val)) => {
            let key = translate_expr(ctxt, key, false, errors);
            let val = translate_expr(ctxt, val, false, errors);

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = field_token_type(&ctxt.sm, &field);

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::BorrowIn,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::Require(*span,
                mk_and(
                    mk_eq(&Expr::Verbatim(quote! {#ident.key}), &key),
                    mk_eq(&Expr::Verbatim(quote! {#ident.value}), &val),
                )
            )
        }

        TransitionStmt::Special(span, id, SpecialOp::AddKV(key, val)) => {
            let key = translate_expr(ctxt, key, false, errors);
            let val = translate_expr(ctxt, val, false, errors);

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = field_token_type(&ctxt.sm, &field);

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::Out,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::PostCondition(
                *span,
                mk_and(
                    mk_eq(&Expr::Verbatim(quote! {#ident.key}), &key),
                    mk_eq(&Expr::Verbatim(quote! {#ident.value}), &val),
                )
            )
        }

        TransitionStmt::Special(span, id, SpecialOp::RemoveKV(key, val)) => {
            let key = translate_expr(ctxt, key, false, errors);
            let val = translate_expr(ctxt, val, false, errors);

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = field_token_type(&ctxt.sm, &field);

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::In,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::Require(*span,
                mk_and(
                    mk_eq(&Expr::Verbatim(quote! {#ident.key}), &key),
                    mk_eq(&Expr::Verbatim(quote! {#ident.value}), &val),
                )
            )
        }


        TransitionStmt::Special(span, id, SpecialOp::GuardSome(e)) => {
            let e = translate_expr(ctxt, e, false, errors);

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = stored_object_type(&field);

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::BorrowOut,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::PostCondition(*span, mk_eq(&Expr::Verbatim(quote! {*#ident}), &e))
        }

        TransitionStmt::Special(span, id, SpecialOp::DepositSome(e)) => {
            let e = translate_expr(ctxt, e, false, errors);

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = stored_object_type(&field);

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::In,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::Require(*span, mk_eq(&Expr::Verbatim(quote! {#ident}), &e))
        }

        TransitionStmt::Special(span, id, SpecialOp::WithdrawSome(e)) => {
            let e = translate_expr(ctxt, e, false, errors);

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = stored_object_type(&field);

            ctxt.params.get_mut(&field.name.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::Out,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::PostCondition(*span, mk_eq(&Expr::Verbatim(quote! {#ident}), &e))
        }

        TransitionStmt::PostCondition(..) => {
            return Ok(());
        }
    };

    *ts = new_ts;

    Ok(())
}

/// Perform translation on the Rust AST Exprs.
/// We need to find expressions like `self.foo` that refer to individual fields and replace
/// them with some expression in terms of the parameters of the exchange function.
/// There are a few ways this can happen, depending on the context:
///
///  * Reading a 'Constant' field. In this case, we replace it with the constant value
///    from the instance object, e.g., `instance.foo()`.
///
///  * Reading a 'Variable' field. Replace it with the value from the input token
///    e.g., `token_foo.value` or `old(token_foo).value`.
///
///  * A nondeterministic read. In this case, we replace it with the value of one of the
///    _out_ parameters. Previous well-formedness checks (`check_birds_eye`) should ensure
///    that this will only happen in contexts that will ultimately appears in the
///    post-conditions, never pre-conditions.

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
                            *node = get_old_field_value(ctxt, &field);
                        } else {
                            *node = get_nondeterministic_out_value(ctxt, &field);
                        }
                    }
                    ShardableType::Constant(_ty) => {
                        // Always handle constants as normal, since we always have access to them.
                        *node = get_const_field_value(ctxt, &field);
                    }
                    _ => {
                        *node = get_nondeterministic_out_value(ctxt, &field);
                    }
                }
            } else {
                match &field.stype {
                    ShardableType::Variable(_ty) => {
                        *node = get_old_field_value(ctxt, &field);
                    }
                    ShardableType::Constant(_ty) => {
                        *node = get_const_field_value(ctxt, &field);
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

fn get_const_field_value(ctxt: &Ctxt, field: &Field) -> Expr {
    let inst = get_inst_value(ctxt);
    let field_name = field_token_field_name(&field);
    Expr::Verbatim(quote! { #inst.#field_name() })
}

fn get_nondeterministic_out_value(_ctxt: &Ctxt, field: &Field) -> Expr {
    let name = nondeterministic_read_spec_out_name(field);
    Expr::Verbatim(quote! { #name.value() })
}

fn get_old_field_value(ctxt: &Ctxt, field: &Field) -> Expr {
    let arg = transition_arg_name(&field);
    let field_name = field_token_field_name(&field);
    if ctxt.fields_written.contains(&field.name.to_string()) {
        Expr::Verbatim(quote! { ::builtin::old(#arg).#field_name })
    } else {
        Expr::Verbatim(quote! { #arg.#field_name })
    }
}

fn get_new_field_value(field: &Field) -> Expr {
    let arg = transition_arg_name(&field);
    let field = field_token_field_name(&field);
    Expr::Verbatim(quote! { #arg.#field })
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
    Let(Ident, Expr),
}

fn exchange_collect(
    ctxt: &mut Ctxt,
    ts: &TransitionStmt,
    prequel: Vec<PrequelElement>,
) -> syn::parse::Result<Vec<PrequelElement>> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            let mut p = prequel;
            for child in v.iter() {
                let p1 = exchange_collect(ctxt, child, p)?;
                p = p1;
            }
            Ok(p)
        }
        TransitionStmt::Let(_span, id, _lk, init_e, child) => {
            let mut p = prequel.clone();
            p.push(PrequelElement::Let(id.clone(), init_e.clone()));
            let _ = exchange_collect(ctxt, child, p);

            let mut prequel = prequel;
            if let Some(e) = asserts_to_single_predicate(ts) {
                prequel.push(PrequelElement::AssertCondition(Expr::Verbatim(e)));
            }
            Ok(prequel)
        }
        TransitionStmt::If(_span, cond_e, e1, e2) => {
            let cond = PrequelElement::Condition(cond_e.clone());
            let not_cond = PrequelElement::Condition(bool_not_expr(cond_e));

            let mut p1 = prequel.clone();
            p1.push(cond);
            let _ = exchange_collect(ctxt, e1, p1)?;

            let mut p2 = prequel.clone();
            p2.push(not_cond);
            let _ = exchange_collect(ctxt, e2, p2)?;

            let mut prequel = prequel;
            if let Some(e) = asserts_to_single_predicate(ts) {
                prequel.push(PrequelElement::AssertCondition(Expr::Verbatim(e)));
            }
            Ok(prequel)
        }
        TransitionStmt::Require(_span, req_e) => {
            ctxt.requires.push(with_prequel(&prequel, true, req_e.clone()));
            Ok(prequel)
        }
        TransitionStmt::Assert(_span, assert_e) => {
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
        TransitionStmt::Initialize(..) => Ok(prequel),

        TransitionStmt::Special(..) => {
            panic!("should have been removed in preprocessing");
        }
    }
}

fn bool_not_expr(e: &Expr) -> Expr {
    Expr::Verbatim(quote! { !(#e) })
}

fn with_prequel(pre: &Vec<PrequelElement>, include_assert_conditions: bool, e: Expr) -> Expr {
    let mut e = e;
    for p in pre.iter().rev() {
        match p {
            PrequelElement::Let(id, init_e) => {
                e = Expr::Verbatim(quote! { { let #id = #init_e; #e } });
            }
            PrequelElement::Condition(cond_e) => {
                e = Expr::Verbatim(quote! { ::builtin::imply(#cond_e, #e) });
            }
            PrequelElement::AssertCondition(cond_e) => {
                if include_assert_conditions {
                    e = Expr::Verbatim(quote! { ::builtin::imply(#cond_e, #e) });
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
        TransitionStmt::Let(span, id, lk, init_e, box child) => {
            match prune_irrelevant_ops_rec(ctxt, child) {
                None => None,
                Some(new_child) => {
                    Some(TransitionStmt::Let(span, id, lk, init_e, Box::new(new_child)))
                }
            }
        }
        TransitionStmt::If(span, cond_e, box thn, box els) => {
            let new_thn = prune_irrelevant_ops_rec(ctxt, thn);
            let new_els = prune_irrelevant_ops_rec(ctxt, els);
            if new_thn.is_none() && new_els.is_none() {
                None
            } else {
                let new_thn = new_thn.unwrap_or(TransitionStmt::Block(span, vec![]));
                let new_els = new_els.unwrap_or(TransitionStmt::Block(span, vec![]));
                Some(TransitionStmt::If(span, cond_e, Box::new(new_thn), Box::new(new_els)))
            }
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
        TransitionStmt::Assert(span, assert_e) => Some(TransitionStmt::Assert(span, assert_e)),
        TransitionStmt::PostCondition(span, post_e) => {
            Some(TransitionStmt::PostCondition(span, post_e))
        }
        TransitionStmt::Special(span, id, op) => Some(TransitionStmt::Special(span, id, op)),
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
        TransitionStmt::Let(_span, id, _lk, e, child) => {
            let o = get_post_value_for_variable(ctxt, child, field);
            match o {
                None => None,
                Some(child_e) => Some(Expr::Verbatim(quote! {
                    { let #id = #e; #child_e }
                })),
            }
        }
        TransitionStmt::If(_span, cond_e, e1, e2) => {
            let o1 = get_post_value_for_variable(ctxt, e1, field);
            let o2 = get_post_value_for_variable(ctxt, e2, field);
            if o1.is_none() && o2.is_none() {
                None
            } else {
                let e1 = match o1 {
                    None => get_old_field_value(ctxt, &field),
                    Some(e) => e,
                };
                let e2 = match o2 {
                    None => get_old_field_value(ctxt, &field),
                    Some(e) => e,
                };
                Some(Expr::Verbatim(quote! { if #cond_e { #e1 } else { #e2 } }))
            }
        }
        TransitionStmt::Initialize(_span, id, e) | TransitionStmt::Update(_span, id, e) => {
            if *id.to_string() == *field.name.to_string() { Some(e.clone()) } else { None }
        }
        TransitionStmt::Require(_, _)
        | TransitionStmt::Assert(_, _)
        | TransitionStmt::Special(..)
        | TransitionStmt::PostCondition(..) => None,
    }
}
