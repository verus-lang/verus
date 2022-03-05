//! Output all the generated code specific to concurrent state machines.
//! We print declarations for:
//!
//!  * The Instance type
//!  * All the Token types for shardable fields
//!  * #[proof] methods for each transition (including init and readonly transitions)

use crate::ast::{
    Field, Lemma, ShardableType, SpecialOp, Transition, TransitionKind, TransitionStmt, SM, LetKind,
};
use crate::checks::{check_ordering_remove_have_add, check_unsupported_updates_in_conditionals};
use crate::parse_token_stream::SMBundle;
use crate::safety_conditions::{has_any_assert};
use crate::to_relation::asserts_to_single_predicate;
use crate::to_token_stream::{
    get_self_ty, get_self_ty_double_colon, impl_decl_stream, name_with_type_args,
    name_with_type_args_double_colon, shardable_type_to_type,
};
use crate::util::combine_errors_or_ok;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;
use std::collections::HashSet;
use syn::parse::Error;
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;
use syn::{Expr, ExprField, ExprPath, Ident, Member, Type};

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
    let name = sm_name.to_string() + "_" + &field.ident.to_string();
    Ident::new(&name, field.ident.span())
}

fn field_token_type(sm: &SM, field: &Field) -> Type {
    name_with_type_args(&field_token_type_name(&sm.name, field), sm)
}

fn field_token_type_double_colon(sm: &SM, field: &Field) -> Type {
    name_with_type_args_double_colon(&field_token_type_name(&sm.name, field), sm)
}

fn field_token_field_name(field: &Field) -> Ident {
    // just call it value rather than repeat the field name
    // else, the user will be writing foo.foo everywhere
    Ident::new("value", field.ident.span())
}

fn nondeterministic_read_spec_out_name(field: &Field) -> Ident {
    let name = "original_field_".to_string() + &field.ident.to_string();
    Ident::new(&name, field.ident.span())
}

// The type that goes in the created struct, e.g.,
//     struct Token {
//         instance: X_Instance,
//         value: [[THIS_TYPE]],
//     }
fn field_token_field_type(field: &Field) -> Type {
    match &field.stype {
        ShardableType::Variable(ty) => ty.clone(),
        ShardableType::Constant(ty) => ty.clone(),
        ShardableType::NotTokenized(_ty) => {
            panic!("no token field for NotTokenized");
        }
        ShardableType::Multiset(ty) => ty.clone(),
        ShardableType::Optional(ty) => ty.clone(),
        ShardableType::StorageOptional(_ty) => {
            panic!("no token field for StorageOptional");
        }
    }
}

fn stored_object_type(field: &Field) -> Type {
    match &field.stype {
        ShardableType::StorageOptional(ty) => ty.clone(),
        ShardableType::Variable(_)
        | ShardableType::Constant(_)
        | ShardableType::NotTokenized(_)
        | ShardableType::Multiset(_)
        | ShardableType::Optional(_) => {
            panic!("stored_object_type");
        }
    }
}

fn exchange_name(tr: &Transition) -> Ident {
    tr.name.clone()
}

fn transition_arg_name(field: &Field) -> Ident {
    let name = "token_".to_string() + &field.ident.to_string();
    Ident::new(&name, field.ident.span())
}

fn multiset_relation_post_condition_name(field: &Field) -> Ident {
    Ident::new("multiset_agree", field.ident.span())
}

fn multiset_relation_post_condition_qualified_name(sm: &SM, field: &Field) -> Type {
    let ty = field_token_type_double_colon(sm, field);
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
/// machine state. (See `formalism.md`.) Since that formalism is not implemented mechanically
/// in Verus, we instead make the state itself a field. This is kind of meaningless, but it
/// serves as a placeholder and does result in the necessary dependency edge between this
/// struct and the type struct. The fields are private, so they shouldn't matter to the user.
fn instance_struct_stream(sm: &SM) -> TokenStream {
    let insttype = inst_type_name(&sm.name);
    let self_ty = get_self_ty(sm);
    let gen = &sm.generics;
    return quote! {
        #[proof]
        #[allow(non_camel_case_types)]
        #[verifier(unforgeable)]
        pub struct #insttype #gen {
            #[spec] state: #self_ty,
            #[spec] location: ::builtin::int,
        }
    };
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

/// Create the struct for a Token that derives from a
/// sharding(variable) field.
fn token_struct_stream(sm: &SM, field: &Field) -> TokenStream {
    let tokenname = field_token_type_name(&sm.name, field);
    let fieldname = field_token_field_name(field);
    let fieldtype = field_token_field_type(field);
    let insttype = inst_type(sm);
    let gen = &sm.generics;

    let impldecl = impl_decl_stream(&field_token_type(sm, field), &sm.generics);
    let impl_token_stream = collection_relation_fns_stream(sm, field);

    return quote! {
        #[proof]
        #[verifier(unforgeable)]
        #[allow(non_camel_case_types)]
        pub struct #tokenname#gen {
            #[spec] pub instance: #insttype,
            #[spec] pub #fieldname: #fieldtype,
        }

        #impldecl {
            #impl_token_stream
        }
    };
}

/// Create the struct for a Token that derives from a
/// sharding(multiset) field.
fn token_struct_stream_multiset(sm: &SM, field: &Field) -> TokenStream {
    token_struct_stream(sm, field)
}

/// Create the struct for a Token that derives from a
/// sharding(optional) field.
fn token_struct_stream_optional(sm: &SM, field: &Field) -> TokenStream {
    token_struct_stream(sm, field)
}

/// For a given sharding(constant) field, add that constant
/// as a #[spec] fn on the Instance type. (The field is constant
/// for the entire instance.)
///
/// TODO we could make these fields on the Instance type instead
/// (this is safe as long as the Instance type is an unforgeable proof type)
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
) -> syn::parse::Result<()> {
    let mut inst_impl_token_stream = TokenStream::new();

    token_stream.extend(instance_struct_stream(&bundle.sm));
    inst_impl_token_stream.extend(trusted_clone());

    for field in &bundle.sm.fields {
        match field.stype {
            ShardableType::Constant(_) => {
                inst_impl_token_stream.extend(const_fn_stream(field));
            }
            ShardableType::Variable(_) => {
                token_stream.extend(token_struct_stream(&bundle.sm, field));
            }
            ShardableType::NotTokenized(_) => {
                // don't need to add a struct in this case
            }
            ShardableType::Multiset(_) => {
                token_stream.extend(token_struct_stream_multiset(&bundle.sm, field));
            }
            ShardableType::Optional(_) => {
                token_stream.extend(token_struct_stream_optional(&bundle.sm, field));
            }
            ShardableType::StorageOptional(_) => {
                // storage types don't have tokens; the 'token type' is just the
                // the type of the field
            }
        }
    }

    let mut errors = Vec::new();
    for tr in &bundle.sm.transitions {
        match exchange_stream(bundle, tr) {
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
    pub fn get_field_by_ident(&self, span: Span, ident: &Ident) -> syn::parse::Result<Field> {
        match self.ident_to_field.get(&ident.to_string()) {
            Some(f) => Ok(f.clone()),
            None => Err(Error::new(
                span,
                "in a concurrent transition, any field access but be a state field",
            )),
        }
    }

    pub fn get_field_or_panic(&self, ident: &Ident) -> Field {
        match self.ident_to_field.get(&ident.to_string()) {
            Some(f) => f.clone(),
            None => panic!("should have already checked field updates are valid"),
        }
    }

    pub fn mark_field_as_read(&mut self, field: &Field) {
        self.fields_read.insert(field.ident.to_string());
    }

    pub fn mark_field_as_nondeterministic_read(&mut self, field: &Field) {
        self.fields_read_birds_eye.insert(field.ident.to_string());
    }

    pub fn get_numbered_token_ident(&mut self, base_id: &Ident) -> Ident {
        let i = self.fresh_num_counter;
        self.fresh_num_counter += 1;
        Ident::new(&format!("token_{}_{}", i, base_id.to_string()), base_id.span())
    }

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

pub fn exchange_stream(bundle: &SMBundle, tr: &Transition) -> syn::parse::Result<TokenStream> {
    let sm = &bundle.sm;

    let is_init = tr.kind == TransitionKind::Init;

    let mut ident_to_field = HashMap::new();
    let mut init_params = HashMap::new();
    for field in &sm.fields {
        ident_to_field.insert(field.ident.to_string(), field.clone());

        if !is_init {
            match &field.stype {
                ShardableType::Multiset(_)
                | ShardableType::Optional(_)
                | ShardableType::StorageOptional(_) => {
                    init_params.insert(field.ident.to_string(), Vec::new());
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

    // Potentially remove stuff that won't be useful
    tr.body = prune_irrelevant_ops(&ctxt, tr.body);

    // determine output tokens based on 'update' statements
    determine_outputs(&mut ctxt, &tr.body)?;

    // translate the expressions in the TransitionStmt so that
    // where they previously referred to fields like `self.foo`,
    // they now refer to the field that comes from an input.
    // (in the process, we also determine inputs).
    walk_translate_expressions(&mut ctxt, &mut tr.body, false)?;
    walk_translate_expressions(&mut ctxt, &mut tr.body, true)?;

    // translate the (new) TransitionStmt into an expressions that
    // can be used as pre-conditions and post-conditions
    let _ = exchange_collect(&mut ctxt, &tr.body, Vec::new())?;

    let mut in_args: Vec<TokenStream> = Vec::new();
    let mut out_args: Vec<(TokenStream, TokenStream)> = Vec::new();

    // For our purposes here, a 'readonly' is just a special case of a normal transition.
    // The 'init' transitions are the interesting case.
    // For the most part, there are two key differences:
    //
    //   * An 'init' returns an arbitrary new Instance object, whereas a normal transition
    //     takes an Instance as input.
    //   * An 'init' will always return tokens for every field, and take no tokens as input.
    //     A normal transition takes only those as input that are necessary.

    if ctxt.is_init {
        let itn = inst_type(sm);
        out_args.push((quote! { instance }, quote! { #itn }));
    } else {
        in_args.push(quote! { #[proof] &self });
    }

    // Take the transition parameters (the normal parameters defined in the transition)
    // and make them input parameters (spec-mode) to the corresponding exchange method.
    for param in &tr.params {
        let id = &param.ident;
        let ty = &param.ty;
        in_args.push(quote! { #[spec] #id: #ty });
    }

    // We need some pre/post conditions that the input/output
    // tokens are all of the correct Instance.
    let mut inst_eq_reqs = Vec::new();
    let mut inst_eq_enss = Vec::new();

    let use_explicit_lifetime = ctxt.get_explicit_lifetime();

    for field in &sm.fields {
        if ctxt.is_init {
            match &field.stype {
                ShardableType::NotTokenized(..) => {
                    continue;
                }
                _ => {}
            }

            assert!(!use_explicit_lifetime);
            assert!(ctxt.fields_written.contains(&field.ident.to_string()));
            assert!(!ctxt.fields_read.contains(&field.ident.to_string()));
            assert!(!ctxt.fields_read_birds_eye.contains(&field.ident.to_string()));

            match &field.stype {
                ShardableType::Constant(_) => {
                    let e_opt = get_post_value_for_variable(&ctxt, &tr.body, field);
                    let e = e_opt.expect("get_post_value_for_variable");
                    let lhs = get_const_field_value(&ctxt, field);
                    ctxt.ensures.push(mk_eq(&lhs, &e));
                }
                _ => {}
            }

            if let Some(init_input_token_type) = get_init_param_input_type(sm, &field) {
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
                    &mut ctxt.ensures,
                    e,
                    Expr::Verbatim(quote! { #arg_name }),
                );
            } else if let Some(init_output_token_type) = get_init_param_output_type(sm, &field) {
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
            let nondeterministic_read =
                ctxt.fields_read_birds_eye.contains(&field.ident.to_string());

            if nondeterministic_read {
                // It is possible to read a value non-deterministically without it coming
                // from an input token.
                // In that case, we need to make the field value an _output_ argument.
                let ty = shardable_type_to_type(&field.stype);
                let name = nondeterministic_read_spec_out_name(field);
                out_args.push((quote! { #name }, quote! { crate::modes::Spec<#ty> }));
            }

            match field.stype {
                ShardableType::Constant(_) => {
                    // We can't update a constant field in a non-init transition.
                    // This should have been checked already.
                    assert!(!ctxt.fields_written.contains(&field.ident.to_string()));
                }
                ShardableType::NotTokenized(_) => {
                    // Do nothing.
                    // This field can only be accessed via nondeterministic
                    // read which was handled above.
                    // Nothing to do for writes (they simply aren't reflected in output tokens).
                }
                ShardableType::Variable(_) => {
                    let is_written = ctxt.fields_written.contains(&field.ident.to_string());
                    let is_read = ctxt.fields_read.contains(&field.ident.to_string());

                    if is_written || is_read {
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
                        // TODO, maybe instead of doing this here, we could translate the
                        // `Update` statements into `PostCondition` statements like we
                        // do for other kinds of tokens. Then we wouldn't have to have this here.

                        let e_opt = get_post_value_for_variable(&ctxt, &tr.body, field);
                        let e = e_opt.expect("get_post_value_for_variable");
                        let lhs = get_new_field_value(field);
                        ctxt.ensures.push(mk_eq(&lhs, &e));
                    }
                }
                ShardableType::Multiset(_)
                | ShardableType::StorageOptional(_)
                | ShardableType::Optional(_) => {
                    assert!(!ctxt.fields_written.contains(&field.ident.to_string()));
                    assert!(
                        nondeterministic_read
                            || !ctxt.fields_read.contains(&field.ident.to_string())
                    );

                    for p in &ctxt.params[&field.ident.to_string()] {
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

                    // Any pre-conditions or post-conditions we need should have been
                    // placed into the TransitionStmt as a `Require` or `PostCondition`
                    // statement, so we don't need to explicitly add them here.
                }
            };
        }
    }

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

    let extra_deps = get_extra_deps(bundle, &tr);

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
        ShardableType::StorageOptional(ty) => Some(Type::Verbatim(quote! {
            crate::pervasive::option::Option<#ty>
        })),
    }
}

fn add_initialization_input_conditions(
    field: &Field,
    ensures: &mut Vec<Expr>,
    init_value: Expr,
    param_value: Expr,
) {
    match &field.stype {
        ShardableType::StorageOptional(_) => {
            ensures.push(mk_eq(&param_value, &init_value));
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
            // TODO factor this into a helper function to simplify the generated code
            let field_name = field_token_field_name(field);
            ensures.push(Expr::Verbatim(quote! {
                match #init_value {
                    crate::pervasive::option::Option::None => {
                        #param_value.is_None()
                    }
                    crate::pervasive::option::Option::Some(tmp_e) => {
                        #param_value.is_Some()
                        && ::builtin::equal(
                            #param_value.get_Some_0().instance,
                            #inst_value)
                        && ::builtin::equal(
                            #param_value.get_Some_0().#field_name,
                            tmp_e)
                    }
                }
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

fn collection_relation_fns_stream(sm: &SM, field: &Field) -> TokenStream {
    match &field.stype {
        ShardableType::Multiset(ty) => {
            let fn_name = multiset_relation_post_condition_name(field);
            let constructor_name = field_token_type_double_colon(sm, field);
            let field_name = field_token_field_name(field);
            let inst_ty = inst_type(sm);
            let token_ty = field_token_type(sm, field);
            let multiset_token_ty = Type::Verbatim(quote! {
                crate::pervasive::multiset::Multiset<#token_ty>
            });
            let multiset_normal_ty = Type::Verbatim(quote! {
                crate::pervasive::multiset::Multiset<#ty>
            });

            // TODO what should the visibility of this fn be?
            quote! {
                #[spec]
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

fn mk_eq(lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::Verbatim(quote! {
        ::builtin::equal(#lhs, #rhs)
    })
}

fn get_extra_deps(bundle: &SMBundle, trans: &Transition) -> TokenStream {
    let ty = get_self_ty_double_colon(&bundle.sm);
    let deps: Vec<TokenStream> = get_all_lemmas_for_transition(bundle, trans)
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
fn get_all_lemmas_for_transition(bundle: &SMBundle, trans: &Transition) -> Vec<Ident> {
    let mut v = Vec::new();

    if trans.kind != TransitionKind::Readonly {
        let l = get_main_lemma_for_transition_or_panic(&bundle.extras.lemmas, &trans.name);
        v.push(l.func.sig.ident.clone());
    }

    // TODO This isn't right!!! we need to check for other kinds of safety conditions!!!
    if has_any_assert(&trans.body) {
        let name = Ident::new(&(trans.name.to_string() + "_asserts"), trans.name.span());
        v.push(name);
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
            // TODO consider if this is necessary or useful
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

/// Translate expressions
///
/// The function has several purposes:
///
///   1. Identify any fields `self.foo` that are read
///   2. Make sure `self` is never used on its own other than for field accesses
///   3. Replace `self.foo` with the corresponding value from the input tokens,
///      e.g., `token_foo.foo`
///
/// Unfortunately, there are a variety of technical challenges here which have to
/// do with the fact that this pass operates on raw Rust AST, i.e., it runs BEFORE
/// type-resolution and even before macro-expansion.
///
/// In order to ensure this transformation is done correctly, we need to:
///
///   * Make sure that identifiers like `token_foo` are not shadowed in the expression
///   * Disallow macros entirely, which could interfere in a number of ways
///
/// Both these things are done in ident_visitor.rs.
///
/// This is all very awkward, and it's also hard to be sure we've really handled every
/// case. The awkwardness here suggests that it would be more principled to do this
/// in VIR, or with VIR support. Unfortunately, this plan has its own problems: namely,
/// the type signatures we generate (namely the input tokens) actually depend on the
/// results of this analysis.
///
/// There are a handful of ways that we could address this, but I think we will learn
/// a lot about the right way to structure this as we try to understand the design behind
/// more advanced sharding strategies, so I'm not committing to an overhaul right now.

// Note: we run this in two phases.
// The second phase, birds_eye, handles the birds_eye statements,
// while the first phase handles everything else.
// We have to split it in to because the first phase computes
// `ctxt.fields_read`, while the second phase needs to read it.
// TODO two-phase thing sucks; just factor the field_read computation into an earlier phase

fn walk_translate_expressions(
    ctxt: &mut Ctxt,
    ts: &mut TransitionStmt,
    birds_eye_phase: bool,
) -> syn::parse::Result<()> {
    let new_ts = match ts {
        TransitionStmt::Block(_span, v) => {
            for child in v.iter_mut() {
                walk_translate_expressions(
                    ctxt,
                    child,
                    birds_eye_phase,
                )?;
            }
            return Ok(());
        }
        TransitionStmt::Let(_span, _id, lk, e, child) => {
            let this_stmt_birds_eye = *lk == LetKind::BirdsEye;
            if birds_eye_phase == this_stmt_birds_eye {
                let init_e = translate_expr(ctxt, e, this_stmt_birds_eye)?;
                *e = init_e;
            }
            walk_translate_expressions(ctxt, child, birds_eye_phase)?;
            return Ok(());
        }
        TransitionStmt::If(_span, cond, e1, e2) => {
            if !birds_eye_phase {
                let cond_e = translate_expr(
                    ctxt,
                    cond,
                    false)?;
                *cond = cond_e;
            }
            walk_translate_expressions(ctxt, e1, birds_eye_phase)?;
            walk_translate_expressions(ctxt, e2, birds_eye_phase)?;
            return Ok(());
        }
        TransitionStmt::Require(_span, e) => {
            if !birds_eye_phase {
                let req_e = translate_expr(ctxt, e, false)?;
                *e = req_e;
            }
            return Ok(());
        }
        TransitionStmt::Assert(_span, e) => {
            if !birds_eye_phase {
                let assert_e = translate_expr(ctxt, e, false)?;
                *e = assert_e;
            }
            return Ok(());
        }

        TransitionStmt::Initialize(_span, _id, e) | TransitionStmt::Update(_span, _id, e) => {
            if !birds_eye_phase {
                let update_e = translate_expr(ctxt, e, false)?;
                *e = update_e;
            }
            return Ok(());
        }

        TransitionStmt::Special(span, id, SpecialOp::HaveSome(e))
        | TransitionStmt::Special(span, id, SpecialOp::HaveElement(e)) => {
            assert!(!birds_eye_phase);

            let e = translate_expr(ctxt, e, false)?;

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = field_token_type(&ctxt.sm, &field);
            let field_name = field_token_field_name(&field);

            ctxt.params.get_mut(&field.ident.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::BorrowIn,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::Require(*span, mk_eq(&Expr::Verbatim(quote! {#ident.#field_name}), &e))
        }

        TransitionStmt::Special(span, id, SpecialOp::AddSome(e))
        | TransitionStmt::Special(span, id, SpecialOp::AddElement(e)) => {
            assert!(!birds_eye_phase);

            let e = translate_expr(ctxt, e, false)?;

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = field_token_type(&ctxt.sm, &field);
            let field_name = field_token_field_name(&field);

            ctxt.params.get_mut(&field.ident.to_string()).expect("get_mut").push(TokenParam {
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
            assert!(!birds_eye_phase);

            let e = translate_expr(ctxt, e, false)?;

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = field_token_type(&ctxt.sm, &field);
            let field_name = field_token_field_name(&field);

            ctxt.params.get_mut(&field.ident.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::In,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::Require(*span, mk_eq(&Expr::Verbatim(quote! {#ident.#field_name}), &e))
        }

        TransitionStmt::Special(span, id, SpecialOp::GuardSome(e)) => {
            assert!(!birds_eye_phase);

            let e = translate_expr(ctxt, e, false)?;

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = stored_object_type(&field);

            ctxt.params.get_mut(&field.ident.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::BorrowOut,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::PostCondition(*span, mk_eq(&Expr::Verbatim(quote! {*#ident}), &e))
        }

        TransitionStmt::Special(span, id, SpecialOp::DepositSome(e)) => {
            assert!(!birds_eye_phase);

            let e = translate_expr(ctxt, e, false)?;

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = stored_object_type(&field);

            ctxt.params.get_mut(&field.ident.to_string()).expect("get_mut").push(TokenParam {
                inout_type: InoutType::In,
                name: ident.clone(),
                ty: ty,
            });

            TransitionStmt::Require(*span, mk_eq(&Expr::Verbatim(quote! {#ident}), &e))
        }

        TransitionStmt::Special(span, id, SpecialOp::WithdrawSome(e)) => {
            assert!(!birds_eye_phase);

            let e = translate_expr(ctxt, e, false)?;

            let ident = ctxt.get_numbered_token_ident(id);
            let field = ctxt.get_field_or_panic(id);
            let ty = stored_object_type(&field);

            ctxt.params.get_mut(&field.ident.to_string()).expect("get_mut").push(TokenParam {
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

fn translate_expr(
    ctxt: &mut Ctxt,
    expr: &Expr,
    birds_eye: bool,
) -> syn::parse::Result<Expr> {
    let mut v = TranslatorVisitor::new(ctxt, birds_eye);
    let mut e = expr.clone();
    v.visit_expr_mut(&mut e);
    if v.errors.len() > 0 {
        let mut error = v.errors[0].clone();
        for i in 1..v.errors.len() {
            error.combine(v.errors[i].clone());
        }
        return Err(error);
    }
    Ok(e)
}

struct TranslatorVisitor<'a> {
    pub errors: Vec<Error>,
    pub ctxt: &'a mut Ctxt,
    pub birds_eye: bool,
}

impl<'a> TranslatorVisitor<'a> {
    pub fn new(ctxt: &'a mut Ctxt, birds_eye: bool) -> TranslatorVisitor<'a> {
        TranslatorVisitor { errors: Vec::new(), ctxt, birds_eye }
    }
}

impl<'a> VisitMut for TranslatorVisitor<'a> {
    fn visit_expr_mut(&mut self, node: &mut Expr) {
        let span = node.span();
        match node {
            Expr::Verbatim(_) => {
                panic!(
                    "can't process a Verbatim expression; (and there shouldn't be one a user-provided expression in the first place)"
                );
            }
            Expr::Path(ExprPath { attrs: _, qself: None, path }) if path.is_ident("self") => {
                self.errors.push(Error::new(span,
                    "in a concurrent state machine, 'self' cannot be used opaquely; it may only be used by accessing its fields"));
            }
            Expr::Field(ExprField {
                base: box Expr::Path(ExprPath { attrs: _, qself: None, path }),
                member,
                attrs: _,
                dot_token: _,
            }) if path.is_ident("self") => {
                match member {
                    Member::Named(ident) => {
                        match self.ctxt.get_field_by_ident(span, ident) {
                            Err(err) => self.errors.push(err),
                            Ok(field) => {
                                if self.birds_eye {
                                    match &field.stype {
                                        ShardableType::Variable(_ty) => {
                                            // Handle it as a 'nondeterministic' value UNLESS
                                            // we're already reading this token anyway.
                                            if self.ctxt.fields_read.contains(&field.ident.to_string()) {
                                                *node = get_old_field_value(&self.ctxt, &field);
                                            } else {
                                                self.ctxt.mark_field_as_nondeterministic_read(&field);
                                                *node = get_nondeterministic_out_value(&self.ctxt, &field);
                                            }
                                        }
                                        ShardableType::Constant(_ty) => {
                                            // Handle constants as normal
                                            *node = get_const_field_value(&self.ctxt, &field);
                                        }
                                        _ => {
                                            self.ctxt.mark_field_as_nondeterministic_read(&field);
                                            *node = get_nondeterministic_out_value(&self.ctxt, &field);
                                        }
                                    }
                                } else {
                                    self.ctxt.mark_field_as_read(&field);
                                    match &field.stype {
                                        ShardableType::Variable(_ty) => {
                                            *node = get_old_field_value(&self.ctxt, &field);
                                        }
                                        ShardableType::Constant(_ty) => {
                                            *node = get_const_field_value(&self.ctxt, &field);
                                        }
                                        _ => {
                                            let strat = field.stype.strategy_name();
                                            self.errors.push(Error::new(span,
                                                format!("A '{strat:}' field cannot be directly referenced here"))); // TODO be more specific
                                        }
                                    }
                                }
                            }
                        }
                    }
                    _ => {
                        self.errors.push(Error::new(span, "expected a named field"));
                    }
                }
            }
            _ => syn::visit_mut::visit_expr_mut(self, node),
        }
    }
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
    if ctxt.fields_written.contains(&field.ident.to_string()) {
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
            if *id.to_string() == *field.ident.to_string() { Some(e.clone()) } else { None }
        }
        TransitionStmt::Require(_, _)
        | TransitionStmt::Assert(_, _)
        | TransitionStmt::Special(..)
        | TransitionStmt::PostCondition(..) => None,
    }
}
