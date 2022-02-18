//! Output all the generated code specific to concurrent state machines.
//! We print declarations for:
//!
//!  * The Instance type
//!  * All the Token types for shardable fields
//!  * #[proof] methods for each transition (including init and readonly transitions)
//!
//! Currently supports: 'variable' and 'constant' sharding
//!
//! For a state machine named X, we produce code that looks like:
//!    
//!    // Primary Instance object:
//!    
//!    #[proof]
//!    #[allow(non_camel_case_types)]
//!    #[verifier(external_body)]
//!    #[verifier(unforgeable)]
//!    pub struct X_Instance {
//!        #[proof] pub dummy_field: ::std::marker::PhantomData<X>,
//!    }
//!    
//!    // Token types, each of which look something like:
//!    
//!    #[proof]
//!    #[verifier(unforgeable)]
//!    #[allow(non_camel_case_types)]
//!    pub struct X_counter {
//!        #[spec] pub instance: X_Instance,
//!        #[spec] pub counter: int,
//!    }
//!    
//!    // Clone method for the instance:
//!    
//!    impl X_Instance {
//!        #[proof]
//!        #[verifier(external_body)]
//!        #[verifier(returns(proof))]
//!        pub fn clone(#[proof] &self) -> Self {
//!            ensures(|s: Self| ::builtin::equal(*self, s));
//!            ::core::panicking::panic("not implemented");
//!        }
//!    }
//!    
//!    // Exchange methods. An initialization looks something like this
//!    
//!    #[proof]
//!    #[verifier(returns(proof))]
//!    #[verifier(external_body)]
//!    pub fn X_initialize(params...) -> (X_Instance, /* ... tokens */) {
//!        ::builtin::requires(/* enabling conditions for the Init */)
//!        ::builtin::ensures(|tmp_tuple: (X_Instance, /* ... tokens */)| {
//!            [{
//!                let (instance, /* ... tokens */) = tmp_tuple;
//!                // ensure the new tokens are of the new instance
//!                (::builtin::equal(token_counter.instance, instance))
//!                // ...
//!                // post-conditions on the values of the tokens
//!                (::builtin::equal(token_counter.counter, 0))
//!            }]
//!        });
//!        ::core::panicking::panic("not implemented");
//!    }
//!    
//!    // A normal transition looks something like:
//!    
//!    #[proof]
//!    #[verifier(external_body)]
//!    pub fn X_tr_inc_a(
//!        #[proof] instance: X_Instance,
//!        // input tokens:
//!        #[proof] token_counter: &mut X_counter,
//!        #[proof] token_inc_a: &mut X_inc_a,
//!    ) {
//!        ::builtin::requires([
//!            // Check that input tokens are of the right instance
//!            ::builtin::equal(::builtin::old(token_counter).instance, instance),
//!            // ...
//!            // Other enabling conditions here ...
//!        ]);
//!        ::builtin::ensures([
//!            // Check that output tokens are of the right instance
//!            ::builtin::equal(token_counter.instance, instance),
//!            // ...
//!            // Other conditions on input/output tokens assured by the transition ...
//!        ]);
//!        ::core::panicking::panic("not implemented");
//!    }

use crate::ast::{Field, Lemma, ShardableType, Transition, TransitionKind, TransitionStmt, SM};
use crate::parse_token_stream::SMBundle;
use crate::safety_conditions::has_any_assert;
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

fn field_token_type_name(sm_name: &Ident, field: &Field) -> Ident {
    let name = sm_name.to_string() + "_" + &field.ident.to_string();
    Ident::new(&name, field.ident.span())
}

fn field_token_field_name(field: &Field) -> Ident {
    field.ident.clone()
}

fn field_token_field_type(field: &Field) -> Type {
    match &field.stype {
        ShardableType::Variable(ty) => ty.clone(),
        ShardableType::Constant(ty) => ty.clone(),
    }
}

fn exchange_name(sm_name: &Ident, tr: &Transition) -> Ident {
    let name = sm_name.to_string() + "_" + &tr.name.to_string();
    Ident::new(&name, tr.name.span())
}

fn transition_arg_name(field: &Field) -> Ident {
    let name = "token_".to_string() + &field.ident.to_string();
    Ident::new(&name, field.ident.span())
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
    let smname = &sm.name;
    return quote! {
        #[proof]
        #[allow(non_camel_case_types)]
        #[verifier(unforgeable)]
        pub struct #insttype {
            #[spec] state: #smname,
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
fn token_struct_stream(sm_name: &Ident, field: &Field) -> TokenStream {
    let tokenname = field_token_type_name(sm_name, field);
    let fieldname = field_token_field_name(field);
    let fieldtype = field_token_field_type(field);
    let insttype = inst_type_name(sm_name);

    return quote! {
        #[proof]
        #[verifier(unforgeable)]
        #[allow(non_camel_case_types)]
        pub struct #tokenname {
            #[spec] pub instance: #insttype,
            #[spec] pub #fieldname: #fieldtype,
        }
    };
}

/// For a given sharding(constant) field, add that constant
/// as a #[spec] fn on the Instance type. (The field is constant
/// for the entire instance.)
///
/// TODO we could make these fields on the Instance type instead
/// (this is safe as long as the Instance type is an unforgeable proof type)
fn const_fn_stream(field: &Field) -> TokenStream {
    let fieldname = field_token_field_name(field);
    let fieldtype = field_token_field_type(field);

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
                token_stream.extend(token_struct_stream(&bundle.sm.name, field));
            }
        }
    }

    let insttype = inst_type_name(&bundle.sm.name);
    token_stream.extend(quote! {
        impl #insttype {
            #inst_impl_token_stream
        }
    });

    for tr in &bundle.sm.transitions {
        token_stream.extend(exchange_stream(bundle, tr)?);
    }
    Ok(())
}

/// Context object for the complex task of translating a single
/// transition into a token-exchange method.

struct Ctxt {
    fields_read: HashSet<Ident>,
    fields_written: HashSet<Ident>,
    requires: Vec<Expr>,
    ensures: Vec<Expr>,
    ident_to_field: HashMap<Ident, Field>,
    is_init: bool,
}

impl Ctxt {
    pub fn get_field_by_ident(&self, span: Span, ident: &Ident) -> syn::parse::Result<Field> {
        match self.ident_to_field.get(ident) {
            Some(f) => Ok(f.clone()),
            None => Err(Error::new(
                span,
                "in a concurrent transition, any field access but be a state field",
            )),
        }
    }

    pub fn get_field_or_panic(&self, ident: &Ident) -> Field {
        match self.ident_to_field.get(ident) {
            Some(f) => f.clone(),
            None => panic!("should have already checked field updates are valid"),
        }
    }

    pub fn mark_field_as_read(&mut self, field: &Field) {
        self.fields_read.insert(field.ident.clone());
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

    let mut ident_to_field = HashMap::new();
    for field in &sm.fields {
        ident_to_field.insert(field.ident.clone(), field.clone());
    }

    let mut ctxt = Ctxt {
        fields_read: HashSet::new(),
        fields_written: HashSet::new(),
        requires: Vec::new(),
        ensures: Vec::new(),
        ident_to_field,
        is_init: tr.kind == TransitionKind::Init,
    };

    let mut tr = tr.clone();

    // determine output tokens based on 'update' statements
    determine_outputs(&mut ctxt, &tr.body)?;

    // translate the expressions in the TransitionStmt so that
    // where they previously referred to fields like `self.foo`,
    // they now refer to the field that comes from an input.
    // (in the process, we also determine inputs).
    walk_translate_expressions(&mut ctxt, &mut tr.body)?;

    // translate the (new) TransitionStmt into an expressions that
    // can be used as pre-conditions and post-conditions
    exchange_collect(&mut ctxt, &tr.body, Vec::new(), Vec::new())?;

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
        let itn = inst_type_name(&sm.name);
        out_args.push((quote! { instance }, quote! { #itn }));
    } else {
        let itn = inst_type_name(&sm.name);
        in_args.push(quote! { #[proof] instance: #itn }); // TODO make this argument self?
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

    for field in &sm.fields {
        // Determine if the field is an input, output, or both.
        // (If neither, we get to skip.)

        let is_output;
        let is_input;
        if tr.kind == TransitionKind::Init {
            assert!(ctxt.fields_written.contains(&field.ident));
            assert!(!ctxt.fields_read.contains(&field.ident));
            is_output = true;
            is_input = false;
        } else {
            is_output = ctxt.fields_written.contains(&field.ident);
            is_input = is_output || ctxt.fields_read.contains(&field.ident);
        }

        if !is_input && !is_output {
            continue;
        }

        let arg_name = transition_arg_name(field);
        let arg_type = field_token_type_name(&sm.name, field);

        let is_const = match field.stype {
            ShardableType::Constant(_) => true,
            _ => false,
        };

        if is_output {
            // For a normal transition, we are not allowed to update a constant
            // field. (This should have been checked already.)
            assert!(!is_const || ctxt.is_init);

            // We need to create a post-condition that says
            //     field_value == (expression from update statement)
            let (e, lhs) = match field.stype {
                ShardableType::Variable(_) => {
                    let e_opt = get_output_value_for_variable(&ctxt, &tr.body, field);
                    let e = e_opt.expect("get_output_value_for_variable");
                    let lhs = get_new_field_value(field);
                    (e, lhs)
                }
                ShardableType::Constant(_) => {
                    let e_opt = get_output_value_for_variable(&ctxt, &tr.body, field);
                    let e = e_opt.expect("get_output_value_for_variable");
                    let lhs = get_const_field_value(&ctxt, field);
                    (e, lhs)
                }
            };
            let eq_e = Expr::Verbatim(quote! { ::builtin::equal(#lhs, #e) });
            ctxt.ensures.push(eq_e);

            if is_input {
                // If it's both an input and an output, make it a &mut parameter
                in_args.push(quote! { #[proof] #arg_name: &mut #arg_type });
            } else if !is_const {
                out_args.push((quote! {#arg_name}, quote! {#arg_type}));
            }
        } else {
            // For sharding(constant), the field is input via the Instance object
            // so we don't have to add anything here.
            // For sharding(variable), we add a token that corresponds to the field.
            if !is_const {
                in_args.push(quote! { #[proof] #arg_name: &#arg_type });
            }
        }

        if !is_const {
            let inst = get_inst_value(&ctxt);
            if is_output {
                let lhs = get_new_field_inst(field);
                inst_eq_enss.push(Expr::Verbatim(quote! {
                    ::builtin::equal(#lhs, #inst)
                }));
            }
            if is_input {
                let lhs = get_old_field_inst(&ctxt, field);
                inst_eq_reqs.push(Expr::Verbatim(quote! {
                    ::builtin::equal(#lhs, #inst)
                }));
            }
        }
    }

    let mut reqs = inst_eq_reqs;
    reqs.extend(ctxt.requires);

    let mut enss = inst_eq_enss;
    enss.extend(ctxt.ensures);

    let exch_name = exchange_name(&sm.name, &tr);

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

    return Ok(quote! {
        #[proof]
        #return_value_mode
        #[verifier(external_body)]
        pub fn #exch_name(#(#in_args),*) #out_args_ret {
            #req_stream
            #ens_stream
            #extra_deps
            unimplemented!();
        }
    });
}

fn get_extra_deps(bundle: &SMBundle, trans: &Transition) -> TokenStream {
    let smname = &bundle.sm.name;
    let deps: Vec<TokenStream> = get_all_lemma_for_transition(bundle, trans)
        .iter()
        .map(|ident| {
            quote! {
                ::builtin::extra_dependency(#smname::#ident);
            }
        })
        .collect();
    quote! { #(#deps)* }
}

/// Gets the lemmas that prove validity of the given transition.
fn get_all_lemma_for_transition(bundle: &SMBundle, trans: &Transition) -> Vec<Ident> {
    let mut v = Vec::new();

    if trans.kind != TransitionKind::Readonly {
        let l = get_main_lemma_for_transition_or_panic(&bundle.extras.lemmas, &trans.name);
        v.push(l.func.sig.ident.clone());
    }

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
        TransitionStmt::Let(_span, _id, _init_e) => Ok(()),
        TransitionStmt::If(_span, _cond_e, e1, e2) => {
            determine_outputs(ctxt, e1)?;
            determine_outputs(ctxt, e2)?;
            Ok(())
        }
        TransitionStmt::Require(_span, _req_e) => Ok(()),
        TransitionStmt::Assert(_span, _assert_e) => Ok(()),
        TransitionStmt::Update(span, id, _e) => {
            let f = ctxt.get_field_or_panic(id);
            if !ctxt.is_init {
                match f.stype {
                    ShardableType::Constant(_) => {
                        return Err(Error::new(
                            *span,
                            "cannot update a field marked constant outside of initialization",
                        ));
                    }
                    _ => {}
                }
            }

            ctxt.fields_written.insert(id.clone());
            Ok(())
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

fn walk_translate_expressions(ctxt: &mut Ctxt, ts: &mut TransitionStmt) -> syn::parse::Result<()> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            for child in v.iter_mut() {
                walk_translate_expressions(ctxt, child)?;
            }
            Ok(())
        }
        TransitionStmt::Let(_span, _id, e) => {
            let init_e = translate_expr(ctxt, e)?;
            *e = init_e;
            Ok(())
        }
        TransitionStmt::If(_span, cond, e1, e2) => {
            let cond_e = translate_expr(ctxt, cond)?;
            *cond = cond_e;
            walk_translate_expressions(ctxt, e1)?;
            walk_translate_expressions(ctxt, e2)?;
            Ok(())
        }
        TransitionStmt::Require(_span, e) => {
            let req_e = translate_expr(ctxt, e)?;
            *e = req_e;
            Ok(())
        }
        TransitionStmt::Assert(_span, e) => {
            let assert_e = translate_expr(ctxt, e)?;
            *e = assert_e;
            Ok(())
        }
        TransitionStmt::Update(_span, _id, e) => {
            let update_e = translate_expr(ctxt, e)?;
            *e = update_e;
            Ok(())
        }
    }
}

fn translate_expr(ctxt: &mut Ctxt, expr: &Expr) -> syn::parse::Result<Expr> {
    let mut v = TranslatorVisitor::new(ctxt);
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
}

impl<'a> TranslatorVisitor<'a> {
    pub fn new(ctxt: &'a mut Ctxt) -> TranslatorVisitor<'a> {
        TranslatorVisitor { errors: Vec::new(), ctxt: ctxt }
    }
}

impl<'a> VisitMut for TranslatorVisitor<'a> {
    fn visit_expr_mut(&mut self, node: &mut Expr) {
        let span = node.span();
        match node {
            Expr::Path(ExprPath { attrs: _, qself: None, path }) if path.is_ident("self") => {
                self.errors.push(Error::new(span,
                    "in a concurrent state machine, 'self' cannot be used opaquely; it may only be used by accessing its fields"));
            }
            Expr::Field(ExprField {
                base: box Expr::Path(ExprPath { attrs: _, qself: None, path }),
                member,
                attrs: _,
                dot_token: _,
            }) if path.is_ident("self") => match member {
                Member::Named(ident) => match self.ctxt.get_field_by_ident(span, ident) {
                    Err(err) => self.errors.push(err),
                    Ok(field) => {
                        self.ctxt.mark_field_as_read(&field);
                        match &field.stype {
                            ShardableType::Variable(_ty) => {
                                *node = get_old_field_value(&self.ctxt, &field);
                            }
                            ShardableType::Constant(_ty) => {
                                *node = get_const_field_value(&self.ctxt, &field);
                            }
                        }
                    }
                },
                _ => {
                    self.errors.push(Error::new(span, "expected a named field"));
                }
            },
            _ => syn::visit_mut::visit_expr_mut(self, node),
        }
    }
}

fn get_inst_value(_ctxt: &Ctxt) -> Expr {
    Expr::Verbatim(quote! { instance })
}

fn get_const_field_value(ctxt: &Ctxt, field: &Field) -> Expr {
    let inst = get_inst_value(ctxt);
    let field_name = field_token_field_name(&field);
    Expr::Verbatim(quote! { #inst.#field_name() })
}

fn get_old_field_value(ctxt: &Ctxt, field: &Field) -> Expr {
    let arg = transition_arg_name(&field);
    let field_name = field_token_field_name(&field);
    if ctxt.fields_written.contains(&field.ident) {
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

fn get_old_field_inst(ctxt: &Ctxt, field: &Field) -> Expr {
    let arg = transition_arg_name(&field);
    if ctxt.fields_written.contains(&field.ident) {
        Expr::Verbatim(quote! { ::builtin::old(#arg).instance })
    } else {
        Expr::Verbatim(quote! { #arg.instance })
    }
}

fn get_new_field_inst(field: &Field) -> Expr {
    let arg = transition_arg_name(&field);
    Expr::Verbatim(quote! { #arg.instance })
}

// Collect requires and ensures.
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
    Condition(Expr),
    Let(Ident, Expr),
    Branch(Expr, Vec<PrequelElement>, Vec<PrequelElement>),
}

fn exchange_collect(
    ctxt: &mut Ctxt,
    ts: &TransitionStmt,
    prequel: Vec<PrequelElement>,
    prequel_with_asserts: Vec<PrequelElement>,
) -> syn::parse::Result<(Vec<PrequelElement>, Vec<PrequelElement>)> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            let mut p = prequel;
            let mut pa = prequel_with_asserts;
            for child in v.iter() {
                let (p1, pa1) = exchange_collect(ctxt, child, p, pa)?;
                p = p1;
                pa = pa1;
            }
            Ok((p, pa))
        }
        TransitionStmt::Let(_span, id, init_e) => {
            let mut p = prequel;
            let mut pa = prequel_with_asserts;
            let el = PrequelElement::Let(id.clone(), init_e.clone());
            p.push(el.clone());
            pa.push(el);
            Ok((p, pa))
        }
        TransitionStmt::If(_span, cond_e, e1, e2) => {
            let cond = PrequelElement::Condition(cond_e.clone());
            let not_cond = PrequelElement::Condition(bool_not_expr(cond_e));

            let mut p1 = prequel.clone();
            let mut pa1 = prequel_with_asserts.clone();
            p1.push(cond.clone());
            pa1.push(cond);
            let (_p1, pa1) = exchange_collect(ctxt, e1, p1, pa1)?;

            let mut p2 = prequel.clone();
            let mut pa2 = prequel_with_asserts.clone();
            p2.push(not_cond.clone());
            pa2.push(not_cond);
            let (_p2, pa2) = exchange_collect(ctxt, e2, p2, pa2)?;

            let l = prequel_with_asserts.len();
            let joined_pa = join_with_conditional(
                prequel_with_asserts,
                cond_e.clone(),
                pa1[l + 1..].to_vec(),
                pa2[l + 1..].to_vec(),
            );

            Ok((prequel, joined_pa))
        }
        TransitionStmt::Require(_span, req_e) => {
            ctxt.requires.push(with_prequel(&prequel_with_asserts, req_e.clone()));
            Ok((prequel, prequel_with_asserts))
        }
        TransitionStmt::Assert(_span, assert_e) => {
            ctxt.ensures.push(with_prequel(&prequel, assert_e.clone()));
            let mut pa = prequel_with_asserts;
            pa.push(PrequelElement::Condition(assert_e.clone()));
            Ok((prequel, pa))
        }
        TransitionStmt::Update(_span, _id, _e) => Ok((prequel, prequel_with_asserts)),
    }
}

fn join_with_conditional(
    base: Vec<PrequelElement>,
    cond: Expr,
    v1: Vec<PrequelElement>,
    v2: Vec<PrequelElement>,
) -> Vec<PrequelElement> {
    let mut b = base;
    b.push(PrequelElement::Branch(cond, v1, v2));
    b
}

fn bool_not_expr(e: &Expr) -> Expr {
    Expr::Verbatim(quote! { !(#e) })
}

fn with_prequel(pre: &Vec<PrequelElement>, e: Expr) -> Expr {
    let mut e = e;
    for p in pre.iter().rev() {
        match p {
            PrequelElement::Let(id, init_e) => {
                e = Expr::Verbatim(quote! { { let #id = #init_e; #e } });
            }
            PrequelElement::Condition(cond_e) => {
                e = Expr::Verbatim(quote! { ((#cond_e) >>= (#e)) });
            }
            PrequelElement::Branch(_, _, _) => {
                let cond_e = prequel_element_to_expr(p);
                if let Some(ce) = cond_e {
                    e = Expr::Verbatim(quote! { (#ce >>= #e) });
                }
            }
        }
    }
    e
}

fn prequel_element_to_expr(p: &PrequelElement) -> Option<Expr> {
    match p {
        PrequelElement::Condition(e) => Some(e.clone()),
        PrequelElement::Let(_, _) => None,
        PrequelElement::Branch(b, v1, v2) => {
            let e1 = prequel_vec_to_expr(v1);
            let e2 = prequel_vec_to_expr(v2);
            match (e1, e2) {
                (None, None) => None,
                (Some(e1), None) => Some(Expr::Verbatim(quote! { ((#b) >>= (#e1)) })),
                (None, Some(e2)) => Some(Expr::Verbatim(quote! { (!(#b) >>= (#e2)) })),
                (Some(e1), Some(e2)) => {
                    Some(Expr::Verbatim(quote! { (if #b { #e1 } else { #e2 }) }))
                }
            }
        }
    }
}

fn prequel_vec_to_expr(v: &Vec<PrequelElement>) -> Option<Expr> {
    let mut opt = None;
    for p in v.iter().rev() {
        match p {
            PrequelElement::Let(id, init_e) => {
                if let Some(o) = opt {
                    opt = Some(Expr::Verbatim(quote! { { let #id = #init_e; #o } }));
                }
            }
            PrequelElement::Condition(cond_e) => match opt {
                None => {
                    opt = Some(Expr::Verbatim(quote! { (#cond_e) }));
                }
                Some(e) => {
                    opt = Some(Expr::Verbatim(quote! { ((#cond_e) && #e) }));
                }
            },
            PrequelElement::Branch(_, _, _) => {
                let cond_e = prequel_element_to_expr(p);
                if let Some(ce) = cond_e {
                    if let Some(o) = opt {
                        opt = Some(Expr::Verbatim(quote! { (#ce && #o) }));
                    } else {
                        opt = Some(ce);
                    }
                }
            }
        }
    }
    opt
}

/// Get the expression E that a given field gets updated to.
/// This is used in the post-condition of the exchange method.
/// Since the 'update' might be inside a conditional, we may need to build
/// a conditional expression.
///
/// Returns 'None' if it doesn't find an 'update' for the given variable.
fn get_output_value_for_variable(ctxt: &Ctxt, ts: &TransitionStmt, field: &Field) -> Option<Expr> {
    match ts {
        TransitionStmt::Block(_span, v) => {
            let mut opt = None;
            for child in v.iter() {
                let o = get_output_value_for_variable(ctxt, child, field);
                if o.is_some() {
                    // We should have already performed a check that the field
                    // is not updated more than once.
                    assert!(!opt.is_some());
                    opt = o;
                }
            }
            opt
        }
        TransitionStmt::Let(_, _, _)
        | TransitionStmt::Require(_, _)
        | TransitionStmt::Assert(_, _) => None,
        TransitionStmt::If(_span, cond_e, e1, e2) => {
            let o1 = get_output_value_for_variable(ctxt, e1, field);
            let o2 = get_output_value_for_variable(ctxt, e2, field);
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
        TransitionStmt::Update(_span, id, e) => {
            if *id.to_string() == *field.ident.to_string() {
                Some(e.clone())
            } else {
                None
            }
        }
    }
}
