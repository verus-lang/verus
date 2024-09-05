use crate::topological_sort::TopologicalSort;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::ToTokens;
use quote::{quote, quote_spanned};
use std::collections::HashMap;
use std::collections::HashSet;
use syn_verus::buffer::Cursor;
use syn_verus::parse;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::parse_macro_input;
use syn_verus::punctuated::Punctuated;
use syn_verus::spanned::Spanned;
use syn_verus::token;
use syn_verus::token::Comma;
use syn_verus::visit;
use syn_verus::visit::Visit;
use syn_verus::visit_mut;
use syn_verus::visit_mut::VisitMut;
use syn_verus::Token;
use syn_verus::TypeInfer;
use syn_verus::{
    braced, parenthesized, Block, Error, Expr, Field, Fields, FnArg, FnArgKind, FnMode,
    GenericArgument, GenericParam, Ident, Index, ItemStruct, Lifetime, Member, Pat, PatIdent,
    PatType, PathArguments, Receiver, Signature, Type, TypePath, Visibility,
};

pub fn struct_decl_inv(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let sdi: SDI = parse_macro_input!(input as SDI);
    match struct_decl_inv_main(sdi) {
        Ok(t) => t.into(),
        Err(err) => proc_macro::TokenStream::from(err.to_compile_error()),
    }
}

fn struct_decl_inv_main(sdi: SDI) -> parse::Result<TokenStream> {
    let main_name = sdi.item_struct.ident.to_string();

    let fields = get_fields(&sdi.item_struct.fields)?;
    check_dupe_field_names(&fields)?;
    check_dupe_param_names(&sdi)?;
    let partial_fields = get_partial_type_fields(&fields)?;
    check_invs_match_partial_types(&fields, &partial_fields, &sdi.invariant_decls)?;
    let ordering = check_deps_acyclic(&fields, &sdi.invariant_decls)?;
    let used_type_params = field_used_type_params(&sdi, &fields, &ordering);

    let mut stream = TokenStream::new();
    let mut wf_body_stream = quote! { true }; // to be extended with conjuncts

    let mut sdi = sdi;
    fill_in_item_struct(&main_name, &mut sdi.item_struct, &sdi.invariant_decls, &used_type_params);
    sdi.item_struct.to_tokens(&mut stream);

    let fields_filled_in = get_fields(&sdi.item_struct.fields)?;
    for field in fields_filled_in.iter() {
        output_field_type_alias(
            &main_name,
            &sdi.item_struct.vis,
            &mut stream,
            field,
            &used_type_params,
        );
    }

    for inv in sdi.invariant_decls.iter() {
        output_invariant(
            &main_name,
            &sdi,
            &mut stream,
            &mut wf_body_stream,
            &partial_fields,
            inv,
            &used_type_params,
        );
    }

    output_wf(&sdi, &mut stream, wf_body_stream);

    Ok(quote! {
        ::builtin_macros::verus!{
            #stream
        }
    })
}

struct SDI {
    item_struct: ItemStruct,
    wf_vis: Visibility,
    wf_sig: Signature,
    invariant_decls: Vec<InvariantDecl>,
}

enum InvariantDecl {
    NormalExpr(Block),
    Invariant {
        field_name: Ident,
        depends_on: Vec<Ident>,
        quants: Vec<PatType>,
        condition: Option<Expr>,
        specifically: Option<Expr>,
        params: Vec<FnArg>,
        params_span: Span,
        predicate: Block,
    },
}

struct PartialField {
    name: Ident,
    partial_types: Vec<PartialType>,
}

struct PartialType {
    is_atomic_ghost: bool,
    concrete_args: Vec<Type>,
}

impl Parse for SDI {
    fn parse(input: ParseStream) -> parse::Result<SDI> {
        let item_struct: ItemStruct = input.parse()?;

        let wf_vis: Visibility = input.parse()?;
        let wf_sig: Signature = input.parse()?;
        check_wf_sig(&wf_sig)?;

        let brace_content;
        let _ = braced!(brace_content in input);

        let mut invariant_decls = vec![];
        while !brace_content.is_empty() {
            let invariant_decl: InvariantDecl = brace_content.parse()?;
            invariant_decls.push(invariant_decl);
        }

        Ok(SDI { item_struct, wf_vis, wf_sig, invariant_decls })
    }
}

pub(crate) fn peek_keyword(cursor: Cursor, token: &str) -> bool {
    if let Some((ident, _rest)) = cursor.ident() { ident == token } else { false }
}

pub(crate) fn keyword(input: ParseStream, token: &str) -> parse::Result<Span> {
    input.step(|cursor| {
        if let Some((ident, rest)) = cursor.ident() {
            if ident == token {
                return Ok((ident.span(), rest));
            }
        }
        Err(cursor.error(format!("expected `{}`", token)))
    })
}

impl Parse for InvariantDecl {
    fn parse(input: ParseStream) -> parse::Result<InvariantDecl> {
        if peek_keyword(input.cursor(), "invariant") {
            let _ = keyword(input, "invariant");
            let _ = keyword(input, "on");

            let field_name: Ident = input.parse()?;

            let depends_on = if peek_keyword(input.cursor(), "with") {
                let _ = keyword(input, "with");
                let paren_content;
                let _ = parenthesized!(paren_content in input);
                let deps: Punctuated<Ident, token::Comma> =
                    paren_content.parse_terminated(Ident::parse)?;
                deps.into_iter().collect()
            } else {
                Vec::new()
            };

            let quants = if peek_keyword(input.cursor(), "forall") {
                let _ = keyword(input, "forall");
                parse_quants(input)?
            } else {
                Vec::new()
            };

            let condition = if peek_keyword(input.cursor(), "where") {
                let _ = keyword(input, "where");
                let paren_content;
                let _ = parenthesized!(paren_content in input);
                let expr: Expr = paren_content.parse()?;
                Some(expr)
            } else {
                None
            };

            let specifically = if peek_keyword(input.cursor(), "specifically") {
                let _ = keyword(input, "specifically");
                let paren_content;
                let _ = parenthesized!(paren_content in input);
                let expr: Expr = paren_content.parse()?;
                Some(expr)
            } else {
                None
            };

            let _ = keyword(input, "is");

            let (params_span, params) = {
                let paren_content;
                let ptoken = parenthesized!(paren_content in input);
                let params: Punctuated<FnArg, token::Comma> =
                    paren_content.parse_terminated(FnArg::parse)?;
                (ptoken.span, params.into_iter().collect())
            };

            let predicate: Block = input.parse()?;

            Ok(InvariantDecl::Invariant {
                field_name,
                depends_on,
                quants,
                condition,
                params,
                params_span,
                predicate,
                specifically,
            })
        } else if peek_keyword(input.cursor(), "predicate") {
            let _ = keyword(input, "predicate");
            let predicate: Block = input.parse()?;
            Ok(InvariantDecl::NormalExpr(predicate))
        } else {
            Err(input
                .error(format!("expected an 'invariant' declaration or 'predicate' declaration")))
        }
    }
}

fn parse_quants(input: ParseStream) -> parse::Result<Vec<PatType>> {
    let _or1_token: Token![|] = input.parse()?;

    let mut inputs = Vec::new();
    loop {
        if input.peek(Token![|]) {
            break;
        }
        let pat = Pat::parse(input)?;
        let colon_token: Token![:] = input.parse()?;
        let ty = Type::parse(input)?;
        let pat_type = PatType { attrs: vec![], pat: Box::new(pat), colon_token, ty: Box::new(ty) };
        inputs.push(pat_type);

        if input.peek(Token![|]) {
            break;
        }
        let _punct: Token![,] = input.parse()?;
    }

    let _or2_token: Token![|] = input.parse()?;

    Ok(inputs)
}

fn check_wf_sig(sig: &Signature) -> parse::Result<()> {
    if !is_spec(sig) {
        return Err(Error::new(
            sig.span(),
            "struct_with_invariants: this signature should be a `spec` function",
        ));
    }

    if !is_first_param_self(sig) {
        return Err(Error::new(
            sig.span(),
            "struct_with_invariants: the first param here should be `self`",
        ));
    }

    Ok(())
}

fn get_fields(f: &Fields) -> parse::Result<Vec<Field>> {
    match f {
        Fields::Named(fields_named) => Ok(fields_named.named.clone().into_iter().collect()),
        _ => {
            return Err(Error::new(f.span(), "struct_with_invariants: expected named fields"));
        }
    }
}

fn check_dupe_field_names(fields: &Vec<Field>) -> parse::Result<()> {
    let mut names = HashSet::new();
    for field in fields {
        match &field.ident {
            None => {
                return Err(Error::new(
                    field.span(),
                    "struct_with_invariants: each field must have a name",
                ));
            }
            Some(id) => {
                let name = id.to_string();
                if names.contains(&name) {
                    return Err(Error::new(field.span(), "duplicate field name"));
                }
                names.insert(name.clone());
            }
        }
    }
    Ok(())
}

fn check_dupe_param_names(sdi: &SDI) -> parse::Result<()> {
    for inv_decl in sdi.invariant_decls.iter() {
        if let InvariantDecl::Invariant { depends_on, quants, params, .. } = inv_decl {
            let mut names = vec![];

            for dep in depends_on.iter() {
                names.push(dep.clone());
            }
            for quant in quants.iter() {
                match &*quant.pat {
                    Pat::Ident(PatIdent {
                        attrs: _,
                        by_ref: None,
                        mutability: None,
                        ident,
                        subpat: None,
                    }) => {
                        names.push(ident.clone());
                    }
                    _ => {
                        return Err(Error::new(
                            quant.pat.span(),
                            "declate_struct_with_invariants: expected identifier here",
                        ));
                    }
                }
            }
            for fn_arg in params.iter() {
                match &fn_arg.kind {
                    FnArgKind::Typed(pat_type) => match &*pat_type.pat {
                        Pat::Ident(PatIdent {
                            attrs: _,
                            by_ref: None,
                            mutability: None,
                            ident,
                            subpat: None,
                        }) => {
                            names.push(ident.clone());
                        }
                        _ => {
                            return Err(Error::new(
                                fn_arg.kind.span(),
                                "declate_struct_with_invariants: expected identifier here",
                            ));
                        }
                    },
                    _ => {
                        return Err(Error::new(
                            fn_arg.kind.span(),
                            "struct_with_invariants: this kind of argument not expected here",
                        ));
                    }
                }
            }

            let mut map: HashMap<String, usize> = HashMap::new();
            for (i, name) in names.iter().enumerate() {
                let s = name.to_string();
                if map.contains_key(&s) {
                    let mut er1 = Error::new(
                        names[map[&s]].span(),
                        "struct_with_invariants: duplicate identifier used in parameters to invariant",
                    );
                    let er2 = Error::new(
                        name.span(),
                        "struct_with_invariants: duplicate identifier used in parameters to invariant",
                    );
                    er1.combine(er2);
                    return Err(er1);
                }
                map.insert(s, i);
            }
        }
    }

    Ok(())
}

fn get_partial_type_fields(fields: &Vec<Field>) -> parse::Result<Vec<PartialField>> {
    let mut res = vec![];
    for field in fields {
        let partial_types = get_partial_types(&field.ty)?;
        let name = field.ident.clone().unwrap();
        res.push(PartialField { name, partial_types });
    }
    Ok(res)
}

fn check_invs_match_partial_types(
    all_fields: &Vec<Field>,
    partial_fields: &Vec<PartialField>,
    invariant_decls: &Vec<InvariantDecl>,
) -> parse::Result<()> {
    let mut indices: HashMap<String, usize> = HashMap::new();

    for field in all_fields.iter() {
        let name = field.ident.as_ref().unwrap().to_string();
        indices.insert(name, 0);
    }

    for invariant_decl in invariant_decls.iter() {
        if let InvariantDecl::Invariant {
            field_name,
            depends_on,
            params,
            params_span,
            predicate: _,
            condition: _,
            quants: _,
            specifically: _,
        } = invariant_decl
        {
            let name = field_name.to_string();

            let pf = get_partial_field_by_name(partial_fields, &name);
            let pf = match pf {
                Some(pf) => pf,
                None => {
                    return Err(Error::new(
                        field_name.span(),
                        "struct_with_invariants: no field declared of this name",
                    ));
                }
            };

            for dep in depends_on.iter() {
                check_dep_in_fields(all_fields, dep)?;
            }

            let idx = indices[&name];
            if idx < pf.partial_types.len() {
                *indices.get_mut(&name).unwrap() = idx + 1;
                check_invdecl_params_match(params_span, params, &pf.partial_types[idx])?;
            } else {
                if pf.partial_types.len() == 0 {
                    return Err(Error::new(
                        field_name.span(),
                        "struct_with_invariants: the type for this field needs to be declared with wildcard placeholders in order to have an invariant",
                    ));
                } else {
                    return Err(Error::new(
                        field_name.span(),
                        "struct_with_invariants: too many invariants declared for this field",
                    ));
                }
            }
        }
    }

    for pf in partial_fields.iter() {
        let idx = indices[&pf.name.to_string()];
        if idx != pf.partial_types.len() {
            if idx == 0 {
                return Err(Error::new(
                    pf.name.span(),
                    "struct_with_invariants: no invariant declared for this field",
                ));
            } else {
                return Err(Error::new(
                    pf.name.span(),
                    "struct_with_invariants: not enough invariants declared for this field",
                ));
            }
        }
    }

    Ok(())
}

fn check_invdecl_params_match(
    params_span: &Span,
    params: &Vec<FnArg>,
    partial_type: &PartialType,
) -> parse::Result<()> {
    for (fn_arg, concrete_arg) in params.iter().zip(partial_type.concrete_args.iter()) {
        match &fn_arg.kind {
            FnArgKind::Typed(pat_type) => {
                let ty1 = &pat_type.ty;
                let ty2 = concrete_arg;
                if ty1.to_token_stream().to_string() != ty2.to_token_stream().to_string() {
                    return Err(Error::new(
                        ty1.span(),
                        format!(
                            "struct_with_invariants: this type is expected to be {:}",
                            ty2.to_token_stream().to_string()
                        ),
                    ));
                }
            }
            _ => {
                return Err(Error::new(
                    fn_arg.kind.span(),
                    "struct_with_invariants: this kind of argument not expected here",
                ));
            }
        }
    }

    if params.len() != partial_type.concrete_args.len() {
        return Err(Error::new(
            params_span.clone(),
            format!(
                "struct_with_invariants: expected {:} params here",
                partial_type.concrete_args.len(),
            ),
        ));
    }

    Ok(())
}

fn check_dep_in_fields(fields: &Vec<Field>, dep: &Ident) -> parse::Result<()> {
    if !fields_contains(fields, &dep.to_string()) {
        Err(Error::new(
            dep.span(),
            "struct_with_invariants: field not found as a member of the declared struct",
        ))
    } else {
        Ok(())
    }
}

fn check_deps_acyclic(
    fields: &Vec<Field>,
    invs: &Vec<InvariantDecl>,
) -> parse::Result<Vec<String>> {
    let mut ts = TopologicalSort::new();
    for f in fields.iter() {
        ts.add_node(f.ident.as_ref().unwrap().to_string());
    }
    for inv in invs.iter() {
        match inv {
            InvariantDecl::Invariant { field_name, depends_on, .. } => {
                let f = field_name.to_string();
                for dep in depends_on.iter() {
                    ts.add_edge(&f, &dep.to_string());
                }
            }
            InvariantDecl::NormalExpr(..) => {}
        }
    }

    match ts.compute_topological_sort() {
        None => Err(Error::new(
            Span::call_site(),
            "struct_with_invariants: dependencies between fields should be acyclic",
        )),
        Some(ordering) => Ok(ordering),
    }
}

// Manipulation and output

fn field_used_type_params(
    sdi: &SDI,
    fields: &Vec<Field>,
    ordering: &Vec<String>,
) -> HashMap<String, Vec<GenericParam>> {
    let mut hs = HashMap::<String, HashSet<String>>::new();
    let mut res = HashMap::<String, Vec<GenericParam>>::new();
    for field_name in ordering.iter().rev() {
        let field = get_field_by_name(fields, &field_name).unwrap();
        let mut used_params: HashSet<String> =
            get_params_used_in_type(&sdi.item_struct.generics.params, &field.ty);

        let invariant_decls = get_invariant_decls_by_name(&sdi.invariant_decls, &field_name);
        for invariant_decl in invariant_decls.iter() {
            if let InvariantDecl::Invariant { depends_on, .. } = invariant_decl {
                for dep in depends_on {
                    let k = hs.get(&dep.to_string()).expect("should exist because of top. sort");
                    for j in k.iter() {
                        used_params.insert(j.clone());
                    }
                }
            }
        }

        let p = sdi
            .item_struct
            .generics
            .params
            .clone()
            .into_iter()
            .filter(|generic_param| used_params.contains(&generic_param_to_string(generic_param)))
            .collect();

        hs.insert(field_name.clone(), used_params);
        res.insert(field_name.clone(), p);
    }

    res
}

fn fill_in_item_struct(
    main_name: &str,
    item_struct: &mut ItemStruct,
    invariant_decls: &Vec<InvariantDecl>,
    used_type_params: &HashMap<String, Vec<GenericParam>>,
) {
    match &mut item_struct.fields {
        Fields::Named(fields_named) => {
            for field in fields_named.named.iter_mut() {
                let name = field.ident.as_ref().unwrap().to_string();
                let invdecls = get_invariant_decls_by_name(invariant_decls, &name);
                field.ty = fill_in_type(&field.ty, main_name, invdecls, used_type_params);
            }
        }
        _ => {
            panic!("fill_in_item_struct expected Fields::Named");
        }
    }
}

fn output_invariant(
    main_name: &str,
    sdi: &SDI,
    stream: &mut TokenStream,
    wf_stream: &mut TokenStream,
    partial_fields: &Vec<PartialField>,
    invariant_decl: &InvariantDecl,
    used_type_params: &HashMap<String, Vec<GenericParam>>,
) {
    let mut indices: HashMap<String, usize> = HashMap::new();

    for field in partial_fields.iter() {
        let name = field.name.to_string();
        indices.insert(name, 0);
    }

    match invariant_decl {
        InvariantDecl::Invariant {
            field_name,
            depends_on,
            quants,
            condition,
            specifically,
            params,
            predicate,
            params_span: _,
        } => {
            let pf = get_partial_field_by_name(partial_fields, &field_name.to_string());
            let pf = pf.unwrap();

            let field_name_string = field_name.to_string();
            let idx = indices[&field_name_string];
            *indices.get_mut(&field_name_string).unwrap() = idx + 1;

            let partial_type = &pf.partial_types[idx];

            let predname = get_pred_typename(main_name, field_name);

            let k_type = get_constant_type(main_name, depends_on, quants, used_type_params);
            let tmp_k = Ident::new("declare_struct_with_invariants_tmp_k", Span::call_site());
            let tmp_v = Ident::new("declare_struct_with_invariants_tmp_v", Span::call_site());
            let tmp_g = Ident::new("declare_struct_with_invariants_tmp_g", Span::call_site());

            let quant_idents = quants.iter().map(|pat_type| match &*pat_type.pat {
                Pat::Ident(pat_ident) => &pat_ident.ident,
                _ => panic!("expect Pat::Ident"),
            });
            let all_idents: Vec<&Ident> = depends_on.iter().chain(quant_idents).collect();
            let k_pat = maybe_tuple(&all_idents);

            let v_pats: Vec<&Pat> = params
                .iter()
                .map(|fn_arg| match &fn_arg.kind {
                    FnArgKind::Typed(p) => &*p.pat,
                    _ => {
                        panic!("should have been ruled out by check_invdecl_params_match");
                    }
                })
                .collect();

            let type_params = &sdi.item_struct.generics.params;
            let where_clause = &sdi.item_struct.generics.where_clause;
            let vis = &sdi.item_struct.vis;

            let span = field_name.span();

            let mut e_stream_conjuncts = vec![];

            let specifically_expr = if let Some(specifically) = specifically {
                quote_spanned! { specifically.span() => (#specifically) }
            } else {
                quote_spanned! { field_name.span() => self.#field_name }
            };

            if partial_type.is_atomic_ghost {
                let v_type = &partial_type.concrete_args[0];
                let g_type = &partial_type.concrete_args[1];
                let v_pat = &v_pats[0];
                let g_pat = &v_pats[1];

                // TODO make it possible to configure open-ness?

                stream.extend(quote_spanned! { predicate.span() =>
                    #vis struct #predname { }
                    impl<#type_params> vstd::atomic_ghost::AtomicInvariantPredicate<#k_type, #v_type, #g_type> for #predname #where_clause {
                        open spec fn atomic_inv(#tmp_k: #k_type, #tmp_v: #v_type, #tmp_g: #g_type) -> bool {
                            let #k_pat = #tmp_k;
                            let #v_pat = #tmp_v;
                            let #g_pat = #tmp_g;
                            #predicate
                        }
                    }
                });

                e_stream_conjuncts.push(quote_spanned! { predicate.span() =>
                    #specifically_expr.well_formed()
                })
            } else {
                let v_type = maybe_tuple(&partial_type.concrete_args);
                let v_pat = maybe_tuple(&v_pats);
                stream.extend(quote_spanned! { predicate.span() =>
                    #vis struct #predname { }
                    impl<#type_params> vstd::invariant::InvariantPredicate<#k_type, #v_type> for #predname #where_clause {
                        open spec fn inv(#tmp_k: #k_type, #tmp_v: #v_type) -> bool {
                            let #k_pat = #tmp_k;
                            let #v_pat = #tmp_v;
                            #predicate
                        }
                    }
                });
            }

            for (i, dep) in depends_on.iter().enumerate() {
                let field_access = if depends_on.len() + quants.len() == 1 {
                    TokenStream::new()
                } else {
                    let j = Member::Unnamed(Index { index: i as u32, span: dep.span() });
                    quote_spanned! { dep.span() => .#j }
                };
                e_stream_conjuncts.push(quote_spanned_builtin! { builtin, dep.span() =>
                    #builtin::equal(#specifically_expr.constant()#field_access, self.#dep)
                });
            }
            for (i, quant) in quants.iter().enumerate() {
                let field_access = if depends_on.len() + quants.len() == 1 {
                    TokenStream::new()
                } else {
                    let i = i + depends_on.len();
                    let j = Member::Unnamed(Index { index: i as u32, span: quant.span() });
                    quote_spanned! { quant.span() => .#j }
                };
                let quant_pat = &quant.pat;
                e_stream_conjuncts.push(quote_spanned_builtin! { builtin, quant.span() =>
                    #builtin::equal(#specifically_expr.constant()#field_access, #quant_pat)
                });
            }

            if e_stream_conjuncts.len() > 0 {
                let mut e_stream = e_stream_conjuncts[0].clone();
                for e in e_stream_conjuncts.iter().skip(1) {
                    e_stream.extend(quote_spanned! { e.span() => && #e });
                }

                if let Some(cond) = condition {
                    e_stream = quote_spanned_builtin! { builtin, span =>
                        #builtin::imply(
                            #cond,
                            #e_stream
                        )
                    }
                }
                if quants.len() > 0 {
                    e_stream = quote_spanned_builtin! { builtin, span =>
                        #builtin::forall(|#(#quants),*|
                            #builtin::with_triggers(
                                ((#specifically_expr,),),
                                #e_stream
                            )
                        )
                    };
                }

                wf_stream.extend(quote_spanned! { span =>
                    && #e_stream
                });
            }
        }
        InvariantDecl::NormalExpr(e) => {
            wf_stream.extend(quote_spanned! { e.span() =>
                && #e
            });
        }
    }
}

fn output_wf(sdi: &SDI, stream: &mut TokenStream, wf_body_stream: TokenStream) {
    let wf_sig = &sdi.wf_sig;
    let wf_vis = &sdi.wf_vis;
    let type_params = &sdi.item_struct.generics.params;
    let where_clause = &sdi.item_struct.generics.where_clause;
    let self_type = get_self_type(&sdi.item_struct);
    stream.extend(quote! {
        impl <#type_params> #self_type #where_clause {
            // Something like `pub open spec fn well_formed(&self) -> bool`
            #wf_vis #wf_sig {
                #wf_body_stream
            }
        }
    });
}

fn output_field_type_alias(
    main_name: &str,
    vis: &Visibility,
    stream: &mut TokenStream,
    field: &Field,
    used_type_params: &HashMap<String, Vec<GenericParam>>,
) {
    let field_ident = field.ident.as_ref().unwrap();
    let alias = get_type_alias(main_name, field_ident, used_type_params);
    let field_ty = &field.ty;

    stream.extend(quote! {
        #vis type #alias = #field_ty;
    });
}

// Defs

fn get_pred_typename(main_name: &str, field_name: &Ident) -> Ident {
    Ident::new(
        &format!("InvariantPredicate_auto_{:}_{:}", main_name, field_name.to_string()),
        Span::call_site(),
    )
}

fn get_type_alias(
    main_name: &str,
    field_ident: &Ident,
    used_type_params: &HashMap<String, Vec<GenericParam>>,
) -> TokenStream {
    let ident = Ident::new(
        &format!("FieldType_{:}_{:}", main_name, field_ident.to_string()),
        Span::call_site(),
    );
    let utp = used_type_params.get(&field_ident.to_string()).unwrap();
    if utp.len() == 0 {
        quote! { #ident }
    } else {
        let p = remove_bounds_vec(utp);
        quote! { #ident<#p> }
    }
}

fn get_constant_type(
    main_name: &str,
    depends_on: &Vec<Ident>,
    quants: &Vec<PatType>,
    used_type_params: &HashMap<String, Vec<GenericParam>>,
) -> Type {
    let t1 = depends_on.iter().map(|dep| get_type_alias(main_name, dep, used_type_params));
    let t2 = quants.iter().map(|pat_type| {
        let ty = &pat_type.ty;
        quote! { #ty }
    });
    Type::Verbatim(maybe_tuple(&t1.chain(t2).collect()))
}

// Analyzing types, modifying them

fn get_partial_types(ty: &Type) -> parse::Result<Vec<PartialType>> {
    let mut fptv = FindPartialTypeVisitor { ptypes: vec![], errors: vec![] };
    fptv.visit_type(ty);
    let FindPartialTypeVisitor { errors, ptypes } = fptv;

    combine_errors_or_ok(errors)?;

    let c = count_infers(ty);
    let expected_c = 2 * ptypes.len();
    if c != expected_c {
        return Err(Error::new(
            ty.span(),
            "struct_with_invariants: cannot handle this type (expected 2 placeholder arguments)",
        ));
    }

    Ok(ptypes)
}

struct FindPartialTypeVisitor {
    ptypes: Vec<PartialType>,
    errors: Vec<Error>,
}

impl<'ast> Visit<'ast> for FindPartialTypeVisitor {
    fn visit_type_path(&mut self, type_path: &'ast TypePath) {
        let cargs = get_concrete_args(type_path);
        match cargs {
            Err(e) => {
                self.errors.push(e);
                return;
            }
            Ok(None) => {
                visit::visit_type_path(self, type_path);
            }
            Ok(Some(ptype)) => {
                self.ptypes.push(ptype);
            }
        };
    }

    fn visit_type_infer(&mut self, infer: &TypeInfer) {
        self.errors.push(Error::new(
            infer.span(),
            "struct_with_invariants: cannot handle placeholders here",
        ));
    }
}

fn get_concrete_args(type_path: &TypePath) -> parse::Result<Option<PartialType>> {
    match &type_path.path.segments.last().unwrap().arguments {
        PathArguments::AngleBracketed(abga) => {
            let mut infer_count = 0;
            let mut concrete_args: Vec<Type> = Vec::new();

            let mut args_iter = abga.args.iter();

            let last_ident = type_path.path.segments.last().unwrap().ident.to_string();
            let is_atomic_ghost = match get_builtin_concrete_arg(&last_ident) {
                Some(a) => {
                    concrete_args.push(a);
                    true
                }
                None if &last_ident == "AtomicPtr" => {
                    let ty_opt = args_iter.next();
                    let Some(ty) = ty_opt else {
                        return Err(Error::new(type_path.span(), "AtomicPtr expects arguments"));
                    };
                    concrete_args.push(Type::Verbatim(quote! { *mut #ty }));
                    true
                }
                None => false,
            };

            // For AtomicPtr, we skip the first argument
            // (which was pulled out of the iterator earlier)
            for arg in args_iter {
                if let GenericArgument::Type(arg_type) = arg {
                    if let Type::Infer(_) = arg_type {
                        infer_count += 1;
                    } else {
                        concrete_args.push(arg_type.clone());
                    }
                }
            }

            if infer_count == 0 {
                Ok(None)
            } else if infer_count != 2 {
                Err(Error::new(type_path.span(), "struct_with_invariants: cannot handle this type"))
            } else if is_atomic_ghost && concrete_args.len() != 2 {
                Err(Error::new(type_path.span(), "struct_with_invariants: cannot handle this type"))
            } else {
                Ok(Some(PartialType { concrete_args, is_atomic_ghost }))
            }
        }
        _ => Ok(None),
    }
}

fn get_builtin_concrete_arg(name: &str) -> Option<Type> {
    match name {
        "AtomicBool" => Some(Type::Verbatim(quote! { bool })),
        "AtomicU64" => Some(Type::Verbatim(quote! { u64 })),
        "AtomicU32" => Some(Type::Verbatim(quote! { u32 })),
        "AtomicU16" => Some(Type::Verbatim(quote! { u16 })),
        "AtomicU8" => Some(Type::Verbatim(quote! { u8 })),
        "AtomicUsize" => Some(Type::Verbatim(quote! { usize })),
        "AtomicI64" => Some(Type::Verbatim(quote! { i64 })),
        "AtomicI32" => Some(Type::Verbatim(quote! { i32 })),
        "AtomicI16" => Some(Type::Verbatim(quote! { i16 })),
        "AtomicI8" => Some(Type::Verbatim(quote! { i8 })),
        "AtomicIsize" => Some(Type::Verbatim(quote! { isize })),
        _ => None,
    }
}

fn fill_in_type(
    ty: &Type,
    main_name: &str,
    inv_decls: Vec<&InvariantDecl>,
    used_type_params: &HashMap<String, Vec<GenericParam>>,
) -> Type {
    let mut typs = vec![];

    for inv_decl in inv_decls {
        let (field_name, depends_on, quants) = match inv_decl {
            InvariantDecl::Invariant { field_name, depends_on, quants, .. } => {
                (field_name, depends_on, quants)
            }
            _ => {
                panic!("fill_in_type expected InvariantDecl::Invariant");
            }
        };
        let pred = get_pred_typename(main_name, field_name);
        typs.push(get_constant_type(main_name, depends_on, quants, used_type_params));
        typs.push(Type::Verbatim(quote! { #pred }));
    }

    fill_in_infers(ty, typs)
}

// Misc

fn get_partial_field_by_name<'a>(
    partial_fields: &'a Vec<PartialField>,
    name: &str,
) -> Option<&'a PartialField> {
    for pf in partial_fields.iter() {
        if pf.name.to_string() == name {
            return Some(pf);
        }
    }
    None
}

fn get_field_by_name<'a>(fields: &'a Vec<Field>, name: &str) -> Option<&'a Field> {
    for f in fields.iter() {
        if f.ident.as_ref().unwrap().to_string() == name {
            return Some(f);
        }
    }
    None
}

fn get_invariant_decls_by_name<'a>(
    invariant_decls: &'a Vec<InvariantDecl>,
    name: &str,
) -> Vec<&'a InvariantDecl> {
    let mut res = Vec::new();
    for invdecl in invariant_decls.iter() {
        if let InvariantDecl::Invariant { field_name, .. } = invdecl {
            if field_name.to_string() == name {
                res.push(invdecl);
            }
        }
    }
    res
}

fn maybe_tuple<T>(v: &Vec<T>) -> TokenStream
where
    T: ToTokens,
{
    if v.len() == 1 {
        let x = &v[0];
        quote! { #x }
    } else {
        quote! { ( #(#v),* ) }
    }
}

fn count_infers(ty: &Type) -> usize {
    let mut iv = InferVisitor { count: 0 };
    iv.visit_type(ty);
    iv.count
}

struct InferVisitor {
    count: usize,
}

impl<'ast> Visit<'ast> for InferVisitor {
    fn visit_type_infer(&mut self, _i: &'ast TypeInfer) {
        self.count += 1;
    }
}

fn fill_in_infers(ty: &Type, v: Vec<Type>) -> Type {
    let mut fiv = FillInferVisitor { v: v.into_iter() };
    let mut ty = ty.clone();
    fiv.visit_type_mut(&mut ty);
    assert!(fiv.v.next().is_none());
    ty
}

struct FillInferVisitor {
    v: std::vec::IntoIter<Type>,
}

impl VisitMut for FillInferVisitor {
    fn visit_type_mut(&mut self, ty: &mut Type) {
        let is_infer = match ty {
            Type::Infer(_) => true,
            _ => false,
        };
        if is_infer {
            *ty = self.v.next().unwrap();
        } else {
            visit_mut::visit_type_mut(self, ty);
        }
    }
}

fn fields_contains(fields: &Vec<Field>, name: &str) -> bool {
    for field in fields.iter() {
        if field.ident.as_ref().unwrap().to_string() == name {
            return true;
        }
    }
    false
}

fn get_self_type(item_struct: &ItemStruct) -> Type {
    let ident = &item_struct.ident;
    if item_struct.generics.params.len() > 0 {
        let p = remove_bounds(&item_struct.generics.params);
        Type::Verbatim(quote! {
            #ident<#p>
        })
    } else {
        Type::Verbatim(quote! {
            #ident
        })
    }
}

fn remove_bounds_vec(p: &Vec<GenericParam>) -> TokenStream {
    let mut toks = TokenStream::new();
    for (i, generic_param) in p.iter().enumerate() {
        match generic_param {
            GenericParam::Type(tp) => {
                tp.ident.to_tokens(&mut toks);
            }
            GenericParam::Lifetime(ld) => {
                ld.lifetime.to_tokens(&mut toks);
            }
            GenericParam::Const(c) => {
                c.ident.to_tokens(&mut toks);
            }
        }

        if i + 1 < p.len() {
            toks.extend(quote! { , });
        }
    }
    toks
}

fn remove_bounds(p: &Punctuated<GenericParam, Comma>) -> TokenStream {
    let mut toks = TokenStream::new();
    for (i, generic_param) in p.iter().enumerate() {
        match generic_param {
            GenericParam::Type(tp) => {
                tp.ident.to_tokens(&mut toks);
            }
            GenericParam::Lifetime(ld) => {
                ld.lifetime.to_tokens(&mut toks);
            }
            GenericParam::Const(c) => {
                c.ident.to_tokens(&mut toks);
            }
        }

        if i + 1 < p.len() {
            toks.extend(quote! { , });
        }
    }
    toks
}

fn is_first_param_self(sig: &Signature) -> bool {
    if sig.inputs.len() == 0 {
        return false;
    }
    match &sig.inputs[0].kind {
        FnArgKind::Receiver(Receiver {
            attrs: _,
            reference: _,
            mutability: None,
            self_token: _,
        }) => true,
        _ => false,
    }
}

fn is_spec(sig: &Signature) -> bool {
    match &sig.mode {
        FnMode::Spec(_) | FnMode::SpecChecked(_) => true,
        FnMode::Proof(_) | FnMode::Exec(_) | FnMode::Default => false,
    }
}

fn generic_param_to_string(gp: &GenericParam) -> String {
    match gp {
        GenericParam::Type(tp) => tp.ident.to_string(),
        GenericParam::Const(cp) => cp.ident.to_string(),
        GenericParam::Lifetime(l) => "'".to_string() + &l.lifetime.ident.to_string(),
    }
}

fn get_params_used_in_type(params: &Punctuated<GenericParam, Comma>, ty: &Type) -> HashSet<String> {
    let mut hs = HashSet::new();
    for p in params.iter() {
        hs.insert(generic_param_to_string(p));
    }
    let mut upv = UsedParamsVisitor { params: hs, result: HashSet::new() };
    upv.visit_type(ty);
    upv.result
}

struct UsedParamsVisitor {
    params: HashSet<String>,
    result: HashSet<String>,
}

impl<'ast> Visit<'ast> for UsedParamsVisitor {
    fn visit_type_path(&mut self, type_path: &TypePath) {
        let TypePath { qself, path } = type_path;
        if qself.is_none()
            && path.leading_colon.is_none()
            && path.segments.len() == 1
            && path.segments[0].arguments == PathArguments::None
        {
            let id = path.segments[0].ident.to_string();
            if self.params.contains(&id) {
                self.result.insert(id);
            }
        }

        visit::visit_type_path(self, type_path);
    }

    fn visit_lifetime(&mut self, lt: &Lifetime) {
        let id = "'".to_string() + &lt.ident.to_string();
        self.result.insert(id);
    }
}

pub fn combine_errors_or_ok(errors: Vec<Error>) -> parse::Result<()> {
    let mut res = Ok(());
    for e in errors {
        match res {
            Ok(()) => {
                res = Err(e);
            }
            Err(e0) => {
                let mut e0 = e0;
                e0.combine(e);
                res = Err(e0);
            }
        }
    }
    res
}
