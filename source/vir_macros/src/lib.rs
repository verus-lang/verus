use synstructure::quote;

fn to_node_inner(
    s: synstructure::Structure,
    attribute: Option<proc_macro2::TokenStream>,
) -> proc_macro2::TokenStream {
    let input = s.ast();

    let mut name_override = None;

    let (attr_args, trait_impl): (Option<proc_macro2::TokenStream>, bool) =
        if let Some(attr) = attribute {
            let attr_args = if !attr.is_empty() { Some(attr.clone()) } else { None };
            (attr_args, false)
        } else {
            let attr_args = match input
                .attrs
                .iter()
                .find(|attr| match attr.path().get_ident() {
                    Some(attr_ident) if attr_ident == "to_node" => true,
                    _ => false,
                })
                .map(|attr| attr.meta.clone())
            {
                Some(syn::Meta::List(args)) => Some(args.tokens.clone()),
                Some(otherwise) => {
                    let err = format!("Invalid to_node attribute: {:?}", otherwise);
                    return quote! { compile_error!(#err) };
                }
                None => None,
            };
            (attr_args, true)
        };

    if let Some(args) = attr_args {
        let parser = syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated;
        use syn::parse::Parser;
        let parsed_args = parser.parse2(args).expect("invalid macro input");
        for arg in parsed_args.iter() {
            match arg {
                syn::Meta::NameValue(syn::MetaNameValue { path, value, .. }) => {
                    if let Some(param) = path.get_ident() {
                        if param == "name" {
                            if let syn::Expr::Lit(syn::ExprLit {
                                lit: syn::Lit::Str(lit_str),
                                attrs: _,
                            }) = value
                            {
                                name_override = Some(lit_str.value().clone());
                                continue;
                            }
                        }
                    }
                    let err = format!("Invalid to_node attribute: {:?}", path);
                    return quote! { compile_error!(#err) };
                }
                other => {
                    let err = format!("Invalid to_node attribute: {:?}", other);
                    return quote! { compile_error!(#err) };
                }
            }
        }
    }

    let is_enum = match input.data {
        syn::Data::Struct(_) => false,
        syn::Data::Enum(_) => true,
        syn::Data::Union(_) => {
            return quote! { compile_error!("ToDebugSNode derive doesn't support unions") };
        }
    };

    let name = if let Some(name_override) = name_override {
        name_override
    } else {
        let mut name = input.ident.to_string();
        if name.chars().last() == Some('X') {
            name.pop();
        }
        name
    };

    let field_arms: proc_macro2::TokenStream = s.each_variant(|v| {
        let mut stmts = vec![];
        if is_enum {
            let variant_name = &v.ast().ident.to_string();
            stmts.push(quote!(nodes.push(::sise::Node::Atom(#variant_name.to_string()));));
        }
        for bi in v.bindings() {
            if let Some(field_name) = &bi.ast().ident {
                let field_name = field_name.to_string();
                stmts.push(quote!(nodes.push(::sise::Node::Atom(format!(":{}", #field_name.to_string())));));
            }
            stmts.push(quote!(nodes.push(crate::printer::ToDebugSNode::to_node(#bi, opts.clone()));));
        }
        stmts.into_iter().collect::<proc_macro2::TokenStream>()
    });

    if trait_impl {
        s.gen_impl(quote! {
            #[automatically_derived]
            gen impl crate::printer::ToDebugSNode for @Self {
                fn to_node(&self, opts: &crate::printer::ToDebugSNodeOpts) -> ::sise::Node {
                    let mut nodes = vec![];
                    nodes.push(::sise::Node::Atom(#name.to_string()));
                    match *self {
                        #field_arms
                    }
                    ::sise::Node::List(nodes)
                }
            }
        })
    } else {
        let item_name = &input.ident;
        quote! {
            #input

            #[automatically_derived]
            impl #item_name {
                pub fn to_node_inner(&self, opts: &crate::printer::ToDebugSNodeOpts) -> ::sise::Node {
                    let mut nodes = vec![];
                    nodes.push(::sise::Node::Atom(#name.to_string()));
                    match *self {
                        #field_arms
                    }
                    ::sise::Node::List(nodes)
                }
            }
        }
    }
}

fn to_node_m(s: synstructure::Structure) -> proc_macro2::TokenStream {
    to_node_inner(s, None)
}

fn to_node_impl_m(
    attr: proc_macro2::TokenStream,
    s: synstructure::Structure,
) -> proc_macro2::TokenStream {
    to_node_inner(s, Some(attr))
}

synstructure::decl_derive!([ToDebugSNode, attributes(to_node)] => to_node_m);

synstructure::decl_attribute!([to_node_impl] => to_node_impl_m);
