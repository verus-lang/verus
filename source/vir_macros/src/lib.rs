use synstructure::quote;

fn to_node_inner(
    s: synstructure::Structure,
    attribute: Option<proc_macro2::TokenStream>,
) -> proc_macro2::TokenStream {
    let input = s.ast();

    let mut name_override = None;

    let (attr_args, trait_impl) = if let Some(attr) = attribute {
        let attr_args = if !attr.is_empty() {
            let parser =
                syn::punctuated::Punctuated::<syn::NestedMeta, syn::Token![,]>::parse_terminated;
            use syn::parse::Parser;
            Some(parser.parse2(attr).expect("invalid macro input"))
        } else {
            None
        };
        (attr_args, false)
    } else {
        let attr_args = match input
            .attrs
            .iter()
            .find(|attr| match attr.path.get_ident() {
                Some(attr_ident) if attr_ident == "to_node" => true,
                _ => false,
            })
            .map(|attr| attr.parse_meta())
        {
            Some(Ok(syn::Meta::List(args))) => Some(args.nested),
            Some(Ok(e)) => {
                let err = format!("Invalid to_node attribute: {:?}", e);
                return quote! { compile_error!(#err) };
            }
            Some(Err(err)) => {
                let e_string = format!("Invalid to_node attribute: {}", err);
                return quote! { compile_error!(#e_string) };
            }
            None => None,
        };
        (attr_args, true)
    };

    if let Some(args) = attr_args {
        for arg in args.iter() {
            match arg {
                syn::NestedMeta::Meta(syn::Meta::NameValue(syn::MetaNameValue {
                    path,
                    lit,
                    ..
                })) => {
                    if let Some(param) = path.get_ident() {
                        if param == "name" {
                            if let syn::Lit::Str(lit_str) = lit {
                                name_override = Some(lit_str.value().clone());
                                continue;
                            }
                        }
                    }
                    let err = format!("Invalid to_node attribute: {:?}", path);
                    return quote! { compile_error!(#err) };
                }
                syn::NestedMeta::Meta(_) => {
                    return quote! { compile_error!("Invalid to_node attribute") };
                }
                syn::NestedMeta::Lit(lit) => {
                    let err = format!("Invalid to_node attribute: {:?}", lit);
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
