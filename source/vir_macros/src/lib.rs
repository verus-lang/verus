use synstructure::quote;

fn to_node(s: synstructure::Structure) -> proc_macro2::TokenStream {
    let input = s.ast();

    let mut name_override = None;

    for attr in &input.attrs {
        if let Some(attr_ident) = attr.path.get_ident() {
            if attr_ident == "to_node" {
                match attr.parse_meta() {
                    Ok(syn::Meta::List(args)) => {
                        for arg in args.nested.iter() {
                            match arg {
                                syn::NestedMeta::Meta(syn::Meta::NameValue(
                                    syn::MetaNameValue { path, lit, .. },
                                )) => {
                                    if let Some(param) = path.get_ident() {
                                        if param == "name" {
                                            if let syn::Lit::Str(lit_str) = lit {
                                                name_override = Some(lit_str.value().clone());
                                                continue;
                                            }
                                        }
                                    }
                                    return quote! { compile_error!("Invalid to_node attribute: {}", path) };
                                }
                                syn::NestedMeta::Meta(_) => {
                                    return quote! { compile_error!("Invalid to_node attribute") };
                                }
                                syn::NestedMeta::Lit(lit) => {
                                    return quote! { compile_error!("Invalid to_node attribute: {}", #lit) };
                                }
                            }
                        }
                    }
                    Ok(_) => {
                        return quote! { compile_error!("Invalid to_node attribute") };
                    }
                    Err(err) => {
                        let e_string = format!("{}", err);
                        return quote! { compile_error!("Invalid to_node attribute: {}", #e_string) };
                    }
                }
            }
        }
    }

    let is_enum = match input.data {
        syn::Data::Struct(_) => false,
        syn::Data::Enum(_) => true,
        syn::Data::Union(_) => {
            return quote! { compile_error!("ToNode derive doesn't support unions") };
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
            stmts.push(quote!(nodes.push(crate::printer::ToNode::to_node(#bi));));
        }
        stmts.into_iter().collect::<proc_macro2::TokenStream>()
    });

    let out = s.gen_impl(quote! {
        #[automatically_derived]
        gen impl crate::printer::ToNode for @Self {
            fn to_node(&self) -> ::sise::Node {
                let mut nodes = vec![];
                nodes.push(::sise::Node::Atom(#name.to_string()));
                match *self {
                    #field_arms
                }
                ::sise::Node::List(nodes)
            }
        }
    });

    out
}

synstructure::decl_derive!([ToNode, attributes(to_node)] => to_node);
