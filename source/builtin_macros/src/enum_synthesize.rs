use std::collections::HashMap;

#[cfg(verus_keep_ghost)]
use syn_verus::parse_macro_input;

use syn_verus::{spanned::Spanned, Ident, Item, ItemEnum};

use crate::EraseGhost;

use quote::{quote, quote_spanned};

#[cfg(verus_keep_ghost)]
use quote::TokenStreamExt;

#[cfg(verus_keep_ghost)]
pub(crate) fn attribute_verus_enum_synthesize(
    erase_ghost: &EraseGhost,
    _attr: proc_macro::TokenStream,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    use quote::ToTokens;
    let rejoined_stream = crate::syntax::rejoin_tokens(stream.clone());
    let mut enum_: ItemEnum = parse_macro_input!(rejoined_stream as ItemEnum);

    let mut new_stream = proc_macro2::TokenStream::new();

    let stream: proc_macro2::TokenStream = stream.into();
    new_stream.append_all(stream);
    if let Some(item) = visit_item_enum_synthesize(erase_ghost, &mut enum_) {
        item.to_tokens(&mut new_stream)
    }

    proc_macro::TokenStream::from(new_stream)
}

#[cfg(not(verus_keep_ghost))]
pub(crate) fn attribute_verus_enum_synthesize(
    _erase_ghost: &EraseGhost,
    _attr: proc_macro::TokenStream,
    stream: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    stream
}

pub(crate) fn visit_item_enum_synthesize(
    erase_ghost: &EraseGhost,
    enum_: &mut ItemEnum,
) -> Option<Item> {
    let mut allow_inconsistent_fields = false;

    enum_.attrs.retain(|attr| {
        if let syn_verus::AttrStyle::Outer = attr.style {
            match &attr.path.segments.iter().map(|x| &x.ident).collect::<Vec<_>>()[..] {
                [attr_name] if attr_name.to_string() == "allow" => {
                    if attr.tokens.to_string() == "(inconsistent_fields)" {
                        allow_inconsistent_fields = true;
                        return false;
                    }
                }
                _ => (),
            }
        }
        true
    });

    if erase_ghost.erase_all() {
        return None;
    }

    #[derive(PartialEq, Eq, Hash, Debug, Clone)]
    enum FieldName {
        Named(syn_verus::Ident),
        Unnamed(usize),
    }

    #[derive(PartialEq, Eq, Debug, Clone)]
    struct FieldInfo {
        ty: syn_verus::Type,
        vis: syn_verus::Visibility,
    }

    impl FieldInfo {
        fn from(field: &syn_verus::Field) -> FieldInfo {
            FieldInfo { ty: field.ty.clone(), vis: field.vis.clone() }
        }
    }

    let mut direct_fields: HashMap<FieldName, (FieldInfo, Vec<Ident>)> = HashMap::new();
    let mut all_fields: Vec<(Ident, FieldName, FieldInfo)> = Vec::new();
    let mut invalid_fields: Vec<Ident> = Vec::new();
    for variant in &enum_.variants {
        match &variant.fields {
            syn_verus::Fields::Named(named) => {
                for field in &named.named {
                    let ident = field.ident.as_ref().expect("named field").clone();
                    let name = FieldName::Named(ident.clone());
                    let info = FieldInfo::from(field);
                    use std::collections::hash_map::Entry;
                    match direct_fields.entry(name.clone()) {
                        Entry::Occupied(mut occ) => {
                            if occ.get().0 != info {
                                occ.remove_entry();
                                invalid_fields.push(ident);
                            } else {
                                occ.get_mut().1.push(variant.ident.clone());
                            }
                        }
                        Entry::Vacant(vac) => {
                            vac.insert((info.clone(), vec![variant.ident.clone()]));
                        }
                    }
                    all_fields.push((variant.ident.clone(), name.clone(), info));
                }
            }
            syn_verus::Fields::Unnamed(unnamed) => {
                for (i, field) in unnamed.unnamed.iter().enumerate() {
                    let name = FieldName::Unnamed(i);
                    let info = FieldInfo::from(field);
                    use std::collections::hash_map::Entry;
                    match direct_fields.entry(name.clone()) {
                        Entry::Occupied(mut occ) => {
                            if occ.get().0 != info {
                                occ.remove_entry();
                            } else {
                                occ.get_mut().1.push(variant.ident.clone());
                            }
                        }
                        Entry::Vacant(vac) => {
                            vac.insert((info.clone(), vec![variant.ident.clone()]));
                        }
                    }
                    all_fields.push((variant.ident.clone(), name.clone(), info));
                }
            }
            syn_verus::Fields::Unit => {}
        }
    }

    #[cfg(verus_keep_ghost)]
    if !erase_ghost.erase() && !allow_inconsistent_fields {
        for invalid_field in invalid_fields {
            proc_macro::Diagnostic::spanned(enum_.span().unwrap(), proc_macro::Level::Warning, {
                format!("field `{}` has inconsistent type or visibility in different variants\n->{} syntax will not be available for this field\nuse #[allow(inconsistent_fields)] on the struct to silence the warnign", &invalid_field, &invalid_field)
            }).emit();
        }
    }

    let enum_vis_pub = !matches!(enum_.vis, syn_verus::Visibility::Inherited);
    if direct_fields.len() != 0 || all_fields.len() != 0 {
        let enum_ident = &enum_.ident;
        let methods_direct = direct_fields
            .iter()
            .map(|(name, (info, variants))| {
                let method_ident = match name {
                    FieldName::Named(named) => quote::format_ident!("arrow_{}", named),
                    FieldName::Unnamed(unnamed) => {
                        quote::format_ident!("arrow_{}", unnamed)
                    }
                };
                let field_str = match name {
                    FieldName::Named(named) => named.to_string(),
                    FieldName::Unnamed(unnamed) => unnamed.to_string(),
                };
                let ty_ = &info.ty;
                let vis = enum_.vis.clone();

                let publish = if enum_vis_pub {
                    quote! {
                        #[verus::internal(open)]
                    }
                } else {
                    quote! {}
                };

                assert!(!variants.is_empty());
                if variants.len() == 1 {
                    let variant_ident = variants[0].to_string();
                    quote_spanned_builtin! { builtin, enum_.span() =>
                        #[cfg(verus_keep_ghost)]
                        #[allow(non_snake_case)]
                        #[verus::internal(verus_macro)]
                        #[verus::internal(spec)]
                        #[verifier::inline]
                        #publish
                        #vis fn #method_ident(self) -> #ty_ {
                            #builtin::get_variant_field(self, #variant_ident, #field_str)
                        }
                    }
                } else {
                    quote_spanned! { enum_.span() =>
                        #[cfg(verus_keep_ghost)]
                        #[allow(non_snake_case)]
                        #[verus::internal(verus_macro)]
                        #[verus::internal(spec)]
                        #[verus::internal(get_field_many_variants)]
                        #[verifier::external]
                        #publish
                        #vis fn #method_ident(self) -> #ty_ {
                            unimplemented!()
                        }
                    }
                }
            })
            .collect::<proc_macro2::TokenStream>();

        let methods_all = all_fields
            .iter()
            .map(|(variant, name, info)| {
                let method_ident = match name {
                    FieldName::Named(named) => {
                        quote::format_ident!("arrow_{}_{}", variant, named)
                    }
                    FieldName::Unnamed(unnamed) => {
                        quote::format_ident!("arrow_{}_{}", variant, unnamed)
                    }
                };
                let field_str = match name {
                    FieldName::Named(named) => named.to_string(),
                    FieldName::Unnamed(unnamed) => unnamed.to_string(),
                };
                let ty_ = &info.ty;
                let vis = enum_.vis.clone();

                let publish = if enum_vis_pub {
                    quote! {
                        #[verus::internal(open)]
                    }
                } else {
                    quote! {}
                };

                let variant_ident = variant.to_string();
                quote_spanned_builtin! { builtin, enum_.span() =>
                    #[cfg(verus_keep_ghost)]
                    #[allow(non_snake_case)]
                    #[verus::internal(verus_macro)]
                    #[verus::internal(spec)]
                    #[verifier::inline]
                    #publish
                    #vis fn #method_ident(self) -> #ty_ {
                        #builtin::get_variant_field(self, #variant_ident, #field_str)
                    }
                }
            })
            .collect::<proc_macro2::TokenStream>();

        let mut methods = methods_direct;
        methods.extend(methods_all.into_iter());

        let (impl_generics, ty_generics, where_clause) = enum_.generics.split_for_impl();
        Some(Item::Verbatim(quote_spanned! { enum_.span() =>
            #[verus::internal(verus_macro)]
            impl #impl_generics #enum_ident #ty_generics #where_clause {
                #methods
            }
        }))
    } else {
        None
    }
}
