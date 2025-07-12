use proc_macro::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;
use syn::{
    Data, DeriveInput, Error, Fields, GenericArgument, GenericParam, Ident, Meta, PathArguments,
    Token, Type, punctuated::Punctuated,
};

/// Generates a spec type and implements DeepView/View traits for a struct or enum.
///
/// # Supported Features
/// - Structs
/// - Enums with unit, tuple, and struct variants
/// - Generic types and lifetimes
/// - Nested collections (Vec, HashSet) and references
/// - Field exclusion with `exclude(field1, field2, ...)` for struct fields only
///
/// # Limitations
/// - Union types are not supported
/// - Cannot exclude enum variants (only struct fields can be excluded)
/// - Cannot exclude tuple variant fields (only named fields)
/// - All field types must implement DeepView trait
/// - No support for generic parameters
///
/// # Example
/// ```
/// #[make_spec_type(exclude(private_field))]
/// pub struct MyStruct<'a> {
///     pub id: u32,
///     pub data: Vec<String>,
///     pub private_field: String, // Excluded from spec
/// }
/// ```
pub fn make_spec_type(attr: TokenStream, item: TokenStream) -> TokenStream {
    let excluded_fields: HashSet<String> = if attr.is_empty() {
        HashSet::new()
    } else {
        match syn::parse(attr) {
            Ok(meta) => match parse_excluded_fields(meta) {
                Ok(fields) => fields,
                Err(err) => return err.to_compile_error().into(),
            },
            Err(err) => return err.to_compile_error().into(),
        }
    };

    let input: DeriveInput = match syn::parse(item) {
        Ok(input) => input,
        Err(err) => return err.to_compile_error().into(),
    };

    // Validate input
    if let Err(err) = validate_input(&input) {
        return err.to_compile_error().into();
    }

    match make_spec_type_impl(input, excluded_fields) {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error().into(),
    }
}

fn make_spec_type_impl(
    input: DeriveInput,
    excluded_fields: HashSet<String>,
) -> Result<TokenStream, Error> {
    // Validate that excluded fields exist
    if !excluded_fields.is_empty() {
        validate_excluded_fields(&input.data, &excluded_fields)?;
    }

    let name = &input.ident;
    let spec_name = format_ident!("{}Spec", name);
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let (spec_data, deep_view_impl) = match &input.data {
        Data::Struct(data_struct) => generate_struct_impls(
            name,
            &spec_name,
            data_struct,
            &excluded_fields,
            impl_generics,
            ty_generics,
            where_clause,
        ),
        Data::Enum(data_enum) => generate_enum_impls(
            name,
            &spec_name,
            data_enum,
            &excluded_fields,
            impl_generics,
            ty_generics,
            where_clause,
        ),
        Data::Union(_) => {
            return Err(Error::new_spanned(&input, "Union types are not supported"));
        }
    };

    let output = quote! {
        ::builtin_macros::verus! {
            #input
            #spec_data
            #deep_view_impl
        }
    };

    Ok(output.into())
}

fn parse_excluded_fields(meta: Meta) -> Result<HashSet<String>, Error> {
    match meta {
        Meta::List(meta_list) if meta_list.path.is_ident("exclude") => Ok(meta_list
            .parse_args_with(Punctuated::<Ident, Token![,]>::parse_terminated)
            .map(|nested| nested.into_iter().map(|ident| ident.to_string()).collect())
            .unwrap_or_default()),
        Meta::Path(path) if path.is_ident("exclude") => Err(Error::new_spanned(
            path,
            "exclude attribute requires parameters: exclude(field1, field2, ...)",
        )),
        _ => Err(Error::new_spanned(
            meta,
            "make_spec_type only accepts 'exclude' attribute or no parameters",
        )),
    }
}

fn validate_excluded_fields(data: &Data, excluded_fields: &HashSet<String>) -> Result<(), Error> {
    let mut actual_fields = HashSet::new();

    match data {
        Data::Struct(data_struct) => {
            for field in &data_struct.fields {
                if let Some(ident) = &field.ident {
                    actual_fields.insert(ident.to_string());
                }
            }
        }
        Data::Enum(data_enum) => {
            for variant in &data_enum.variants {
                if let Fields::Named(fields_named) = &variant.fields {
                    for field in &fields_named.named {
                        if let Some(ident) = &field.ident {
                            actual_fields.insert(ident.to_string());
                        }
                    }
                }
            }
        }
        Data::Union(_) => {}
    }

    for excluded_field in excluded_fields {
        if !actual_fields.contains(excluded_field) {
            return Err(Error::new(
                proc_macro2::Span::call_site(),
                format!("Field '{}' does not exist and cannot be excluded", excluded_field),
            ));
        }
    }

    Ok(())
}

fn validate_input(input: &DeriveInput) -> Result<(), Error> {
    // Check for generic type parameters
    if input.generics.params.iter().any(|param| matches!(param, GenericParam::Type(_))) {
        return Err(Error::new_spanned(
            &input.generics,
            "Generic type parameters are not supported in make_spec_type macro",
        ));
    }

    // Check for self-referential types
    if contains_self_reference_in_data(&input.data, &input.ident) {
        return Err(Error::new_spanned(
            &input,
            "Self-referential types are not supported in make_spec_type macro. Please implement spec type and DeepView and View implementations manually.",
        ));
    }

    Ok(())
}

fn is_field_excluded(field_name: &Option<Ident>, excluded_fields: &HashSet<String>) -> bool {
    field_name.as_ref().map_or(false, |name| excluded_fields.contains(&name.to_string()))
}

fn generate_spec_field_type(ty: &Type) -> proc_macro2::TokenStream {
    let ftype = strip_references_from_type(ty);
    quote! { <#ftype as DeepView>::V }
}

fn generate_field_access(field_name: &Ident, ty: &Type) -> proc_macro2::TokenStream {
    if matches!(ty, Type::Reference(_)) {
        quote! { (*self.#field_name).deep_view() }
    } else {
        quote! { self.#field_name.deep_view() }
    }
}

fn generate_struct_impls(
    name: &Ident,
    spec_name: &Ident,
    data_struct: &syn::DataStruct,
    excluded_fields: &HashSet<String>,
    impl_generics: syn::ImplGenerics,
    ty_generics: syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
    let spec_fields = data_struct.fields.iter().filter_map(|f| {
        if is_field_excluded(&f.ident, excluded_fields) {
            None
        } else {
            let fname = &f.ident;
            let field_type = generate_spec_field_type(&f.ty);
            Some(quote! { pub #fname : #field_type })
        }
    });

    let impl_fields = data_struct.fields.iter().filter_map(|f| {
        if is_field_excluded(&f.ident, excluded_fields) {
            None
        } else {
            let fname = f.ident.as_ref().unwrap();
            let field_access = generate_field_access(fname, &f.ty);
            Some(quote! { #fname: #field_access })
        }
    });

    let spec_data = quote! {
        #[cfg(verus_keep_ghost)]
        pub ghost struct #spec_name {
            #(#spec_fields),*
        }
    };

    let deep_view_impl = generate_trait_impls(
        name,
        spec_name,
        impl_generics,
        ty_generics,
        where_clause,
        quote! {
            #spec_name {
                #(#impl_fields),*
            }
        },
    );

    (spec_data, deep_view_impl)
}

fn generate_enum_impls(
    name: &Ident,
    spec_name: &Ident,
    data_enum: &syn::DataEnum,
    excluded_fields: &HashSet<String>,
    impl_generics: syn::ImplGenerics,
    ty_generics: syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
    let spec_variants = data_enum.variants.iter().map(|variant| {
        let vname = &variant.ident;
        generate_spec_variant_fields(vname, &variant.fields, excluded_fields)
    });

    let match_arms = data_enum.variants.iter().map(|variant| {
        let vname = &variant.ident;
        generate_match_arm(spec_name, vname, &variant.fields)
    });

    let spec_data = quote! {
        #[cfg(verus_keep_ghost)]
        pub ghost enum #spec_name {
            #(#spec_variants),*
        }
    };

    let deep_view_impl = generate_trait_impls(
        name,
        spec_name,
        impl_generics,
        ty_generics,
        where_clause,
        quote! {
            match *self {
                #(#match_arms),*
            }
        },
    );

    (spec_data, deep_view_impl)
}

fn generate_spec_variant_fields(
    vname: &Ident,
    fields: &Fields,
    excluded_fields: &HashSet<String>,
) -> proc_macro2::TokenStream {
    match fields {
        Fields::Named(fields_named) => {
            let fields = fields_named.named.iter().filter_map(|f| {
                if is_field_excluded(&f.ident, excluded_fields) {
                    None
                } else {
                    let fname = &f.ident;
                    let field_type = generate_spec_field_type(&f.ty);
                    Some(quote! { #fname : #field_type })
                }
            });
            quote! { #vname { #(#fields),* } }
        }
        Fields::Unnamed(fields_unnamed) => {
            let fields = fields_unnamed.unnamed.iter().map(|f| generate_spec_field_type(&f.ty));
            quote! { #vname ( #(#fields),* ) }
        }
        Fields::Unit => quote! { #vname },
    }
}

fn generate_match_arm(
    spec_name: &Ident,
    vname: &Ident,
    fields: &Fields,
) -> proc_macro2::TokenStream {
    match fields {
        Fields::Named(fields_named) => {
            let field_names = fields_named.named.iter().map(|f| &f.ident);
            let field_views = fields_named.named.iter().map(|f| {
                let fname = &f.ident;
                quote! { #fname: #fname.deep_view() }
            });
            quote! {
                Self::#vname { #(#field_names),* } => #spec_name::#vname {
                    #(#field_views),*
                }
            }
        }
        Fields::Unnamed(fields_unnamed) => {
            let field_bindings: Vec<_> =
                (0..fields_unnamed.unnamed.len()).map(|i| format_ident!("f{}", i)).collect();
            let field_views = field_bindings.iter().map(|ident| quote! { #ident.deep_view() });
            quote! {
                Self::#vname(#(#field_bindings),*) => #spec_name::#vname(#(#field_views),*)
            }
        }
        Fields::Unit => quote! { Self::#vname => #spec_name::#vname },
    }
}

fn generate_trait_impls(
    name: &Ident,
    spec_name: &Ident,
    impl_generics: syn::ImplGenerics,
    ty_generics: syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
    deep_view_body: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    quote! {
        #[cfg(verus_keep_ghost)]
        impl #impl_generics DeepView for #name #ty_generics #where_clause {
            type V = #spec_name;

            open spec fn deep_view(&self) -> Self::V {
                #deep_view_body
            }
        }

        #[cfg(verus_keep_ghost)]
        impl #impl_generics View for #name #ty_generics #where_clause {
            type V = <Self as DeepView>::V;

            open spec fn view(&self) -> Self::V {
                self.deep_view()
            }
        }
    }
}

fn contains_self_reference_in_data(data: &Data, self_name: &syn::Ident) -> bool {
    match data {
        Data::Struct(data_struct) => {
            data_struct.fields.iter().any(|f| contains_self_reference(&f.ty, self_name))
        }
        Data::Enum(data_enum) => data_enum
            .variants
            .iter()
            .any(|variant| fields_contain_self_reference(&variant.fields, self_name)),
        Data::Union(_) => false,
    }
}

fn fields_contain_self_reference(fields: &Fields, self_name: &syn::Ident) -> bool {
    match fields {
        Fields::Named(fields_named) => {
            fields_named.named.iter().any(|f| contains_self_reference(&f.ty, self_name))
        }
        Fields::Unnamed(fields_unnamed) => {
            fields_unnamed.unnamed.iter().any(|f| contains_self_reference(&f.ty, self_name))
        }
        Fields::Unit => false,
    }
}

fn contains_self_reference(ty: &Type, self_name: &syn::Ident) -> bool {
    match ty {
        Type::Reference(type_ref) => contains_self_reference(&type_ref.elem, self_name),
        Type::Path(type_path) => {
            if let Some(segment) = type_path.path.segments.first() {
                if segment.ident == *self_name {
                    return true;
                }
                if let PathArguments::AngleBracketed(args) = &segment.arguments {
                    for arg in &args.args {
                        if let GenericArgument::Type(inner_ty) = arg {
                            if contains_self_reference(inner_ty, self_name) {
                                return true;
                            }
                        }
                    }
                }
            }
            false
        }
        Type::Slice(type_slice) => contains_self_reference(&type_slice.elem, self_name),
        Type::Tuple(type_tuple) => {
            type_tuple.elems.iter().any(|elem| contains_self_reference(elem, self_name))
        }
        _ => false,
    }
}

fn strip_references_from_type(ty: &Type) -> Type {
    match ty {
        Type::Reference(type_ref) => {
            // Check if this is &str or &'a str and convert to String
            if is_str_reference(type_ref) {
                syn::parse2(quote! { String }).unwrap()
            } else {
                strip_references_from_type(&type_ref.elem)
            }
        }
        Type::Path(type_path) => {
            let mut new_path = type_path.clone();
            for segment in &mut new_path.path.segments {
                if let PathArguments::AngleBracketed(ref mut args) = segment.arguments {
                    args.args = args
                        .args
                        .iter()
                        .map(|arg| match arg {
                            GenericArgument::Type(inner_ty) => {
                                GenericArgument::Type(strip_references_from_type(inner_ty))
                            }
                            GenericArgument::Lifetime(_) => {
                                GenericArgument::Lifetime(syn::parse2(quote! { 'static }).unwrap())
                            }
                            _ => arg.clone(),
                        })
                        .collect();
                }
            }
            Type::Path(new_path)
        }
        Type::Slice(type_slice) => {
            let elem_type = strip_references_from_type(&type_slice.elem);
            syn::parse2(quote! { Vec<#elem_type> }).unwrap()
        }
        Type::Tuple(type_tuple) => {
            let mut new_tuple = type_tuple.clone();
            new_tuple.elems = new_tuple.elems.iter().map(strip_references_from_type).collect();
            Type::Tuple(new_tuple)
        }
        _ => ty.clone(),
    }
}

fn is_str_reference(type_ref: &syn::TypeReference) -> bool {
    match &*type_ref.elem {
        Type::Path(type_path) => {
            type_path.path.segments.len() == 1
                && type_path.path.segments.first().unwrap().ident == "str"
        }
        _ => false,
    }
}

/// Implements DeepView and View traits where the view is the type itself.
///
/// Use this for types that are already "spec-like" and don't need transformation,
/// such as primitive types or types that should be viewed as themselves.
///
/// # Supported Features
/// - Structs with any field types
/// - Enums with any variant types
/// - Generic types and lifetimes
///
/// # Limitations
/// - No customization options available
/// - All fields are included in the view (no exclusions)
/// - Type must be copyable for the implementation to work correctly
///
/// # Example
/// ```
/// #[self_view]
/// pub enum Status {
///     Active,
///     Inactive,
///     Pending { reason: String },
/// }
/// ```
pub fn self_view(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return Error::new_spanned(
            proc_macro2::TokenStream::from(attr),
            "self_view macro does not accept any parameters",
        )
        .to_compile_error()
        .into();
    }

    match self_view_impl(item) {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error().into(),
    }
}

fn self_view_impl(item: TokenStream) -> Result<TokenStream, Error> {
    let input: DeriveInput = syn::parse(item)?;
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let output = quote! {
        ::builtin_macros::verus! {
            #input

            #[cfg(verus_keep_ghost)]
            impl #impl_generics DeepView for #name #ty_generics #where_clause {
                type V = Self;

                #[verifier::inline]
                #[verus::internal(spec)]
                open spec fn deep_view(&self) -> Self::V {
                    *self
                }
            }

            #[cfg(verus_keep_ghost)]
            impl #impl_generics View for #name #ty_generics #where_clause {
                type V = <Self as DeepView>::V;

                #[verifier::inline]
                #[verus::internal(spec)]
                open spec fn view(&self) -> Self::V {
                    self.deep_view()
                }
            }
        }
    };

    Ok(output.into())
}
