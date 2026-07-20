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
    let (excluded_fields, closed) = match parse_make_spec_type_attr(attr) {
        Ok(parsed) => parsed,
        Err(err) => return err.to_compile_error().into(),
    };

    let input: DeriveInput = match syn::parse(item) {
        Ok(input) => input,
        Err(err) => return err.to_compile_error().into(),
    };

    // Validate input
    if let Err(err) = validate_input(&input) {
        return err.to_compile_error().into();
    }

    match make_spec_type_impl(input, excluded_fields, closed) {
        Ok(tokens) => tokens,
        Err(err) => err.to_compile_error().into(),
    }
}

fn make_spec_type_impl(
    input: DeriveInput,
    excluded_fields: HashSet<String>,
    closed: bool,
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
            closed,
            impl_generics,
            ty_generics,
            where_clause,
        ),
        Data::Enum(data_enum) => generate_enum_impls(
            name,
            &spec_name,
            data_enum,
            &excluded_fields,
            closed,
            impl_generics,
            ty_generics,
            where_clause,
        ),
        Data::Union(_) => {
            return Err(Error::new_spanned(&input, "Union types are not supported"));
        }
    };

    let output = quote_vstd! { vstd =>
        #vstd::prelude::verus! {
            #input
            #spec_data
            #deep_view_impl
        }
    };

    Ok(output.into())
}

/// Parse the `make_spec_type` attribute arguments. Accepts a comma-separated list of:
/// - `exclude(field1, field2, ...)` — struct fields to omit from the spec type, and
/// - `closed` — generate `closed spec fn` views (visible only in the defining module), so the
///   macro can be applied to types with `pub(crate)`/private fields without leaking them via an
///   `open spec` body. The generated spec *type*'s fields stay `pub`, so callers can still project
///   the view (`x@.0`); only the *computation* of the view is hidden.
fn parse_make_spec_type_attr(attr: TokenStream) -> Result<(HashSet<String>, bool), Error> {
    if attr.is_empty() {
        return Ok((HashSet::new(), false));
    }

    let metas: Punctuated<Meta, Token![,]> =
        syn::parse::Parser::parse(Punctuated::<Meta, Token![,]>::parse_terminated, attr)?;

    let mut excluded_fields = HashSet::new();
    let mut closed = false;

    for meta in metas {
        match meta {
            Meta::List(meta_list) if meta_list.path.is_ident("exclude") => {
                let fields = meta_list
                    .parse_args_with(Punctuated::<Ident, Token![,]>::parse_terminated)
                    .map(|nested| nested.into_iter().map(|ident| ident.to_string()))?;
                excluded_fields.extend(fields);
            }
            Meta::Path(path) if path.is_ident("exclude") => {
                return Err(Error::new_spanned(
                    path,
                    "exclude attribute requires parameters: exclude(field1, field2, ...)",
                ));
            }
            Meta::Path(path) if path.is_ident("closed") => {
                closed = true;
            }
            other => {
                return Err(Error::new_spanned(
                    other,
                    "make_spec_type only accepts 'exclude(...)' and/or 'closed'",
                ));
            }
        }
    }

    Ok((excluded_fields, closed))
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
    generate_field_access_expr(quote! { self.#field_name }, ty)
}

/// `deep_view()` of an arbitrary field-access expression (e.g. `self.field` or `self.0`),
/// dereferencing first when the field is a reference type.
fn generate_field_access_expr(
    access: proc_macro2::TokenStream,
    ty: &Type,
) -> proc_macro2::TokenStream {
    if matches!(ty, Type::Reference(_)) {
        quote! { (*#access).deep_view() }
    } else {
        quote! { #access.deep_view() }
    }
}

fn generate_struct_impls(
    name: &Ident,
    spec_name: &Ident,
    data_struct: &syn::DataStruct,
    excluded_fields: &HashSet<String>,
    closed: bool,
    impl_generics: syn::ImplGenerics,
    ty_generics: syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
    let (spec_data, deep_view_body) = match &data_struct.fields {
        // Named-field struct: `XSpec { field: <T as DeepView>::V, ... }`.
        Fields::Named(_) => {
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
            (
                quote! {
                    #[cfg(verus_keep_ghost)]
                    pub ghost struct #spec_name {
                        #(#spec_fields),*
                    }
                },
                quote! { #spec_name { #(#impl_fields),* } },
            )
        }
        // Tuple struct: `XSpec(<T0 as DeepView>::V, ...)`. Field exclusion is named-only, so it
        // does not apply here (consistent with tuple enum variants).
        Fields::Unnamed(fields_unnamed) => {
            let spec_fields = fields_unnamed.unnamed.iter().map(|f| {
                let field_type = generate_spec_field_type(&f.ty);
                quote! { pub #field_type }
            });
            let impl_fields = fields_unnamed.unnamed.iter().enumerate().map(|(i, f)| {
                let idx = syn::Index::from(i);
                generate_field_access_expr(quote! { self.#idx }, &f.ty)
            });
            (
                quote! {
                    #[cfg(verus_keep_ghost)]
                    pub ghost struct #spec_name ( #(#spec_fields),* );
                },
                quote! { #spec_name ( #(#impl_fields),* ) },
            )
        }
        // Unit struct: the spec type is also a unit struct.
        Fields::Unit => (
            quote! {
                #[cfg(verus_keep_ghost)]
                pub ghost struct #spec_name;
            },
            quote! { #spec_name },
        ),
    };

    let deep_view_impl = generate_trait_impls(
        name,
        spec_name,
        closed,
        impl_generics,
        ty_generics,
        where_clause,
        deep_view_body,
    );

    (spec_data, deep_view_impl)
}

fn generate_enum_impls(
    name: &Ident,
    spec_name: &Ident,
    data_enum: &syn::DataEnum,
    excluded_fields: &HashSet<String>,
    closed: bool,
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
        closed,
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
    closed: bool,
    impl_generics: syn::ImplGenerics,
    ty_generics: syn::TypeGenerics,
    where_clause: Option<&syn::WhereClause>,
    deep_view_body: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    // `closed` views can read `pub(crate)`/private fields without leaking them (the body is only
    // visible in the defining module); `open` views require fully-`pub` fields. `View::view`
    // simply forwards to `deep_view`, so it can stay `open` regardless.
    let deep_view_vis = if closed {
        quote! { closed }
    } else {
        quote! { open }
    };
    quote! {
        #[cfg(verus_keep_ghost)]
        impl #impl_generics DeepView for #name #ty_generics #where_clause {
            type V = #spec_name;

            #deep_view_vis spec fn deep_view(&self) -> Self::V {
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

    let output = quote_vstd! { vstd =>
        #vstd::prelude::verus! {
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
