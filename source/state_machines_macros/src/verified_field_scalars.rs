//! Exact sparse scalar field owners over the existing checked logical token.
use crate::ast::{Field, ShardableType, SM};
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use verus_syn::Error;

/// Return a nominal owner with a private actual resource. Optional values and
/// collections use separate present/bulk roles and are emitted elsewhere.
pub fn scalar_wrapper(sm: &SM, field: &Field) -> Result<TokenStream, Error> {
    if !matches!(
        field.stype,
        ShardableType::Variable(_)
            | ShardableType::Constant(_)
            | ShardableType::Count
            | ShardableType::PersistentCount
            | ShardableType::PersistentBool
    ) {
        return Err(Error::new(
            field.name.span(),
            "unsupported scalar field owner",
        ));
    }
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let n = &field.name;
    let factory = format_ident!("field_{}", n);
    let getter = format_ident!("value_{}", n);
    let owns = format_ident!("owns_{}", n);
    let ty = field.get_type();
    let count = matches!(
        field.stype,
        ShardableType::Count | ShardableType::PersistentCount
    );
    let observation = if count {
        format_ident!("count")
    } else {
        format_ident!("value")
    };
    let tag = if count {
        quote! {true}
    } else {
        quote! {self.raw.fragment().#owns()}
    };
    let rawtag = if count {
        quote! {true}
    } else {
        quote! {raw.fragment().#owns()}
    };
    let methods = if crate::verified_field_monoids::supported(&field.stype) {
        crate::verified_field_monoids::methods(
            field,
            &quote! {Fragment #types},
            &quote! {Token #types},
            &quote! {Protocol #expr},
        )?
    } else {
        quote! {}
    };
    Ok(quote! {
        #(#attrs)* #[allow(non_camel_case_types)]
        pub tracked struct #n #decl #wc {raw:Token #types}
        impl #decl #n #types #wc {
            #[verifier::type_invariant]
            spec fn invariant(self)->bool {
                #tag && self.raw.fragment()==Fragment #expr::#factory(self.raw.fragment().#getter())
            }
            pub closed spec fn instance_id(&self)->::vstd::resource::Loc {self.raw.loc()}
            pub closed spec fn #observation(&self)->#ty {self.raw.fragment().#getter()}
            pub proof fn borrow_token(tracked &self)->(tracked out:&Token #types)
                ensures out.loc()==self.instance_id(),
                    out.fragment()==Fragment #expr::#factory(self.#observation())
            {::vstd::prelude::use_type_invariant(self);&self.raw}
            proof fn __from_token(tracked raw:Token #types)->(tracked out:Self)
                requires #rawtag,
                    raw.fragment()==Fragment #expr::#factory(raw.fragment().#getter())
                ensures out.instance_id()==raw.loc(),out.#observation()==raw.fragment().#getter()
            {Self{raw}}
            #methods
        }
    })
}
