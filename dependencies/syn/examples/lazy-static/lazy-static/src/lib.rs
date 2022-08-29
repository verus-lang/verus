#![feature(proc_macro_diagnostic)]

use proc_macro::TokenStream;
use quote::{quote, quote_spanned};
use syn::parse::{Parse, ParseStream, Result};
use syn::spanned::Spanned;
use syn::{parse_macro_input, Expr, Ident, Token, Type, Visibility};

/// Parses the following syntax, which aligns with the input of the real
/// `lazy_static` crate.
///
///     lazy_static! {
///         $VISIBILITY static ref $NAME: $TYPE = $EXPR;
///     }
///
/// For example:
///
///     lazy_static! {
///         static ref USERNAME: Regex = Regex::new("^[a-z0-9_-]{3,16}$").unwrap();
///     }
struct LazyStatic {
    visibility: Visibility,
    name: Ident,
    ty: Type,
    init: Expr,
}

impl Parse for LazyStatic {
    fn parse(input: ParseStream) -> Result<Self> {
        let visibility: Visibility = input.parse()?;
        input.parse::<Token![static]>()?;
        input.parse::<Token![ref]>()?;
        let name: Ident = input.parse()?;
        input.parse::<Token![:]>()?;
        let ty: Type = input.parse()?;
        input.parse::<Token![=]>()?;
        let init: Expr = input.parse()?;
        input.parse::<Token![;]>()?;
        Ok(LazyStatic {
            visibility,
            name,
            ty,
            init,
        })
    }
}

#[proc_macro]
pub fn lazy_static(input: TokenStream) -> TokenStream {
    let LazyStatic {
        visibility,
        name,
        ty,
        init,
    } = parse_macro_input!(input as LazyStatic);

    // The warning looks like this.
    //
    //     warning: come on, pick a more creative name
    //       --> src/main.rs:10:16
    //        |
    //     10 |     static ref FOO: String = "lazy_static".to_owned();
    //        |                ^^^
    if name == "FOO" {
        name.span()
            .unwrap()
            .warning("come on, pick a more creative name")
            .emit();
    }

    // The error looks like this.
    //
    //     error: I can't think of a legitimate use for lazily initializing the value `()`
    //       --> src/main.rs:10:27
    //        |
    //     10 |     static ref UNIT: () = ();
    //        |                           ^^
    if let Expr::Tuple(ref init) = init {
        if init.elems.is_empty() {
            init.span()
                .unwrap()
                .error("I can't think of a legitimate use for lazily initializing the value `()`")
                .emit();
            return TokenStream::new();
        }
    }

    // Assert that the static type implements Sync. If not, user sees an error
    // message like the following. We span this assertion with the field type's
    // line/column so that the error message appears in the correct place.
    //
    //     error[E0277]: the trait bound `*const (): std::marker::Sync` is not satisfied
    //       --> src/main.rs:10:21
    //        |
    //     10 |     static ref PTR: *const () = &();
    //        |                     ^^^^^^^^^ `*const ()` cannot be shared between threads safely
    let assert_sync = quote_spanned! {ty.span()=>
        struct _AssertSync where #ty: std::marker::Sync;
    };

    // Check for Sized. Not vital to check here, but the error message is less
    // confusing this way than if they get a Sized error in one of our
    // implementation details where it assumes Sized.
    //
    //     error[E0277]: the trait bound `str: std::marker::Sized` is not satisfied
    //       --> src/main.rs:10:19
    //        |
    //     10 |     static ref A: str = "";
    //        |                   ^^^ `str` does not have a constant size known at compile-time
    let assert_sized = quote_spanned! {ty.span()=>
        struct _AssertSized where #ty: std::marker::Sized;
    };

    let init_ptr = quote_spanned! {init.span()=>
        Box::into_raw(Box::new(#init))
    };

    let expanded = quote! {
        #visibility struct #name;

        impl std::ops::Deref for #name {
            type Target = #ty;

            fn deref(&self) -> &#ty {
                #assert_sync
                #assert_sized

                static ONCE: std::sync::Once = std::sync::Once::new();
                static mut VALUE: *mut #ty = 0 as *mut #ty;

                unsafe {
                    ONCE.call_once(|| VALUE = #init_ptr);
                    &*VALUE
                }
            }
        }
    };

    TokenStream::from(expanded)
}
