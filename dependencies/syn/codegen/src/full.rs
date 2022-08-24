use proc_macro2::TokenStream;
use quote::quote;

pub fn get_macro() -> TokenStream {
    quote! {
        #[cfg(feature = "full")]
        macro_rules! full {
            ($e:expr) => {
                $e
            };
        }

        #[cfg(all(feature = "derive", not(feature = "full")))]
        macro_rules! full {
            ($e:expr) => {
                unreachable!()
            };
        }
    }
}
