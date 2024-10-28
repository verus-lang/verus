use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::{quote_spanned, ToTokens};
use std::sync::atomic::{AtomicBool, Ordering};

pub static IS_VSTD: AtomicBool = AtomicBool::new(false);
pub static IS_CORE: AtomicBool = AtomicBool::new(false);

pub fn set_is_vstd(b: bool) {
    IS_VSTD.store(b, Ordering::Relaxed);
}

pub fn set_is_core(b: bool) {
    IS_CORE.store(b, Ordering::Relaxed);
}

pub struct Vstd(pub Span);

impl ToTokens for Vstd {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        if IS_CORE.load(Ordering::Relaxed) {
            tokens.extend(quote_spanned! { self.0 => crate::vstd });
        } else if IS_VSTD.load(Ordering::Relaxed) {
            tokens.extend(quote_spanned! { self.0 => crate });
        } else {
            tokens.extend(quote_spanned! { self.0 => ::vstd });
        }
    }
}

macro_rules! quote_spanned_vstd {
    ($b:ident, $span:expr => $($tt:tt)*) => {
        {
            let sp = $span;
            let $b = crate::vstd_path::Vstd(sp);
            ::quote::quote_spanned!{ sp => $($tt)* }
        }
    }
}

macro_rules! quote_vstd {
    ($b:ident => $($tt:tt)*) => {
        {
            let sp = ::proc_macro2::Span::call_site();
            let $b = crate::vstd_path::Vstd(sp);
            ::quote::quote_spanned!{ sp => $($tt)* }
        }
    }
}
