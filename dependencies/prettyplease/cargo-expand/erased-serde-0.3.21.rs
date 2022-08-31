#![feature(prelude_import)]
#![doc(html_root_url = "https://docs.rs/erased-serde/0.3.21")]
#![deny(unsafe_op_in_unsafe_fn)]
#![allow(
    clippy::derive_partial_eq_without_eq,
    clippy::items_after_statements,
    clippy::manual_map,
    clippy::missing_errors_doc,
    clippy::needless_doctest_main,
    clippy::semicolon_if_nothing_returned,
    clippy::unused_self,
    clippy::wildcard_imports
)]
#[prelude_import]
use std::prelude::rust_2018::*;
#[macro_use]
extern crate std;
mod alloc {
    #[cfg(feature = "std")]
    use std as alloc;
    pub use self::alloc::borrow::ToOwned;
    pub use self::alloc::boxed::Box;
    pub use self::alloc::string::{String, ToString};
    pub use self::alloc::{vec, vec::Vec};
}
#[macro_use]
mod macros {}
mod any {
    use crate::alloc::Box;
    use core::mem;
    #[cfg(not(no_maybe_uninit))]
    use core::mem::MaybeUninit;
    use core::ptr;
    pub struct Any {
        value: Value,
        drop: unsafe fn(&mut Value),
        fingerprint: Fingerprint,
    }
    union Value {
        ptr: *mut (),
        inline: [MaybeUninit<usize>; 2],
    }
    fn is_small<T>() -> bool {
        true && mem::size_of::<T>() <= mem::size_of::<Value>()
            && mem::align_of::<T>() <= mem::align_of::<Value>()
    }
    impl Any {
        pub(crate) unsafe fn new<T>(t: T) -> Self {
            let value: Value;
            let drop: unsafe fn(&mut Value);
            let fingerprint = Fingerprint::of::<T>();
            if is_small::<T>() {
                let mut inline = [MaybeUninit::uninit(); 2];
                unsafe { ptr::write(inline.as_mut_ptr() as *mut T, t) };
                value = Value { inline };
                unsafe fn inline_drop<T>(value: &mut Value) {
                    unsafe { ptr::drop_in_place(value.inline.as_mut_ptr() as *mut T) }
                }
                drop = inline_drop::<T>;
            } else {
                let ptr = Box::into_raw(Box::new(t)) as *mut ();
                value = Value { ptr };
                unsafe fn ptr_drop<T>(value: &mut Value) {
                    mem::drop(unsafe { Box::from_raw(value.ptr as *mut T) });
                }
                drop = ptr_drop::<T>;
            };
            #[cfg(not(feature = "unstable-debug"))] { Any { value, drop, fingerprint } }
        }
        pub(crate) unsafe fn view<T>(&mut self) -> &mut T {
            if true && self.fingerprint != Fingerprint::of::<T>() {
                self.invalid_cast_to::<T>();
            }
            let ptr = if is_small::<T>() {
                unsafe { self.value.inline.as_mut_ptr() as *mut T }
            } else {
                unsafe { self.value.ptr as *mut T }
            };
            unsafe { &mut *ptr }
        }
        pub(crate) unsafe fn take<T>(mut self) -> T {
            if true && self.fingerprint != Fingerprint::of::<T>() {
                self.invalid_cast_to::<T>();
            }
            if is_small::<T>() {
                let ptr = unsafe { self.value.inline.as_mut_ptr() as *mut T };
                let value = unsafe { ptr::read(ptr) };
                mem::forget(self);
                value
            } else {
                let ptr = unsafe { self.value.ptr as *mut T };
                let box_t = unsafe { Box::from_raw(ptr) };
                mem::forget(self);
                *box_t
            }
        }
        #[cfg(not(feature = "unstable-debug"))]
        fn invalid_cast_to<T>(&self) -> ! {
            {
                ::std::rt::begin_panic(
                    "invalid cast; enable `unstable-debug` feature to debug",
                )
            };
        }
    }
    impl Drop for Any {
        fn drop(&mut self) {
            unsafe { (self.drop)(&mut self.value) }
        }
    }
    struct Fingerprint {
        size: usize,
        align: usize,
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::fmt::Debug for Fingerprint {
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match *self {
                Self { size: ref __self_0_0, align: ref __self_0_1 } => {
                    let debug_trait_builder = &mut ::core::fmt::Formatter::debug_struct(
                        f,
                        "Fingerprint",
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "size",
                        &&(*__self_0_0),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "align",
                        &&(*__self_0_1),
                    );
                    ::core::fmt::DebugStruct::finish(debug_trait_builder)
                }
            }
        }
    }
    impl ::core::marker::StructuralEq for Fingerprint {}
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::cmp::Eq for Fingerprint {
        #[inline]
        #[doc(hidden)]
        #[no_coverage]
        fn assert_receiver_is_total_eq(&self) -> () {
            {
                let _: ::core::cmp::AssertParamIsEq<usize>;
                let _: ::core::cmp::AssertParamIsEq<usize>;
            }
        }
    }
    impl ::core::marker::StructuralPartialEq for Fingerprint {}
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::cmp::PartialEq for Fingerprint {
        #[inline]
        fn eq(&self, other: &Fingerprint) -> bool {
            match *other {
                Self { size: ref __self_1_0, align: ref __self_1_1 } => {
                    match *self {
                        Self { size: ref __self_0_0, align: ref __self_0_1 } => {
                            (*__self_0_0) == (*__self_1_0)
                                && (*__self_0_1) == (*__self_1_1)
                        }
                    }
                }
            }
        }
        #[inline]
        fn ne(&self, other: &Fingerprint) -> bool {
            match *other {
                Self { size: ref __self_1_0, align: ref __self_1_1 } => {
                    match *self {
                        Self { size: ref __self_0_0, align: ref __self_0_1 } => {
                            (*__self_0_0) != (*__self_1_0)
                                || (*__self_0_1) != (*__self_1_1)
                        }
                    }
                }
            }
        }
    }
    impl Fingerprint {
        fn of<T>() -> Fingerprint {
            Fingerprint {
                size: mem::size_of::<T>(),
                align: mem::align_of::<T>(),
            }
        }
    }
}
mod de {
    use crate::alloc::*;
    use crate::any::Any;
    use crate::error::Error;
    use crate::map::{OptionExt, ResultExt};
    use core::fmt::{self, Display};
    use serde::serde_if_integer128;
    pub fn deserialize<'de, T>(
        deserializer: &mut dyn Deserializer<'de>,
    ) -> Result<T, Error>
    where
        T: serde::Deserialize<'de>,
    {
        serde::Deserialize::deserialize(deserializer)
    }
    pub trait DeserializeSeed<'de> {
        fn erased_deserialize_seed(
            &mut self,
            d: &mut dyn Deserializer<'de>,
        ) -> Result<Out, Error>;
    }
    pub trait Deserializer<'de> {
        fn erased_deserialize_any(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_bool(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_u8(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_u16(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_u32(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_u64(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_i8(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_i16(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_i32(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_i64(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_i128(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_u128(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_f32(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_f64(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_char(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_str(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_string(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_bytes(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_byte_buf(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_option(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_unit(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_unit_struct(
            &mut self,
            name: &'static str,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_newtype_struct(
            &mut self,
            name: &'static str,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_seq(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_tuple(
            &mut self,
            len: usize,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_map(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_struct(
            &mut self,
            name: &'static str,
            fields: &'static [&'static str],
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_identifier(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_enum(
            &mut self,
            name: &'static str,
            variants: &'static [&'static str],
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_deserialize_ignored_any(
            &mut self,
            v: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>;
        fn erased_is_human_readable(&self) -> bool;
    }
    pub trait Visitor<'de> {
        fn erased_expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result;
        fn erased_visit_bool(&mut self, v: bool) -> Result<Out, Error>;
        fn erased_visit_i8(&mut self, v: i8) -> Result<Out, Error>;
        fn erased_visit_i16(&mut self, v: i16) -> Result<Out, Error>;
        fn erased_visit_i32(&mut self, v: i32) -> Result<Out, Error>;
        fn erased_visit_i64(&mut self, v: i64) -> Result<Out, Error>;
        fn erased_visit_u8(&mut self, v: u8) -> Result<Out, Error>;
        fn erased_visit_u16(&mut self, v: u16) -> Result<Out, Error>;
        fn erased_visit_u32(&mut self, v: u32) -> Result<Out, Error>;
        fn erased_visit_u64(&mut self, v: u64) -> Result<Out, Error>;
        fn erased_visit_i128(&mut self, v: i128) -> Result<Out, Error>;
        fn erased_visit_u128(&mut self, v: u128) -> Result<Out, Error>;
        fn erased_visit_f32(&mut self, v: f32) -> Result<Out, Error>;
        fn erased_visit_f64(&mut self, v: f64) -> Result<Out, Error>;
        fn erased_visit_char(&mut self, v: char) -> Result<Out, Error>;
        fn erased_visit_str(&mut self, v: &str) -> Result<Out, Error>;
        fn erased_visit_borrowed_str(&mut self, v: &'de str) -> Result<Out, Error>;
        #[cfg(any(feature = "std", feature = "alloc"))]
        fn erased_visit_string(&mut self, v: String) -> Result<Out, Error>;
        fn erased_visit_bytes(&mut self, v: &[u8]) -> Result<Out, Error>;
        fn erased_visit_borrowed_bytes(&mut self, v: &'de [u8]) -> Result<Out, Error>;
        #[cfg(any(feature = "std", feature = "alloc"))]
        fn erased_visit_byte_buf(&mut self, v: Vec<u8>) -> Result<Out, Error>;
        fn erased_visit_none(&mut self) -> Result<Out, Error>;
        fn erased_visit_some(
            &mut self,
            d: &mut dyn Deserializer<'de>,
        ) -> Result<Out, Error>;
        fn erased_visit_unit(&mut self) -> Result<Out, Error>;
        fn erased_visit_newtype_struct(
            &mut self,
            d: &mut dyn Deserializer<'de>,
        ) -> Result<Out, Error>;
        fn erased_visit_seq(&mut self, s: &mut dyn SeqAccess<'de>) -> Result<Out, Error>;
        fn erased_visit_map(&mut self, m: &mut dyn MapAccess<'de>) -> Result<Out, Error>;
        fn erased_visit_enum(
            &mut self,
            e: &mut dyn EnumAccess<'de>,
        ) -> Result<Out, Error>;
    }
    pub trait SeqAccess<'de> {
        fn erased_next_element(
            &mut self,
            d: &mut dyn DeserializeSeed<'de>,
        ) -> Result<Option<Out>, Error>;
        fn erased_size_hint(&self) -> Option<usize>;
    }
    pub trait MapAccess<'de> {
        fn erased_next_key(
            &mut self,
            d: &mut dyn DeserializeSeed<'de>,
        ) -> Result<Option<Out>, Error>;
        fn erased_next_value(
            &mut self,
            d: &mut dyn DeserializeSeed<'de>,
        ) -> Result<Out, Error>;
        fn erased_next_entry(
            &mut self,
            key: &mut dyn DeserializeSeed<'de>,
            value: &mut dyn DeserializeSeed<'de>,
        ) -> Result<Option<(Out, Out)>, Error>;
        fn erased_size_hint(&self) -> Option<usize>;
    }
    pub trait EnumAccess<'de> {
        fn erased_variant_seed(
            &mut self,
            d: &mut dyn DeserializeSeed<'de>,
        ) -> Result<(Out, Variant<'de>), Error>;
    }
    impl<'de> dyn Deserializer<'de> {
        pub fn erase<D>(deserializer: D) -> erase::Deserializer<D>
        where
            D: serde::Deserializer<'de>,
        {
            erase::Deserializer {
                state: Some(deserializer),
            }
        }
    }
    pub struct Out(Any);
    impl Out {
        unsafe fn new<T>(t: T) -> Self {
            Out(unsafe { Any::new(t) })
        }
        unsafe fn take<T>(self) -> T {
            unsafe { self.0.take() }
        }
    }
    mod erase {
        pub struct DeserializeSeed<D> {
            pub(crate) state: Option<D>,
        }
        impl<D> DeserializeSeed<D> {
            pub(crate) fn take(&mut self) -> D {
                self.state.take().unwrap()
            }
        }
        pub struct Deserializer<D> {
            pub(crate) state: Option<D>,
        }
        impl<D> Deserializer<D> {
            pub(crate) fn take(&mut self) -> D {
                self.state.take().unwrap()
            }
            pub(crate) fn as_ref(&self) -> &D {
                self.state.as_ref().unwrap()
            }
        }
        pub struct Visitor<D> {
            pub(crate) state: Option<D>,
        }
        impl<D> Visitor<D> {
            pub(crate) fn take(&mut self) -> D {
                self.state.take().unwrap()
            }
            pub(crate) fn as_ref(&self) -> &D {
                self.state.as_ref().unwrap()
            }
        }
        pub struct SeqAccess<D> {
            pub(crate) state: D,
        }
        impl<D> SeqAccess<D> {
            pub(crate) fn as_ref(&self) -> &D {
                &self.state
            }
            pub(crate) fn as_mut(&mut self) -> &mut D {
                &mut self.state
            }
        }
        pub struct MapAccess<D> {
            pub(crate) state: D,
        }
        impl<D> MapAccess<D> {
            pub(crate) fn as_ref(&self) -> &D {
                &self.state
            }
            pub(crate) fn as_mut(&mut self) -> &mut D {
                &mut self.state
            }
        }
        pub struct EnumAccess<D> {
            pub(crate) state: Option<D>,
        }
        impl<D> EnumAccess<D> {
            pub(crate) fn take(&mut self) -> D {
                self.state.take().unwrap()
            }
        }
    }
    impl<'de, T> DeserializeSeed<'de> for erase::DeserializeSeed<T>
    where
        T: serde::de::DeserializeSeed<'de>,
    {
        fn erased_deserialize_seed(
            &mut self,
            deserializer: &mut dyn Deserializer<'de>,
        ) -> Result<Out, Error> {
            unsafe { self.take().deserialize(deserializer).unsafe_map(Out::new) }
        }
    }
    impl<'de, T> Deserializer<'de> for erase::Deserializer<T>
    where
        T: serde::Deserializer<'de>,
    {
        fn erased_deserialize_any(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_any(visitor).map_err(erase)
        }
        fn erased_deserialize_bool(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_bool(visitor).map_err(erase)
        }
        fn erased_deserialize_u8(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_u8(visitor).map_err(erase)
        }
        fn erased_deserialize_u16(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_u16(visitor).map_err(erase)
        }
        fn erased_deserialize_u32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_u32(visitor).map_err(erase)
        }
        fn erased_deserialize_u64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_u64(visitor).map_err(erase)
        }
        fn erased_deserialize_i8(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_i8(visitor).map_err(erase)
        }
        fn erased_deserialize_i16(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_i16(visitor).map_err(erase)
        }
        fn erased_deserialize_i32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_i32(visitor).map_err(erase)
        }
        fn erased_deserialize_i64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_i64(visitor).map_err(erase)
        }
        fn erased_deserialize_i128(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_i128(visitor).map_err(erase)
        }
        fn erased_deserialize_u128(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_u128(visitor).map_err(erase)
        }
        fn erased_deserialize_f32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_f32(visitor).map_err(erase)
        }
        fn erased_deserialize_f64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_f64(visitor).map_err(erase)
        }
        fn erased_deserialize_char(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_char(visitor).map_err(erase)
        }
        fn erased_deserialize_str(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_str(visitor).map_err(erase)
        }
        fn erased_deserialize_string(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_string(visitor).map_err(erase)
        }
        fn erased_deserialize_bytes(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_bytes(visitor).map_err(erase)
        }
        fn erased_deserialize_byte_buf(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_byte_buf(visitor).map_err(erase)
        }
        fn erased_deserialize_option(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_option(visitor).map_err(erase)
        }
        fn erased_deserialize_unit(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_unit(visitor).map_err(erase)
        }
        fn erased_deserialize_unit_struct(
            &mut self,
            name: &'static str,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_unit_struct(name, visitor).map_err(erase)
        }
        fn erased_deserialize_newtype_struct(
            &mut self,
            name: &'static str,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_newtype_struct(name, visitor).map_err(erase)
        }
        fn erased_deserialize_seq(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_seq(visitor).map_err(erase)
        }
        fn erased_deserialize_tuple(
            &mut self,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_tuple(len, visitor).map_err(erase)
        }
        fn erased_deserialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_tuple_struct(name, len, visitor).map_err(erase)
        }
        fn erased_deserialize_map(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_map(visitor).map_err(erase)
        }
        fn erased_deserialize_struct(
            &mut self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_struct(name, fields, visitor).map_err(erase)
        }
        fn erased_deserialize_identifier(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_identifier(visitor).map_err(erase)
        }
        fn erased_deserialize_enum(
            &mut self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_enum(name, variants, visitor).map_err(erase)
        }
        fn erased_deserialize_ignored_any(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            self.take().deserialize_ignored_any(visitor).map_err(erase)
        }
        fn erased_is_human_readable(&self) -> bool {
            self.as_ref().is_human_readable()
        }
    }
    impl<'de, T> Visitor<'de> for erase::Visitor<T>
    where
        T: serde::de::Visitor<'de>,
    {
        fn erased_expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            self.as_ref().expecting(formatter)
        }
        fn erased_visit_bool(&mut self, v: bool) -> Result<Out, Error> {
            unsafe { self.take().visit_bool(v).unsafe_map(Out::new) }
        }
        fn erased_visit_i8(&mut self, v: i8) -> Result<Out, Error> {
            unsafe { self.take().visit_i8(v).unsafe_map(Out::new) }
        }
        fn erased_visit_i16(&mut self, v: i16) -> Result<Out, Error> {
            unsafe { self.take().visit_i16(v).unsafe_map(Out::new) }
        }
        fn erased_visit_i32(&mut self, v: i32) -> Result<Out, Error> {
            unsafe { self.take().visit_i32(v).unsafe_map(Out::new) }
        }
        fn erased_visit_i64(&mut self, v: i64) -> Result<Out, Error> {
            unsafe { self.take().visit_i64(v).unsafe_map(Out::new) }
        }
        fn erased_visit_u8(&mut self, v: u8) -> Result<Out, Error> {
            unsafe { self.take().visit_u8(v).unsafe_map(Out::new) }
        }
        fn erased_visit_u16(&mut self, v: u16) -> Result<Out, Error> {
            unsafe { self.take().visit_u16(v).unsafe_map(Out::new) }
        }
        fn erased_visit_u32(&mut self, v: u32) -> Result<Out, Error> {
            unsafe { self.take().visit_u32(v).unsafe_map(Out::new) }
        }
        fn erased_visit_u64(&mut self, v: u64) -> Result<Out, Error> {
            unsafe { self.take().visit_u64(v).unsafe_map(Out::new) }
        }
        fn erased_visit_i128(&mut self, v: i128) -> Result<Out, Error> {
            unsafe { self.take().visit_i128(v).unsafe_map(Out::new) }
        }
        fn erased_visit_u128(&mut self, v: u128) -> Result<Out, Error> {
            unsafe { self.take().visit_u128(v).unsafe_map(Out::new) }
        }
        fn erased_visit_f32(&mut self, v: f32) -> Result<Out, Error> {
            unsafe { self.take().visit_f32(v).unsafe_map(Out::new) }
        }
        fn erased_visit_f64(&mut self, v: f64) -> Result<Out, Error> {
            unsafe { self.take().visit_f64(v).unsafe_map(Out::new) }
        }
        fn erased_visit_char(&mut self, v: char) -> Result<Out, Error> {
            unsafe { self.take().visit_char(v).unsafe_map(Out::new) }
        }
        fn erased_visit_str(&mut self, v: &str) -> Result<Out, Error> {
            unsafe { self.take().visit_str(v).unsafe_map(Out::new) }
        }
        fn erased_visit_borrowed_str(&mut self, v: &'de str) -> Result<Out, Error> {
            unsafe { self.take().visit_borrowed_str(v).unsafe_map(Out::new) }
        }
        #[cfg(any(feature = "std", feature = "alloc"))]
        fn erased_visit_string(&mut self, v: String) -> Result<Out, Error> {
            unsafe { self.take().visit_string(v).unsafe_map(Out::new) }
        }
        fn erased_visit_bytes(&mut self, v: &[u8]) -> Result<Out, Error> {
            unsafe { self.take().visit_bytes(v).unsafe_map(Out::new) }
        }
        fn erased_visit_borrowed_bytes(&mut self, v: &'de [u8]) -> Result<Out, Error> {
            unsafe { self.take().visit_borrowed_bytes(v).unsafe_map(Out::new) }
        }
        #[cfg(any(feature = "std", feature = "alloc"))]
        fn erased_visit_byte_buf(&mut self, v: Vec<u8>) -> Result<Out, Error> {
            unsafe { self.take().visit_byte_buf(v).unsafe_map(Out::new) }
        }
        fn erased_visit_none(&mut self) -> Result<Out, Error> {
            unsafe { self.take().visit_none().unsafe_map(Out::new) }
        }
        fn erased_visit_some(
            &mut self,
            deserializer: &mut dyn Deserializer<'de>,
        ) -> Result<Out, Error> {
            unsafe { self.take().visit_some(deserializer).unsafe_map(Out::new) }
        }
        fn erased_visit_unit(&mut self) -> Result<Out, Error> {
            unsafe { self.take().visit_unit().unsafe_map(Out::new) }
        }
        fn erased_visit_newtype_struct(
            &mut self,
            deserializer: &mut dyn Deserializer<'de>,
        ) -> Result<Out, Error> {
            unsafe {
                self.take().visit_newtype_struct(deserializer).unsafe_map(Out::new)
            }
        }
        fn erased_visit_seq(
            &mut self,
            seq: &mut dyn SeqAccess<'de>,
        ) -> Result<Out, Error> {
            unsafe { self.take().visit_seq(seq).unsafe_map(Out::new) }
        }
        fn erased_visit_map(
            &mut self,
            map: &mut dyn MapAccess<'de>,
        ) -> Result<Out, Error> {
            unsafe { self.take().visit_map(map).unsafe_map(Out::new) }
        }
        fn erased_visit_enum(
            &mut self,
            data: &mut dyn EnumAccess<'de>,
        ) -> Result<Out, Error> {
            unsafe { self.take().visit_enum(data).unsafe_map(Out::new) }
        }
    }
    impl<'de, T> SeqAccess<'de> for erase::SeqAccess<T>
    where
        T: serde::de::SeqAccess<'de>,
    {
        fn erased_next_element(
            &mut self,
            seed: &mut dyn DeserializeSeed<'de>,
        ) -> Result<Option<Out>, Error> {
            self.as_mut().next_element_seed(seed).map_err(erase)
        }
        fn erased_size_hint(&self) -> Option<usize> {
            self.as_ref().size_hint()
        }
    }
    impl<'de, T> MapAccess<'de> for erase::MapAccess<T>
    where
        T: serde::de::MapAccess<'de>,
    {
        fn erased_next_key(
            &mut self,
            seed: &mut dyn DeserializeSeed<'de>,
        ) -> Result<Option<Out>, Error> {
            self.as_mut().next_key_seed(seed).map_err(erase)
        }
        fn erased_next_value(
            &mut self,
            seed: &mut dyn DeserializeSeed<'de>,
        ) -> Result<Out, Error> {
            self.as_mut().next_value_seed(seed).map_err(erase)
        }
        fn erased_next_entry(
            &mut self,
            k: &mut dyn DeserializeSeed<'de>,
            v: &mut dyn DeserializeSeed<'de>,
        ) -> Result<Option<(Out, Out)>, Error> {
            self.as_mut().next_entry_seed(k, v).map_err(erase)
        }
        fn erased_size_hint(&self) -> Option<usize> {
            self.as_ref().size_hint()
        }
    }
    impl<'de, T> EnumAccess<'de> for erase::EnumAccess<T>
    where
        T: serde::de::EnumAccess<'de>,
    {
        fn erased_variant_seed(
            &mut self,
            seed: &mut dyn DeserializeSeed<'de>,
        ) -> Result<(Out, Variant<'de>), Error> {
            self.take()
                .variant_seed(seed)
                .map(|(out, variant)| {
                    use serde::de::VariantAccess;
                    let erased = Variant {
                        data: unsafe { Any::new(variant) },
                        unit_variant: {
                            unsafe fn unit_variant<'de, T>(a: Any) -> Result<(), Error>
                            where
                                T: serde::de::EnumAccess<'de>,
                            {
                                unsafe {
                                    a.take::<T::Variant>().unit_variant().map_err(erase)
                                }
                            }
                            unit_variant::<T>
                        },
                        visit_newtype: {
                            unsafe fn visit_newtype<'de, T>(
                                a: Any,
                                seed: &mut dyn DeserializeSeed<'de>,
                            ) -> Result<Out, Error>
                            where
                                T: serde::de::EnumAccess<'de>,
                            {
                                unsafe {
                                    a
                                        .take::<T::Variant>()
                                        .newtype_variant_seed(seed)
                                        .map_err(erase)
                                }
                            }
                            visit_newtype::<T>
                        },
                        tuple_variant: {
                            unsafe fn tuple_variant<'de, T>(
                                a: Any,
                                len: usize,
                                visitor: &mut dyn Visitor<'de>,
                            ) -> Result<Out, Error>
                            where
                                T: serde::de::EnumAccess<'de>,
                            {
                                unsafe {
                                    a
                                        .take::<T::Variant>()
                                        .tuple_variant(len, visitor)
                                        .map_err(erase)
                                }
                            }
                            tuple_variant::<T>
                        },
                        struct_variant: {
                            unsafe fn struct_variant<'de, T>(
                                a: Any,
                                fields: &'static [&'static str],
                                visitor: &mut dyn Visitor<'de>,
                            ) -> Result<Out, Error>
                            where
                                T: serde::de::EnumAccess<'de>,
                            {
                                unsafe {
                                    a
                                        .take::<T::Variant>()
                                        .struct_variant(fields, visitor)
                                        .map_err(erase)
                                }
                            }
                            struct_variant::<T>
                        },
                    };
                    (out, erased)
                })
                .map_err(erase)
        }
    }
    impl<'de, 'a> serde::de::DeserializeSeed<'de> for &'a mut dyn DeserializeSeed<'de> {
        type Value = Out;
        fn deserialize<D>(self, deserializer: D) -> Result<Out, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            let mut erased = erase::Deserializer {
                state: Some(deserializer),
            };
            self.erased_deserialize_seed(&mut erased).map_err(unerase)
        }
    }
    impl<'de, 'a> serde::Deserializer<'de> for &'a mut dyn Deserializer<'de> {
        type Error = Error;
        fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_any(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bool(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i128<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u128<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_char(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_str(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_string(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bytes(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_byte_buf(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_option(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_unit(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit_struct<V>(
            self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_unit_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_newtype_struct<V>(
            self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_newtype_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_seq(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_tuple(len, &mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_tuple_struct<V>(
            self,
            name: &'static str,
            len: usize,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_tuple_struct(name, len, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_map(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_struct<V>(
            self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_struct(name, fields, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_identifier(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_enum<V>(
            self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_enum(name, variants, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_ignored_any(&mut erased).unsafe_map(Out::take)
            }
        }
        fn is_human_readable(&self) -> bool {
            self.erased_is_human_readable()
        }
    }
    impl<'de, 'a> serde::Deserializer<'de> for &'a mut (dyn Deserializer<'de> + Send) {
        type Error = Error;
        fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_any(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bool(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i128<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u128<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_char(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_str(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_string(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bytes(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_byte_buf(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_option(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_unit(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit_struct<V>(
            self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_unit_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_newtype_struct<V>(
            self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_newtype_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_seq(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_tuple(len, &mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_tuple_struct<V>(
            self,
            name: &'static str,
            len: usize,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_tuple_struct(name, len, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_map(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_struct<V>(
            self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_struct(name, fields, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_identifier(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_enum<V>(
            self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_enum(name, variants, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_ignored_any(&mut erased).unsafe_map(Out::take)
            }
        }
        fn is_human_readable(&self) -> bool {
            self.erased_is_human_readable()
        }
    }
    impl<'de, 'a> serde::Deserializer<'de> for &'a mut (dyn Deserializer<'de> + Sync) {
        type Error = Error;
        fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_any(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bool(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i128<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u128<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_char(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_str(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_string(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bytes(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_byte_buf(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_option(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_unit(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit_struct<V>(
            self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_unit_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_newtype_struct<V>(
            self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_newtype_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_seq(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_tuple(len, &mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_tuple_struct<V>(
            self,
            name: &'static str,
            len: usize,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_tuple_struct(name, len, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_map(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_struct<V>(
            self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_struct(name, fields, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_identifier(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_enum<V>(
            self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_enum(name, variants, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_ignored_any(&mut erased).unsafe_map(Out::take)
            }
        }
        fn is_human_readable(&self) -> bool {
            self.erased_is_human_readable()
        }
    }
    impl<'de, 'a> serde::Deserializer<'de>
    for &'a mut (dyn Deserializer<'de> + Send + Sync) {
        type Error = Error;
        fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_any(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bool(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i128<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u128<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_char(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_str(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_string(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bytes(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_byte_buf(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_option(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_unit(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit_struct<V>(
            self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_unit_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_newtype_struct<V>(
            self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_newtype_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_seq(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_tuple(len, &mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_tuple_struct<V>(
            self,
            name: &'static str,
            len: usize,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_tuple_struct(name, len, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_map(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_struct<V>(
            self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_struct(name, fields, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_identifier(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_enum<V>(
            self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_enum(name, variants, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_ignored_any(&mut erased).unsafe_map(Out::take)
            }
        }
        fn is_human_readable(&self) -> bool {
            self.erased_is_human_readable()
        }
    }
    impl<'de> serde::Deserializer<'de> for Box<dyn Deserializer<'de>> {
        type Error = Error;
        fn deserialize_any<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_any(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bool<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bool(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u8<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u16<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u32<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u64<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i8<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i16<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i32<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i64<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i128<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u128<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f32<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f64<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_char<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_char(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_str<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_str(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_string<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_string(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bytes<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bytes(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_byte_buf<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_byte_buf(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_option<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_option(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_unit(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit_struct<V>(
            mut self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_unit_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_newtype_struct<V>(
            mut self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_newtype_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_seq<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_seq(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_tuple<V>(
            mut self,
            len: usize,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_tuple(len, &mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_tuple_struct<V>(
            mut self,
            name: &'static str,
            len: usize,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_tuple_struct(name, len, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_map<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_map(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_struct<V>(
            mut self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_struct(name, fields, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_identifier<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_identifier(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_enum<V>(
            mut self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_enum(name, variants, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_ignored_any<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_ignored_any(&mut erased).unsafe_map(Out::take)
            }
        }
        fn is_human_readable(&self) -> bool {
            self.erased_is_human_readable()
        }
    }
    impl<'de> serde::Deserializer<'de> for Box<dyn Deserializer<'de> + Send> {
        type Error = Error;
        fn deserialize_any<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_any(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bool<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bool(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u8<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u16<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u32<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u64<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i8<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i16<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i32<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i64<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i128<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u128<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f32<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f64<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_char<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_char(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_str<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_str(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_string<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_string(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bytes<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bytes(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_byte_buf<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_byte_buf(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_option<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_option(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_unit(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit_struct<V>(
            mut self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_unit_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_newtype_struct<V>(
            mut self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_newtype_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_seq<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_seq(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_tuple<V>(
            mut self,
            len: usize,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_tuple(len, &mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_tuple_struct<V>(
            mut self,
            name: &'static str,
            len: usize,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_tuple_struct(name, len, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_map<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_map(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_struct<V>(
            mut self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_struct(name, fields, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_identifier<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_identifier(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_enum<V>(
            mut self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_enum(name, variants, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_ignored_any<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_ignored_any(&mut erased).unsafe_map(Out::take)
            }
        }
        fn is_human_readable(&self) -> bool {
            self.erased_is_human_readable()
        }
    }
    impl<'de> serde::Deserializer<'de> for Box<dyn Deserializer<'de> + Sync> {
        type Error = Error;
        fn deserialize_any<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_any(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bool<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bool(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u8<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u16<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u32<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u64<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i8<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i16<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i32<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i64<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i128<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u128<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f32<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f64<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_char<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_char(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_str<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_str(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_string<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_string(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bytes<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bytes(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_byte_buf<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_byte_buf(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_option<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_option(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_unit(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit_struct<V>(
            mut self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_unit_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_newtype_struct<V>(
            mut self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_newtype_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_seq<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_seq(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_tuple<V>(
            mut self,
            len: usize,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_tuple(len, &mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_tuple_struct<V>(
            mut self,
            name: &'static str,
            len: usize,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_tuple_struct(name, len, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_map<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_map(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_struct<V>(
            mut self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_struct(name, fields, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_identifier<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_identifier(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_enum<V>(
            mut self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_enum(name, variants, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_ignored_any<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_ignored_any(&mut erased).unsafe_map(Out::take)
            }
        }
        fn is_human_readable(&self) -> bool {
            self.erased_is_human_readable()
        }
    }
    impl<'de> serde::Deserializer<'de> for Box<dyn Deserializer<'de> + Send + Sync> {
        type Error = Error;
        fn deserialize_any<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_any(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bool<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bool(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u8<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u16<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u32<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u64<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i8<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i8(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i16<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i16(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i32<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i64<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_i128<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_i128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_u128<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_u128(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f32<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f32(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_f64<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_f64(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_char<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_char(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_str<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_str(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_string<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_string(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_bytes<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_bytes(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_byte_buf<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_byte_buf(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_option<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_option(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_unit(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_unit_struct<V>(
            mut self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_unit_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_newtype_struct<V>(
            mut self,
            name: &'static str,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_newtype_struct(name, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_seq<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_seq(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_tuple<V>(
            mut self,
            len: usize,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_tuple(len, &mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_tuple_struct<V>(
            mut self,
            name: &'static str,
            len: usize,
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_tuple_struct(name, len, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_map<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe { self.erased_deserialize_map(&mut erased).unsafe_map(Out::take) }
        }
        fn deserialize_struct<V>(
            mut self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_struct(name, fields, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_identifier<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_identifier(&mut erased).unsafe_map(Out::take)
            }
        }
        fn deserialize_enum<V>(
            mut self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self
                    .erased_deserialize_enum(name, variants, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
        fn deserialize_ignored_any<V>(mut self, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                self.erased_deserialize_ignored_any(&mut erased).unsafe_map(Out::take)
            }
        }
        fn is_human_readable(&self) -> bool {
            self.erased_is_human_readable()
        }
    }
    impl<'de, 'a> serde::de::Visitor<'de> for &'a mut dyn Visitor<'de> {
        type Value = Out;
        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            (**self).erased_expecting(formatter)
        }
        fn visit_bool<E>(self, v: bool) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_bool(v).map_err(unerase)
        }
        fn visit_i8<E>(self, v: i8) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_i8(v).map_err(unerase)
        }
        fn visit_i16<E>(self, v: i16) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_i16(v).map_err(unerase)
        }
        fn visit_i32<E>(self, v: i32) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_i32(v).map_err(unerase)
        }
        fn visit_i64<E>(self, v: i64) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_i64(v).map_err(unerase)
        }
        fn visit_u8<E>(self, v: u8) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_u8(v).map_err(unerase)
        }
        fn visit_u16<E>(self, v: u16) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_u16(v).map_err(unerase)
        }
        fn visit_u32<E>(self, v: u32) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_u32(v).map_err(unerase)
        }
        fn visit_u64<E>(self, v: u64) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_u64(v).map_err(unerase)
        }
        fn visit_i128<E>(self, v: i128) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_i128(v).map_err(unerase)
        }
        fn visit_u128<E>(self, v: u128) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_u128(v).map_err(unerase)
        }
        fn visit_f32<E>(self, v: f32) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_f32(v).map_err(unerase)
        }
        fn visit_f64<E>(self, v: f64) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_f64(v).map_err(unerase)
        }
        fn visit_char<E>(self, v: char) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_char(v).map_err(unerase)
        }
        fn visit_str<E>(self, v: &str) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_str(v).map_err(unerase)
        }
        fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_borrowed_str(v).map_err(unerase)
        }
        #[cfg(any(feature = "std", feature = "alloc"))]
        fn visit_string<E>(self, v: String) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_string(v).map_err(unerase)
        }
        fn visit_bytes<E>(self, v: &[u8]) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_bytes(v).map_err(unerase)
        }
        fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_borrowed_bytes(v).map_err(unerase)
        }
        #[cfg(any(feature = "std", feature = "alloc"))]
        fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_byte_buf(v).map_err(unerase)
        }
        fn visit_none<E>(self) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_none().map_err(unerase)
        }
        fn visit_some<D>(self, deserializer: D) -> Result<Out, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            let mut erased = erase::Deserializer {
                state: Some(deserializer),
            };
            self.erased_visit_some(&mut erased).map_err(unerase)
        }
        fn visit_unit<E>(self) -> Result<Out, E>
        where
            E: serde::de::Error,
        {
            self.erased_visit_unit().map_err(unerase)
        }
        fn visit_newtype_struct<D>(self, deserializer: D) -> Result<Out, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            let mut erased = erase::Deserializer {
                state: Some(deserializer),
            };
            self.erased_visit_newtype_struct(&mut erased).map_err(unerase)
        }
        fn visit_seq<V>(self, seq: V) -> Result<Out, V::Error>
        where
            V: serde::de::SeqAccess<'de>,
        {
            let mut erased = erase::SeqAccess { state: seq };
            self.erased_visit_seq(&mut erased).map_err(unerase)
        }
        fn visit_map<V>(self, map: V) -> Result<Out, V::Error>
        where
            V: serde::de::MapAccess<'de>,
        {
            let mut erased = erase::MapAccess { state: map };
            self.erased_visit_map(&mut erased).map_err(unerase)
        }
        fn visit_enum<V>(self, data: V) -> Result<Out, V::Error>
        where
            V: serde::de::EnumAccess<'de>,
        {
            let mut erased = erase::EnumAccess {
                state: Some(data),
            };
            self.erased_visit_enum(&mut erased).map_err(unerase)
        }
    }
    impl<'de, 'a> serde::de::SeqAccess<'de> for &'a mut dyn SeqAccess<'de> {
        type Error = Error;
        fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Error>
        where
            T: serde::de::DeserializeSeed<'de>,
        {
            let mut seed = erase::DeserializeSeed {
                state: Some(seed),
            };
            unsafe {
                (**self)
                    .erased_next_element(&mut seed)
                    .map(|opt| opt.unsafe_map(Out::take))
            }
        }
        fn size_hint(&self) -> Option<usize> {
            (**self).erased_size_hint()
        }
    }
    impl<'de, 'a> serde::de::MapAccess<'de> for &'a mut dyn MapAccess<'de> {
        type Error = Error;
        fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Error>
        where
            K: serde::de::DeserializeSeed<'de>,
        {
            let mut erased = erase::DeserializeSeed {
                state: Some(seed),
            };
            unsafe {
                (**self)
                    .erased_next_key(&mut erased)
                    .map(|opt| opt.unsafe_map(Out::take))
            }
        }
        fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Error>
        where
            V: serde::de::DeserializeSeed<'de>,
        {
            let mut erased = erase::DeserializeSeed {
                state: Some(seed),
            };
            unsafe { (**self).erased_next_value(&mut erased).unsafe_map(Out::take) }
        }
        fn size_hint(&self) -> Option<usize> {
            (**self).erased_size_hint()
        }
    }
    impl<'de, 'a> serde::de::EnumAccess<'de> for &'a mut dyn EnumAccess<'de> {
        type Error = Error;
        type Variant = Variant<'de>;
        fn variant_seed<V>(
            self,
            seed: V,
        ) -> Result<(V::Value, Self::Variant), Self::Error>
        where
            V: serde::de::DeserializeSeed<'de>,
        {
            let mut erased = erase::DeserializeSeed {
                state: Some(seed),
            };
            match self.erased_variant_seed(&mut erased) {
                Ok((out, variant)) => Ok((unsafe { out.take() }, variant)),
                Err(err) => Err(err),
            }
        }
    }
    pub struct Variant<'de> {
        data: Any,
        unit_variant: unsafe fn(Any) -> Result<(), Error>,
        visit_newtype: unsafe fn(
            Any,
            seed: &mut dyn DeserializeSeed<'de>,
        ) -> Result<Out, Error>,
        tuple_variant: unsafe fn(
            Any,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>,
        struct_variant: unsafe fn(
            Any,
            fields: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error>,
    }
    impl<'de> serde::de::VariantAccess<'de> for Variant<'de> {
        type Error = Error;
        fn unit_variant(self) -> Result<(), Error> {
            unsafe { (self.unit_variant)(self.data) }
        }
        fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value, Error>
        where
            T: serde::de::DeserializeSeed<'de>,
        {
            let mut erased = erase::DeserializeSeed {
                state: Some(seed),
            };
            unsafe { (self.visit_newtype)(self.data, &mut erased).unsafe_map(Out::take) }
        }
        fn tuple_variant<V>(self, len: usize, visitor: V) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                (self.tuple_variant)(self.data, len, &mut erased).unsafe_map(Out::take)
            }
        }
        fn struct_variant<V>(
            self,
            fields: &'static [&'static str],
            visitor: V,
        ) -> Result<V::Value, Error>
        where
            V: serde::de::Visitor<'de>,
        {
            let mut erased = erase::Visitor {
                state: Some(visitor),
            };
            unsafe {
                (self.struct_variant)(self.data, fields, &mut erased)
                    .unsafe_map(Out::take)
            }
        }
    }
    impl<'de, 'a> Deserializer<'de> for Box<dyn Deserializer<'de> + 'a> {
        fn erased_deserialize_any(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_any(visitor)
        }
        fn erased_deserialize_bool(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_bool(visitor)
        }
        fn erased_deserialize_u8(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u8(visitor)
        }
        fn erased_deserialize_u16(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u16(visitor)
        }
        fn erased_deserialize_u32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u32(visitor)
        }
        fn erased_deserialize_u64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u64(visitor)
        }
        fn erased_deserialize_i8(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i8(visitor)
        }
        fn erased_deserialize_i16(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i16(visitor)
        }
        fn erased_deserialize_i32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i32(visitor)
        }
        fn erased_deserialize_i64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i64(visitor)
        }
        fn erased_deserialize_i128(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i128(visitor)
        }
        fn erased_deserialize_u128(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u128(visitor)
        }
        fn erased_deserialize_f32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_f32(visitor)
        }
        fn erased_deserialize_f64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_f64(visitor)
        }
        fn erased_deserialize_char(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_char(visitor)
        }
        fn erased_deserialize_str(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_str(visitor)
        }
        fn erased_deserialize_string(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_string(visitor)
        }
        fn erased_deserialize_bytes(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_bytes(visitor)
        }
        fn erased_deserialize_byte_buf(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_byte_buf(visitor)
        }
        fn erased_deserialize_option(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_option(visitor)
        }
        fn erased_deserialize_unit(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_unit(visitor)
        }
        fn erased_deserialize_unit_struct(
            &mut self,
            name: &'static str,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_unit_struct(name, visitor)
        }
        fn erased_deserialize_newtype_struct(
            &mut self,
            name: &'static str,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_newtype_struct(name, visitor)
        }
        fn erased_deserialize_seq(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_seq(visitor)
        }
        fn erased_deserialize_tuple(
            &mut self,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_tuple(len, visitor)
        }
        fn erased_deserialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_tuple_struct(name, len, visitor)
        }
        fn erased_deserialize_map(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_map(visitor)
        }
        fn erased_deserialize_struct(
            &mut self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_struct(name, fields, visitor)
        }
        fn erased_deserialize_identifier(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_identifier(visitor)
        }
        fn erased_deserialize_enum(
            &mut self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_enum(name, variants, visitor)
        }
        fn erased_deserialize_ignored_any(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_ignored_any(visitor)
        }
        fn erased_is_human_readable(&self) -> bool {
            (**self).erased_is_human_readable()
        }
    }
    impl<'de, 'a> Deserializer<'de> for Box<dyn Deserializer<'de> + Send + 'a> {
        fn erased_deserialize_any(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_any(visitor)
        }
        fn erased_deserialize_bool(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_bool(visitor)
        }
        fn erased_deserialize_u8(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u8(visitor)
        }
        fn erased_deserialize_u16(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u16(visitor)
        }
        fn erased_deserialize_u32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u32(visitor)
        }
        fn erased_deserialize_u64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u64(visitor)
        }
        fn erased_deserialize_i8(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i8(visitor)
        }
        fn erased_deserialize_i16(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i16(visitor)
        }
        fn erased_deserialize_i32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i32(visitor)
        }
        fn erased_deserialize_i64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i64(visitor)
        }
        fn erased_deserialize_i128(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i128(visitor)
        }
        fn erased_deserialize_u128(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u128(visitor)
        }
        fn erased_deserialize_f32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_f32(visitor)
        }
        fn erased_deserialize_f64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_f64(visitor)
        }
        fn erased_deserialize_char(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_char(visitor)
        }
        fn erased_deserialize_str(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_str(visitor)
        }
        fn erased_deserialize_string(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_string(visitor)
        }
        fn erased_deserialize_bytes(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_bytes(visitor)
        }
        fn erased_deserialize_byte_buf(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_byte_buf(visitor)
        }
        fn erased_deserialize_option(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_option(visitor)
        }
        fn erased_deserialize_unit(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_unit(visitor)
        }
        fn erased_deserialize_unit_struct(
            &mut self,
            name: &'static str,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_unit_struct(name, visitor)
        }
        fn erased_deserialize_newtype_struct(
            &mut self,
            name: &'static str,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_newtype_struct(name, visitor)
        }
        fn erased_deserialize_seq(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_seq(visitor)
        }
        fn erased_deserialize_tuple(
            &mut self,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_tuple(len, visitor)
        }
        fn erased_deserialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_tuple_struct(name, len, visitor)
        }
        fn erased_deserialize_map(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_map(visitor)
        }
        fn erased_deserialize_struct(
            &mut self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_struct(name, fields, visitor)
        }
        fn erased_deserialize_identifier(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_identifier(visitor)
        }
        fn erased_deserialize_enum(
            &mut self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_enum(name, variants, visitor)
        }
        fn erased_deserialize_ignored_any(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_ignored_any(visitor)
        }
        fn erased_is_human_readable(&self) -> bool {
            (**self).erased_is_human_readable()
        }
    }
    impl<'de, 'a> Deserializer<'de> for Box<dyn Deserializer<'de> + Sync + 'a> {
        fn erased_deserialize_any(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_any(visitor)
        }
        fn erased_deserialize_bool(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_bool(visitor)
        }
        fn erased_deserialize_u8(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u8(visitor)
        }
        fn erased_deserialize_u16(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u16(visitor)
        }
        fn erased_deserialize_u32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u32(visitor)
        }
        fn erased_deserialize_u64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u64(visitor)
        }
        fn erased_deserialize_i8(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i8(visitor)
        }
        fn erased_deserialize_i16(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i16(visitor)
        }
        fn erased_deserialize_i32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i32(visitor)
        }
        fn erased_deserialize_i64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i64(visitor)
        }
        fn erased_deserialize_i128(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i128(visitor)
        }
        fn erased_deserialize_u128(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u128(visitor)
        }
        fn erased_deserialize_f32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_f32(visitor)
        }
        fn erased_deserialize_f64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_f64(visitor)
        }
        fn erased_deserialize_char(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_char(visitor)
        }
        fn erased_deserialize_str(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_str(visitor)
        }
        fn erased_deserialize_string(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_string(visitor)
        }
        fn erased_deserialize_bytes(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_bytes(visitor)
        }
        fn erased_deserialize_byte_buf(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_byte_buf(visitor)
        }
        fn erased_deserialize_option(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_option(visitor)
        }
        fn erased_deserialize_unit(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_unit(visitor)
        }
        fn erased_deserialize_unit_struct(
            &mut self,
            name: &'static str,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_unit_struct(name, visitor)
        }
        fn erased_deserialize_newtype_struct(
            &mut self,
            name: &'static str,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_newtype_struct(name, visitor)
        }
        fn erased_deserialize_seq(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_seq(visitor)
        }
        fn erased_deserialize_tuple(
            &mut self,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_tuple(len, visitor)
        }
        fn erased_deserialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_tuple_struct(name, len, visitor)
        }
        fn erased_deserialize_map(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_map(visitor)
        }
        fn erased_deserialize_struct(
            &mut self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_struct(name, fields, visitor)
        }
        fn erased_deserialize_identifier(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_identifier(visitor)
        }
        fn erased_deserialize_enum(
            &mut self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_enum(name, variants, visitor)
        }
        fn erased_deserialize_ignored_any(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_ignored_any(visitor)
        }
        fn erased_is_human_readable(&self) -> bool {
            (**self).erased_is_human_readable()
        }
    }
    impl<'de, 'a> Deserializer<'de> for Box<dyn Deserializer<'de> + Send + Sync + 'a> {
        fn erased_deserialize_any(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_any(visitor)
        }
        fn erased_deserialize_bool(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_bool(visitor)
        }
        fn erased_deserialize_u8(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u8(visitor)
        }
        fn erased_deserialize_u16(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u16(visitor)
        }
        fn erased_deserialize_u32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u32(visitor)
        }
        fn erased_deserialize_u64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u64(visitor)
        }
        fn erased_deserialize_i8(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i8(visitor)
        }
        fn erased_deserialize_i16(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i16(visitor)
        }
        fn erased_deserialize_i32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i32(visitor)
        }
        fn erased_deserialize_i64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i64(visitor)
        }
        fn erased_deserialize_i128(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i128(visitor)
        }
        fn erased_deserialize_u128(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u128(visitor)
        }
        fn erased_deserialize_f32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_f32(visitor)
        }
        fn erased_deserialize_f64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_f64(visitor)
        }
        fn erased_deserialize_char(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_char(visitor)
        }
        fn erased_deserialize_str(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_str(visitor)
        }
        fn erased_deserialize_string(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_string(visitor)
        }
        fn erased_deserialize_bytes(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_bytes(visitor)
        }
        fn erased_deserialize_byte_buf(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_byte_buf(visitor)
        }
        fn erased_deserialize_option(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_option(visitor)
        }
        fn erased_deserialize_unit(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_unit(visitor)
        }
        fn erased_deserialize_unit_struct(
            &mut self,
            name: &'static str,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_unit_struct(name, visitor)
        }
        fn erased_deserialize_newtype_struct(
            &mut self,
            name: &'static str,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_newtype_struct(name, visitor)
        }
        fn erased_deserialize_seq(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_seq(visitor)
        }
        fn erased_deserialize_tuple(
            &mut self,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_tuple(len, visitor)
        }
        fn erased_deserialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_tuple_struct(name, len, visitor)
        }
        fn erased_deserialize_map(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_map(visitor)
        }
        fn erased_deserialize_struct(
            &mut self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_struct(name, fields, visitor)
        }
        fn erased_deserialize_identifier(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_identifier(visitor)
        }
        fn erased_deserialize_enum(
            &mut self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_enum(name, variants, visitor)
        }
        fn erased_deserialize_ignored_any(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_ignored_any(visitor)
        }
        fn erased_is_human_readable(&self) -> bool {
            (**self).erased_is_human_readable()
        }
    }
    impl<'de, 'a, T: ?Sized + Deserializer<'de>> Deserializer<'de> for &'a mut T {
        fn erased_deserialize_any(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_any(visitor)
        }
        fn erased_deserialize_bool(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_bool(visitor)
        }
        fn erased_deserialize_u8(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u8(visitor)
        }
        fn erased_deserialize_u16(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u16(visitor)
        }
        fn erased_deserialize_u32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u32(visitor)
        }
        fn erased_deserialize_u64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u64(visitor)
        }
        fn erased_deserialize_i8(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i8(visitor)
        }
        fn erased_deserialize_i16(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i16(visitor)
        }
        fn erased_deserialize_i32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i32(visitor)
        }
        fn erased_deserialize_i64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i64(visitor)
        }
        fn erased_deserialize_i128(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_i128(visitor)
        }
        fn erased_deserialize_u128(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_u128(visitor)
        }
        fn erased_deserialize_f32(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_f32(visitor)
        }
        fn erased_deserialize_f64(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_f64(visitor)
        }
        fn erased_deserialize_char(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_char(visitor)
        }
        fn erased_deserialize_str(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_str(visitor)
        }
        fn erased_deserialize_string(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_string(visitor)
        }
        fn erased_deserialize_bytes(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_bytes(visitor)
        }
        fn erased_deserialize_byte_buf(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_byte_buf(visitor)
        }
        fn erased_deserialize_option(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_option(visitor)
        }
        fn erased_deserialize_unit(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_unit(visitor)
        }
        fn erased_deserialize_unit_struct(
            &mut self,
            name: &'static str,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_unit_struct(name, visitor)
        }
        fn erased_deserialize_newtype_struct(
            &mut self,
            name: &'static str,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_newtype_struct(name, visitor)
        }
        fn erased_deserialize_seq(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_seq(visitor)
        }
        fn erased_deserialize_tuple(
            &mut self,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_tuple(len, visitor)
        }
        fn erased_deserialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_tuple_struct(name, len, visitor)
        }
        fn erased_deserialize_map(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_map(visitor)
        }
        fn erased_deserialize_struct(
            &mut self,
            name: &'static str,
            fields: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_struct(name, fields, visitor)
        }
        fn erased_deserialize_identifier(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_identifier(visitor)
        }
        fn erased_deserialize_enum(
            &mut self,
            name: &'static str,
            variants: &'static [&'static str],
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_enum(name, variants, visitor)
        }
        fn erased_deserialize_ignored_any(
            &mut self,
            visitor: &mut dyn Visitor<'de>,
        ) -> Result<Out, Error> {
            (**self).erased_deserialize_ignored_any(visitor)
        }
        fn erased_is_human_readable(&self) -> bool {
            (**self).erased_is_human_readable()
        }
    }
    fn erase<E>(e: E) -> Error
    where
        E: Display,
    {
        serde::de::Error::custom(e)
    }
    fn unerase<E>(e: Error) -> E
    where
        E: serde::de::Error,
    {
        E::custom(e)
    }
}
mod error {
    use crate::alloc::{String, ToString};
    use core::fmt::{self, Display};
    pub struct Error {
        msg: String,
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::fmt::Debug for Error {
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match *self {
                Self { msg: ref __self_0_0 } => {
                    let debug_trait_builder = &mut ::core::fmt::Formatter::debug_struct(
                        f,
                        "Error",
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "msg",
                        &&(*__self_0_0),
                    );
                    ::core::fmt::DebugStruct::finish(debug_trait_builder)
                }
            }
        }
    }
    pub type Result<T> = core::result::Result<T, Error>;
    impl Display for Error {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            self.msg.fmt(formatter)
        }
    }
    impl serde::ser::StdError for Error {}
    impl serde::ser::Error for Error {
        fn custom<T: Display>(msg: T) -> Self {
            Error { msg: msg.to_string() }
        }
    }
    impl serde::de::Error for Error {
        fn custom<T: Display>(msg: T) -> Self {
            Error { msg: msg.to_string() }
        }
    }
}
mod features_check {}
mod map {
    pub(crate) trait ResultExt<T, E> {
        unsafe fn unsafe_map<U>(self, op: unsafe fn(T) -> U) -> Result<U, E>;
    }
    impl<T, E> ResultExt<T, E> for Result<T, E> {
        unsafe fn unsafe_map<U>(self, op: unsafe fn(T) -> U) -> Result<U, E> {
            match self {
                Ok(t) => Ok(unsafe { op(t) }),
                Err(e) => Err(e),
            }
        }
    }
    pub(crate) trait OptionExt<T> {
        unsafe fn unsafe_map<U>(self, op: unsafe fn(T) -> U) -> Option<U>;
    }
    impl<T> OptionExt<T> for Option<T> {
        unsafe fn unsafe_map<U>(self, op: unsafe fn(T) -> U) -> Option<U> {
            match self {
                Some(t) => Some(unsafe { op(t) }),
                None => None,
            }
        }
    }
}
mod ser {
    use crate::alloc::Box;
    use crate::any::Any;
    use crate::error::Error;
    use crate::map::ResultExt;
    use core::fmt::Display;
    use core::marker::PhantomData;
    use serde::ser::{
        SerializeMap, SerializeSeq, SerializeStruct, SerializeStructVariant,
        SerializeTuple, SerializeTupleStruct, SerializeTupleVariant,
    };
    use serde::serde_if_integer128;
    pub trait Serialize {
        fn erased_serialize(&self, v: &mut dyn Serializer) -> Result<Ok, Error>;
    }
    pub trait Serializer {
        fn erased_serialize_bool(&mut self, v: bool) -> Result<Ok, Error>;
        fn erased_serialize_i8(&mut self, v: i8) -> Result<Ok, Error>;
        fn erased_serialize_i16(&mut self, v: i16) -> Result<Ok, Error>;
        fn erased_serialize_i32(&mut self, v: i32) -> Result<Ok, Error>;
        fn erased_serialize_i64(&mut self, v: i64) -> Result<Ok, Error>;
        fn erased_serialize_u8(&mut self, v: u8) -> Result<Ok, Error>;
        fn erased_serialize_u16(&mut self, v: u16) -> Result<Ok, Error>;
        fn erased_serialize_u32(&mut self, v: u32) -> Result<Ok, Error>;
        fn erased_serialize_u64(&mut self, v: u64) -> Result<Ok, Error>;
        fn erased_serialize_i128(&mut self, v: i128) -> Result<Ok, Error>;
        fn erased_serialize_u128(&mut self, v: u128) -> Result<Ok, Error>;
        fn erased_serialize_f32(&mut self, v: f32) -> Result<Ok, Error>;
        fn erased_serialize_f64(&mut self, v: f64) -> Result<Ok, Error>;
        fn erased_serialize_char(&mut self, v: char) -> Result<Ok, Error>;
        fn erased_serialize_str(&mut self, v: &str) -> Result<Ok, Error>;
        fn erased_serialize_bytes(&mut self, v: &[u8]) -> Result<Ok, Error>;
        fn erased_serialize_none(&mut self) -> Result<Ok, Error>;
        fn erased_serialize_some(&mut self, v: &dyn Serialize) -> Result<Ok, Error>;
        fn erased_serialize_unit(&mut self) -> Result<Ok, Error>;
        fn erased_serialize_unit_struct(
            &mut self,
            name: &'static str,
        ) -> Result<Ok, Error>;
        fn erased_serialize_unit_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
        ) -> Result<Ok, Error>;
        fn erased_serialize_newtype_struct(
            &mut self,
            name: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error>;
        fn erased_serialize_newtype_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error>;
        fn erased_serialize_seq(&mut self, len: Option<usize>) -> Result<Seq, Error>;
        fn erased_serialize_tuple(&mut self, len: usize) -> Result<Tuple, Error>;
        fn erased_serialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<TupleStruct, Error>;
        fn erased_serialize_tuple_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<TupleVariant, Error>;
        fn erased_serialize_map(&mut self, len: Option<usize>) -> Result<Map, Error>;
        fn erased_serialize_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<Struct, Error>;
        fn erased_serialize_struct_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<StructVariant, Error>;
        fn erased_is_human_readable(&self) -> bool;
    }
    impl dyn Serializer {
        pub fn erase<S>(serializer: S) -> erase::Serializer<S>
        where
            S: serde::Serializer,
            S::Ok: 'static,
        {
            erase::Serializer {
                state: Some(serializer),
            }
        }
    }
    pub struct Ok {
        data: Any,
    }
    impl Ok {
        unsafe fn new<T>(t: T) -> Self {
            Ok { data: unsafe { Any::new(t) } }
        }
        unsafe fn take<T>(self) -> T {
            unsafe { self.data.take() }
        }
    }
    impl<T> Serialize for T
    where
        T: ?Sized + serde::Serialize,
    {
        fn erased_serialize(
            &self,
            serializer: &mut dyn Serializer,
        ) -> Result<Ok, Error> {
            self.serialize(serializer)
        }
    }
    mod erase {
        pub struct Serializer<S> {
            pub(crate) state: Option<S>,
        }
        impl<S> Serializer<S> {
            pub(crate) fn take(&mut self) -> S {
                self.state.take().unwrap()
            }
            pub(crate) fn as_ref(&self) -> &S {
                self.state.as_ref().unwrap()
            }
        }
    }
    impl<T> Serializer for erase::Serializer<T>
    where
        T: serde::Serializer,
    {
        fn erased_serialize_bool(&mut self, v: bool) -> Result<Ok, Error> {
            unsafe { self.take().serialize_bool(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_i8(&mut self, v: i8) -> Result<Ok, Error> {
            unsafe { self.take().serialize_i8(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_i16(&mut self, v: i16) -> Result<Ok, Error> {
            unsafe { self.take().serialize_i16(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_i32(&mut self, v: i32) -> Result<Ok, Error> {
            unsafe { self.take().serialize_i32(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_i64(&mut self, v: i64) -> Result<Ok, Error> {
            unsafe { self.take().serialize_i64(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_u8(&mut self, v: u8) -> Result<Ok, Error> {
            unsafe { self.take().serialize_u8(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_u16(&mut self, v: u16) -> Result<Ok, Error> {
            unsafe { self.take().serialize_u16(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_u32(&mut self, v: u32) -> Result<Ok, Error> {
            unsafe { self.take().serialize_u32(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_u64(&mut self, v: u64) -> Result<Ok, Error> {
            unsafe { self.take().serialize_u64(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_i128(&mut self, v: i128) -> Result<Ok, Error> {
            unsafe { self.take().serialize_i128(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_u128(&mut self, v: u128) -> Result<Ok, Error> {
            unsafe { self.take().serialize_u128(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_f32(&mut self, v: f32) -> Result<Ok, Error> {
            unsafe { self.take().serialize_f32(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_f64(&mut self, v: f64) -> Result<Ok, Error> {
            unsafe { self.take().serialize_f64(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_char(&mut self, v: char) -> Result<Ok, Error> {
            unsafe { self.take().serialize_char(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_str(&mut self, v: &str) -> Result<Ok, Error> {
            unsafe { self.take().serialize_str(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_bytes(&mut self, v: &[u8]) -> Result<Ok, Error> {
            unsafe { self.take().serialize_bytes(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_none(&mut self) -> Result<Ok, Error> {
            unsafe { self.take().serialize_none().unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_some(&mut self, v: &dyn Serialize) -> Result<Ok, Error> {
            unsafe { self.take().serialize_some(v).unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_unit(&mut self) -> Result<Ok, Error> {
            unsafe { self.take().serialize_unit().unsafe_map(Ok::new).map_err(erase) }
        }
        fn erased_serialize_unit_struct(
            &mut self,
            name: &'static str,
        ) -> Result<Ok, Error> {
            unsafe {
                self
                    .take()
                    .serialize_unit_struct(name)
                    .unsafe_map(Ok::new)
                    .map_err(erase)
            }
        }
        fn erased_serialize_unit_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
        ) -> Result<Ok, Error> {
            unsafe {
                self
                    .take()
                    .serialize_unit_variant(name, variant_index, variant)
                    .unsafe_map(Ok::new)
                    .map_err(erase)
            }
        }
        fn erased_serialize_newtype_struct(
            &mut self,
            name: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error> {
            unsafe {
                self
                    .take()
                    .serialize_newtype_struct(name, v)
                    .unsafe_map(Ok::new)
                    .map_err(erase)
            }
        }
        fn erased_serialize_newtype_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error> {
            unsafe {
                self
                    .take()
                    .serialize_newtype_variant(name, variant_index, variant, v)
                    .unsafe_map(Ok::new)
                    .map_err(erase)
            }
        }
        fn erased_serialize_seq(&mut self, len: Option<usize>) -> Result<Seq, Error> {
            unsafe { self.take().serialize_seq(len).unsafe_map(Seq::new).map_err(erase) }
        }
        fn erased_serialize_tuple(&mut self, len: usize) -> Result<Tuple, Error> {
            unsafe {
                self.take().serialize_tuple(len).unsafe_map(Tuple::new).map_err(erase)
            }
        }
        fn erased_serialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<TupleStruct, Error> {
            unsafe {
                self
                    .take()
                    .serialize_tuple_struct(name, len)
                    .unsafe_map(TupleStruct::new)
                    .map_err(erase)
            }
        }
        fn erased_serialize_tuple_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<TupleVariant, Error> {
            unsafe {
                self
                    .take()
                    .serialize_tuple_variant(name, variant_index, variant, len)
                    .unsafe_map(TupleVariant::new)
                    .map_err(erase)
            }
        }
        fn erased_serialize_map(&mut self, len: Option<usize>) -> Result<Map, Error> {
            unsafe { self.take().serialize_map(len).unsafe_map(Map::new).map_err(erase) }
        }
        fn erased_serialize_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<Struct, Error> {
            unsafe {
                self
                    .take()
                    .serialize_struct(name, len)
                    .unsafe_map(Struct::new)
                    .map_err(erase)
            }
        }
        fn erased_serialize_struct_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<StructVariant, Error> {
            unsafe {
                self
                    .take()
                    .serialize_struct_variant(name, variant_index, variant, len)
                    .unsafe_map(StructVariant::new)
                    .map_err(erase)
            }
        }
        fn erased_is_human_readable(&self) -> bool {
            self.as_ref().is_human_readable()
        }
    }
    pub fn serialize<T, S>(value: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        T: ?Sized + Serialize,
        S: serde::Serializer,
    {
        let mut erased = erase::Serializer {
            state: Some(serializer),
        };
        unsafe {
            value.erased_serialize(&mut erased).unsafe_map(Ok::take).map_err(unerase)
        }
    }
    impl<'erased> crate::private::serde::Serialize for dyn Serialize + 'erased {
        fn serialize<S>(&self, serializer: S) -> crate::private::Result<S::Ok, S::Error>
        where
            S: crate::private::serde::Serializer,
        {
            fn __check_erased_serialize_supertrait<__T>()
            where
                __T: ?crate::private::Sized + Serialize,
            {
                crate::private::require_erased_serialize_impl::<__T>();
            }
            crate::serialize(self, serializer)
        }
    }
    impl<'erased> crate::private::serde::Serialize
    for dyn Serialize + crate::private::Send + 'erased {
        fn serialize<S>(&self, serializer: S) -> crate::private::Result<S::Ok, S::Error>
        where
            S: crate::private::serde::Serializer,
        {
            crate::serialize(self, serializer)
        }
    }
    impl<'erased> crate::private::serde::Serialize
    for dyn Serialize + crate::private::Sync + 'erased {
        fn serialize<S>(&self, serializer: S) -> crate::private::Result<S::Ok, S::Error>
        where
            S: crate::private::serde::Serializer,
        {
            crate::serialize(self, serializer)
        }
    }
    impl<'erased> crate::private::serde::Serialize
    for dyn Serialize + crate::private::Send + crate::private::Sync + 'erased {
        fn serialize<S>(&self, serializer: S) -> crate::private::Result<S::Ok, S::Error>
        where
            S: crate::private::serde::Serializer,
        {
            crate::serialize(self, serializer)
        }
    }
    impl<'a> serde::Serializer for &'a mut dyn Serializer {
        type Ok = Ok;
        type Error = Error;
        type SerializeSeq = Seq<'a>;
        type SerializeTuple = Tuple<'a>;
        type SerializeTupleStruct = TupleStruct<'a>;
        type SerializeTupleVariant = TupleVariant<'a>;
        type SerializeMap = Map<'a>;
        type SerializeStruct = Struct<'a>;
        type SerializeStructVariant = StructVariant<'a>;
        fn serialize_bool(self, v: bool) -> Result<Ok, Error> {
            self.erased_serialize_bool(v)
        }
        fn serialize_i8(self, v: i8) -> Result<Ok, Error> {
            self.erased_serialize_i8(v)
        }
        fn serialize_i16(self, v: i16) -> Result<Ok, Error> {
            self.erased_serialize_i16(v)
        }
        fn serialize_i32(self, v: i32) -> Result<Ok, Error> {
            self.erased_serialize_i32(v)
        }
        fn serialize_i64(self, v: i64) -> Result<Ok, Error> {
            self.erased_serialize_i64(v)
        }
        fn serialize_u8(self, v: u8) -> Result<Ok, Error> {
            self.erased_serialize_u8(v)
        }
        fn serialize_u16(self, v: u16) -> Result<Ok, Error> {
            self.erased_serialize_u16(v)
        }
        fn serialize_u32(self, v: u32) -> Result<Ok, Error> {
            self.erased_serialize_u32(v)
        }
        fn serialize_u64(self, v: u64) -> Result<Ok, Error> {
            self.erased_serialize_u64(v)
        }
        fn serialize_i128(self, v: i128) -> Result<Ok, Error> {
            self.erased_serialize_i128(v)
        }
        fn serialize_u128(self, v: u128) -> Result<Ok, Error> {
            self.erased_serialize_u128(v)
        }
        fn serialize_f32(self, v: f32) -> Result<Ok, Error> {
            self.erased_serialize_f32(v)
        }
        fn serialize_f64(self, v: f64) -> Result<Ok, Error> {
            self.erased_serialize_f64(v)
        }
        fn serialize_char(self, v: char) -> Result<Ok, Error> {
            self.erased_serialize_char(v)
        }
        fn serialize_str(self, v: &str) -> Result<Ok, Error> {
            self.erased_serialize_str(v)
        }
        fn serialize_bytes(self, v: &[u8]) -> Result<Ok, Error> {
            self.erased_serialize_bytes(v)
        }
        fn serialize_none(self) -> Result<Ok, Error> {
            self.erased_serialize_none()
        }
        fn serialize_some<T>(self, v: &T) -> Result<Ok, Error>
        where
            T: ?Sized + serde::Serialize,
        {
            self.erased_serialize_some(&v)
        }
        fn serialize_unit(self) -> Result<Ok, Error> {
            self.erased_serialize_unit()
        }
        fn serialize_unit_struct(self, name: &'static str) -> Result<Ok, Error> {
            self.erased_serialize_unit_struct(name)
        }
        fn serialize_unit_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
        ) -> Result<Ok, Error> {
            self.erased_serialize_unit_variant(name, variant_index, variant)
        }
        fn serialize_newtype_struct<T>(
            self,
            name: &'static str,
            v: &T,
        ) -> Result<Ok, Error>
        where
            T: ?Sized + serde::Serialize,
        {
            self.erased_serialize_newtype_struct(name, &v)
        }
        fn serialize_newtype_variant<T>(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            v: &T,
        ) -> Result<Ok, Error>
        where
            T: ?Sized + serde::Serialize,
        {
            self.erased_serialize_newtype_variant(name, variant_index, variant, &v)
        }
        fn serialize_seq(self, len: Option<usize>) -> Result<Seq<'a>, Error> {
            self.erased_serialize_seq(len)
        }
        fn serialize_tuple(self, len: usize) -> Result<Tuple<'a>, Error> {
            self.erased_serialize_tuple(len)
        }
        fn serialize_tuple_struct(
            self,
            name: &'static str,
            len: usize,
        ) -> Result<TupleStruct<'a>, Error> {
            self.erased_serialize_tuple_struct(name, len)
        }
        fn serialize_tuple_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<TupleVariant<'a>, Error> {
            self.erased_serialize_tuple_variant(name, variant_index, variant, len)
        }
        fn serialize_map(self, len: Option<usize>) -> Result<Map<'a>, Error> {
            self.erased_serialize_map(len)
        }
        fn serialize_struct(
            self,
            name: &'static str,
            len: usize,
        ) -> Result<Struct<'a>, Error> {
            self.erased_serialize_struct(name, len)
        }
        fn serialize_struct_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<StructVariant<'a>, Error> {
            self.erased_serialize_struct_variant(name, variant_index, variant, len)
        }
        fn is_human_readable(&self) -> bool {
            self.erased_is_human_readable()
        }
    }
    impl<'a> serde::Serializer for &'a mut (dyn Serializer + Send) {
        type Ok = Ok;
        type Error = Error;
        type SerializeSeq = Seq<'a>;
        type SerializeTuple = Tuple<'a>;
        type SerializeTupleStruct = TupleStruct<'a>;
        type SerializeTupleVariant = TupleVariant<'a>;
        type SerializeMap = Map<'a>;
        type SerializeStruct = Struct<'a>;
        type SerializeStructVariant = StructVariant<'a>;
        fn serialize_bool(self, v: bool) -> Result<Ok, Error> {
            self.erased_serialize_bool(v)
        }
        fn serialize_i8(self, v: i8) -> Result<Ok, Error> {
            self.erased_serialize_i8(v)
        }
        fn serialize_i16(self, v: i16) -> Result<Ok, Error> {
            self.erased_serialize_i16(v)
        }
        fn serialize_i32(self, v: i32) -> Result<Ok, Error> {
            self.erased_serialize_i32(v)
        }
        fn serialize_i64(self, v: i64) -> Result<Ok, Error> {
            self.erased_serialize_i64(v)
        }
        fn serialize_u8(self, v: u8) -> Result<Ok, Error> {
            self.erased_serialize_u8(v)
        }
        fn serialize_u16(self, v: u16) -> Result<Ok, Error> {
            self.erased_serialize_u16(v)
        }
        fn serialize_u32(self, v: u32) -> Result<Ok, Error> {
            self.erased_serialize_u32(v)
        }
        fn serialize_u64(self, v: u64) -> Result<Ok, Error> {
            self.erased_serialize_u64(v)
        }
        fn serialize_i128(self, v: i128) -> Result<Ok, Error> {
            self.erased_serialize_i128(v)
        }
        fn serialize_u128(self, v: u128) -> Result<Ok, Error> {
            self.erased_serialize_u128(v)
        }
        fn serialize_f32(self, v: f32) -> Result<Ok, Error> {
            self.erased_serialize_f32(v)
        }
        fn serialize_f64(self, v: f64) -> Result<Ok, Error> {
            self.erased_serialize_f64(v)
        }
        fn serialize_char(self, v: char) -> Result<Ok, Error> {
            self.erased_serialize_char(v)
        }
        fn serialize_str(self, v: &str) -> Result<Ok, Error> {
            self.erased_serialize_str(v)
        }
        fn serialize_bytes(self, v: &[u8]) -> Result<Ok, Error> {
            self.erased_serialize_bytes(v)
        }
        fn serialize_none(self) -> Result<Ok, Error> {
            self.erased_serialize_none()
        }
        fn serialize_some<T>(self, v: &T) -> Result<Ok, Error>
        where
            T: ?Sized + serde::Serialize,
        {
            self.erased_serialize_some(&v)
        }
        fn serialize_unit(self) -> Result<Ok, Error> {
            self.erased_serialize_unit()
        }
        fn serialize_unit_struct(self, name: &'static str) -> Result<Ok, Error> {
            self.erased_serialize_unit_struct(name)
        }
        fn serialize_unit_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
        ) -> Result<Ok, Error> {
            self.erased_serialize_unit_variant(name, variant_index, variant)
        }
        fn serialize_newtype_struct<T>(
            self,
            name: &'static str,
            v: &T,
        ) -> Result<Ok, Error>
        where
            T: ?Sized + serde::Serialize,
        {
            self.erased_serialize_newtype_struct(name, &v)
        }
        fn serialize_newtype_variant<T>(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            v: &T,
        ) -> Result<Ok, Error>
        where
            T: ?Sized + serde::Serialize,
        {
            self.erased_serialize_newtype_variant(name, variant_index, variant, &v)
        }
        fn serialize_seq(self, len: Option<usize>) -> Result<Seq<'a>, Error> {
            self.erased_serialize_seq(len)
        }
        fn serialize_tuple(self, len: usize) -> Result<Tuple<'a>, Error> {
            self.erased_serialize_tuple(len)
        }
        fn serialize_tuple_struct(
            self,
            name: &'static str,
            len: usize,
        ) -> Result<TupleStruct<'a>, Error> {
            self.erased_serialize_tuple_struct(name, len)
        }
        fn serialize_tuple_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<TupleVariant<'a>, Error> {
            self.erased_serialize_tuple_variant(name, variant_index, variant, len)
        }
        fn serialize_map(self, len: Option<usize>) -> Result<Map<'a>, Error> {
            self.erased_serialize_map(len)
        }
        fn serialize_struct(
            self,
            name: &'static str,
            len: usize,
        ) -> Result<Struct<'a>, Error> {
            self.erased_serialize_struct(name, len)
        }
        fn serialize_struct_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<StructVariant<'a>, Error> {
            self.erased_serialize_struct_variant(name, variant_index, variant, len)
        }
        fn is_human_readable(&self) -> bool {
            self.erased_is_human_readable()
        }
    }
    impl<'a> serde::Serializer for &'a mut (dyn Serializer + Sync) {
        type Ok = Ok;
        type Error = Error;
        type SerializeSeq = Seq<'a>;
        type SerializeTuple = Tuple<'a>;
        type SerializeTupleStruct = TupleStruct<'a>;
        type SerializeTupleVariant = TupleVariant<'a>;
        type SerializeMap = Map<'a>;
        type SerializeStruct = Struct<'a>;
        type SerializeStructVariant = StructVariant<'a>;
        fn serialize_bool(self, v: bool) -> Result<Ok, Error> {
            self.erased_serialize_bool(v)
        }
        fn serialize_i8(self, v: i8) -> Result<Ok, Error> {
            self.erased_serialize_i8(v)
        }
        fn serialize_i16(self, v: i16) -> Result<Ok, Error> {
            self.erased_serialize_i16(v)
        }
        fn serialize_i32(self, v: i32) -> Result<Ok, Error> {
            self.erased_serialize_i32(v)
        }
        fn serialize_i64(self, v: i64) -> Result<Ok, Error> {
            self.erased_serialize_i64(v)
        }
        fn serialize_u8(self, v: u8) -> Result<Ok, Error> {
            self.erased_serialize_u8(v)
        }
        fn serialize_u16(self, v: u16) -> Result<Ok, Error> {
            self.erased_serialize_u16(v)
        }
        fn serialize_u32(self, v: u32) -> Result<Ok, Error> {
            self.erased_serialize_u32(v)
        }
        fn serialize_u64(self, v: u64) -> Result<Ok, Error> {
            self.erased_serialize_u64(v)
        }
        fn serialize_i128(self, v: i128) -> Result<Ok, Error> {
            self.erased_serialize_i128(v)
        }
        fn serialize_u128(self, v: u128) -> Result<Ok, Error> {
            self.erased_serialize_u128(v)
        }
        fn serialize_f32(self, v: f32) -> Result<Ok, Error> {
            self.erased_serialize_f32(v)
        }
        fn serialize_f64(self, v: f64) -> Result<Ok, Error> {
            self.erased_serialize_f64(v)
        }
        fn serialize_char(self, v: char) -> Result<Ok, Error> {
            self.erased_serialize_char(v)
        }
        fn serialize_str(self, v: &str) -> Result<Ok, Error> {
            self.erased_serialize_str(v)
        }
        fn serialize_bytes(self, v: &[u8]) -> Result<Ok, Error> {
            self.erased_serialize_bytes(v)
        }
        fn serialize_none(self) -> Result<Ok, Error> {
            self.erased_serialize_none()
        }
        fn serialize_some<T>(self, v: &T) -> Result<Ok, Error>
        where
            T: ?Sized + serde::Serialize,
        {
            self.erased_serialize_some(&v)
        }
        fn serialize_unit(self) -> Result<Ok, Error> {
            self.erased_serialize_unit()
        }
        fn serialize_unit_struct(self, name: &'static str) -> Result<Ok, Error> {
            self.erased_serialize_unit_struct(name)
        }
        fn serialize_unit_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
        ) -> Result<Ok, Error> {
            self.erased_serialize_unit_variant(name, variant_index, variant)
        }
        fn serialize_newtype_struct<T>(
            self,
            name: &'static str,
            v: &T,
        ) -> Result<Ok, Error>
        where
            T: ?Sized + serde::Serialize,
        {
            self.erased_serialize_newtype_struct(name, &v)
        }
        fn serialize_newtype_variant<T>(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            v: &T,
        ) -> Result<Ok, Error>
        where
            T: ?Sized + serde::Serialize,
        {
            self.erased_serialize_newtype_variant(name, variant_index, variant, &v)
        }
        fn serialize_seq(self, len: Option<usize>) -> Result<Seq<'a>, Error> {
            self.erased_serialize_seq(len)
        }
        fn serialize_tuple(self, len: usize) -> Result<Tuple<'a>, Error> {
            self.erased_serialize_tuple(len)
        }
        fn serialize_tuple_struct(
            self,
            name: &'static str,
            len: usize,
        ) -> Result<TupleStruct<'a>, Error> {
            self.erased_serialize_tuple_struct(name, len)
        }
        fn serialize_tuple_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<TupleVariant<'a>, Error> {
            self.erased_serialize_tuple_variant(name, variant_index, variant, len)
        }
        fn serialize_map(self, len: Option<usize>) -> Result<Map<'a>, Error> {
            self.erased_serialize_map(len)
        }
        fn serialize_struct(
            self,
            name: &'static str,
            len: usize,
        ) -> Result<Struct<'a>, Error> {
            self.erased_serialize_struct(name, len)
        }
        fn serialize_struct_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<StructVariant<'a>, Error> {
            self.erased_serialize_struct_variant(name, variant_index, variant, len)
        }
        fn is_human_readable(&self) -> bool {
            self.erased_is_human_readable()
        }
    }
    impl<'a> serde::Serializer for &'a mut (dyn Serializer + Send + Sync) {
        type Ok = Ok;
        type Error = Error;
        type SerializeSeq = Seq<'a>;
        type SerializeTuple = Tuple<'a>;
        type SerializeTupleStruct = TupleStruct<'a>;
        type SerializeTupleVariant = TupleVariant<'a>;
        type SerializeMap = Map<'a>;
        type SerializeStruct = Struct<'a>;
        type SerializeStructVariant = StructVariant<'a>;
        fn serialize_bool(self, v: bool) -> Result<Ok, Error> {
            self.erased_serialize_bool(v)
        }
        fn serialize_i8(self, v: i8) -> Result<Ok, Error> {
            self.erased_serialize_i8(v)
        }
        fn serialize_i16(self, v: i16) -> Result<Ok, Error> {
            self.erased_serialize_i16(v)
        }
        fn serialize_i32(self, v: i32) -> Result<Ok, Error> {
            self.erased_serialize_i32(v)
        }
        fn serialize_i64(self, v: i64) -> Result<Ok, Error> {
            self.erased_serialize_i64(v)
        }
        fn serialize_u8(self, v: u8) -> Result<Ok, Error> {
            self.erased_serialize_u8(v)
        }
        fn serialize_u16(self, v: u16) -> Result<Ok, Error> {
            self.erased_serialize_u16(v)
        }
        fn serialize_u32(self, v: u32) -> Result<Ok, Error> {
            self.erased_serialize_u32(v)
        }
        fn serialize_u64(self, v: u64) -> Result<Ok, Error> {
            self.erased_serialize_u64(v)
        }
        fn serialize_i128(self, v: i128) -> Result<Ok, Error> {
            self.erased_serialize_i128(v)
        }
        fn serialize_u128(self, v: u128) -> Result<Ok, Error> {
            self.erased_serialize_u128(v)
        }
        fn serialize_f32(self, v: f32) -> Result<Ok, Error> {
            self.erased_serialize_f32(v)
        }
        fn serialize_f64(self, v: f64) -> Result<Ok, Error> {
            self.erased_serialize_f64(v)
        }
        fn serialize_char(self, v: char) -> Result<Ok, Error> {
            self.erased_serialize_char(v)
        }
        fn serialize_str(self, v: &str) -> Result<Ok, Error> {
            self.erased_serialize_str(v)
        }
        fn serialize_bytes(self, v: &[u8]) -> Result<Ok, Error> {
            self.erased_serialize_bytes(v)
        }
        fn serialize_none(self) -> Result<Ok, Error> {
            self.erased_serialize_none()
        }
        fn serialize_some<T>(self, v: &T) -> Result<Ok, Error>
        where
            T: ?Sized + serde::Serialize,
        {
            self.erased_serialize_some(&v)
        }
        fn serialize_unit(self) -> Result<Ok, Error> {
            self.erased_serialize_unit()
        }
        fn serialize_unit_struct(self, name: &'static str) -> Result<Ok, Error> {
            self.erased_serialize_unit_struct(name)
        }
        fn serialize_unit_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
        ) -> Result<Ok, Error> {
            self.erased_serialize_unit_variant(name, variant_index, variant)
        }
        fn serialize_newtype_struct<T>(
            self,
            name: &'static str,
            v: &T,
        ) -> Result<Ok, Error>
        where
            T: ?Sized + serde::Serialize,
        {
            self.erased_serialize_newtype_struct(name, &v)
        }
        fn serialize_newtype_variant<T>(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            v: &T,
        ) -> Result<Ok, Error>
        where
            T: ?Sized + serde::Serialize,
        {
            self.erased_serialize_newtype_variant(name, variant_index, variant, &v)
        }
        fn serialize_seq(self, len: Option<usize>) -> Result<Seq<'a>, Error> {
            self.erased_serialize_seq(len)
        }
        fn serialize_tuple(self, len: usize) -> Result<Tuple<'a>, Error> {
            self.erased_serialize_tuple(len)
        }
        fn serialize_tuple_struct(
            self,
            name: &'static str,
            len: usize,
        ) -> Result<TupleStruct<'a>, Error> {
            self.erased_serialize_tuple_struct(name, len)
        }
        fn serialize_tuple_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<TupleVariant<'a>, Error> {
            self.erased_serialize_tuple_variant(name, variant_index, variant, len)
        }
        fn serialize_map(self, len: Option<usize>) -> Result<Map<'a>, Error> {
            self.erased_serialize_map(len)
        }
        fn serialize_struct(
            self,
            name: &'static str,
            len: usize,
        ) -> Result<Struct<'a>, Error> {
            self.erased_serialize_struct(name, len)
        }
        fn serialize_struct_variant(
            self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<StructVariant<'a>, Error> {
            self.erased_serialize_struct_variant(name, variant_index, variant, len)
        }
        fn is_human_readable(&self) -> bool {
            self.erased_is_human_readable()
        }
    }
    pub struct Seq<'a> {
        data: Any,
        serialize_element: unsafe fn(&mut Any, &dyn Serialize) -> Result<(), Error>,
        end: unsafe fn(Any) -> Result<Ok, Error>,
        lifetime: PhantomData<&'a dyn Serializer>,
    }
    impl<'a> Seq<'a> {
        unsafe fn new<T>(data: T) -> Self
        where
            T: serde::ser::SerializeSeq,
        {
            Seq {
                data: unsafe { Any::new(data) },
                serialize_element: {
                    unsafe fn serialize_element<T>(
                        data: &mut Any,
                        v: &dyn Serialize,
                    ) -> Result<(), Error>
                    where
                        T: serde::ser::SerializeSeq,
                    {
                        unsafe { data.view::<T>().serialize_element(v).map_err(erase) }
                    }
                    serialize_element::<T>
                },
                end: {
                    unsafe fn end<T>(data: Any) -> Result<Ok, Error>
                    where
                        T: serde::ser::SerializeSeq,
                    {
                        unsafe {
                            data.take::<T>().end().unsafe_map(Ok::new).map_err(erase)
                        }
                    }
                    end::<T>
                },
                lifetime: PhantomData,
            }
        }
    }
    impl<'a> SerializeSeq for Seq<'a> {
        type Ok = Ok;
        type Error = Error;
        fn serialize_element<T>(&mut self, value: &T) -> Result<(), Error>
        where
            T: ?Sized + serde::Serialize,
        {
            unsafe { (self.serialize_element)(&mut self.data, &value) }
        }
        fn end(self) -> Result<Ok, Error> {
            unsafe { (self.end)(self.data) }
        }
    }
    pub struct Tuple<'a> {
        data: Any,
        serialize_element: unsafe fn(&mut Any, &dyn Serialize) -> Result<(), Error>,
        end: unsafe fn(Any) -> Result<Ok, Error>,
        lifetime: PhantomData<&'a dyn Serializer>,
    }
    impl<'a> Tuple<'a> {
        unsafe fn new<T>(data: T) -> Self
        where
            T: serde::ser::SerializeTuple,
        {
            Tuple {
                data: unsafe { Any::new(data) },
                serialize_element: {
                    unsafe fn serialize_element<T>(
                        data: &mut Any,
                        v: &dyn Serialize,
                    ) -> Result<(), Error>
                    where
                        T: serde::ser::SerializeTuple,
                    {
                        unsafe { data.view::<T>().serialize_element(v).map_err(erase) }
                    }
                    serialize_element::<T>
                },
                end: {
                    unsafe fn end<T>(data: Any) -> Result<Ok, Error>
                    where
                        T: serde::ser::SerializeTuple,
                    {
                        unsafe {
                            data.take::<T>().end().unsafe_map(Ok::new).map_err(erase)
                        }
                    }
                    end::<T>
                },
                lifetime: PhantomData,
            }
        }
    }
    impl<'a> SerializeTuple for Tuple<'a> {
        type Ok = Ok;
        type Error = Error;
        fn serialize_element<T>(&mut self, value: &T) -> Result<(), Error>
        where
            T: ?Sized + serde::Serialize,
        {
            unsafe { (self.serialize_element)(&mut self.data, &value) }
        }
        fn end(self) -> Result<Ok, Error> {
            unsafe { (self.end)(self.data) }
        }
    }
    pub struct TupleStruct<'a> {
        data: Any,
        serialize_field: unsafe fn(&mut Any, &dyn Serialize) -> Result<(), Error>,
        end: unsafe fn(Any) -> Result<Ok, Error>,
        lifetime: PhantomData<&'a dyn Serializer>,
    }
    impl<'a> TupleStruct<'a> {
        unsafe fn new<T>(data: T) -> Self
        where
            T: serde::ser::SerializeTupleStruct,
        {
            TupleStruct {
                data: unsafe { Any::new(data) },
                serialize_field: {
                    unsafe fn serialize_field<T>(
                        data: &mut Any,
                        v: &dyn Serialize,
                    ) -> Result<(), Error>
                    where
                        T: serde::ser::SerializeTupleStruct,
                    {
                        unsafe { data.view::<T>().serialize_field(v).map_err(erase) }
                    }
                    serialize_field::<T>
                },
                end: {
                    unsafe fn end<T>(data: Any) -> Result<Ok, Error>
                    where
                        T: serde::ser::SerializeTupleStruct,
                    {
                        unsafe {
                            data.take::<T>().end().unsafe_map(Ok::new).map_err(erase)
                        }
                    }
                    end::<T>
                },
                lifetime: PhantomData,
            }
        }
    }
    impl<'a> SerializeTupleStruct for TupleStruct<'a> {
        type Ok = Ok;
        type Error = Error;
        fn serialize_field<T>(&mut self, value: &T) -> Result<(), Error>
        where
            T: ?Sized + serde::Serialize,
        {
            unsafe { (self.serialize_field)(&mut self.data, &value) }
        }
        fn end(self) -> Result<Ok, Error> {
            unsafe { (self.end)(self.data) }
        }
    }
    pub struct TupleVariant<'a> {
        data: Any,
        serialize_field: unsafe fn(&mut Any, &dyn Serialize) -> Result<(), Error>,
        end: unsafe fn(Any) -> Result<Ok, Error>,
        lifetime: PhantomData<&'a dyn Serializer>,
    }
    impl<'a> TupleVariant<'a> {
        unsafe fn new<T>(data: T) -> Self
        where
            T: serde::ser::SerializeTupleVariant,
        {
            TupleVariant {
                data: unsafe { Any::new(data) },
                serialize_field: {
                    unsafe fn serialize_field<T>(
                        data: &mut Any,
                        v: &dyn Serialize,
                    ) -> Result<(), Error>
                    where
                        T: serde::ser::SerializeTupleVariant,
                    {
                        unsafe { data.view::<T>().serialize_field(v).map_err(erase) }
                    }
                    serialize_field::<T>
                },
                end: {
                    unsafe fn end<T>(data: Any) -> Result<Ok, Error>
                    where
                        T: serde::ser::SerializeTupleVariant,
                    {
                        unsafe {
                            data.take::<T>().end().unsafe_map(Ok::new).map_err(erase)
                        }
                    }
                    end::<T>
                },
                lifetime: PhantomData,
            }
        }
    }
    impl<'a> SerializeTupleVariant for TupleVariant<'a> {
        type Ok = Ok;
        type Error = Error;
        fn serialize_field<T>(&mut self, value: &T) -> Result<(), Error>
        where
            T: ?Sized + serde::Serialize,
        {
            unsafe { (self.serialize_field)(&mut self.data, &value) }
        }
        fn end(self) -> Result<Ok, Error> {
            unsafe { (self.end)(self.data) }
        }
    }
    pub struct Map<'a> {
        data: Any,
        serialize_key: unsafe fn(&mut Any, &dyn Serialize) -> Result<(), Error>,
        serialize_value: unsafe fn(&mut Any, &dyn Serialize) -> Result<(), Error>,
        serialize_entry: unsafe fn(
            &mut Any,
            &dyn Serialize,
            &dyn Serialize,
        ) -> Result<(), Error>,
        end: unsafe fn(Any) -> Result<Ok, Error>,
        lifetime: PhantomData<&'a dyn Serializer>,
    }
    impl<'a> Map<'a> {
        unsafe fn new<T>(data: T) -> Self
        where
            T: serde::ser::SerializeMap,
        {
            Map {
                data: unsafe { Any::new(data) },
                serialize_key: {
                    unsafe fn serialize_key<T>(
                        data: &mut Any,
                        v: &dyn Serialize,
                    ) -> Result<(), Error>
                    where
                        T: serde::ser::SerializeMap,
                    {
                        unsafe { data.view::<T>().serialize_key(v).map_err(erase) }
                    }
                    serialize_key::<T>
                },
                serialize_value: {
                    unsafe fn serialize_value<T>(
                        data: &mut Any,
                        v: &dyn Serialize,
                    ) -> Result<(), Error>
                    where
                        T: serde::ser::SerializeMap,
                    {
                        unsafe { data.view::<T>().serialize_value(v).map_err(erase) }
                    }
                    serialize_value::<T>
                },
                serialize_entry: {
                    unsafe fn serialize_entry<T>(
                        data: &mut Any,
                        k: &dyn Serialize,
                        v: &dyn Serialize,
                    ) -> Result<(), Error>
                    where
                        T: serde::ser::SerializeMap,
                    {
                        unsafe { data.view::<T>().serialize_entry(k, v).map_err(erase) }
                    }
                    serialize_entry::<T>
                },
                end: {
                    unsafe fn end<T>(data: Any) -> Result<Ok, Error>
                    where
                        T: serde::ser::SerializeMap,
                    {
                        unsafe {
                            data.take::<T>().end().unsafe_map(Ok::new).map_err(erase)
                        }
                    }
                    end::<T>
                },
                lifetime: PhantomData,
            }
        }
    }
    impl<'a> SerializeMap for Map<'a> {
        type Ok = Ok;
        type Error = Error;
        fn serialize_key<T>(&mut self, key: &T) -> Result<(), Error>
        where
            T: ?Sized + serde::Serialize,
        {
            unsafe { (self.serialize_key)(&mut self.data, &key) }
        }
        fn serialize_value<T>(&mut self, value: &T) -> Result<(), Error>
        where
            T: ?Sized + serde::Serialize,
        {
            unsafe { (self.serialize_value)(&mut self.data, &value) }
        }
        fn serialize_entry<K, V>(&mut self, key: &K, value: &V) -> Result<(), Error>
        where
            K: ?Sized + serde::Serialize,
            V: ?Sized + serde::Serialize,
        {
            unsafe { (self.serialize_entry)(&mut self.data, &key, &value) }
        }
        fn end(self) -> Result<Ok, Error> {
            unsafe { (self.end)(self.data) }
        }
    }
    pub struct Struct<'a> {
        data: Any,
        serialize_field: unsafe fn(
            &mut Any,
            &'static str,
            &dyn Serialize,
        ) -> Result<(), Error>,
        end: unsafe fn(Any) -> Result<Ok, Error>,
        lifetime: PhantomData<&'a dyn Serializer>,
    }
    impl<'a> Struct<'a> {
        unsafe fn new<T>(data: T) -> Self
        where
            T: serde::ser::SerializeStruct,
        {
            Struct {
                data: unsafe { Any::new(data) },
                serialize_field: {
                    unsafe fn serialize_field<T>(
                        data: &mut Any,
                        k: &'static str,
                        v: &dyn Serialize,
                    ) -> Result<(), Error>
                    where
                        T: serde::ser::SerializeStruct,
                    {
                        unsafe { data.view::<T>().serialize_field(k, v).map_err(erase) }
                    }
                    serialize_field::<T>
                },
                end: {
                    unsafe fn end<T>(data: Any) -> Result<Ok, Error>
                    where
                        T: serde::ser::SerializeStruct,
                    {
                        unsafe {
                            data.take::<T>().end().unsafe_map(Ok::new).map_err(erase)
                        }
                    }
                    end::<T>
                },
                lifetime: PhantomData,
            }
        }
    }
    impl<'a> SerializeStruct for Struct<'a> {
        type Ok = Ok;
        type Error = Error;
        fn serialize_field<T>(
            &mut self,
            name: &'static str,
            field: &T,
        ) -> Result<(), Error>
        where
            T: ?Sized + serde::Serialize,
        {
            unsafe { (self.serialize_field)(&mut self.data, name, &field) }
        }
        fn end(self) -> Result<Ok, Error> {
            unsafe { (self.end)(self.data) }
        }
    }
    pub struct StructVariant<'a> {
        data: Any,
        serialize_field: unsafe fn(
            &mut Any,
            &'static str,
            &dyn Serialize,
        ) -> Result<(), Error>,
        end: unsafe fn(Any) -> Result<Ok, Error>,
        lifetime: PhantomData<&'a dyn Serializer>,
    }
    impl<'a> StructVariant<'a> {
        unsafe fn new<T>(data: T) -> Self
        where
            T: serde::ser::SerializeStructVariant,
        {
            StructVariant {
                data: unsafe { Any::new(data) },
                serialize_field: {
                    unsafe fn serialize_field<T>(
                        data: &mut Any,
                        k: &'static str,
                        v: &dyn Serialize,
                    ) -> Result<(), Error>
                    where
                        T: serde::ser::SerializeStructVariant,
                    {
                        unsafe { data.view::<T>().serialize_field(k, v).map_err(erase) }
                    }
                    serialize_field::<T>
                },
                end: {
                    unsafe fn end<T>(data: Any) -> Result<Ok, Error>
                    where
                        T: serde::ser::SerializeStructVariant,
                    {
                        unsafe {
                            data.take::<T>().end().unsafe_map(Ok::new).map_err(erase)
                        }
                    }
                    end::<T>
                },
                lifetime: PhantomData,
            }
        }
    }
    impl<'a> SerializeStructVariant for StructVariant<'a> {
        type Ok = Ok;
        type Error = Error;
        fn serialize_field<T>(
            &mut self,
            name: &'static str,
            field: &T,
        ) -> Result<(), Error>
        where
            T: ?Sized + serde::Serialize,
        {
            unsafe { (self.serialize_field)(&mut self.data, name, &field) }
        }
        fn end(self) -> Result<Ok, Error> {
            unsafe { (self.end)(self.data) }
        }
    }
    impl<'a> Serializer for Box<dyn Serializer + 'a> {
        fn erased_serialize_bool(&mut self, v: bool) -> Result<Ok, Error> {
            (**self).erased_serialize_bool(v)
        }
        fn erased_serialize_i8(&mut self, v: i8) -> Result<Ok, Error> {
            (**self).erased_serialize_i8(v)
        }
        fn erased_serialize_i16(&mut self, v: i16) -> Result<Ok, Error> {
            (**self).erased_serialize_i16(v)
        }
        fn erased_serialize_i32(&mut self, v: i32) -> Result<Ok, Error> {
            (**self).erased_serialize_i32(v)
        }
        fn erased_serialize_i64(&mut self, v: i64) -> Result<Ok, Error> {
            (**self).erased_serialize_i64(v)
        }
        fn erased_serialize_u8(&mut self, v: u8) -> Result<Ok, Error> {
            (**self).erased_serialize_u8(v)
        }
        fn erased_serialize_u16(&mut self, v: u16) -> Result<Ok, Error> {
            (**self).erased_serialize_u16(v)
        }
        fn erased_serialize_u32(&mut self, v: u32) -> Result<Ok, Error> {
            (**self).erased_serialize_u32(v)
        }
        fn erased_serialize_u64(&mut self, v: u64) -> Result<Ok, Error> {
            (**self).erased_serialize_u64(v)
        }
        fn erased_serialize_i128(&mut self, v: i128) -> Result<Ok, Error> {
            (**self).erased_serialize_i128(v)
        }
        fn erased_serialize_u128(&mut self, v: u128) -> Result<Ok, Error> {
            (**self).erased_serialize_u128(v)
        }
        fn erased_serialize_f32(&mut self, v: f32) -> Result<Ok, Error> {
            (**self).erased_serialize_f32(v)
        }
        fn erased_serialize_f64(&mut self, v: f64) -> Result<Ok, Error> {
            (**self).erased_serialize_f64(v)
        }
        fn erased_serialize_char(&mut self, v: char) -> Result<Ok, Error> {
            (**self).erased_serialize_char(v)
        }
        fn erased_serialize_str(&mut self, v: &str) -> Result<Ok, Error> {
            (**self).erased_serialize_str(v)
        }
        fn erased_serialize_bytes(&mut self, v: &[u8]) -> Result<Ok, Error> {
            (**self).erased_serialize_bytes(v)
        }
        fn erased_serialize_none(&mut self) -> Result<Ok, Error> {
            (**self).erased_serialize_none()
        }
        fn erased_serialize_some(&mut self, v: &dyn Serialize) -> Result<Ok, Error> {
            (**self).erased_serialize_some(v)
        }
        fn erased_serialize_unit(&mut self) -> Result<Ok, Error> {
            (**self).erased_serialize_unit()
        }
        fn erased_serialize_unit_struct(
            &mut self,
            name: &'static str,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_unit_struct(name)
        }
        fn erased_serialize_unit_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_unit_variant(name, variant_index, variant)
        }
        fn erased_serialize_newtype_struct(
            &mut self,
            name: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_newtype_struct(name, v)
        }
        fn erased_serialize_newtype_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_newtype_variant(name, variant_index, variant, v)
        }
        fn erased_serialize_seq(&mut self, len: Option<usize>) -> Result<Seq, Error> {
            (**self).erased_serialize_seq(len)
        }
        fn erased_serialize_tuple(&mut self, len: usize) -> Result<Tuple, Error> {
            (**self).erased_serialize_tuple(len)
        }
        fn erased_serialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<TupleStruct, Error> {
            (**self).erased_serialize_tuple_struct(name, len)
        }
        fn erased_serialize_tuple_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<TupleVariant, Error> {
            (**self).erased_serialize_tuple_variant(name, variant_index, variant, len)
        }
        fn erased_serialize_map(&mut self, len: Option<usize>) -> Result<Map, Error> {
            (**self).erased_serialize_map(len)
        }
        fn erased_serialize_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<Struct, Error> {
            (**self).erased_serialize_struct(name, len)
        }
        fn erased_serialize_struct_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<StructVariant, Error> {
            (**self).erased_serialize_struct_variant(name, variant_index, variant, len)
        }
        fn erased_is_human_readable(&self) -> bool {
            (**self).erased_is_human_readable()
        }
    }
    impl<'a> Serializer for Box<dyn Serializer + Send + 'a> {
        fn erased_serialize_bool(&mut self, v: bool) -> Result<Ok, Error> {
            (**self).erased_serialize_bool(v)
        }
        fn erased_serialize_i8(&mut self, v: i8) -> Result<Ok, Error> {
            (**self).erased_serialize_i8(v)
        }
        fn erased_serialize_i16(&mut self, v: i16) -> Result<Ok, Error> {
            (**self).erased_serialize_i16(v)
        }
        fn erased_serialize_i32(&mut self, v: i32) -> Result<Ok, Error> {
            (**self).erased_serialize_i32(v)
        }
        fn erased_serialize_i64(&mut self, v: i64) -> Result<Ok, Error> {
            (**self).erased_serialize_i64(v)
        }
        fn erased_serialize_u8(&mut self, v: u8) -> Result<Ok, Error> {
            (**self).erased_serialize_u8(v)
        }
        fn erased_serialize_u16(&mut self, v: u16) -> Result<Ok, Error> {
            (**self).erased_serialize_u16(v)
        }
        fn erased_serialize_u32(&mut self, v: u32) -> Result<Ok, Error> {
            (**self).erased_serialize_u32(v)
        }
        fn erased_serialize_u64(&mut self, v: u64) -> Result<Ok, Error> {
            (**self).erased_serialize_u64(v)
        }
        fn erased_serialize_i128(&mut self, v: i128) -> Result<Ok, Error> {
            (**self).erased_serialize_i128(v)
        }
        fn erased_serialize_u128(&mut self, v: u128) -> Result<Ok, Error> {
            (**self).erased_serialize_u128(v)
        }
        fn erased_serialize_f32(&mut self, v: f32) -> Result<Ok, Error> {
            (**self).erased_serialize_f32(v)
        }
        fn erased_serialize_f64(&mut self, v: f64) -> Result<Ok, Error> {
            (**self).erased_serialize_f64(v)
        }
        fn erased_serialize_char(&mut self, v: char) -> Result<Ok, Error> {
            (**self).erased_serialize_char(v)
        }
        fn erased_serialize_str(&mut self, v: &str) -> Result<Ok, Error> {
            (**self).erased_serialize_str(v)
        }
        fn erased_serialize_bytes(&mut self, v: &[u8]) -> Result<Ok, Error> {
            (**self).erased_serialize_bytes(v)
        }
        fn erased_serialize_none(&mut self) -> Result<Ok, Error> {
            (**self).erased_serialize_none()
        }
        fn erased_serialize_some(&mut self, v: &dyn Serialize) -> Result<Ok, Error> {
            (**self).erased_serialize_some(v)
        }
        fn erased_serialize_unit(&mut self) -> Result<Ok, Error> {
            (**self).erased_serialize_unit()
        }
        fn erased_serialize_unit_struct(
            &mut self,
            name: &'static str,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_unit_struct(name)
        }
        fn erased_serialize_unit_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_unit_variant(name, variant_index, variant)
        }
        fn erased_serialize_newtype_struct(
            &mut self,
            name: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_newtype_struct(name, v)
        }
        fn erased_serialize_newtype_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_newtype_variant(name, variant_index, variant, v)
        }
        fn erased_serialize_seq(&mut self, len: Option<usize>) -> Result<Seq, Error> {
            (**self).erased_serialize_seq(len)
        }
        fn erased_serialize_tuple(&mut self, len: usize) -> Result<Tuple, Error> {
            (**self).erased_serialize_tuple(len)
        }
        fn erased_serialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<TupleStruct, Error> {
            (**self).erased_serialize_tuple_struct(name, len)
        }
        fn erased_serialize_tuple_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<TupleVariant, Error> {
            (**self).erased_serialize_tuple_variant(name, variant_index, variant, len)
        }
        fn erased_serialize_map(&mut self, len: Option<usize>) -> Result<Map, Error> {
            (**self).erased_serialize_map(len)
        }
        fn erased_serialize_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<Struct, Error> {
            (**self).erased_serialize_struct(name, len)
        }
        fn erased_serialize_struct_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<StructVariant, Error> {
            (**self).erased_serialize_struct_variant(name, variant_index, variant, len)
        }
        fn erased_is_human_readable(&self) -> bool {
            (**self).erased_is_human_readable()
        }
    }
    impl<'a> Serializer for Box<dyn Serializer + Sync + 'a> {
        fn erased_serialize_bool(&mut self, v: bool) -> Result<Ok, Error> {
            (**self).erased_serialize_bool(v)
        }
        fn erased_serialize_i8(&mut self, v: i8) -> Result<Ok, Error> {
            (**self).erased_serialize_i8(v)
        }
        fn erased_serialize_i16(&mut self, v: i16) -> Result<Ok, Error> {
            (**self).erased_serialize_i16(v)
        }
        fn erased_serialize_i32(&mut self, v: i32) -> Result<Ok, Error> {
            (**self).erased_serialize_i32(v)
        }
        fn erased_serialize_i64(&mut self, v: i64) -> Result<Ok, Error> {
            (**self).erased_serialize_i64(v)
        }
        fn erased_serialize_u8(&mut self, v: u8) -> Result<Ok, Error> {
            (**self).erased_serialize_u8(v)
        }
        fn erased_serialize_u16(&mut self, v: u16) -> Result<Ok, Error> {
            (**self).erased_serialize_u16(v)
        }
        fn erased_serialize_u32(&mut self, v: u32) -> Result<Ok, Error> {
            (**self).erased_serialize_u32(v)
        }
        fn erased_serialize_u64(&mut self, v: u64) -> Result<Ok, Error> {
            (**self).erased_serialize_u64(v)
        }
        fn erased_serialize_i128(&mut self, v: i128) -> Result<Ok, Error> {
            (**self).erased_serialize_i128(v)
        }
        fn erased_serialize_u128(&mut self, v: u128) -> Result<Ok, Error> {
            (**self).erased_serialize_u128(v)
        }
        fn erased_serialize_f32(&mut self, v: f32) -> Result<Ok, Error> {
            (**self).erased_serialize_f32(v)
        }
        fn erased_serialize_f64(&mut self, v: f64) -> Result<Ok, Error> {
            (**self).erased_serialize_f64(v)
        }
        fn erased_serialize_char(&mut self, v: char) -> Result<Ok, Error> {
            (**self).erased_serialize_char(v)
        }
        fn erased_serialize_str(&mut self, v: &str) -> Result<Ok, Error> {
            (**self).erased_serialize_str(v)
        }
        fn erased_serialize_bytes(&mut self, v: &[u8]) -> Result<Ok, Error> {
            (**self).erased_serialize_bytes(v)
        }
        fn erased_serialize_none(&mut self) -> Result<Ok, Error> {
            (**self).erased_serialize_none()
        }
        fn erased_serialize_some(&mut self, v: &dyn Serialize) -> Result<Ok, Error> {
            (**self).erased_serialize_some(v)
        }
        fn erased_serialize_unit(&mut self) -> Result<Ok, Error> {
            (**self).erased_serialize_unit()
        }
        fn erased_serialize_unit_struct(
            &mut self,
            name: &'static str,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_unit_struct(name)
        }
        fn erased_serialize_unit_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_unit_variant(name, variant_index, variant)
        }
        fn erased_serialize_newtype_struct(
            &mut self,
            name: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_newtype_struct(name, v)
        }
        fn erased_serialize_newtype_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_newtype_variant(name, variant_index, variant, v)
        }
        fn erased_serialize_seq(&mut self, len: Option<usize>) -> Result<Seq, Error> {
            (**self).erased_serialize_seq(len)
        }
        fn erased_serialize_tuple(&mut self, len: usize) -> Result<Tuple, Error> {
            (**self).erased_serialize_tuple(len)
        }
        fn erased_serialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<TupleStruct, Error> {
            (**self).erased_serialize_tuple_struct(name, len)
        }
        fn erased_serialize_tuple_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<TupleVariant, Error> {
            (**self).erased_serialize_tuple_variant(name, variant_index, variant, len)
        }
        fn erased_serialize_map(&mut self, len: Option<usize>) -> Result<Map, Error> {
            (**self).erased_serialize_map(len)
        }
        fn erased_serialize_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<Struct, Error> {
            (**self).erased_serialize_struct(name, len)
        }
        fn erased_serialize_struct_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<StructVariant, Error> {
            (**self).erased_serialize_struct_variant(name, variant_index, variant, len)
        }
        fn erased_is_human_readable(&self) -> bool {
            (**self).erased_is_human_readable()
        }
    }
    impl<'a> Serializer for Box<dyn Serializer + Send + Sync + 'a> {
        fn erased_serialize_bool(&mut self, v: bool) -> Result<Ok, Error> {
            (**self).erased_serialize_bool(v)
        }
        fn erased_serialize_i8(&mut self, v: i8) -> Result<Ok, Error> {
            (**self).erased_serialize_i8(v)
        }
        fn erased_serialize_i16(&mut self, v: i16) -> Result<Ok, Error> {
            (**self).erased_serialize_i16(v)
        }
        fn erased_serialize_i32(&mut self, v: i32) -> Result<Ok, Error> {
            (**self).erased_serialize_i32(v)
        }
        fn erased_serialize_i64(&mut self, v: i64) -> Result<Ok, Error> {
            (**self).erased_serialize_i64(v)
        }
        fn erased_serialize_u8(&mut self, v: u8) -> Result<Ok, Error> {
            (**self).erased_serialize_u8(v)
        }
        fn erased_serialize_u16(&mut self, v: u16) -> Result<Ok, Error> {
            (**self).erased_serialize_u16(v)
        }
        fn erased_serialize_u32(&mut self, v: u32) -> Result<Ok, Error> {
            (**self).erased_serialize_u32(v)
        }
        fn erased_serialize_u64(&mut self, v: u64) -> Result<Ok, Error> {
            (**self).erased_serialize_u64(v)
        }
        fn erased_serialize_i128(&mut self, v: i128) -> Result<Ok, Error> {
            (**self).erased_serialize_i128(v)
        }
        fn erased_serialize_u128(&mut self, v: u128) -> Result<Ok, Error> {
            (**self).erased_serialize_u128(v)
        }
        fn erased_serialize_f32(&mut self, v: f32) -> Result<Ok, Error> {
            (**self).erased_serialize_f32(v)
        }
        fn erased_serialize_f64(&mut self, v: f64) -> Result<Ok, Error> {
            (**self).erased_serialize_f64(v)
        }
        fn erased_serialize_char(&mut self, v: char) -> Result<Ok, Error> {
            (**self).erased_serialize_char(v)
        }
        fn erased_serialize_str(&mut self, v: &str) -> Result<Ok, Error> {
            (**self).erased_serialize_str(v)
        }
        fn erased_serialize_bytes(&mut self, v: &[u8]) -> Result<Ok, Error> {
            (**self).erased_serialize_bytes(v)
        }
        fn erased_serialize_none(&mut self) -> Result<Ok, Error> {
            (**self).erased_serialize_none()
        }
        fn erased_serialize_some(&mut self, v: &dyn Serialize) -> Result<Ok, Error> {
            (**self).erased_serialize_some(v)
        }
        fn erased_serialize_unit(&mut self) -> Result<Ok, Error> {
            (**self).erased_serialize_unit()
        }
        fn erased_serialize_unit_struct(
            &mut self,
            name: &'static str,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_unit_struct(name)
        }
        fn erased_serialize_unit_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_unit_variant(name, variant_index, variant)
        }
        fn erased_serialize_newtype_struct(
            &mut self,
            name: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_newtype_struct(name, v)
        }
        fn erased_serialize_newtype_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_newtype_variant(name, variant_index, variant, v)
        }
        fn erased_serialize_seq(&mut self, len: Option<usize>) -> Result<Seq, Error> {
            (**self).erased_serialize_seq(len)
        }
        fn erased_serialize_tuple(&mut self, len: usize) -> Result<Tuple, Error> {
            (**self).erased_serialize_tuple(len)
        }
        fn erased_serialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<TupleStruct, Error> {
            (**self).erased_serialize_tuple_struct(name, len)
        }
        fn erased_serialize_tuple_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<TupleVariant, Error> {
            (**self).erased_serialize_tuple_variant(name, variant_index, variant, len)
        }
        fn erased_serialize_map(&mut self, len: Option<usize>) -> Result<Map, Error> {
            (**self).erased_serialize_map(len)
        }
        fn erased_serialize_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<Struct, Error> {
            (**self).erased_serialize_struct(name, len)
        }
        fn erased_serialize_struct_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<StructVariant, Error> {
            (**self).erased_serialize_struct_variant(name, variant_index, variant, len)
        }
        fn erased_is_human_readable(&self) -> bool {
            (**self).erased_is_human_readable()
        }
    }
    impl<'a, T: ?Sized + Serializer> Serializer for &'a mut T {
        fn erased_serialize_bool(&mut self, v: bool) -> Result<Ok, Error> {
            (**self).erased_serialize_bool(v)
        }
        fn erased_serialize_i8(&mut self, v: i8) -> Result<Ok, Error> {
            (**self).erased_serialize_i8(v)
        }
        fn erased_serialize_i16(&mut self, v: i16) -> Result<Ok, Error> {
            (**self).erased_serialize_i16(v)
        }
        fn erased_serialize_i32(&mut self, v: i32) -> Result<Ok, Error> {
            (**self).erased_serialize_i32(v)
        }
        fn erased_serialize_i64(&mut self, v: i64) -> Result<Ok, Error> {
            (**self).erased_serialize_i64(v)
        }
        fn erased_serialize_u8(&mut self, v: u8) -> Result<Ok, Error> {
            (**self).erased_serialize_u8(v)
        }
        fn erased_serialize_u16(&mut self, v: u16) -> Result<Ok, Error> {
            (**self).erased_serialize_u16(v)
        }
        fn erased_serialize_u32(&mut self, v: u32) -> Result<Ok, Error> {
            (**self).erased_serialize_u32(v)
        }
        fn erased_serialize_u64(&mut self, v: u64) -> Result<Ok, Error> {
            (**self).erased_serialize_u64(v)
        }
        fn erased_serialize_i128(&mut self, v: i128) -> Result<Ok, Error> {
            (**self).erased_serialize_i128(v)
        }
        fn erased_serialize_u128(&mut self, v: u128) -> Result<Ok, Error> {
            (**self).erased_serialize_u128(v)
        }
        fn erased_serialize_f32(&mut self, v: f32) -> Result<Ok, Error> {
            (**self).erased_serialize_f32(v)
        }
        fn erased_serialize_f64(&mut self, v: f64) -> Result<Ok, Error> {
            (**self).erased_serialize_f64(v)
        }
        fn erased_serialize_char(&mut self, v: char) -> Result<Ok, Error> {
            (**self).erased_serialize_char(v)
        }
        fn erased_serialize_str(&mut self, v: &str) -> Result<Ok, Error> {
            (**self).erased_serialize_str(v)
        }
        fn erased_serialize_bytes(&mut self, v: &[u8]) -> Result<Ok, Error> {
            (**self).erased_serialize_bytes(v)
        }
        fn erased_serialize_none(&mut self) -> Result<Ok, Error> {
            (**self).erased_serialize_none()
        }
        fn erased_serialize_some(&mut self, v: &dyn Serialize) -> Result<Ok, Error> {
            (**self).erased_serialize_some(v)
        }
        fn erased_serialize_unit(&mut self) -> Result<Ok, Error> {
            (**self).erased_serialize_unit()
        }
        fn erased_serialize_unit_struct(
            &mut self,
            name: &'static str,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_unit_struct(name)
        }
        fn erased_serialize_unit_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_unit_variant(name, variant_index, variant)
        }
        fn erased_serialize_newtype_struct(
            &mut self,
            name: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_newtype_struct(name, v)
        }
        fn erased_serialize_newtype_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            v: &dyn Serialize,
        ) -> Result<Ok, Error> {
            (**self).erased_serialize_newtype_variant(name, variant_index, variant, v)
        }
        fn erased_serialize_seq(&mut self, len: Option<usize>) -> Result<Seq, Error> {
            (**self).erased_serialize_seq(len)
        }
        fn erased_serialize_tuple(&mut self, len: usize) -> Result<Tuple, Error> {
            (**self).erased_serialize_tuple(len)
        }
        fn erased_serialize_tuple_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<TupleStruct, Error> {
            (**self).erased_serialize_tuple_struct(name, len)
        }
        fn erased_serialize_tuple_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<TupleVariant, Error> {
            (**self).erased_serialize_tuple_variant(name, variant_index, variant, len)
        }
        fn erased_serialize_map(&mut self, len: Option<usize>) -> Result<Map, Error> {
            (**self).erased_serialize_map(len)
        }
        fn erased_serialize_struct(
            &mut self,
            name: &'static str,
            len: usize,
        ) -> Result<Struct, Error> {
            (**self).erased_serialize_struct(name, len)
        }
        fn erased_serialize_struct_variant(
            &mut self,
            name: &'static str,
            variant_index: u32,
            variant: &'static str,
            len: usize,
        ) -> Result<StructVariant, Error> {
            (**self).erased_serialize_struct_variant(name, variant_index, variant, len)
        }
        fn erased_is_human_readable(&self) -> bool {
            (**self).erased_is_human_readable()
        }
    }
    fn erase<E>(e: E) -> Error
    where
        E: Display,
    {
        serde::ser::Error::custom(e)
    }
    fn unerase<E>(e: Error) -> E
    where
        E: serde::ser::Error,
    {
        E::custom(e)
    }
}
pub use crate::de::{deserialize, Deserializer};
pub use crate::error::{Error, Result};
pub use crate::ser::{serialize, Serialize, Serializer};
#[doc(hidden)]
pub mod private {
    pub use core::marker::{Send, Sized, Sync};
    pub use core::result::Result;
    pub use serde;
    pub fn require_erased_serialize_impl<T>()
    where
        T: ?Sized + crate::Serialize,
    {}
}
