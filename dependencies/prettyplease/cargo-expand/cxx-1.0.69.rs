#![feature(prelude_import)]
#![no_std]
#![doc(html_root_url = "https://docs.rs/cxx/1.0.69")]
#![deny(improper_ctypes, improper_ctypes_definitions, missing_docs)]
#![deny(unsafe_op_in_unsafe_fn)]
#![allow(non_camel_case_types)]
#![allow(
    clippy::cognitive_complexity,
    clippy::declare_interior_mutable_const,
    clippy::doc_markdown,
    clippy::empty_enum,
    clippy::inherent_to_string,
    clippy::items_after_statements,
    clippy::large_enum_variant,
    clippy::len_without_is_empty,
    clippy::missing_errors_doc,
    clippy::missing_safety_doc,
    clippy::module_inception,
    clippy::module_name_repetitions,
    clippy::must_use_candidate,
    clippy::needless_doctest_main,
    clippy::new_without_default,
    clippy::or_fun_call,
    clippy::ptr_arg,
    clippy::toplevel_ref_arg,
    clippy::transmute_undefined_repr,
    clippy::useless_let_if_seq,
    clippy::wrong_self_convention
)]
#[prelude_import]
use core::prelude::rust_2018::*;
#[macro_use]
extern crate core;
#[macro_use]
extern crate compiler_builtins;
#[cfg(built_with_cargo)]
extern crate link_cplusplus;
extern crate self as cxx;
#[doc(hidden)]
pub extern crate core;
#[cfg(feature = "alloc")]
#[doc(hidden)]
pub extern crate alloc;
#[cfg(feature = "std")]
#[doc(hidden)]
pub extern crate std;
#[macro_use]
mod macros {
    #[macro_use]
    mod assert {}
    #[macro_use]
    mod concat {}
}
mod c_char {
    #![cfg(feature = "alloc")]
    pub type c_char = c_char_definition::c_char;
    #[allow(dead_code)]
    mod c_char_definition {
        pub use self::signed::*;
        mod unsigned {
            pub type c_char = u8;
        }
        mod signed {
            pub type c_char = i8;
        }
    }
}
mod cxx_vector {
    use crate::extern_type::ExternType;
    use crate::kind::Trivial;
    use crate::string::CxxString;
    use core::ffi::c_void;
    use core::fmt::{self, Debug};
    use core::iter::FusedIterator;
    use core::marker::{PhantomData, PhantomPinned};
    use core::mem::{self, ManuallyDrop, MaybeUninit};
    use core::pin::Pin;
    use core::slice;
    #[repr(C, packed)]
    pub struct CxxVector<T> {
        _void: [c_void; 0],
        _elements: PhantomData<[T]>,
        _pinned: PhantomData<PhantomPinned>,
    }
    impl<T> CxxVector<T>
    where
        T: VectorElement,
    {
        pub fn len(&self) -> usize {
            T::__vector_size(self)
        }
        pub fn is_empty(&self) -> bool {
            self.len() == 0
        }
        pub fn get(&self, pos: usize) -> Option<&T> {
            if pos < self.len() {
                Some(unsafe { self.get_unchecked(pos) })
            } else {
                None
            }
        }
        pub fn index_mut(self: Pin<&mut Self>, pos: usize) -> Option<Pin<&mut T>> {
            if pos < self.len() {
                Some(unsafe { self.index_unchecked_mut(pos) })
            } else {
                None
            }
        }
        pub unsafe fn get_unchecked(&self, pos: usize) -> &T {
            let this = self as *const CxxVector<T> as *mut CxxVector<T>;
            unsafe {
                let ptr = T::__get_unchecked(this, pos) as *const T;
                &*ptr
            }
        }
        pub unsafe fn index_unchecked_mut(
            self: Pin<&mut Self>,
            pos: usize,
        ) -> Pin<&mut T> {
            unsafe {
                let ptr = T::__get_unchecked(self.get_unchecked_mut(), pos);
                Pin::new_unchecked(&mut *ptr)
            }
        }
        pub fn as_slice(&self) -> &[T]
        where
            T: ExternType<Kind = Trivial>,
        {
            let len = self.len();
            if len == 0 {
                &[]
            } else {
                let this = self as *const CxxVector<T> as *mut CxxVector<T>;
                let ptr = unsafe { T::__get_unchecked(this, 0) };
                unsafe { slice::from_raw_parts(ptr, len) }
            }
        }
        pub fn as_mut_slice(self: Pin<&mut Self>) -> &mut [T]
        where
            T: ExternType<Kind = Trivial>,
        {
            let len = self.len();
            if len == 0 {
                &mut []
            } else {
                let ptr = unsafe { T::__get_unchecked(self.get_unchecked_mut(), 0) };
                unsafe { slice::from_raw_parts_mut(ptr, len) }
            }
        }
        pub fn iter(&self) -> Iter<T> {
            Iter { v: self, index: 0 }
        }
        pub fn iter_mut(self: Pin<&mut Self>) -> IterMut<T> {
            IterMut { v: self, index: 0 }
        }
        pub fn push(self: Pin<&mut Self>, value: T)
        where
            T: ExternType<Kind = Trivial>,
        {
            let mut value = ManuallyDrop::new(value);
            unsafe {
                T::__push_back(self, &mut value);
            }
        }
        pub fn pop(self: Pin<&mut Self>) -> Option<T>
        where
            T: ExternType<Kind = Trivial>,
        {
            if self.is_empty() {
                None
            } else {
                let mut value = MaybeUninit::uninit();
                Some(unsafe {
                    T::__pop_back(self, &mut value);
                    value.assume_init()
                })
            }
        }
    }
    pub struct Iter<'a, T> {
        v: &'a CxxVector<T>,
        index: usize,
    }
    impl<'a, T> IntoIterator for &'a CxxVector<T>
    where
        T: VectorElement,
    {
        type Item = &'a T;
        type IntoIter = Iter<'a, T>;
        fn into_iter(self) -> Self::IntoIter {
            self.iter()
        }
    }
    impl<'a, T> Iterator for Iter<'a, T>
    where
        T: VectorElement,
    {
        type Item = &'a T;
        fn next(&mut self) -> Option<Self::Item> {
            let next = self.v.get(self.index)?;
            self.index += 1;
            Some(next)
        }
        fn size_hint(&self) -> (usize, Option<usize>) {
            let len = self.len();
            (len, Some(len))
        }
    }
    impl<'a, T> ExactSizeIterator for Iter<'a, T>
    where
        T: VectorElement,
    {
        fn len(&self) -> usize {
            self.v.len() - self.index
        }
    }
    impl<'a, T> FusedIterator for Iter<'a, T>
    where
        T: VectorElement,
    {}
    pub struct IterMut<'a, T> {
        v: Pin<&'a mut CxxVector<T>>,
        index: usize,
    }
    impl<'a, T> IntoIterator for Pin<&'a mut CxxVector<T>>
    where
        T: VectorElement,
    {
        type Item = Pin<&'a mut T>;
        type IntoIter = IterMut<'a, T>;
        fn into_iter(self) -> Self::IntoIter {
            self.iter_mut()
        }
    }
    impl<'a, T> Iterator for IterMut<'a, T>
    where
        T: VectorElement,
    {
        type Item = Pin<&'a mut T>;
        fn next(&mut self) -> Option<Self::Item> {
            let next = self.v.as_mut().index_mut(self.index)?;
            self.index += 1;
            unsafe {
                let ptr = Pin::into_inner_unchecked(next) as *mut T;
                Some(Pin::new_unchecked(&mut *ptr))
            }
        }
        fn size_hint(&self) -> (usize, Option<usize>) {
            let len = self.len();
            (len, Some(len))
        }
    }
    impl<'a, T> ExactSizeIterator for IterMut<'a, T>
    where
        T: VectorElement,
    {
        fn len(&self) -> usize {
            self.v.len() - self.index
        }
    }
    impl<'a, T> FusedIterator for IterMut<'a, T>
    where
        T: VectorElement,
    {}
    impl<T> Debug for CxxVector<T>
    where
        T: VectorElement + Debug,
    {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.debug_list().entries(self).finish()
        }
    }
    pub unsafe trait VectorElement: Sized {
        #[doc(hidden)]
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result;
        #[doc(hidden)]
        fn __vector_size(v: &CxxVector<Self>) -> usize;
        #[doc(hidden)]
        unsafe fn __get_unchecked(v: *mut CxxVector<Self>, pos: usize) -> *mut Self;
        #[doc(hidden)]
        unsafe fn __push_back(
            v: Pin<&mut CxxVector<Self>>,
            value: &mut ManuallyDrop<Self>,
        ) {
            let _ = v;
            let _ = value;
            ::core::panicking::panic("internal error: entered unreachable code")
        }
        #[doc(hidden)]
        unsafe fn __pop_back(v: Pin<&mut CxxVector<Self>>, out: &mut MaybeUninit<Self>) {
            let _ = v;
            let _ = out;
            ::core::panicking::panic("internal error: entered unreachable code")
        }
        #[doc(hidden)]
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void>;
        #[doc(hidden)]
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void>;
        #[doc(hidden)]
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self>;
        #[doc(hidden)]
        unsafe fn __unique_ptr_release(
            repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self>;
        #[doc(hidden)]
        unsafe fn __unique_ptr_drop(repr: MaybeUninit<*mut c_void>);
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<u8>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<u8>>()];
    unsafe impl VectorElement for u8 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("u8")
        }
        fn __vector_size(v: &CxxVector<u8>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u8$size"]
                fn __vector_size(_: &CxxVector<u8>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(v: *mut CxxVector<u8>, pos: usize) -> *mut u8 {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u8$get_unchecked"]
                fn __get_unchecked(_: *mut CxxVector<u8>, _: usize) -> *mut u8;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        unsafe fn __push_back(v: Pin<&mut CxxVector<u8>>, value: &mut ManuallyDrop<u8>) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u8$push_back"]
                fn __push_back(_: Pin<&mut CxxVector<u8>>, _: &mut ManuallyDrop<u8>);
            }
            unsafe { __push_back(v, value) }
        }
        unsafe fn __pop_back(v: Pin<&mut CxxVector<u8>>, out: &mut MaybeUninit<u8>) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u8$pop_back"]
                fn __pop_back(_: Pin<&mut CxxVector<u8>>, _: &mut MaybeUninit<u8>);
            }
            unsafe { __pop_back(v, out) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u8$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u8$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<u8>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u8$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<u8>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u8$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<u8>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u8$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<u16>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<u16>>()];
    unsafe impl VectorElement for u16 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("u16")
        }
        fn __vector_size(v: &CxxVector<u16>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u16$size"]
                fn __vector_size(_: &CxxVector<u16>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(v: *mut CxxVector<u16>, pos: usize) -> *mut u16 {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u16$get_unchecked"]
                fn __get_unchecked(_: *mut CxxVector<u16>, _: usize) -> *mut u16;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        unsafe fn __push_back(
            v: Pin<&mut CxxVector<u16>>,
            value: &mut ManuallyDrop<u16>,
        ) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u16$push_back"]
                fn __push_back(_: Pin<&mut CxxVector<u16>>, _: &mut ManuallyDrop<u16>);
            }
            unsafe { __push_back(v, value) }
        }
        unsafe fn __pop_back(v: Pin<&mut CxxVector<u16>>, out: &mut MaybeUninit<u16>) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u16$pop_back"]
                fn __pop_back(_: Pin<&mut CxxVector<u16>>, _: &mut MaybeUninit<u16>);
            }
            unsafe { __pop_back(v, out) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u16$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u16$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<u16>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u16$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<u16>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u16$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<u16>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u16$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<u32>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<u32>>()];
    unsafe impl VectorElement for u32 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("u32")
        }
        fn __vector_size(v: &CxxVector<u32>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u32$size"]
                fn __vector_size(_: &CxxVector<u32>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(v: *mut CxxVector<u32>, pos: usize) -> *mut u32 {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u32$get_unchecked"]
                fn __get_unchecked(_: *mut CxxVector<u32>, _: usize) -> *mut u32;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        unsafe fn __push_back(
            v: Pin<&mut CxxVector<u32>>,
            value: &mut ManuallyDrop<u32>,
        ) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u32$push_back"]
                fn __push_back(_: Pin<&mut CxxVector<u32>>, _: &mut ManuallyDrop<u32>);
            }
            unsafe { __push_back(v, value) }
        }
        unsafe fn __pop_back(v: Pin<&mut CxxVector<u32>>, out: &mut MaybeUninit<u32>) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u32$pop_back"]
                fn __pop_back(_: Pin<&mut CxxVector<u32>>, _: &mut MaybeUninit<u32>);
            }
            unsafe { __pop_back(v, out) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u32$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u32$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<u32>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u32$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<u32>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u32$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<u32>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u32$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<u64>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<u64>>()];
    unsafe impl VectorElement for u64 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("u64")
        }
        fn __vector_size(v: &CxxVector<u64>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u64$size"]
                fn __vector_size(_: &CxxVector<u64>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(v: *mut CxxVector<u64>, pos: usize) -> *mut u64 {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u64$get_unchecked"]
                fn __get_unchecked(_: *mut CxxVector<u64>, _: usize) -> *mut u64;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        unsafe fn __push_back(
            v: Pin<&mut CxxVector<u64>>,
            value: &mut ManuallyDrop<u64>,
        ) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u64$push_back"]
                fn __push_back(_: Pin<&mut CxxVector<u64>>, _: &mut ManuallyDrop<u64>);
            }
            unsafe { __push_back(v, value) }
        }
        unsafe fn __pop_back(v: Pin<&mut CxxVector<u64>>, out: &mut MaybeUninit<u64>) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$u64$pop_back"]
                fn __pop_back(_: Pin<&mut CxxVector<u64>>, _: &mut MaybeUninit<u64>);
            }
            unsafe { __pop_back(v, out) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u64$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u64$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<u64>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u64$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<u64>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u64$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<u64>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$u64$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<usize>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<usize>>()];
    unsafe impl VectorElement for usize {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("usize")
        }
        fn __vector_size(v: &CxxVector<usize>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$usize$size"]
                fn __vector_size(_: &CxxVector<usize>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(v: *mut CxxVector<usize>, pos: usize) -> *mut usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$usize$get_unchecked"]
                fn __get_unchecked(_: *mut CxxVector<usize>, _: usize) -> *mut usize;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        unsafe fn __push_back(
            v: Pin<&mut CxxVector<usize>>,
            value: &mut ManuallyDrop<usize>,
        ) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$usize$push_back"]
                fn __push_back(
                    _: Pin<&mut CxxVector<usize>>,
                    _: &mut ManuallyDrop<usize>,
                );
            }
            unsafe { __push_back(v, value) }
        }
        unsafe fn __pop_back(
            v: Pin<&mut CxxVector<usize>>,
            out: &mut MaybeUninit<usize>,
        ) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$usize$pop_back"]
                fn __pop_back(_: Pin<&mut CxxVector<usize>>, _: &mut MaybeUninit<usize>);
            }
            unsafe { __pop_back(v, out) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$usize$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$usize$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<usize>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$usize$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<usize>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$usize$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<usize>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$usize$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<i8>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<i8>>()];
    unsafe impl VectorElement for i8 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("i8")
        }
        fn __vector_size(v: &CxxVector<i8>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i8$size"]
                fn __vector_size(_: &CxxVector<i8>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(v: *mut CxxVector<i8>, pos: usize) -> *mut i8 {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i8$get_unchecked"]
                fn __get_unchecked(_: *mut CxxVector<i8>, _: usize) -> *mut i8;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        unsafe fn __push_back(v: Pin<&mut CxxVector<i8>>, value: &mut ManuallyDrop<i8>) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i8$push_back"]
                fn __push_back(_: Pin<&mut CxxVector<i8>>, _: &mut ManuallyDrop<i8>);
            }
            unsafe { __push_back(v, value) }
        }
        unsafe fn __pop_back(v: Pin<&mut CxxVector<i8>>, out: &mut MaybeUninit<i8>) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i8$pop_back"]
                fn __pop_back(_: Pin<&mut CxxVector<i8>>, _: &mut MaybeUninit<i8>);
            }
            unsafe { __pop_back(v, out) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i8$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i8$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<i8>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i8$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<i8>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i8$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<i8>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i8$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<i16>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<i16>>()];
    unsafe impl VectorElement for i16 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("i16")
        }
        fn __vector_size(v: &CxxVector<i16>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i16$size"]
                fn __vector_size(_: &CxxVector<i16>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(v: *mut CxxVector<i16>, pos: usize) -> *mut i16 {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i16$get_unchecked"]
                fn __get_unchecked(_: *mut CxxVector<i16>, _: usize) -> *mut i16;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        unsafe fn __push_back(
            v: Pin<&mut CxxVector<i16>>,
            value: &mut ManuallyDrop<i16>,
        ) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i16$push_back"]
                fn __push_back(_: Pin<&mut CxxVector<i16>>, _: &mut ManuallyDrop<i16>);
            }
            unsafe { __push_back(v, value) }
        }
        unsafe fn __pop_back(v: Pin<&mut CxxVector<i16>>, out: &mut MaybeUninit<i16>) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i16$pop_back"]
                fn __pop_back(_: Pin<&mut CxxVector<i16>>, _: &mut MaybeUninit<i16>);
            }
            unsafe { __pop_back(v, out) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i16$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i16$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<i16>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i16$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<i16>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i16$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<i16>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i16$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<i32>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<i32>>()];
    unsafe impl VectorElement for i32 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("i32")
        }
        fn __vector_size(v: &CxxVector<i32>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i32$size"]
                fn __vector_size(_: &CxxVector<i32>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(v: *mut CxxVector<i32>, pos: usize) -> *mut i32 {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i32$get_unchecked"]
                fn __get_unchecked(_: *mut CxxVector<i32>, _: usize) -> *mut i32;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        unsafe fn __push_back(
            v: Pin<&mut CxxVector<i32>>,
            value: &mut ManuallyDrop<i32>,
        ) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i32$push_back"]
                fn __push_back(_: Pin<&mut CxxVector<i32>>, _: &mut ManuallyDrop<i32>);
            }
            unsafe { __push_back(v, value) }
        }
        unsafe fn __pop_back(v: Pin<&mut CxxVector<i32>>, out: &mut MaybeUninit<i32>) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i32$pop_back"]
                fn __pop_back(_: Pin<&mut CxxVector<i32>>, _: &mut MaybeUninit<i32>);
            }
            unsafe { __pop_back(v, out) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i32$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i32$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<i32>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i32$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<i32>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i32$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<i32>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i32$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<i64>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<i64>>()];
    unsafe impl VectorElement for i64 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("i64")
        }
        fn __vector_size(v: &CxxVector<i64>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i64$size"]
                fn __vector_size(_: &CxxVector<i64>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(v: *mut CxxVector<i64>, pos: usize) -> *mut i64 {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i64$get_unchecked"]
                fn __get_unchecked(_: *mut CxxVector<i64>, _: usize) -> *mut i64;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        unsafe fn __push_back(
            v: Pin<&mut CxxVector<i64>>,
            value: &mut ManuallyDrop<i64>,
        ) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i64$push_back"]
                fn __push_back(_: Pin<&mut CxxVector<i64>>, _: &mut ManuallyDrop<i64>);
            }
            unsafe { __push_back(v, value) }
        }
        unsafe fn __pop_back(v: Pin<&mut CxxVector<i64>>, out: &mut MaybeUninit<i64>) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$i64$pop_back"]
                fn __pop_back(_: Pin<&mut CxxVector<i64>>, _: &mut MaybeUninit<i64>);
            }
            unsafe { __pop_back(v, out) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i64$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i64$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<i64>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i64$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<i64>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i64$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<i64>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$i64$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<isize>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<isize>>()];
    unsafe impl VectorElement for isize {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("isize")
        }
        fn __vector_size(v: &CxxVector<isize>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$isize$size"]
                fn __vector_size(_: &CxxVector<isize>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(v: *mut CxxVector<isize>, pos: usize) -> *mut isize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$isize$get_unchecked"]
                fn __get_unchecked(_: *mut CxxVector<isize>, _: usize) -> *mut isize;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        unsafe fn __push_back(
            v: Pin<&mut CxxVector<isize>>,
            value: &mut ManuallyDrop<isize>,
        ) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$isize$push_back"]
                fn __push_back(
                    _: Pin<&mut CxxVector<isize>>,
                    _: &mut ManuallyDrop<isize>,
                );
            }
            unsafe { __push_back(v, value) }
        }
        unsafe fn __pop_back(
            v: Pin<&mut CxxVector<isize>>,
            out: &mut MaybeUninit<isize>,
        ) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$isize$pop_back"]
                fn __pop_back(_: Pin<&mut CxxVector<isize>>, _: &mut MaybeUninit<isize>);
            }
            unsafe { __pop_back(v, out) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$isize$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$isize$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<isize>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$isize$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<isize>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$isize$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<isize>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$isize$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<f32>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<f32>>()];
    unsafe impl VectorElement for f32 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("f32")
        }
        fn __vector_size(v: &CxxVector<f32>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$f32$size"]
                fn __vector_size(_: &CxxVector<f32>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(v: *mut CxxVector<f32>, pos: usize) -> *mut f32 {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$f32$get_unchecked"]
                fn __get_unchecked(_: *mut CxxVector<f32>, _: usize) -> *mut f32;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        unsafe fn __push_back(
            v: Pin<&mut CxxVector<f32>>,
            value: &mut ManuallyDrop<f32>,
        ) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$f32$push_back"]
                fn __push_back(_: Pin<&mut CxxVector<f32>>, _: &mut ManuallyDrop<f32>);
            }
            unsafe { __push_back(v, value) }
        }
        unsafe fn __pop_back(v: Pin<&mut CxxVector<f32>>, out: &mut MaybeUninit<f32>) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$f32$pop_back"]
                fn __pop_back(_: Pin<&mut CxxVector<f32>>, _: &mut MaybeUninit<f32>);
            }
            unsafe { __pop_back(v, out) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$f32$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$f32$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<f32>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$f32$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<f32>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$f32$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<f32>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$f32$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<f64>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<f64>>()];
    unsafe impl VectorElement for f64 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("f64")
        }
        fn __vector_size(v: &CxxVector<f64>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$f64$size"]
                fn __vector_size(_: &CxxVector<f64>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(v: *mut CxxVector<f64>, pos: usize) -> *mut f64 {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$f64$get_unchecked"]
                fn __get_unchecked(_: *mut CxxVector<f64>, _: usize) -> *mut f64;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        unsafe fn __push_back(
            v: Pin<&mut CxxVector<f64>>,
            value: &mut ManuallyDrop<f64>,
        ) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$f64$push_back"]
                fn __push_back(_: Pin<&mut CxxVector<f64>>, _: &mut ManuallyDrop<f64>);
            }
            unsafe { __push_back(v, value) }
        }
        unsafe fn __pop_back(v: Pin<&mut CxxVector<f64>>, out: &mut MaybeUninit<f64>) {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$f64$pop_back"]
                fn __pop_back(_: Pin<&mut CxxVector<f64>>, _: &mut MaybeUninit<f64>);
            }
            unsafe { __pop_back(v, out) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$f64$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$f64$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<f64>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$f64$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<f64>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$f64$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<f64>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$f64$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
    const _: [(); 0] = [(); mem::size_of::<CxxVector<CxxString>>()];
    const _: [(); 1] = [(); mem::align_of::<CxxVector<CxxString>>()];
    unsafe impl VectorElement for CxxString {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("CxxString")
        }
        fn __vector_size(v: &CxxVector<CxxString>) -> usize {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$string$size"]
                fn __vector_size(_: &CxxVector<CxxString>) -> usize;
            }
            unsafe { __vector_size(v) }
        }
        unsafe fn __get_unchecked(
            v: *mut CxxVector<CxxString>,
            pos: usize,
        ) -> *mut CxxString {
            extern "C" {
                #[link_name = "cxxbridge1$std$vector$string$get_unchecked"]
                fn __get_unchecked(
                    _: *mut CxxVector<CxxString>,
                    _: usize,
                ) -> *mut CxxString;
            }
            unsafe { __get_unchecked(v, pos) }
        }
        fn __unique_ptr_null() -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$string$null"]
                fn __unique_ptr_null(this: *mut MaybeUninit<*mut c_void>);
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_null(&mut repr) }
            repr
        }
        unsafe fn __unique_ptr_raw(
            raw: *mut CxxVector<Self>,
        ) -> MaybeUninit<*mut c_void> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$string$raw"]
                fn __unique_ptr_raw(
                    this: *mut MaybeUninit<*mut c_void>,
                    raw: *mut CxxVector<CxxString>,
                );
            }
            let mut repr = MaybeUninit::uninit();
            unsafe { __unique_ptr_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __unique_ptr_get(
            repr: MaybeUninit<*mut c_void>,
        ) -> *const CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$string$get"]
                fn __unique_ptr_get(
                    this: *const MaybeUninit<*mut c_void>,
                ) -> *const CxxVector<CxxString>;
            }
            unsafe { __unique_ptr_get(&repr) }
        }
        unsafe fn __unique_ptr_release(
            mut repr: MaybeUninit<*mut c_void>,
        ) -> *mut CxxVector<Self> {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$string$release"]
                fn __unique_ptr_release(
                    this: *mut MaybeUninit<*mut c_void>,
                ) -> *mut CxxVector<CxxString>;
            }
            unsafe { __unique_ptr_release(&mut repr) }
        }
        unsafe fn __unique_ptr_drop(mut repr: MaybeUninit<*mut c_void>) {
            extern "C" {
                #[link_name = "cxxbridge1$unique_ptr$std$vector$string$drop"]
                fn __unique_ptr_drop(this: *mut MaybeUninit<*mut c_void>);
            }
            unsafe { __unique_ptr_drop(&mut repr) }
        }
    }
}
mod exception {
    #![cfg(feature = "alloc")]
    use alloc::boxed::Box;
    use core::fmt::{self, Display};
    pub struct Exception {
        pub(crate) what: Box<str>,
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::fmt::Debug for Exception {
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match *self {
                Self { what: ref __self_0_0 } => {
                    let debug_trait_builder = &mut ::core::fmt::Formatter::debug_struct(
                        f,
                        "Exception",
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "what",
                        &&(*__self_0_0),
                    );
                    ::core::fmt::DebugStruct::finish(debug_trait_builder)
                }
            }
        }
    }
    impl Display for Exception {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str(&self.what)
        }
    }
    #[cfg(feature = "std")]
    impl std::error::Error for Exception {}
    impl Exception {
        #[allow(missing_docs)]
        pub fn what(&self) -> &str {
            &self.what
        }
    }
}
mod extern_type {
    use self::kind::{Kind, Opaque, Trivial};
    use crate::CxxString;
    #[cfg(feature = "alloc")]
    use alloc::string::String;
    pub unsafe trait ExternType {
        type Id;
        type Kind: Kind;
    }
    pub mod kind {
        use super::private;
        pub enum Opaque {}
        pub enum Trivial {}
        #[allow(missing_docs)]
        pub trait Kind: private::Sealed {}
        impl Kind for Opaque {}
        impl Kind for Trivial {}
    }
    mod private {
        pub trait Sealed {}
        impl Sealed for super::Opaque {}
        impl Sealed for super::Trivial {}
    }
    #[doc(hidden)]
    pub fn verify_extern_type<T: ExternType<Id = Id>, Id>() {}
    #[doc(hidden)]
    pub fn verify_extern_kind<T: ExternType<Kind = Kind>, Kind: self::Kind>() {}
    unsafe impl ExternType for bool {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (crate::b, crate::o, crate::o, crate::l);
        type Kind = Trivial;
    }
    unsafe impl ExternType for u8 {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (
            crate::s,
            crate::t,
            crate::d,
            (),
            crate::u,
            crate::i,
            crate::n,
            crate::t,
            crate::_8,
            crate::__,
            crate::t,
        );
        type Kind = Trivial;
    }
    unsafe impl ExternType for u16 {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (
            crate::s,
            crate::t,
            crate::d,
            (),
            crate::u,
            crate::i,
            crate::n,
            crate::t,
            crate::_1,
            crate::_6,
            crate::__,
            crate::t,
        );
        type Kind = Trivial;
    }
    unsafe impl ExternType for u32 {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (
            crate::s,
            crate::t,
            crate::d,
            (),
            crate::u,
            crate::i,
            crate::n,
            crate::t,
            crate::_3,
            crate::_2,
            crate::__,
            crate::t,
        );
        type Kind = Trivial;
    }
    unsafe impl ExternType for u64 {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (
            crate::s,
            crate::t,
            crate::d,
            (),
            crate::u,
            crate::i,
            crate::n,
            crate::t,
            crate::_6,
            crate::_4,
            crate::__,
            crate::t,
        );
        type Kind = Trivial;
    }
    unsafe impl ExternType for usize {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (crate::s, crate::i, crate::z, crate::e, crate::__, crate::t);
        type Kind = Trivial;
    }
    unsafe impl ExternType for i8 {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (
            crate::s,
            crate::t,
            crate::d,
            (),
            crate::i,
            crate::n,
            crate::t,
            crate::_8,
            crate::__,
            crate::t,
        );
        type Kind = Trivial;
    }
    unsafe impl ExternType for i16 {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (
            crate::s,
            crate::t,
            crate::d,
            (),
            crate::i,
            crate::n,
            crate::t,
            crate::_1,
            crate::_6,
            crate::__,
            crate::t,
        );
        type Kind = Trivial;
    }
    unsafe impl ExternType for i32 {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (
            crate::s,
            crate::t,
            crate::d,
            (),
            crate::i,
            crate::n,
            crate::t,
            crate::_3,
            crate::_2,
            crate::__,
            crate::t,
        );
        type Kind = Trivial;
    }
    unsafe impl ExternType for i64 {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (
            crate::s,
            crate::t,
            crate::d,
            (),
            crate::i,
            crate::n,
            crate::t,
            crate::_6,
            crate::_4,
            crate::__,
            crate::t,
        );
        type Kind = Trivial;
    }
    unsafe impl ExternType for isize {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (
            crate::r,
            crate::u,
            crate::s,
            crate::t,
            (),
            crate::i,
            crate::s,
            crate::i,
            crate::z,
            crate::e,
        );
        type Kind = Trivial;
    }
    unsafe impl ExternType for f32 {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (crate::f, crate::l, crate::o, crate::a, crate::t);
        type Kind = Trivial;
    }
    unsafe impl ExternType for f64 {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (crate::d, crate::o, crate::u, crate::b, crate::l, crate::e);
        type Kind = Trivial;
    }
    #[cfg(feature = "alloc")]
    unsafe impl ExternType for String {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (
            crate::r,
            crate::u,
            crate::s,
            crate::t,
            (),
            crate::S,
            crate::t,
            crate::r,
            crate::i,
            crate::n,
            crate::g,
        );
        type Kind = Trivial;
    }
    unsafe impl ExternType for CxxString {
        #[allow(unused_attributes)]
        #[doc(hidden)]
        type Id = (
            crate::s,
            crate::t,
            crate::d,
            (),
            crate::s,
            crate::t,
            crate::r,
            crate::i,
            crate::n,
            crate::g,
        );
        type Kind = Opaque;
    }
}
mod fmt {
    use core::fmt::{self, Display};
    pub(crate) fn display(
        fmt: impl Fn(&mut fmt::Formatter) -> fmt::Result,
    ) -> impl Display {
        DisplayInvoke(fmt)
    }
    struct DisplayInvoke<T>(T);
    impl<T> Display for DisplayInvoke<T>
    where
        T: Fn(&mut fmt::Formatter) -> fmt::Result,
    {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            (self.0)(formatter)
        }
    }
}
mod function {
    #![allow(missing_docs)]
    use core::ffi::c_void;
    #[repr(C)]
    pub struct FatFunction {
        pub trampoline: *const c_void,
        pub ptr: *const c_void,
    }
}
mod hash {
    use core::hash::{Hash, Hasher};
    #[doc(hidden)]
    pub fn hash<V: Hash>(value: &V) -> usize {
        #[cfg(feature = "std")]
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        Hash::hash(value, &mut hasher);
        Hasher::finish(&hasher) as usize
    }
}
mod lossy {
    use core::char;
    use core::fmt::{self, Write as _};
    use core::str;
    pub fn display(mut bytes: &[u8], f: &mut fmt::Formatter) -> fmt::Result {
        loop {
            match str::from_utf8(bytes) {
                Ok(valid) => return f.write_str(valid),
                Err(utf8_error) => {
                    let valid_up_to = utf8_error.valid_up_to();
                    let valid = unsafe {
                        str::from_utf8_unchecked(&bytes[..valid_up_to])
                    };
                    f.write_str(valid)?;
                    f.write_char(char::REPLACEMENT_CHARACTER)?;
                    if let Some(error_len) = utf8_error.error_len() {
                        bytes = &bytes[valid_up_to + error_len..];
                    } else {
                        return Ok(());
                    }
                }
            }
        }
    }
    pub fn debug(mut bytes: &[u8], f: &mut fmt::Formatter) -> fmt::Result {
        f.write_char('"')?;
        while !bytes.is_empty() {
            let from_utf8_result = str::from_utf8(bytes);
            let valid = match from_utf8_result {
                Ok(valid) => valid,
                Err(utf8_error) => {
                    let valid_up_to = utf8_error.valid_up_to();
                    unsafe { str::from_utf8_unchecked(&bytes[..valid_up_to]) }
                }
            };
            let mut written = 0;
            for (i, ch) in valid.char_indices() {
                let esc = ch.escape_debug();
                if esc.len() != 1 {
                    f.write_str(&valid[written..i])?;
                    for ch in esc {
                        f.write_char(ch)?;
                    }
                    written = i + ch.len_utf8();
                }
            }
            f.write_str(&valid[written..])?;
            match from_utf8_result {
                Ok(_valid) => break,
                Err(utf8_error) => {
                    let end_of_broken = if let Some(error_len) = utf8_error.error_len() {
                        valid.len() + error_len
                    } else {
                        bytes.len()
                    };
                    for b in &bytes[valid.len()..end_of_broken] {
                        {
                            let result = f
                                .write_fmt(
                                    ::core::fmt::Arguments::new_v1_formatted(
                                        &["\\x"],
                                        &[::core::fmt::ArgumentV1::new_lower_hex(&b)],
                                        &[
                                            ::core::fmt::rt::v1::Argument {
                                                position: 0usize,
                                                format: ::core::fmt::rt::v1::FormatSpec {
                                                    fill: ' ',
                                                    align: ::core::fmt::rt::v1::Alignment::Unknown,
                                                    flags: 8u32,
                                                    precision: ::core::fmt::rt::v1::Count::Implied,
                                                    width: ::core::fmt::rt::v1::Count::Is(2usize),
                                                },
                                            },
                                        ],
                                        unsafe { ::core::fmt::UnsafeArg::new() },
                                    ),
                                );
                            result
                        }?;
                    }
                    bytes = &bytes[end_of_broken..];
                }
            }
        }
        f.write_char('"')
    }
}
pub mod memory {
    pub use crate::shared_ptr::SharedPtrTarget;
    pub use crate::unique_ptr::UniquePtrTarget;
    pub use crate::weak_ptr::WeakPtrTarget;
    #[doc(no_inline)]
    pub use cxx::{SharedPtr, UniquePtr};
}
mod opaque {
    #![allow(missing_docs)]
    use crate::void;
    use core::marker::{PhantomData, PhantomPinned};
    use core::mem;
    #[repr(C, packed)]
    pub struct Opaque {
        _private: [*const void; 0],
        _pinned: PhantomData<PhantomPinned>,
    }
    const _: [(); 0] = [(); mem::size_of::<Opaque>()];
    const _: [(); 1] = [(); mem::align_of::<Opaque>()];
}
mod result {
    #![cfg(feature = "alloc")]
    #![allow(missing_docs)]
    use crate::exception::Exception;
    use alloc::boxed::Box;
    use alloc::string::{String, ToString};
    use core::fmt::Display;
    use core::ptr::{self, NonNull};
    use core::result::Result as StdResult;
    use core::slice;
    use core::str;
    #[repr(C)]
    struct PtrLen {
        ptr: NonNull<u8>,
        len: usize,
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::marker::Copy for PtrLen {}
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::clone::Clone for PtrLen {
        #[inline]
        fn clone(&self) -> PtrLen {
            {
                let _: ::core::clone::AssertParamIsClone<NonNull<u8>>;
                let _: ::core::clone::AssertParamIsClone<usize>;
                *self
            }
        }
    }
    #[repr(C)]
    pub union Result {
        err: PtrLen,
        ok: *const u8,
    }
    pub unsafe fn r#try<T, E>(ret: *mut T, result: StdResult<T, E>) -> Result
    where
        E: Display,
    {
        match result {
            Ok(ok) => {
                unsafe { ptr::write(ret, ok) }
                Result { ok: ptr::null() }
            }
            Err(err) => unsafe { to_c_error(err.to_string()) }
        }
    }
    unsafe fn to_c_error(msg: String) -> Result {
        let mut msg = msg;
        unsafe { msg.as_mut_vec() }.push(b'\0');
        let ptr = msg.as_ptr();
        let len = msg.len();
        extern "C" {
            #[link_name = "cxxbridge1$error"]
            fn error(ptr: *const u8, len: usize) -> NonNull<u8>;
        }
        let copy = unsafe { error(ptr, len) };
        let err = PtrLen { ptr: copy, len };
        Result { err }
    }
    impl Result {
        pub unsafe fn exception(self) -> StdResult<(), Exception> {
            unsafe {
                if self.ok.is_null() {
                    Ok(())
                } else {
                    let err = self.err;
                    let slice = slice::from_raw_parts_mut(err.ptr.as_ptr(), err.len);
                    let s = str::from_utf8_unchecked_mut(slice);
                    Err(Exception {
                        what: Box::from_raw(s),
                    })
                }
            }
        }
    }
}
mod rust_slice {
    #![allow(missing_docs)]
    use core::mem::{self, MaybeUninit};
    use core::ptr::{self, NonNull};
    use core::slice;
    #[repr(C)]
    pub struct RustSlice {
        repr: [MaybeUninit<
            usize,
        >; mem::size_of::<NonNull<[()]>>() / mem::size_of::<usize>()],
    }
    impl RustSlice {
        pub fn from_ref<T>(slice: &[T]) -> Self {
            let ptr = NonNull::from(slice).cast::<T>();
            let len = slice.len();
            Self::from_raw_parts(ptr, len)
        }
        pub fn from_mut<T>(slice: &mut [T]) -> Self {
            let ptr = NonNull::from(&mut *slice).cast::<T>();
            let len = slice.len();
            Self::from_raw_parts(ptr, len)
        }
        pub unsafe fn as_slice<'a, T>(self) -> &'a [T] {
            let ptr = self.as_non_null_ptr().as_ptr();
            let len = self.len();
            unsafe { slice::from_raw_parts(ptr, len) }
        }
        pub unsafe fn as_mut_slice<'a, T>(self) -> &'a mut [T] {
            let ptr = self.as_non_null_ptr().as_ptr();
            let len = self.len();
            unsafe { slice::from_raw_parts_mut(ptr, len) }
        }
        pub(crate) fn from_raw_parts<T>(ptr: NonNull<T>, len: usize) -> Self {
            let ptr = ptr::slice_from_raw_parts_mut(ptr.as_ptr().cast(), len);
            unsafe {
                mem::transmute::<NonNull<[()]>, RustSlice>(NonNull::new_unchecked(ptr))
            }
        }
        pub(crate) fn as_non_null_ptr<T>(&self) -> NonNull<T> {
            let rust_slice = RustSlice { repr: self.repr };
            let repr = unsafe { mem::transmute::<RustSlice, NonNull<[()]>>(rust_slice) };
            repr.cast()
        }
        pub(crate) fn len(&self) -> usize {
            let rust_slice = RustSlice { repr: self.repr };
            let repr = unsafe { mem::transmute::<RustSlice, NonNull<[()]>>(rust_slice) };
            unsafe { repr.as_ref() }.len()
        }
    }
    const _: [(); mem::size_of::<NonNull<[()]>>()] = [(); mem::size_of::<RustSlice>()];
    const _: [(); mem::align_of::<NonNull<[()]>>()] = [(); mem::align_of::<RustSlice>()];
}
mod rust_str {
    #![allow(missing_docs)]
    use core::mem::{self, MaybeUninit};
    use core::ptr::NonNull;
    use core::str;
    #[repr(C)]
    pub struct RustStr {
        repr: [MaybeUninit<
            usize,
        >; mem::size_of::<NonNull<str>>() / mem::size_of::<usize>()],
    }
    impl RustStr {
        pub fn from(repr: &str) -> Self {
            let repr = NonNull::from(repr);
            unsafe { mem::transmute::<NonNull<str>, RustStr>(repr) }
        }
        pub unsafe fn as_str<'a>(self) -> &'a str {
            unsafe {
                let repr = mem::transmute::<RustStr, NonNull<str>>(self);
                &*repr.as_ptr()
            }
        }
    }
    const _: [(); mem::size_of::<NonNull<str>>()] = [(); mem::size_of::<RustStr>()];
    const _: [(); mem::align_of::<NonNull<str>>()] = [(); mem::align_of::<RustStr>()];
}
mod rust_string {
    #![cfg(feature = "alloc")]
    #![allow(missing_docs)]
    use alloc::string::String;
    use core::mem::{self, MaybeUninit};
    use core::ptr;
    #[repr(C)]
    pub struct RustString {
        repr: [MaybeUninit<usize>; mem::size_of::<String>() / mem::size_of::<usize>()],
    }
    impl RustString {
        pub fn from(s: String) -> Self {
            unsafe { mem::transmute::<String, RustString>(s) }
        }
        pub fn from_ref(s: &String) -> &Self {
            unsafe { &*(s as *const String as *const RustString) }
        }
        pub fn from_mut(s: &mut String) -> &mut Self {
            unsafe { &mut *(s as *mut String as *mut RustString) }
        }
        pub fn into_string(self) -> String {
            unsafe { mem::transmute::<RustString, String>(self) }
        }
        pub fn as_string(&self) -> &String {
            unsafe { &*(self as *const RustString as *const String) }
        }
        pub fn as_mut_string(&mut self) -> &mut String {
            unsafe { &mut *(self as *mut RustString as *mut String) }
        }
    }
    impl Drop for RustString {
        fn drop(&mut self) {
            unsafe { ptr::drop_in_place(self.as_mut_string()) }
        }
    }
    const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<RustString>()];
    const _: [(); mem::size_of::<String>()] = [(); mem::size_of::<RustString>()];
    const _: [(); mem::align_of::<String>()] = [(); mem::align_of::<RustString>()];
}
mod rust_type {
    #![allow(missing_docs)]
    pub unsafe trait RustType {}
    pub unsafe trait ImplBox {}
    pub unsafe trait ImplVec {}
}
mod rust_vec {
    #![cfg(feature = "alloc")]
    #![allow(missing_docs)]
    use crate::rust_string::RustString;
    use alloc::string::String;
    use alloc::vec::Vec;
    use core::ffi::c_void;
    use core::marker::PhantomData;
    use core::mem::{self, ManuallyDrop, MaybeUninit};
    use core::ptr;
    #[repr(C)]
    pub struct RustVec<T> {
        repr: [MaybeUninit<
            usize,
        >; mem::size_of::<Vec<c_void>>() / mem::size_of::<usize>()],
        marker: PhantomData<Vec<T>>,
    }
    impl<T> RustVec<T> {
        pub fn new() -> Self {
            Self::from(Vec::new())
        }
        pub fn from(v: Vec<T>) -> Self {
            unsafe { mem::transmute::<Vec<T>, RustVec<T>>(v) }
        }
        pub fn from_ref(v: &Vec<T>) -> &Self {
            unsafe { &*(v as *const Vec<T> as *const RustVec<T>) }
        }
        pub fn from_mut(v: &mut Vec<T>) -> &mut Self {
            unsafe { &mut *(v as *mut Vec<T> as *mut RustVec<T>) }
        }
        pub fn into_vec(self) -> Vec<T> {
            unsafe { mem::transmute::<RustVec<T>, Vec<T>>(self) }
        }
        pub fn as_vec(&self) -> &Vec<T> {
            unsafe { &*(self as *const RustVec<T> as *const Vec<T>) }
        }
        pub fn as_mut_vec(&mut self) -> &mut Vec<T> {
            unsafe { &mut *(self as *mut RustVec<T> as *mut Vec<T>) }
        }
        pub fn len(&self) -> usize {
            self.as_vec().len()
        }
        pub fn capacity(&self) -> usize {
            self.as_vec().capacity()
        }
        pub fn as_ptr(&self) -> *const T {
            self.as_vec().as_ptr()
        }
        pub fn reserve_total(&mut self, new_cap: usize) {
            let vec = self.as_mut_vec();
            if new_cap > vec.capacity() {
                let additional = new_cap - vec.len();
                vec.reserve(additional);
            }
        }
        pub unsafe fn set_len(&mut self, len: usize) {
            unsafe { self.as_mut_vec().set_len(len) }
        }
        pub fn truncate(&mut self, len: usize) {
            self.as_mut_vec().truncate(len);
        }
    }
    impl RustVec<RustString> {
        pub fn from_vec_string(v: Vec<String>) -> Self {
            let mut v = ManuallyDrop::new(v);
            let ptr = v.as_mut_ptr().cast::<RustString>();
            let len = v.len();
            let cap = v.capacity();
            Self::from(unsafe { Vec::from_raw_parts(ptr, len, cap) })
        }
        pub fn from_ref_vec_string(v: &Vec<String>) -> &Self {
            Self::from_ref(unsafe {
                &*(v as *const Vec<String> as *const Vec<RustString>)
            })
        }
        pub fn from_mut_vec_string(v: &mut Vec<String>) -> &mut Self {
            Self::from_mut(unsafe {
                &mut *(v as *mut Vec<String> as *mut Vec<RustString>)
            })
        }
        pub fn into_vec_string(self) -> Vec<String> {
            let mut v = ManuallyDrop::new(self.into_vec());
            let ptr = v.as_mut_ptr().cast::<String>();
            let len = v.len();
            let cap = v.capacity();
            unsafe { Vec::from_raw_parts(ptr, len, cap) }
        }
        pub fn as_vec_string(&self) -> &Vec<String> {
            unsafe { &*(self as *const RustVec<RustString> as *const Vec<String>) }
        }
        pub fn as_mut_vec_string(&mut self) -> &mut Vec<String> {
            unsafe { &mut *(self as *mut RustVec<RustString> as *mut Vec<String>) }
        }
    }
    impl<T> Drop for RustVec<T> {
        fn drop(&mut self) {
            unsafe { ptr::drop_in_place(self.as_mut_vec()) }
        }
    }
}
mod shared_ptr {
    use crate::fmt::display;
    use crate::kind::Trivial;
    use crate::string::CxxString;
    use crate::weak_ptr::{WeakPtr, WeakPtrTarget};
    use crate::ExternType;
    use core::ffi::c_void;
    use core::fmt::{self, Debug, Display};
    use core::marker::PhantomData;
    use core::mem::MaybeUninit;
    use core::ops::Deref;
    #[repr(C)]
    pub struct SharedPtr<T>
    where
        T: SharedPtrTarget,
    {
        repr: [MaybeUninit<*mut c_void>; 2],
        ty: PhantomData<T>,
    }
    impl<T> SharedPtr<T>
    where
        T: SharedPtrTarget,
    {
        pub fn null() -> Self {
            let mut shared_ptr = MaybeUninit::<SharedPtr<T>>::uninit();
            let new = shared_ptr.as_mut_ptr().cast();
            unsafe {
                T::__null(new);
                shared_ptr.assume_init()
            }
        }
        pub fn new(value: T) -> Self
        where
            T: ExternType<Kind = Trivial>,
        {
            let mut shared_ptr = MaybeUninit::<SharedPtr<T>>::uninit();
            let new = shared_ptr.as_mut_ptr().cast();
            unsafe {
                T::__new(value, new);
                shared_ptr.assume_init()
            }
        }
        pub fn is_null(&self) -> bool {
            let this = self as *const Self as *const c_void;
            let ptr = unsafe { T::__get(this) };
            ptr.is_null()
        }
        pub fn as_ref(&self) -> Option<&T> {
            let this = self as *const Self as *const c_void;
            unsafe { T::__get(this).as_ref() }
        }
        pub fn downgrade(self: &SharedPtr<T>) -> WeakPtr<T>
        where
            T: WeakPtrTarget,
        {
            let this = self as *const Self as *const c_void;
            let mut weak_ptr = MaybeUninit::<WeakPtr<T>>::uninit();
            let new = weak_ptr.as_mut_ptr().cast();
            unsafe {
                T::__downgrade(this, new);
                weak_ptr.assume_init()
            }
        }
    }
    unsafe impl<T> Send for SharedPtr<T>
    where
        T: Send + Sync + SharedPtrTarget,
    {}
    unsafe impl<T> Sync for SharedPtr<T>
    where
        T: Send + Sync + SharedPtrTarget,
    {}
    impl<T> Clone for SharedPtr<T>
    where
        T: SharedPtrTarget,
    {
        fn clone(&self) -> Self {
            let mut shared_ptr = MaybeUninit::<SharedPtr<T>>::uninit();
            let new = shared_ptr.as_mut_ptr().cast();
            let this = self as *const Self as *mut c_void;
            unsafe {
                T::__clone(this, new);
                shared_ptr.assume_init()
            }
        }
    }
    impl<T> Drop for SharedPtr<T>
    where
        T: SharedPtrTarget,
    {
        fn drop(&mut self) {
            let this = self as *mut Self as *mut c_void;
            unsafe { T::__drop(this) }
        }
    }
    impl<T> Deref for SharedPtr<T>
    where
        T: SharedPtrTarget,
    {
        type Target = T;
        fn deref(&self) -> &Self::Target {
            match self.as_ref() {
                Some(target) => target,
                None => {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(
                            &["called deref on a null SharedPtr<", ">"],
                            &[
                                ::core::fmt::ArgumentV1::new_display(
                                    &display(T::__typename),
                                ),
                            ],
                        ),
                    )
                }
            }
        }
    }
    impl<T> Debug for SharedPtr<T>
    where
        T: Debug + SharedPtrTarget,
    {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            match self.as_ref() {
                None => formatter.write_str("nullptr"),
                Some(value) => Debug::fmt(value, formatter),
            }
        }
    }
    impl<T> Display for SharedPtr<T>
    where
        T: Display + SharedPtrTarget,
    {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            match self.as_ref() {
                None => formatter.write_str("nullptr"),
                Some(value) => Display::fmt(value, formatter),
            }
        }
    }
    pub unsafe trait SharedPtrTarget {
        #[doc(hidden)]
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result;
        #[doc(hidden)]
        unsafe fn __null(new: *mut c_void);
        #[doc(hidden)]
        unsafe fn __new(value: Self, new: *mut c_void)
        where
            Self: Sized,
        {
            let _ = value;
            let _ = new;
            ::core::panicking::panic("internal error: entered unreachable code")
        }
        #[doc(hidden)]
        unsafe fn __clone(this: *const c_void, new: *mut c_void);
        #[doc(hidden)]
        unsafe fn __get(this: *const c_void) -> *const Self;
        #[doc(hidden)]
        unsafe fn __drop(this: *mut c_void);
    }
    unsafe impl SharedPtrTarget for bool {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("bool")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$bool$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$bool$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<bool>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$bool$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$bool$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$bool$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for u8 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("u8")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u8$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u8$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<u8>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u8$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u8$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u8$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for u16 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("u16")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u16$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u16$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<u16>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u16$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u16$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u16$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for u32 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("u32")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u32$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u32$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<u32>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u32$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u32$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u32$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for u64 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("u64")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u64$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u64$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<u64>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u64$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u64$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$u64$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for usize {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("usize")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$usize$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$usize$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<usize>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$usize$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$usize$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$usize$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for i8 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("i8")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i8$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i8$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<i8>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i8$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i8$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i8$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for i16 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("i16")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i16$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i16$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<i16>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i16$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i16$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i16$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for i32 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("i32")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i32$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i32$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<i32>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i32$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i32$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i32$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for i64 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("i64")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i64$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i64$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<i64>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i64$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i64$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$i64$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for isize {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("isize")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$isize$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$isize$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<isize>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$isize$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$isize$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$isize$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for f32 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("f32")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$f32$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$f32$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<f32>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$f32$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$f32$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$f32$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for f64 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("f64")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$f64$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$f64$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<f64>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$f64$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$f64$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$f64$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl SharedPtrTarget for CxxString {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("CxxString")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$string$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __new(value: Self, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$string$uninit"]
                fn __uninit(new: *mut c_void) -> *mut c_void;
            }
            unsafe { __uninit(new).cast::<CxxString>().write(value) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$string$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __get(this: *const c_void) -> *const Self {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$string$get"]
                fn __get(this: *const c_void) -> *const c_void;
            }
            unsafe { __get(this) }.cast()
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$shared_ptr$string$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
}
#[path = "cxx_string.rs"]
mod string {
    use crate::actually_private::Private;
    use crate::lossy;
    #[cfg(feature = "alloc")]
    use alloc::borrow::Cow;
    #[cfg(feature = "alloc")]
    use alloc::string::String;
    use core::cmp::Ordering;
    use core::fmt::{self, Debug, Display};
    use core::hash::{Hash, Hasher};
    use core::marker::{PhantomData, PhantomPinned};
    use core::mem::MaybeUninit;
    use core::pin::Pin;
    use core::slice;
    use core::str::{self, Utf8Error};
    extern "C" {
        #[link_name = "cxxbridge1$cxx_string$init"]
        fn string_init(this: &mut MaybeUninit<CxxString>, ptr: *const u8, len: usize);
        #[link_name = "cxxbridge1$cxx_string$destroy"]
        fn string_destroy(this: &mut MaybeUninit<CxxString>);
        #[link_name = "cxxbridge1$cxx_string$data"]
        fn string_data(this: &CxxString) -> *const u8;
        #[link_name = "cxxbridge1$cxx_string$length"]
        fn string_length(this: &CxxString) -> usize;
        #[link_name = "cxxbridge1$cxx_string$clear"]
        fn string_clear(this: Pin<&mut CxxString>);
        #[link_name = "cxxbridge1$cxx_string$reserve_total"]
        fn string_reserve_total(this: Pin<&mut CxxString>, new_cap: usize);
        #[link_name = "cxxbridge1$cxx_string$push"]
        fn string_push(this: Pin<&mut CxxString>, ptr: *const u8, len: usize);
    }
    #[repr(C)]
    pub struct CxxString {
        _private: [u8; 0],
        _pinned: PhantomData<PhantomPinned>,
    }
    impl CxxString {
        pub fn new<T: Private>() -> Self {
            ::core::panicking::panic("internal error: entered unreachable code")
        }
        pub fn len(&self) -> usize {
            unsafe { string_length(self) }
        }
        pub fn is_empty(&self) -> bool {
            self.len() == 0
        }
        pub fn as_bytes(&self) -> &[u8] {
            let data = self.as_ptr();
            let len = self.len();
            unsafe { slice::from_raw_parts(data, len) }
        }
        pub fn as_ptr(&self) -> *const u8 {
            unsafe { string_data(self) }
        }
        pub fn to_str(&self) -> Result<&str, Utf8Error> {
            str::from_utf8(self.as_bytes())
        }
        #[cfg(feature = "alloc")]
        pub fn to_string_lossy(&self) -> Cow<str> {
            String::from_utf8_lossy(self.as_bytes())
        }
        pub fn clear(self: Pin<&mut Self>) {
            unsafe { string_clear(self) }
        }
        pub fn reserve(self: Pin<&mut Self>, additional: usize) {
            let new_cap = self
                .len()
                .checked_add(additional)
                .expect("CxxString capacity overflow");
            unsafe { string_reserve_total(self, new_cap) }
        }
        pub fn push_str(self: Pin<&mut Self>, s: &str) {
            self.push_bytes(s.as_bytes());
        }
        pub fn push_bytes(self: Pin<&mut Self>, bytes: &[u8]) {
            unsafe { string_push(self, bytes.as_ptr(), bytes.len()) }
        }
    }
    impl Display for CxxString {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            lossy::display(self.as_bytes(), f)
        }
    }
    impl Debug for CxxString {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            lossy::debug(self.as_bytes(), f)
        }
    }
    impl PartialEq for CxxString {
        fn eq(&self, other: &Self) -> bool {
            self.as_bytes() == other.as_bytes()
        }
    }
    impl PartialEq<CxxString> for str {
        fn eq(&self, other: &CxxString) -> bool {
            self.as_bytes() == other.as_bytes()
        }
    }
    impl PartialEq<str> for CxxString {
        fn eq(&self, other: &str) -> bool {
            self.as_bytes() == other.as_bytes()
        }
    }
    impl Eq for CxxString {}
    impl PartialOrd for CxxString {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            self.as_bytes().partial_cmp(other.as_bytes())
        }
    }
    impl Ord for CxxString {
        fn cmp(&self, other: &Self) -> Ordering {
            self.as_bytes().cmp(other.as_bytes())
        }
    }
    impl Hash for CxxString {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.as_bytes().hash(state);
        }
    }
    #[doc(hidden)]
    #[repr(C)]
    pub struct StackString {
        space: MaybeUninit<[usize; 8]>,
    }
    #[allow(missing_docs)]
    impl StackString {
        pub fn new() -> Self {
            StackString {
                space: MaybeUninit::uninit(),
            }
        }
        pub unsafe fn init(&mut self, value: impl AsRef<[u8]>) -> Pin<&mut CxxString> {
            let value = value.as_ref();
            unsafe {
                let this = &mut *self
                    .space
                    .as_mut_ptr()
                    .cast::<MaybeUninit<CxxString>>();
                string_init(this, value.as_ptr(), value.len());
                Pin::new_unchecked(&mut *this.as_mut_ptr())
            }
        }
    }
    impl Drop for StackString {
        fn drop(&mut self) {
            unsafe {
                let this = &mut *self
                    .space
                    .as_mut_ptr()
                    .cast::<MaybeUninit<CxxString>>();
                string_destroy(this);
            }
        }
    }
}
mod symbols {
    mod exception {
        #![cfg(feature = "alloc")]
        use alloc::boxed::Box;
        use alloc::string::String;
        use core::slice;
        #[export_name = "cxxbridge1$exception"]
        unsafe extern "C" fn exception(ptr: *const u8, len: usize) -> *const u8 {
            let slice = unsafe { slice::from_raw_parts(ptr, len) };
            let boxed = String::from_utf8_lossy(slice).into_owned().into_boxed_str();
            Box::leak(boxed).as_ptr()
        }
    }
    mod rust_slice {
        use crate::rust_slice::RustSlice;
        use core::mem::MaybeUninit;
        use core::ptr::{self, NonNull};
        #[export_name = "cxxbridge1$slice$new"]
        unsafe extern "C" fn slice_new(
            this: &mut MaybeUninit<RustSlice>,
            ptr: NonNull<()>,
            len: usize,
        ) {
            let this = this.as_mut_ptr();
            let rust_slice = RustSlice::from_raw_parts(ptr, len);
            unsafe { ptr::write(this, rust_slice) }
        }
        #[export_name = "cxxbridge1$slice$ptr"]
        unsafe extern "C" fn slice_ptr(this: &RustSlice) -> NonNull<()> {
            this.as_non_null_ptr()
        }
        #[export_name = "cxxbridge1$slice$len"]
        unsafe extern "C" fn slice_len(this: &RustSlice) -> usize {
            this.len()
        }
    }
    mod rust_str {
        #[cfg(feature = "alloc")]
        use alloc::string::String;
        use core::mem::MaybeUninit;
        use core::ptr;
        use core::slice;
        use core::str;
        #[export_name = "cxxbridge1$str$new"]
        unsafe extern "C" fn str_new(this: &mut MaybeUninit<&str>) {
            let this = this.as_mut_ptr();
            unsafe { ptr::write(this, "") }
        }
        #[cfg(feature = "alloc")]
        #[export_name = "cxxbridge1$str$ref"]
        unsafe extern "C" fn str_ref<'a>(
            this: &mut MaybeUninit<&'a str>,
            string: &'a String,
        ) {
            let this = this.as_mut_ptr();
            let s = string.as_str();
            unsafe { ptr::write(this, s) }
        }
        #[export_name = "cxxbridge1$str$from"]
        unsafe extern "C" fn str_from(
            this: &mut MaybeUninit<&str>,
            ptr: *const u8,
            len: usize,
        ) -> bool {
            let slice = unsafe { slice::from_raw_parts(ptr, len) };
            match str::from_utf8(slice) {
                Ok(s) => {
                    let this = this.as_mut_ptr();
                    unsafe { ptr::write(this, s) }
                    true
                }
                Err(_) => false,
            }
        }
        #[export_name = "cxxbridge1$str$ptr"]
        unsafe extern "C" fn str_ptr(this: &&str) -> *const u8 {
            this.as_ptr()
        }
        #[export_name = "cxxbridge1$str$len"]
        unsafe extern "C" fn str_len(this: &&str) -> usize {
            this.len()
        }
    }
    mod rust_string {
        #![cfg(feature = "alloc")]
        use alloc::borrow::ToOwned;
        use alloc::string::String;
        use core::mem::{ManuallyDrop, MaybeUninit};
        use core::ptr;
        use core::slice;
        use core::str;
        #[export_name = "cxxbridge1$string$new"]
        unsafe extern "C" fn string_new(this: &mut MaybeUninit<String>) {
            let this = this.as_mut_ptr();
            let new = String::new();
            unsafe { ptr::write(this, new) }
        }
        #[export_name = "cxxbridge1$string$clone"]
        unsafe extern "C" fn string_clone(
            this: &mut MaybeUninit<String>,
            other: &String,
        ) {
            let this = this.as_mut_ptr();
            let clone = other.clone();
            unsafe { ptr::write(this, clone) }
        }
        #[export_name = "cxxbridge1$string$from_utf8"]
        unsafe extern "C" fn string_from_utf8(
            this: &mut MaybeUninit<String>,
            ptr: *const u8,
            len: usize,
        ) -> bool {
            let slice = unsafe { slice::from_raw_parts(ptr, len) };
            match str::from_utf8(slice) {
                Ok(s) => {
                    let this = this.as_mut_ptr();
                    let owned = s.to_owned();
                    unsafe { ptr::write(this, owned) }
                    true
                }
                Err(_) => false,
            }
        }
        #[export_name = "cxxbridge1$string$from_utf8_lossy"]
        unsafe extern "C" fn string_from_utf8_lossy(
            this: &mut MaybeUninit<String>,
            ptr: *const u8,
            len: usize,
        ) {
            let slice = unsafe { slice::from_raw_parts(ptr, len) };
            let owned = String::from_utf8_lossy(slice).into_owned();
            let this = this.as_mut_ptr();
            unsafe { ptr::write(this, owned) }
        }
        #[export_name = "cxxbridge1$string$from_utf16"]
        unsafe extern "C" fn string_from_utf16(
            this: &mut MaybeUninit<String>,
            ptr: *const u16,
            len: usize,
        ) -> bool {
            let slice = unsafe { slice::from_raw_parts(ptr, len) };
            match String::from_utf16(slice) {
                Ok(s) => {
                    let this = this.as_mut_ptr();
                    unsafe { ptr::write(this, s) }
                    true
                }
                Err(_) => false,
            }
        }
        #[export_name = "cxxbridge1$string$from_utf16_lossy"]
        unsafe extern "C" fn string_from_utf16_lossy(
            this: &mut MaybeUninit<String>,
            ptr: *const u16,
            len: usize,
        ) {
            let slice = unsafe { slice::from_raw_parts(ptr, len) };
            let owned = String::from_utf16_lossy(slice);
            let this = this.as_mut_ptr();
            unsafe { ptr::write(this, owned) }
        }
        #[export_name = "cxxbridge1$string$drop"]
        unsafe extern "C" fn string_drop(this: &mut ManuallyDrop<String>) {
            unsafe { ManuallyDrop::drop(this) }
        }
        #[export_name = "cxxbridge1$string$ptr"]
        unsafe extern "C" fn string_ptr(this: &String) -> *const u8 {
            this.as_ptr()
        }
        #[export_name = "cxxbridge1$string$len"]
        unsafe extern "C" fn string_len(this: &String) -> usize {
            this.len()
        }
        #[export_name = "cxxbridge1$string$capacity"]
        unsafe extern "C" fn string_capacity(this: &String) -> usize {
            this.capacity()
        }
        #[export_name = "cxxbridge1$string$reserve_additional"]
        unsafe extern "C" fn string_reserve_additional(
            this: &mut String,
            additional: usize,
        ) {
            this.reserve(additional);
        }
        #[export_name = "cxxbridge1$string$reserve_total"]
        unsafe extern "C" fn string_reserve_total(this: &mut String, new_cap: usize) {
            if new_cap > this.capacity() {
                let additional = new_cap - this.len();
                this.reserve(additional);
            }
        }
    }
    mod rust_vec {
        #![cfg(feature = "alloc")]
        use crate::c_char::c_char;
        use crate::rust_string::RustString;
        use crate::rust_vec::RustVec;
        use alloc::vec::Vec;
        use core::mem;
        use core::ptr;
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<bool>,
        >()];
        const _: [(); mem::size_of::<Vec<bool>>()] = [(); mem::size_of::<
            RustVec<bool>,
        >()];
        const _: [(); mem::align_of::<Vec<bool>>()] = [(); mem::align_of::<
            RustVec<bool>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$bool$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<bool>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$bool$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<bool>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$bool$len"]
            unsafe extern "C" fn __len(this: *const RustVec<bool>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$bool$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<bool>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$bool$data"]
            unsafe extern "C" fn __data(this: *const RustVec<bool>) -> *const bool {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$bool$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<bool>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$bool$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<bool>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$bool$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<bool>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<u8>,
        >()];
        const _: [(); mem::size_of::<Vec<u8>>()] = [(); mem::size_of::<RustVec<u8>>()];
        const _: [(); mem::align_of::<Vec<u8>>()] = [(); mem::align_of::<RustVec<u8>>()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$u8$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<u8>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$u8$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<u8>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$u8$len"]
            unsafe extern "C" fn __len(this: *const RustVec<u8>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$u8$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<u8>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$u8$data"]
            unsafe extern "C" fn __data(this: *const RustVec<u8>) -> *const u8 {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$u8$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<u8>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$u8$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<u8>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$u8$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<u8>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<u16>,
        >()];
        const _: [(); mem::size_of::<Vec<u16>>()] = [(); mem::size_of::<RustVec<u16>>()];
        const _: [(); mem::align_of::<Vec<u16>>()] = [(); mem::align_of::<
            RustVec<u16>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$u16$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<u16>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$u16$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<u16>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$u16$len"]
            unsafe extern "C" fn __len(this: *const RustVec<u16>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$u16$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<u16>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$u16$data"]
            unsafe extern "C" fn __data(this: *const RustVec<u16>) -> *const u16 {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$u16$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<u16>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$u16$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<u16>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$u16$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<u16>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<u32>,
        >()];
        const _: [(); mem::size_of::<Vec<u32>>()] = [(); mem::size_of::<RustVec<u32>>()];
        const _: [(); mem::align_of::<Vec<u32>>()] = [(); mem::align_of::<
            RustVec<u32>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$u32$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<u32>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$u32$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<u32>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$u32$len"]
            unsafe extern "C" fn __len(this: *const RustVec<u32>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$u32$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<u32>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$u32$data"]
            unsafe extern "C" fn __data(this: *const RustVec<u32>) -> *const u32 {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$u32$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<u32>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$u32$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<u32>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$u32$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<u32>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<u64>,
        >()];
        const _: [(); mem::size_of::<Vec<u64>>()] = [(); mem::size_of::<RustVec<u64>>()];
        const _: [(); mem::align_of::<Vec<u64>>()] = [(); mem::align_of::<
            RustVec<u64>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$u64$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<u64>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$u64$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<u64>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$u64$len"]
            unsafe extern "C" fn __len(this: *const RustVec<u64>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$u64$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<u64>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$u64$data"]
            unsafe extern "C" fn __data(this: *const RustVec<u64>) -> *const u64 {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$u64$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<u64>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$u64$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<u64>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$u64$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<u64>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<usize>,
        >()];
        const _: [(); mem::size_of::<Vec<usize>>()] = [(); mem::size_of::<
            RustVec<usize>,
        >()];
        const _: [(); mem::align_of::<Vec<usize>>()] = [(); mem::align_of::<
            RustVec<usize>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$usize$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<usize>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$usize$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<usize>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$usize$len"]
            unsafe extern "C" fn __len(this: *const RustVec<usize>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$usize$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<usize>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$usize$data"]
            unsafe extern "C" fn __data(this: *const RustVec<usize>) -> *const usize {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$usize$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<usize>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$usize$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<usize>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$usize$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<usize>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<i8>,
        >()];
        const _: [(); mem::size_of::<Vec<i8>>()] = [(); mem::size_of::<RustVec<i8>>()];
        const _: [(); mem::align_of::<Vec<i8>>()] = [(); mem::align_of::<RustVec<i8>>()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$i8$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<i8>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$i8$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<i8>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$i8$len"]
            unsafe extern "C" fn __len(this: *const RustVec<i8>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$i8$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<i8>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$i8$data"]
            unsafe extern "C" fn __data(this: *const RustVec<i8>) -> *const i8 {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$i8$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<i8>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$i8$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<i8>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$i8$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<i8>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<i16>,
        >()];
        const _: [(); mem::size_of::<Vec<i16>>()] = [(); mem::size_of::<RustVec<i16>>()];
        const _: [(); mem::align_of::<Vec<i16>>()] = [(); mem::align_of::<
            RustVec<i16>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$i16$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<i16>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$i16$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<i16>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$i16$len"]
            unsafe extern "C" fn __len(this: *const RustVec<i16>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$i16$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<i16>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$i16$data"]
            unsafe extern "C" fn __data(this: *const RustVec<i16>) -> *const i16 {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$i16$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<i16>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$i16$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<i16>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$i16$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<i16>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<i32>,
        >()];
        const _: [(); mem::size_of::<Vec<i32>>()] = [(); mem::size_of::<RustVec<i32>>()];
        const _: [(); mem::align_of::<Vec<i32>>()] = [(); mem::align_of::<
            RustVec<i32>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$i32$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<i32>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$i32$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<i32>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$i32$len"]
            unsafe extern "C" fn __len(this: *const RustVec<i32>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$i32$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<i32>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$i32$data"]
            unsafe extern "C" fn __data(this: *const RustVec<i32>) -> *const i32 {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$i32$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<i32>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$i32$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<i32>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$i32$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<i32>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<i64>,
        >()];
        const _: [(); mem::size_of::<Vec<i64>>()] = [(); mem::size_of::<RustVec<i64>>()];
        const _: [(); mem::align_of::<Vec<i64>>()] = [(); mem::align_of::<
            RustVec<i64>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$i64$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<i64>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$i64$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<i64>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$i64$len"]
            unsafe extern "C" fn __len(this: *const RustVec<i64>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$i64$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<i64>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$i64$data"]
            unsafe extern "C" fn __data(this: *const RustVec<i64>) -> *const i64 {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$i64$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<i64>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$i64$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<i64>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$i64$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<i64>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<isize>,
        >()];
        const _: [(); mem::size_of::<Vec<isize>>()] = [(); mem::size_of::<
            RustVec<isize>,
        >()];
        const _: [(); mem::align_of::<Vec<isize>>()] = [(); mem::align_of::<
            RustVec<isize>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$isize$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<isize>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$isize$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<isize>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$isize$len"]
            unsafe extern "C" fn __len(this: *const RustVec<isize>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$isize$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<isize>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$isize$data"]
            unsafe extern "C" fn __data(this: *const RustVec<isize>) -> *const isize {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$isize$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<isize>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$isize$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<isize>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$isize$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<isize>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<f32>,
        >()];
        const _: [(); mem::size_of::<Vec<f32>>()] = [(); mem::size_of::<RustVec<f32>>()];
        const _: [(); mem::align_of::<Vec<f32>>()] = [(); mem::align_of::<
            RustVec<f32>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$f32$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<f32>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$f32$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<f32>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$f32$len"]
            unsafe extern "C" fn __len(this: *const RustVec<f32>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$f32$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<f32>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$f32$data"]
            unsafe extern "C" fn __data(this: *const RustVec<f32>) -> *const f32 {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$f32$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<f32>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$f32$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<f32>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$f32$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<f32>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<f64>,
        >()];
        const _: [(); mem::size_of::<Vec<f64>>()] = [(); mem::size_of::<RustVec<f64>>()];
        const _: [(); mem::align_of::<Vec<f64>>()] = [(); mem::align_of::<
            RustVec<f64>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$f64$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<f64>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$f64$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<f64>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$f64$len"]
            unsafe extern "C" fn __len(this: *const RustVec<f64>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$f64$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<f64>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$f64$data"]
            unsafe extern "C" fn __data(this: *const RustVec<f64>) -> *const f64 {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$f64$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<f64>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$f64$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<f64>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$f64$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<f64>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<c_char>,
        >()];
        const _: [(); mem::size_of::<Vec<c_char>>()] = [(); mem::size_of::<
            RustVec<c_char>,
        >()];
        const _: [(); mem::align_of::<Vec<c_char>>()] = [(); mem::align_of::<
            RustVec<c_char>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$char$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<c_char>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$char$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<c_char>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$char$len"]
            unsafe extern "C" fn __len(this: *const RustVec<c_char>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$char$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<c_char>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$char$data"]
            unsafe extern "C" fn __data(this: *const RustVec<c_char>) -> *const c_char {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$char$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<c_char>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$char$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<c_char>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$char$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<c_char>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<RustString>,
        >()];
        const _: [(); mem::size_of::<Vec<RustString>>()] = [(); mem::size_of::<
            RustVec<RustString>,
        >()];
        const _: [(); mem::align_of::<Vec<RustString>>()] = [(); mem::align_of::<
            RustVec<RustString>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$string$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<RustString>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$string$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<RustString>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$string$len"]
            unsafe extern "C" fn __len(this: *const RustVec<RustString>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$string$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<RustString>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$string$data"]
            unsafe extern "C" fn __data(
                this: *const RustVec<RustString>,
            ) -> *const RustString {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$string$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<RustString>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$string$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<RustString>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$string$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<RustString>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
        const _: [(); mem::size_of::<[usize; 3]>()] = [(); mem::size_of::<
            RustVec<&str>,
        >()];
        const _: [(); mem::size_of::<Vec<&str>>()] = [(); mem::size_of::<
            RustVec<&str>,
        >()];
        const _: [(); mem::align_of::<Vec<&str>>()] = [(); mem::align_of::<
            RustVec<&str>,
        >()];
        const _: () = {
            #[export_name = "cxxbridge1$rust_vec$str$new"]
            unsafe extern "C" fn __new(this: *mut RustVec<&str>) {
                unsafe { ptr::write(this, RustVec::new()) }
            }
            #[export_name = "cxxbridge1$rust_vec$str$drop"]
            unsafe extern "C" fn __drop(this: *mut RustVec<&str>) {
                unsafe { ptr::drop_in_place(this) }
            }
            #[export_name = "cxxbridge1$rust_vec$str$len"]
            unsafe extern "C" fn __len(this: *const RustVec<&str>) -> usize {
                unsafe { &*this }.len()
            }
            #[export_name = "cxxbridge1$rust_vec$str$capacity"]
            unsafe extern "C" fn __capacity(this: *const RustVec<&str>) -> usize {
                unsafe { &*this }.capacity()
            }
            #[export_name = "cxxbridge1$rust_vec$str$data"]
            unsafe extern "C" fn __data(this: *const RustVec<&str>) -> *const &str {
                unsafe { &*this }.as_ptr()
            }
            #[export_name = "cxxbridge1$rust_vec$str$reserve_total"]
            unsafe extern "C" fn __reserve_total(
                this: *mut RustVec<&str>,
                new_cap: usize,
            ) {
                unsafe { &mut *this }.reserve_total(new_cap);
            }
            #[export_name = "cxxbridge1$rust_vec$str$set_len"]
            unsafe extern "C" fn __set_len(this: *mut RustVec<&str>, len: usize) {
                unsafe { (*this).set_len(len) }
            }
            #[export_name = "cxxbridge1$rust_vec$str$truncate"]
            unsafe extern "C" fn __truncate(this: *mut RustVec<&str>, len: usize) {
                unsafe { (*this).truncate(len) }
            }
        };
    }
}
mod type_id {}
mod unique_ptr {
    use crate::cxx_vector::{CxxVector, VectorElement};
    use crate::fmt::display;
    use crate::kind::Trivial;
    use crate::string::CxxString;
    use crate::ExternType;
    use core::ffi::c_void;
    use core::fmt::{self, Debug, Display};
    use core::marker::PhantomData;
    use core::mem::{self, MaybeUninit};
    use core::ops::{Deref, DerefMut};
    use core::pin::Pin;
    #[repr(C)]
    pub struct UniquePtr<T>
    where
        T: UniquePtrTarget,
    {
        repr: MaybeUninit<*mut c_void>,
        ty: PhantomData<T>,
    }
    impl<T> UniquePtr<T>
    where
        T: UniquePtrTarget,
    {
        pub fn null() -> Self {
            UniquePtr {
                repr: T::__null(),
                ty: PhantomData,
            }
        }
        pub fn new(value: T) -> Self
        where
            T: ExternType<Kind = Trivial>,
        {
            UniquePtr {
                repr: T::__new(value),
                ty: PhantomData,
            }
        }
        pub fn is_null(&self) -> bool {
            let ptr = unsafe { T::__get(self.repr) };
            ptr.is_null()
        }
        pub fn as_ref(&self) -> Option<&T> {
            unsafe { T::__get(self.repr).as_ref() }
        }
        pub fn as_mut(&mut self) -> Option<Pin<&mut T>> {
            unsafe {
                let mut_reference = (T::__get(self.repr) as *mut T).as_mut()?;
                Some(Pin::new_unchecked(mut_reference))
            }
        }
        pub fn pin_mut(&mut self) -> Pin<&mut T> {
            match self.as_mut() {
                Some(target) => target,
                None => {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(
                            &["called pin_mut on a null UniquePtr<", ">"],
                            &[
                                ::core::fmt::ArgumentV1::new_display(
                                    &display(T::__typename),
                                ),
                            ],
                        ),
                    )
                }
            }
        }
        pub fn into_raw(self) -> *mut T {
            let ptr = unsafe { T::__release(self.repr) };
            mem::forget(self);
            ptr
        }
        pub unsafe fn from_raw(raw: *mut T) -> Self {
            UniquePtr {
                repr: unsafe { T::__raw(raw) },
                ty: PhantomData,
            }
        }
    }
    unsafe impl<T> Send for UniquePtr<T>
    where
        T: Send + UniquePtrTarget,
    {}
    unsafe impl<T> Sync for UniquePtr<T>
    where
        T: Sync + UniquePtrTarget,
    {}
    impl<T> Drop for UniquePtr<T>
    where
        T: UniquePtrTarget,
    {
        fn drop(&mut self) {
            unsafe { T::__drop(self.repr) }
        }
    }
    impl<T> Deref for UniquePtr<T>
    where
        T: UniquePtrTarget,
    {
        type Target = T;
        fn deref(&self) -> &Self::Target {
            match self.as_ref() {
                Some(target) => target,
                None => {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(
                            &["called deref on a null UniquePtr<", ">"],
                            &[
                                ::core::fmt::ArgumentV1::new_display(
                                    &display(T::__typename),
                                ),
                            ],
                        ),
                    )
                }
            }
        }
    }
    impl<T> DerefMut for UniquePtr<T>
    where
        T: UniquePtrTarget + Unpin,
    {
        fn deref_mut(&mut self) -> &mut Self::Target {
            match self.as_mut() {
                Some(target) => Pin::into_inner(target),
                None => {
                    ::core::panicking::panic_fmt(
                        ::core::fmt::Arguments::new_v1(
                            &["called deref_mut on a null UniquePtr<", ">"],
                            &[
                                ::core::fmt::ArgumentV1::new_display(
                                    &display(T::__typename),
                                ),
                            ],
                        ),
                    )
                }
            }
        }
    }
    impl<T> Debug for UniquePtr<T>
    where
        T: Debug + UniquePtrTarget,
    {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            match self.as_ref() {
                None => formatter.write_str("nullptr"),
                Some(value) => Debug::fmt(value, formatter),
            }
        }
    }
    impl<T> Display for UniquePtr<T>
    where
        T: Display + UniquePtrTarget,
    {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            match self.as_ref() {
                None => formatter.write_str("nullptr"),
                Some(value) => Display::fmt(value, formatter),
            }
        }
    }
    pub unsafe trait UniquePtrTarget {
        #[doc(hidden)]
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result;
        #[doc(hidden)]
        fn __null() -> MaybeUninit<*mut c_void>;
        #[doc(hidden)]
        fn __new(value: Self) -> MaybeUninit<*mut c_void>
        where
            Self: Sized,
        {
            let _ = value;
            ::core::panicking::panic("internal error: entered unreachable code")
        }
        #[doc(hidden)]
        unsafe fn __raw(raw: *mut Self) -> MaybeUninit<*mut c_void>;
        #[doc(hidden)]
        unsafe fn __get(repr: MaybeUninit<*mut c_void>) -> *const Self;
        #[doc(hidden)]
        unsafe fn __release(repr: MaybeUninit<*mut c_void>) -> *mut Self;
        #[doc(hidden)]
        unsafe fn __drop(repr: MaybeUninit<*mut c_void>);
    }
    extern "C" {
        #[link_name = "cxxbridge1$unique_ptr$std$string$null"]
        fn unique_ptr_std_string_null(this: *mut MaybeUninit<*mut c_void>);
        #[link_name = "cxxbridge1$unique_ptr$std$string$raw"]
        fn unique_ptr_std_string_raw(
            this: *mut MaybeUninit<*mut c_void>,
            raw: *mut CxxString,
        );
        #[link_name = "cxxbridge1$unique_ptr$std$string$get"]
        fn unique_ptr_std_string_get(
            this: *const MaybeUninit<*mut c_void>,
        ) -> *const CxxString;
        #[link_name = "cxxbridge1$unique_ptr$std$string$release"]
        fn unique_ptr_std_string_release(
            this: *mut MaybeUninit<*mut c_void>,
        ) -> *mut CxxString;
        #[link_name = "cxxbridge1$unique_ptr$std$string$drop"]
        fn unique_ptr_std_string_drop(this: *mut MaybeUninit<*mut c_void>);
    }
    unsafe impl UniquePtrTarget for CxxString {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("CxxString")
        }
        fn __null() -> MaybeUninit<*mut c_void> {
            let mut repr = MaybeUninit::uninit();
            unsafe {
                unique_ptr_std_string_null(&mut repr);
            }
            repr
        }
        unsafe fn __raw(raw: *mut Self) -> MaybeUninit<*mut c_void> {
            let mut repr = MaybeUninit::uninit();
            unsafe { unique_ptr_std_string_raw(&mut repr, raw) }
            repr
        }
        unsafe fn __get(repr: MaybeUninit<*mut c_void>) -> *const Self {
            unsafe { unique_ptr_std_string_get(&repr) }
        }
        unsafe fn __release(mut repr: MaybeUninit<*mut c_void>) -> *mut Self {
            unsafe { unique_ptr_std_string_release(&mut repr) }
        }
        unsafe fn __drop(mut repr: MaybeUninit<*mut c_void>) {
            unsafe { unique_ptr_std_string_drop(&mut repr) }
        }
    }
    unsafe impl<T> UniquePtrTarget for CxxVector<T>
    where
        T: VectorElement,
    {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            {
                let result = f
                    .write_fmt(
                        ::core::fmt::Arguments::new_v1(
                            &["CxxVector<", ">"],
                            &[
                                ::core::fmt::ArgumentV1::new_display(
                                    &display(T::__typename),
                                ),
                            ],
                        ),
                    );
                result
            }
        }
        fn __null() -> MaybeUninit<*mut c_void> {
            T::__unique_ptr_null()
        }
        unsafe fn __raw(raw: *mut Self) -> MaybeUninit<*mut c_void> {
            unsafe { T::__unique_ptr_raw(raw) }
        }
        unsafe fn __get(repr: MaybeUninit<*mut c_void>) -> *const Self {
            unsafe { T::__unique_ptr_get(repr) }
        }
        unsafe fn __release(repr: MaybeUninit<*mut c_void>) -> *mut Self {
            unsafe { T::__unique_ptr_release(repr) }
        }
        unsafe fn __drop(repr: MaybeUninit<*mut c_void>) {
            unsafe { T::__unique_ptr_drop(repr) }
        }
    }
}
mod unwind {
    #![allow(missing_docs)]
    use core::mem;
    pub fn prevent_unwind<F, R>(label: &'static str, foreign_call: F) -> R
    where
        F: FnOnce() -> R,
    {
        let guard = Guard { label };
        let ret = foreign_call();
        mem::forget(guard);
        ret
    }
    struct Guard {
        label: &'static str,
    }
    impl Drop for Guard {
        #[cold]
        fn drop(&mut self) {
            ::core::panicking::panic_fmt(
                ::core::fmt::Arguments::new_v1(
                    &["panic in ffi function ", ", aborting."],
                    &[::core::fmt::ArgumentV1::new_display(&self.label)],
                ),
            );
        }
    }
}
pub mod vector {
    pub use crate::cxx_vector::{Iter, IterMut, VectorElement};
    #[doc(inline)]
    pub use crate::Vector;
    #[doc(no_inline)]
    pub use cxx::CxxVector;
}
mod weak_ptr {
    use crate::shared_ptr::{SharedPtr, SharedPtrTarget};
    use crate::string::CxxString;
    use core::ffi::c_void;
    use core::fmt::{self, Debug};
    use core::marker::PhantomData;
    use core::mem::MaybeUninit;
    #[repr(C)]
    pub struct WeakPtr<T>
    where
        T: WeakPtrTarget,
    {
        repr: [MaybeUninit<*mut c_void>; 2],
        ty: PhantomData<T>,
    }
    impl<T> WeakPtr<T>
    where
        T: WeakPtrTarget,
    {
        pub fn null() -> Self {
            let mut weak_ptr = MaybeUninit::<WeakPtr<T>>::uninit();
            let new = weak_ptr.as_mut_ptr().cast();
            unsafe {
                T::__null(new);
                weak_ptr.assume_init()
            }
        }
        pub fn upgrade(&self) -> SharedPtr<T>
        where
            T: SharedPtrTarget,
        {
            let this = self as *const Self as *const c_void;
            let mut shared_ptr = MaybeUninit::<SharedPtr<T>>::uninit();
            let new = shared_ptr.as_mut_ptr().cast();
            unsafe {
                T::__upgrade(this, new);
                shared_ptr.assume_init()
            }
        }
    }
    unsafe impl<T> Send for WeakPtr<T>
    where
        T: Send + Sync + WeakPtrTarget,
    {}
    unsafe impl<T> Sync for WeakPtr<T>
    where
        T: Send + Sync + WeakPtrTarget,
    {}
    impl<T> Clone for WeakPtr<T>
    where
        T: WeakPtrTarget,
    {
        fn clone(&self) -> Self {
            let mut weak_ptr = MaybeUninit::<WeakPtr<T>>::uninit();
            let new = weak_ptr.as_mut_ptr().cast();
            let this = self as *const Self as *mut c_void;
            unsafe {
                T::__clone(this, new);
                weak_ptr.assume_init()
            }
        }
    }
    impl<T> Drop for WeakPtr<T>
    where
        T: WeakPtrTarget,
    {
        fn drop(&mut self) {
            let this = self as *mut Self as *mut c_void;
            unsafe { T::__drop(this) }
        }
    }
    impl<T> Debug for WeakPtr<T>
    where
        T: Debug + WeakPtrTarget + SharedPtrTarget,
    {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            Debug::fmt(&self.upgrade(), formatter)
        }
    }
    pub unsafe trait WeakPtrTarget {
        #[doc(hidden)]
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result;
        #[doc(hidden)]
        unsafe fn __null(new: *mut c_void);
        #[doc(hidden)]
        unsafe fn __clone(this: *const c_void, new: *mut c_void);
        #[doc(hidden)]
        unsafe fn __downgrade(shared: *const c_void, new: *mut c_void);
        #[doc(hidden)]
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void);
        #[doc(hidden)]
        unsafe fn __drop(this: *mut c_void);
    }
    unsafe impl WeakPtrTarget for bool {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("bool")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$bool$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$bool$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$bool$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$bool$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$bool$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for u8 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("u8")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u8$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u8$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u8$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u8$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u8$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for u16 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("u16")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u16$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u16$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u16$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u16$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u16$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for u32 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("u32")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u32$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u32$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u32$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u32$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u32$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for u64 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("u64")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u64$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u64$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u64$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u64$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$u64$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for usize {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("usize")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$usize$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$usize$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$usize$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$usize$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$usize$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for i8 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("i8")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i8$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i8$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i8$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i8$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i8$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for i16 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("i16")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i16$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i16$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i16$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i16$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i16$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for i32 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("i32")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i32$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i32$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i32$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i32$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i32$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for i64 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("i64")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i64$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i64$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i64$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i64$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$i64$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for isize {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("isize")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$isize$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$isize$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$isize$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$isize$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$isize$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for f32 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("f32")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$f32$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$f32$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$f32$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$f32$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$f32$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for f64 {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("f64")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$f64$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$f64$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$f64$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$f64$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$f64$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
    unsafe impl WeakPtrTarget for CxxString {
        fn __typename(f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("CxxString")
        }
        unsafe fn __null(new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$string$null"]
                fn __null(new: *mut c_void);
            }
            unsafe { __null(new) }
        }
        unsafe fn __clone(this: *const c_void, new: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$string$clone"]
                fn __clone(this: *const c_void, new: *mut c_void);
            }
            unsafe { __clone(this, new) }
        }
        unsafe fn __downgrade(shared: *const c_void, weak: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$string$downgrade"]
                fn __downgrade(shared: *const c_void, weak: *mut c_void);
            }
            unsafe { __downgrade(shared, weak) }
        }
        unsafe fn __upgrade(weak: *const c_void, shared: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$string$upgrade"]
                fn __upgrade(weak: *const c_void, shared: *mut c_void);
            }
            unsafe { __upgrade(weak, shared) }
        }
        unsafe fn __drop(this: *mut c_void) {
            extern "C" {
                #[link_name = "cxxbridge1$std$weak_ptr$string$drop"]
                fn __drop(this: *mut c_void);
            }
            unsafe { __drop(this) }
        }
    }
}
pub use crate::cxx_vector::CxxVector;
#[cfg(feature = "alloc")]
pub use crate::exception::Exception;
pub use crate::extern_type::{kind, ExternType};
pub use crate::shared_ptr::SharedPtr;
pub use crate::string::CxxString;
pub use crate::unique_ptr::UniquePtr;
pub use crate::weak_ptr::WeakPtr;
pub use cxxbridge_macro::bridge;
pub type String = CxxString;
pub type Vector<T> = CxxVector<T>;
#[doc(hidden)]
pub mod private {
    pub use crate::cxx_vector::VectorElement;
    pub use crate::extern_type::{verify_extern_kind, verify_extern_type};
    pub use crate::function::FatFunction;
    pub use crate::hash::hash;
    pub use crate::opaque::Opaque;
    #[cfg(feature = "alloc")]
    pub use crate::result::{r#try, Result};
    pub use crate::rust_slice::RustSlice;
    pub use crate::rust_str::RustStr;
    #[cfg(feature = "alloc")]
    pub use crate::rust_string::RustString;
    pub use crate::rust_type::{ImplBox, ImplVec, RustType};
    #[cfg(feature = "alloc")]
    pub use crate::rust_vec::RustVec;
    pub use crate::shared_ptr::SharedPtrTarget;
    pub use crate::string::StackString;
    pub use crate::unique_ptr::UniquePtrTarget;
    pub use crate::unwind::prevent_unwind;
    pub use crate::weak_ptr::WeakPtrTarget;
    pub use core::{concat, module_path};
    pub use cxxbridge_macro::type_id;
}
mod actually_private {
    pub trait Private {}
}
#[doc(hidden)]
pub enum _0 {}
#[doc(hidden)]
pub enum _1 {}
#[doc(hidden)]
pub enum _2 {}
#[doc(hidden)]
pub enum _3 {}
#[doc(hidden)]
pub enum _4 {}
#[doc(hidden)]
pub enum _5 {}
#[doc(hidden)]
pub enum _6 {}
#[doc(hidden)]
pub enum _7 {}
#[doc(hidden)]
pub enum _8 {}
#[doc(hidden)]
pub enum _9 {}
#[doc(hidden)]
pub enum A {}
#[doc(hidden)]
pub enum B {}
#[doc(hidden)]
pub enum C {}
#[doc(hidden)]
pub enum D {}
#[doc(hidden)]
pub enum E {}
#[doc(hidden)]
pub enum F {}
#[doc(hidden)]
pub enum G {}
#[doc(hidden)]
pub enum H {}
#[doc(hidden)]
pub enum I {}
#[doc(hidden)]
pub enum J {}
#[doc(hidden)]
pub enum K {}
#[doc(hidden)]
pub enum L {}
#[doc(hidden)]
pub enum M {}
#[doc(hidden)]
pub enum N {}
#[doc(hidden)]
pub enum O {}
#[doc(hidden)]
pub enum P {}
#[doc(hidden)]
pub enum Q {}
#[doc(hidden)]
pub enum R {}
#[doc(hidden)]
pub enum S {}
#[doc(hidden)]
pub enum T {}
#[doc(hidden)]
pub enum U {}
#[doc(hidden)]
pub enum V {}
#[doc(hidden)]
pub enum W {}
#[doc(hidden)]
pub enum X {}
#[doc(hidden)]
pub enum Y {}
#[doc(hidden)]
pub enum Z {}
#[doc(hidden)]
pub enum a {}
#[doc(hidden)]
pub enum b {}
#[doc(hidden)]
pub enum c {}
#[doc(hidden)]
pub enum d {}
#[doc(hidden)]
pub enum e {}
#[doc(hidden)]
pub enum f {}
#[doc(hidden)]
pub enum g {}
#[doc(hidden)]
pub enum h {}
#[doc(hidden)]
pub enum i {}
#[doc(hidden)]
pub enum j {}
#[doc(hidden)]
pub enum k {}
#[doc(hidden)]
pub enum l {}
#[doc(hidden)]
pub enum m {}
#[doc(hidden)]
pub enum n {}
#[doc(hidden)]
pub enum o {}
#[doc(hidden)]
pub enum p {}
#[doc(hidden)]
pub enum q {}
#[doc(hidden)]
pub enum r {}
#[doc(hidden)]
pub enum s {}
#[doc(hidden)]
pub enum t {}
#[doc(hidden)]
pub enum u {}
#[doc(hidden)]
pub enum v {}
#[doc(hidden)]
pub enum w {}
#[doc(hidden)]
pub enum x {}
#[doc(hidden)]
pub enum y {}
#[doc(hidden)]
pub enum z {}
#[doc(hidden)]
pub enum __ {}
#[repr(transparent)]
struct void(core::ffi::c_void);
