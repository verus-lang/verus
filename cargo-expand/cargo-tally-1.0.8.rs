#![feature(prelude_import)]
#[prelude_import]
use std::prelude::rust_2018::*;
#[macro_use]
extern crate std;
#[path = "lib.rs"]
mod lib {
    #![allow(non_camel_case_types)]
    #![allow(
        clippy::borrow_as_ptr,
        clippy::borrowed_box,
        clippy::cast_possible_truncation,
        clippy::cast_precision_loss,
        clippy::cast_ptr_alignment,
        clippy::cast_sign_loss,
        clippy::items_after_statements,
        clippy::iter_not_returning_iterator,
        clippy::mismatching_type_param_order,
        clippy::missing_errors_doc,
        clippy::missing_panics_doc,
        clippy::module_name_repetitions,
        clippy::must_use_candidate,
        clippy::needless_pass_by_value,
        clippy::option_if_let_else,
        clippy::ptr_as_ptr,
        clippy::significant_drop_in_scrutinee,
        clippy::too_many_lines,
        clippy::unseparated_literal_suffix
    )]
    #[macro_use]
    mod stream {}
    pub mod arena {
        use once_cell::sync::OnceCell;
        use std::any::TypeId;
        use std::collections::HashMap as Map;
        use std::fmt::{self, Debug};
        use std::iter::{Copied, FromIterator};
        use std::slice::Iter;
        use std::sync::{Mutex, PoisonError};
        use typed_arena::Arena;
        pub struct Slice<T: 'static> {
            contents: &'static [T],
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl<T: ::core::cmp::Ord + 'static> ::core::cmp::Ord for Slice<T> {
            #[inline]
            fn cmp(&self, other: &Slice<T>) -> ::core::cmp::Ordering {
                match *other {
                    Self { contents: ref __self_1_0 } => {
                        match *self {
                            Self { contents: ref __self_0_0 } => {
                                match ::core::cmp::Ord::cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::cmp::Ordering::Equal => ::core::cmp::Ordering::Equal,
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl<T: ::core::cmp::PartialOrd + 'static> ::core::cmp::PartialOrd for Slice<T> {
            #[inline]
            fn partial_cmp(
                &self,
                other: &Slice<T>,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self { contents: ref __self_1_0 } => {
                        match *self {
                            Self { contents: ref __self_0_0 } => {
                                match ::core::cmp::PartialOrd::partial_cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::option::Option::Some(
                                        ::core::cmp::Ordering::Equal,
                                    ) => {
                                        ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        impl<T: 'static> ::core::marker::StructuralEq for Slice<T> {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl<T: ::core::cmp::Eq + 'static> ::core::cmp::Eq for Slice<T> {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<&'static [T]>;
                }
            }
        }
        impl<T: 'static> ::core::marker::StructuralPartialEq for Slice<T> {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl<T: ::core::cmp::PartialEq + 'static> ::core::cmp::PartialEq for Slice<T> {
            #[inline]
            fn eq(&self, other: &Slice<T>) -> bool {
                match *other {
                    Self { contents: ref __self_1_0 } => {
                        match *self {
                            Self { contents: ref __self_0_0 } => {
                                (*__self_0_0) == (*__self_1_0)
                            }
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &Slice<T>) -> bool {
                match *other {
                    Self { contents: ref __self_1_0 } => {
                        match *self {
                            Self { contents: ref __self_0_0 } => {
                                (*__self_0_0) != (*__self_1_0)
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl<T: ::core::hash::Hash + 'static> ::core::hash::Hash for Slice<T> {
            fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) -> () {
                match *self {
                    Self { contents: ref __self_0_0 } => {
                        ::core::hash::Hash::hash(&(*__self_0_0), state)
                    }
                }
            }
        }
        impl<T> Slice<T>
        where
            T: 'static,
        {
            pub const EMPTY: Self = Slice { contents: &[] };
            pub fn new(slice: &[T]) -> Self
            where
                T: Send + Clone,
            {
                slice.iter().cloned().collect()
            }
            pub const fn from(contents: &'static [T]) -> Self {
                Slice { contents }
            }
            pub fn iter(&self) -> impl Iterator<Item = T>
            where
                T: Copy,
            {
                (*self).into_iter()
            }
            pub fn iter_ref(&self) -> impl Iterator<Item = &'static T> {
                self.contents.iter()
            }
            pub fn is_empty(&self) -> bool {
                self.contents.is_empty()
            }
        }
        impl<T> Copy for Slice<T>
        where
            T: 'static,
        {}
        impl<T> Clone for Slice<T>
        where
            T: 'static,
        {
            fn clone(&self) -> Self {
                *self
            }
        }
        impl<T> FromIterator<T> for Slice<T>
        where
            T: 'static + Send + Clone,
        {
            fn from_iter<I>(iter: I) -> Self
            where
                I: IntoIterator<Item = T>,
            {
                let iter = iter.into_iter();
                if iter.size_hint() == (0, Some(0)) {
                    return Slice::EMPTY;
                }
                static ARENA: OnceCell<Mutex<Map<TypeId, Box<dyn Send>>>> = OnceCell::new();
                let mut map = ARENA
                    .get_or_init(Mutex::default)
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner);
                let arena: &Box<dyn Send> = map
                    .entry(TypeId::of::<T>())
                    .or_insert_with(|| Box::new(Arena::<T>::new()));
                let arena = unsafe {
                    &*(&**arena as *const dyn Send as *const Arena<T>)
                };
                Slice {
                    contents: arena.alloc_extend(iter),
                }
            }
        }
        impl<T> IntoIterator for Slice<T>
        where
            T: 'static + Copy,
        {
            type Item = T;
            type IntoIter = Copied<Iter<'static, T>>;
            fn into_iter(self) -> Self::IntoIter {
                self.contents.iter().copied()
            }
        }
        impl<T> Debug for Slice<T>
        where
            T: 'static + Debug,
        {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                Debug::fmt(self.contents, formatter)
            }
        }
    }
    pub(crate) mod collect {
        use differential_dataflow::collection::Collection;
        use differential_dataflow::difference::Semigroup;
        use std::mem;
        use std::sync::{Arc, Mutex, PoisonError};
        use timely::dataflow::Scope;
        use timely::Data;
        pub(crate) trait Collect<T> {
            fn collect_into(&self, result: &Emitter<T>);
        }
        pub(crate) struct ResultCollection<T> {
            out: Arc<Mutex<Vec<T>>>,
        }
        pub(crate) struct Emitter<T> {
            out: Arc<Mutex<Vec<T>>>,
        }
        impl<T> ResultCollection<T> {
            pub(crate) fn new() -> Self {
                let out = Arc::new(Mutex::new(Vec::new()));
                ResultCollection { out }
            }
            pub(crate) fn emitter(&self) -> Emitter<T> {
                let out = Arc::clone(&self.out);
                Emitter { out }
            }
        }
        impl<D, T, R> ResultCollection<(D, T, R)>
        where
            T: Ord,
        {
            pub(crate) fn sort(&self) {
                self.out
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .sort_by(|
                        (_ldata, ltimestamp, _ldiff),
                        (_rdata, rtimestamp, _rdiff)|
                    { ltimestamp.cmp(rtimestamp) });
            }
        }
        impl<G, D, R> Collect<(D, G::Timestamp, R)> for Collection<G, D, R>
        where
            G: Scope,
            D: Data,
            R: Semigroup,
            G::Timestamp: Data,
        {
            fn collect_into(&self, result: &Emitter<(D, G::Timestamp, R)>) {
                let out = Arc::clone(&result.out);
                self.inspect_batch(move |_timestamp, slice| {
                    out.lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .extend_from_slice(slice);
                });
            }
        }
        impl<T> IntoIterator for ResultCollection<T> {
            type Item = T;
            type IntoIter = <Vec<T> as IntoIterator>::IntoIter;
            fn into_iter(self) -> Self::IntoIter {
                let mut out = self.out.lock().unwrap_or_else(PoisonError::into_inner);
                mem::take(&mut *out).into_iter()
            }
        }
    }
    mod communication {
        impl abomonation::Abomonation for crate::Dependency {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::Dependency {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::Dependency {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::Query {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::Query {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::Query {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::Release {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::Release {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::Release {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<T> abomonation::Abomonation for crate::arena::Slice<T>
        where
            T: 'static,
        {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<T> serde::Serialize for crate::arena::Slice<T>
        where
            T: 'static,
        {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de, T> serde::Deserialize<'de> for crate::arena::Slice<T>
        where
            T: 'static,
        {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::feature::CrateFeature {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::feature::CrateFeature {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::feature::CrateFeature {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::feature::DefaultFeatures {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::feature::DefaultFeatures {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::feature::DefaultFeatures {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::feature::FeatureId {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::feature::FeatureId {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::feature::FeatureId {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::feature::VersionFeature {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::feature::VersionFeature {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::feature::VersionFeature {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::id::CrateId {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::id::CrateId {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::id::CrateId {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::id::DependencyId {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::id::DependencyId {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::id::DependencyId {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::id::QueryId {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::id::QueryId {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::id::QueryId {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::id::VersionId {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::id::VersionId {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::id::VersionId {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<T> abomonation::Abomonation for crate::max::Max<T> {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<T> serde::Serialize for crate::max::Max<T> {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de, T> serde::Deserialize<'de> for crate::max::Max<T> {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::present::Present {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::present::Present {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::present::Present {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::timestamp::NaiveDateTime {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::timestamp::NaiveDateTime {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::timestamp::NaiveDateTime {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::version::Version {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::version::Version {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::version::Version {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl abomonation::Abomonation for crate::version::VersionReq {
            unsafe fn entomb<W: std::io::Write>(
                &self,
                _write: &mut W,
            ) -> std::io::Result<()> {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation entomb"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
            unsafe fn exhume<'a, 'b>(
                &'a mut self,
                _bytes: &'b mut [u8],
            ) -> Option<&'b mut [u8]> {
                std::process::exit(1);
            }
            fn extent(&self) -> usize {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected abomonation extent"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl serde::Serialize for crate::version::VersionReq {
            fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde serialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
        impl<'de> serde::Deserialize<'de> for crate::version::VersionReq {
            fn deserialize<D>(_deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                ::core::panicking::panic_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &["not implemented: "],
                        &[
                            ::core::fmt::ArgumentV1::new_display(
                                &::core::fmt::Arguments::new_v1(
                                    &["unexpected serde deserialize"],
                                    &[],
                                ),
                            ),
                        ],
                    ),
                );
            }
        }
    }
    pub mod dependency {
        pub enum DependencyKind {
            Normal,
            Build,
            Dev,
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::marker::Copy for DependencyKind {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for DependencyKind {
            #[inline]
            fn clone(&self) -> DependencyKind {
                { *self }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::fmt::Debug for DependencyKind {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match (&*self,) {
                    (&DependencyKind::Normal,) => {
                        ::core::fmt::Formatter::write_str(f, "Normal")
                    }
                    (&DependencyKind::Build,) => {
                        ::core::fmt::Formatter::write_str(f, "Build")
                    }
                    (&DependencyKind::Dev,) => {
                        ::core::fmt::Formatter::write_str(f, "Dev")
                    }
                }
            }
        }
        impl From<db_dump::dependencies::DependencyKind> for DependencyKind {
            fn from(dependency_kind: db_dump::dependencies::DependencyKind) -> Self {
                match dependency_kind {
                    db_dump::dependencies::DependencyKind::Normal => {
                        DependencyKind::Normal
                    }
                    db_dump::dependencies::DependencyKind::Build => DependencyKind::Build,
                    db_dump::dependencies::DependencyKind::Dev => DependencyKind::Dev,
                }
            }
        }
    }
    pub mod feature {
        use crate::arena::Slice;
        use crate::id::{CrateId, VersionId};
        use std::collections::BTreeMap as Map;
        use std::convert::TryFrom;
        #[repr(transparent)]
        pub struct FeatureId(pub u32);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::marker::Copy for FeatureId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for FeatureId {
            #[inline]
            fn clone(&self) -> FeatureId {
                {
                    let _: ::core::clone::AssertParamIsClone<u32>;
                    *self
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Ord for FeatureId {
            #[inline]
            fn cmp(&self, other: &FeatureId) -> ::core::cmp::Ordering {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::Ord::cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::cmp::Ordering::Equal => ::core::cmp::Ordering::Equal,
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialOrd for FeatureId {
            #[inline]
            fn partial_cmp(
                &self,
                other: &FeatureId,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::PartialOrd::partial_cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::option::Option::Some(
                                        ::core::cmp::Ordering::Equal,
                                    ) => {
                                        ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        impl ::core::marker::StructuralEq for FeatureId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Eq for FeatureId {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<u32>;
                }
            }
        }
        impl ::core::marker::StructuralPartialEq for FeatureId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialEq for FeatureId {
            #[inline]
            fn eq(&self, other: &FeatureId) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) == (*__self_1_0),
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &FeatureId) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) != (*__self_1_0),
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::hash::Hash for FeatureId {
            fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) -> () {
                match *self {
                    Self(ref __self_0_0) => {
                        ::core::hash::Hash::hash(&(*__self_0_0), state)
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::fmt::Debug for FeatureId {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match *self {
                    Self(ref __self_0_0) => {
                        let debug_trait_builder = &mut ::core::fmt::Formatter::debug_tuple(
                            f,
                            "FeatureId",
                        );
                        let _ = ::core::fmt::DebugTuple::field(
                            debug_trait_builder,
                            &&(*__self_0_0),
                        );
                        ::core::fmt::DebugTuple::finish(debug_trait_builder)
                    }
                }
            }
        }
        impl FeatureId {
            pub const CRATE: Self = FeatureId(0);
            pub const DEFAULT: Self = FeatureId(1);
            pub const TBD: Self = FeatureId(!0);
        }
        pub struct CrateFeature {
            pub crate_id: CrateId,
            pub feature_id: FeatureId,
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::marker::Copy for CrateFeature {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for CrateFeature {
            #[inline]
            fn clone(&self) -> CrateFeature {
                {
                    let _: ::core::clone::AssertParamIsClone<CrateId>;
                    let _: ::core::clone::AssertParamIsClone<FeatureId>;
                    *self
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::fmt::Debug for CrateFeature {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match *self {
                    Self { crate_id: ref __self_0_0, feature_id: ref __self_0_1 } => {
                        let debug_trait_builder = &mut ::core::fmt::Formatter::debug_struct(
                            f,
                            "CrateFeature",
                        );
                        let _ = ::core::fmt::DebugStruct::field(
                            debug_trait_builder,
                            "crate_id",
                            &&(*__self_0_0),
                        );
                        let _ = ::core::fmt::DebugStruct::field(
                            debug_trait_builder,
                            "feature_id",
                            &&(*__self_0_1),
                        );
                        ::core::fmt::DebugStruct::finish(debug_trait_builder)
                    }
                }
            }
        }
        pub struct VersionFeature {
            pub version_id: VersionId,
            pub feature_id: FeatureId,
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::marker::Copy for VersionFeature {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for VersionFeature {
            #[inline]
            fn clone(&self) -> VersionFeature {
                {
                    let _: ::core::clone::AssertParamIsClone<VersionId>;
                    let _: ::core::clone::AssertParamIsClone<FeatureId>;
                    *self
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Ord for VersionFeature {
            #[inline]
            fn cmp(&self, other: &VersionFeature) -> ::core::cmp::Ordering {
                match *other {
                    Self { version_id: ref __self_1_0, feature_id: ref __self_1_1 } => {
                        match *self {
                            Self {
                                version_id: ref __self_0_0,
                                feature_id: ref __self_0_1,
                            } => {
                                match ::core::cmp::Ord::cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::cmp::Ordering::Equal => {
                                        match ::core::cmp::Ord::cmp(
                                            &(*__self_0_1),
                                            &(*__self_1_1),
                                        ) {
                                            ::core::cmp::Ordering::Equal => ::core::cmp::Ordering::Equal,
                                            cmp => cmp,
                                        }
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialOrd for VersionFeature {
            #[inline]
            fn partial_cmp(
                &self,
                other: &VersionFeature,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self { version_id: ref __self_1_0, feature_id: ref __self_1_1 } => {
                        match *self {
                            Self {
                                version_id: ref __self_0_0,
                                feature_id: ref __self_0_1,
                            } => {
                                match ::core::cmp::PartialOrd::partial_cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::option::Option::Some(
                                        ::core::cmp::Ordering::Equal,
                                    ) => {
                                        match ::core::cmp::PartialOrd::partial_cmp(
                                            &(*__self_0_1),
                                            &(*__self_1_1),
                                        ) {
                                            ::core::option::Option::Some(
                                                ::core::cmp::Ordering::Equal,
                                            ) => {
                                                ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                                            }
                                            cmp => cmp,
                                        }
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        impl ::core::marker::StructuralEq for VersionFeature {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Eq for VersionFeature {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<VersionId>;
                    let _: ::core::cmp::AssertParamIsEq<FeatureId>;
                }
            }
        }
        impl ::core::marker::StructuralPartialEq for VersionFeature {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialEq for VersionFeature {
            #[inline]
            fn eq(&self, other: &VersionFeature) -> bool {
                match *other {
                    Self { version_id: ref __self_1_0, feature_id: ref __self_1_1 } => {
                        match *self {
                            Self {
                                version_id: ref __self_0_0,
                                feature_id: ref __self_0_1,
                            } => {
                                (*__self_0_0) == (*__self_1_0)
                                    && (*__self_0_1) == (*__self_1_1)
                            }
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &VersionFeature) -> bool {
                match *other {
                    Self { version_id: ref __self_1_0, feature_id: ref __self_1_1 } => {
                        match *self {
                            Self {
                                version_id: ref __self_0_0,
                                feature_id: ref __self_0_1,
                            } => {
                                (*__self_0_0) != (*__self_1_0)
                                    || (*__self_0_1) != (*__self_1_1)
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::hash::Hash for VersionFeature {
            fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) -> () {
                match *self {
                    Self { version_id: ref __self_0_0, feature_id: ref __self_0_1 } => {
                        ::core::hash::Hash::hash(&(*__self_0_0), state);
                        ::core::hash::Hash::hash(&(*__self_0_1), state)
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::fmt::Debug for VersionFeature {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match *self {
                    Self { version_id: ref __self_0_0, feature_id: ref __self_0_1 } => {
                        let debug_trait_builder = &mut ::core::fmt::Formatter::debug_struct(
                            f,
                            "VersionFeature",
                        );
                        let _ = ::core::fmt::DebugStruct::field(
                            debug_trait_builder,
                            "version_id",
                            &&(*__self_0_0),
                        );
                        let _ = ::core::fmt::DebugStruct::field(
                            debug_trait_builder,
                            "feature_id",
                            &&(*__self_0_1),
                        );
                        ::core::fmt::DebugStruct::finish(debug_trait_builder)
                    }
                }
            }
        }
        pub struct DefaultFeatures(pub bool);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::marker::Copy for DefaultFeatures {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for DefaultFeatures {
            #[inline]
            fn clone(&self) -> DefaultFeatures {
                {
                    let _: ::core::clone::AssertParamIsClone<bool>;
                    *self
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Ord for DefaultFeatures {
            #[inline]
            fn cmp(&self, other: &DefaultFeatures) -> ::core::cmp::Ordering {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::Ord::cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::cmp::Ordering::Equal => ::core::cmp::Ordering::Equal,
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialOrd for DefaultFeatures {
            #[inline]
            fn partial_cmp(
                &self,
                other: &DefaultFeatures,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::PartialOrd::partial_cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::option::Option::Some(
                                        ::core::cmp::Ordering::Equal,
                                    ) => {
                                        ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        impl ::core::marker::StructuralEq for DefaultFeatures {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Eq for DefaultFeatures {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<bool>;
                }
            }
        }
        impl ::core::marker::StructuralPartialEq for DefaultFeatures {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialEq for DefaultFeatures {
            #[inline]
            fn eq(&self, other: &DefaultFeatures) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) == (*__self_1_0),
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &DefaultFeatures) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) != (*__self_1_0),
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::fmt::Debug for DefaultFeatures {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match *self {
                    Self(ref __self_0_0) => {
                        let debug_trait_builder = &mut ::core::fmt::Formatter::debug_tuple(
                            f,
                            "DefaultFeatures",
                        );
                        let _ = ::core::fmt::DebugTuple::field(
                            debug_trait_builder,
                            &&(*__self_0_0),
                        );
                        ::core::fmt::DebugTuple::finish(debug_trait_builder)
                    }
                }
            }
        }
        pub struct FeatureNames {
            names: Vec<String>,
            map: Map<String, FeatureId>,
        }
        impl FeatureNames {
            pub fn new() -> Self {
                let mut feature_names = FeatureNames {
                    names: Vec::new(),
                    map: Map::new(),
                };
                match (&feature_names.id(""), &FeatureId::CRATE) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                match (&feature_names.id("default"), &FeatureId::DEFAULT) {
                    (left_val, right_val) => {
                        if !(*left_val == *right_val) {
                            let kind = ::core::panicking::AssertKind::Eq;
                            ::core::panicking::assert_failed(
                                kind,
                                &*left_val,
                                &*right_val,
                                ::core::option::Option::None,
                            );
                        }
                    }
                };
                feature_names
            }
            pub fn id(&mut self, name: &str) -> FeatureId {
                if let Some(id) = self.map.get(name) {
                    *id
                } else {
                    let new_id = FeatureId(u32::try_from(self.names.len()).unwrap());
                    self.names.push(name.to_owned());
                    self.map.insert(name.to_owned(), new_id);
                    new_id
                }
            }
            pub fn name(&self, id: FeatureId) -> &str {
                &self.names[id.0 as usize]
            }
        }
        impl Default for FeatureNames {
            fn default() -> Self {
                FeatureNames::new()
            }
        }
        pub struct FeatureIter {
            krate: bool,
            default: bool,
            other: <Slice<FeatureId> as IntoIterator>::IntoIter,
        }
        impl FeatureIter {
            pub fn new(
                default_features: DefaultFeatures,
                features: Slice<FeatureId>,
            ) -> Self {
                FeatureIter {
                    krate: !default_features.0 && features.is_empty(),
                    default: default_features.0,
                    other: features.into_iter(),
                }
            }
        }
        impl Iterator for FeatureIter {
            type Item = FeatureId;
            fn next(&mut self) -> Option<Self::Item> {
                if self.krate {
                    self.krate = false;
                    Some(FeatureId::CRATE)
                } else if self.default {
                    self.default = false;
                    Some(FeatureId::DEFAULT)
                } else {
                    self.other.next()
                }
            }
        }
    }
    pub(crate) mod hint {
        use differential_dataflow::collection::Collection;
        use differential_dataflow::difference::Semigroup;
        use timely::dataflow::Scope;
        #[allow(non_snake_case)]
        pub(crate) trait TypeHint: Sized {
            type Element;
            fn T<D>(self) -> Self
            where
                Self: TypeHint<Element = D>,
            {
                self
            }
            fn KV<K, V>(self) -> Self
            where
                Self: TypeHint<Element = (K, V)>,
            {
                self
            }
        }
        impl<G, D, R> TypeHint for Collection<G, D, R>
        where
            G: Scope,
            R: Semigroup,
        {
            type Element = D;
        }
        impl<G, D, R> TypeHint for &Collection<G, D, R>
        where
            G: Scope,
            R: Semigroup,
        {
            type Element = D;
        }
    }
    pub mod id {
        #[repr(transparent)]
        pub struct QueryId(pub u8);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::marker::Copy for QueryId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for QueryId {
            #[inline]
            fn clone(&self) -> QueryId {
                {
                    let _: ::core::clone::AssertParamIsClone<u8>;
                    *self
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Ord for QueryId {
            #[inline]
            fn cmp(&self, other: &QueryId) -> ::core::cmp::Ordering {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::Ord::cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::cmp::Ordering::Equal => ::core::cmp::Ordering::Equal,
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialOrd for QueryId {
            #[inline]
            fn partial_cmp(
                &self,
                other: &QueryId,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::PartialOrd::partial_cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::option::Option::Some(
                                        ::core::cmp::Ordering::Equal,
                                    ) => {
                                        ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        impl ::core::marker::StructuralEq for QueryId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Eq for QueryId {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<u8>;
                }
            }
        }
        impl ::core::marker::StructuralPartialEq for QueryId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialEq for QueryId {
            #[inline]
            fn eq(&self, other: &QueryId) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) == (*__self_1_0),
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &QueryId) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) != (*__self_1_0),
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::hash::Hash for QueryId {
            fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) -> () {
                match *self {
                    Self(ref __self_0_0) => {
                        ::core::hash::Hash::hash(&(*__self_0_0), state)
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::fmt::Debug for QueryId {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match *self {
                    Self(ref __self_0_0) => {
                        let debug_trait_builder = &mut ::core::fmt::Formatter::debug_tuple(
                            f,
                            "QueryId",
                        );
                        let _ = ::core::fmt::DebugTuple::field(
                            debug_trait_builder,
                            &&(*__self_0_0),
                        );
                        ::core::fmt::DebugTuple::finish(debug_trait_builder)
                    }
                }
            }
        }
        #[repr(transparent)]
        pub struct CrateId(pub u32);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::marker::Copy for CrateId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for CrateId {
            #[inline]
            fn clone(&self) -> CrateId {
                {
                    let _: ::core::clone::AssertParamIsClone<u32>;
                    *self
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Ord for CrateId {
            #[inline]
            fn cmp(&self, other: &CrateId) -> ::core::cmp::Ordering {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::Ord::cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::cmp::Ordering::Equal => ::core::cmp::Ordering::Equal,
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialOrd for CrateId {
            #[inline]
            fn partial_cmp(
                &self,
                other: &CrateId,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::PartialOrd::partial_cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::option::Option::Some(
                                        ::core::cmp::Ordering::Equal,
                                    ) => {
                                        ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        impl ::core::marker::StructuralEq for CrateId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Eq for CrateId {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<u32>;
                }
            }
        }
        impl ::core::marker::StructuralPartialEq for CrateId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialEq for CrateId {
            #[inline]
            fn eq(&self, other: &CrateId) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) == (*__self_1_0),
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &CrateId) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) != (*__self_1_0),
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::hash::Hash for CrateId {
            fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) -> () {
                match *self {
                    Self(ref __self_0_0) => {
                        ::core::hash::Hash::hash(&(*__self_0_0), state)
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::fmt::Debug for CrateId {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match *self {
                    Self(ref __self_0_0) => {
                        let debug_trait_builder = &mut ::core::fmt::Formatter::debug_tuple(
                            f,
                            "CrateId",
                        );
                        let _ = ::core::fmt::DebugTuple::field(
                            debug_trait_builder,
                            &&(*__self_0_0),
                        );
                        ::core::fmt::DebugTuple::finish(debug_trait_builder)
                    }
                }
            }
        }
        #[repr(transparent)]
        pub struct VersionId(pub u32);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::marker::Copy for VersionId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for VersionId {
            #[inline]
            fn clone(&self) -> VersionId {
                {
                    let _: ::core::clone::AssertParamIsClone<u32>;
                    *self
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Ord for VersionId {
            #[inline]
            fn cmp(&self, other: &VersionId) -> ::core::cmp::Ordering {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::Ord::cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::cmp::Ordering::Equal => ::core::cmp::Ordering::Equal,
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialOrd for VersionId {
            #[inline]
            fn partial_cmp(
                &self,
                other: &VersionId,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::PartialOrd::partial_cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::option::Option::Some(
                                        ::core::cmp::Ordering::Equal,
                                    ) => {
                                        ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        impl ::core::marker::StructuralEq for VersionId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Eq for VersionId {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<u32>;
                }
            }
        }
        impl ::core::marker::StructuralPartialEq for VersionId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialEq for VersionId {
            #[inline]
            fn eq(&self, other: &VersionId) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) == (*__self_1_0),
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &VersionId) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) != (*__self_1_0),
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::hash::Hash for VersionId {
            fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) -> () {
                match *self {
                    Self(ref __self_0_0) => {
                        ::core::hash::Hash::hash(&(*__self_0_0), state)
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::fmt::Debug for VersionId {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match *self {
                    Self(ref __self_0_0) => {
                        let debug_trait_builder = &mut ::core::fmt::Formatter::debug_tuple(
                            f,
                            "VersionId",
                        );
                        let _ = ::core::fmt::DebugTuple::field(
                            debug_trait_builder,
                            &&(*__self_0_0),
                        );
                        ::core::fmt::DebugTuple::finish(debug_trait_builder)
                    }
                }
            }
        }
        #[repr(transparent)]
        pub struct DependencyId(pub u32);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::marker::Copy for DependencyId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for DependencyId {
            #[inline]
            fn clone(&self) -> DependencyId {
                {
                    let _: ::core::clone::AssertParamIsClone<u32>;
                    *self
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Ord for DependencyId {
            #[inline]
            fn cmp(&self, other: &DependencyId) -> ::core::cmp::Ordering {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::Ord::cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::cmp::Ordering::Equal => ::core::cmp::Ordering::Equal,
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialOrd for DependencyId {
            #[inline]
            fn partial_cmp(
                &self,
                other: &DependencyId,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::PartialOrd::partial_cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::option::Option::Some(
                                        ::core::cmp::Ordering::Equal,
                                    ) => {
                                        ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        impl ::core::marker::StructuralEq for DependencyId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Eq for DependencyId {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<u32>;
                }
            }
        }
        impl ::core::marker::StructuralPartialEq for DependencyId {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialEq for DependencyId {
            #[inline]
            fn eq(&self, other: &DependencyId) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) == (*__self_1_0),
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &DependencyId) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) != (*__self_1_0),
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::hash::Hash for DependencyId {
            fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) -> () {
                match *self {
                    Self(ref __self_0_0) => {
                        ::core::hash::Hash::hash(&(*__self_0_0), state)
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::fmt::Debug for DependencyId {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match *self {
                    Self(ref __self_0_0) => {
                        let debug_trait_builder = &mut ::core::fmt::Formatter::debug_tuple(
                            f,
                            "DependencyId",
                        );
                        let _ = ::core::fmt::DebugTuple::field(
                            debug_trait_builder,
                            &&(*__self_0_0),
                        );
                        ::core::fmt::DebugTuple::finish(debug_trait_builder)
                    }
                }
            }
        }
        impl From<db_dump::crates::CrateId> for CrateId {
            fn from(id: db_dump::crates::CrateId) -> Self {
                CrateId(id.0)
            }
        }
        impl From<db_dump::versions::VersionId> for VersionId {
            fn from(id: db_dump::versions::VersionId) -> Self {
                VersionId(id.0)
            }
        }
        impl From<u32> for DependencyId {
            fn from(id: u32) -> Self {
                DependencyId(id)
            }
        }
    }
    mod impls {
        use crate::{Dependency, Query, Release};
        use std::cmp::Ordering;
        impl Ord for Query {
            fn cmp(&self, other: &Self) -> Ordering {
                self.id.cmp(&other.id)
            }
        }
        impl PartialOrd for Query {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Eq for Query {}
        impl PartialEq for Query {
            fn eq(&self, other: &Self) -> bool {
                self.id == other.id
            }
        }
        impl Ord for Release {
            fn cmp(&self, other: &Self) -> Ordering {
                self.id.cmp(&other.id)
            }
        }
        impl PartialOrd for Release {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Eq for Release {}
        impl PartialEq for Release {
            fn eq(&self, other: &Self) -> bool {
                self.id == other.id
            }
        }
        impl Ord for Dependency {
            fn cmp(&self, other: &Self) -> Ordering {
                self.id.cmp(&other.id)
            }
        }
        impl PartialOrd for Dependency {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Eq for Dependency {}
        impl PartialEq for Dependency {
            fn eq(&self, other: &Self) -> bool {
                self.id == other.id
            }
        }
    }
    pub mod matrix {
        use crate::timestamp::NaiveDateTime;
        use ref_cast::RefCast;
        use std::fmt::{self, Debug};
        use std::iter::Copied;
        use std::ops::{Deref, Div, Index};
        use std::slice;
        pub struct Matrix {
            queries: usize,
            rows: Vec<(NaiveDateTime, Vec<u32>)>,
        }
        #[repr(transparent)]
        pub struct Row([u32]);
        impl ::ref_cast::RefCast for Row {
            type From = [u32];
            #[inline]
            fn ref_cast(_from: &Self::From) -> &Self {
                #[cfg(debug_assertions)]
                {
                    #[allow(unused_imports)]
                    use ::ref_cast::private::LayoutUnsized;
                    ::ref_cast::private::assert_layout::<
                        Self,
                        Self::From,
                    >(
                        "Row",
                        ::ref_cast::private::Layout::<Self>::SIZE,
                        ::ref_cast::private::Layout::<Self::From>::SIZE,
                        ::ref_cast::private::Layout::<Self>::ALIGN,
                        ::ref_cast::private::Layout::<Self::From>::ALIGN,
                    );
                }
                unsafe { &*(_from as *const Self::From as *const Self) }
            }
            #[inline]
            fn ref_cast_mut(_from: &mut Self::From) -> &mut Self {
                #[cfg(debug_assertions)]
                {
                    #[allow(unused_imports)]
                    use ::ref_cast::private::LayoutUnsized;
                    ::ref_cast::private::assert_layout::<
                        Self,
                        Self::From,
                    >(
                        "Row",
                        ::ref_cast::private::Layout::<Self>::SIZE,
                        ::ref_cast::private::Layout::<Self::From>::SIZE,
                        ::ref_cast::private::Layout::<Self>::ALIGN,
                        ::ref_cast::private::Layout::<Self::From>::ALIGN,
                    );
                }
                unsafe { &mut *(_from as *mut Self::From as *mut Self) }
            }
        }
        impl Matrix {
            pub(crate) fn new(queries: usize) -> Self {
                Matrix {
                    queries,
                    rows: Vec::new(),
                }
            }
            pub fn width(&self) -> usize {
                self.queries
            }
            pub fn is_empty(&self) -> bool {
                self.rows.is_empty()
            }
            pub fn len(&self) -> usize {
                self.rows.len()
            }
            pub fn iter(&self) -> Iter {
                Iter(self.rows.iter())
            }
            pub(crate) fn push(&mut self, timestamp: NaiveDateTime, data: Vec<u32>) {
                self.rows.push((timestamp, data));
            }
        }
        impl<'a> IntoIterator for &'a Matrix {
            type Item = (NaiveDateTime, &'a Row);
            type IntoIter = Iter<'a>;
            fn into_iter(self) -> Self::IntoIter {
                self.iter()
            }
        }
        pub struct Iter<'a>(slice::Iter<'a, (NaiveDateTime, Vec<u32>)>);
        impl<'a> Iterator for Iter<'a> {
            type Item = (NaiveDateTime, &'a Row);
            fn next(&mut self) -> Option<Self::Item> {
                self.0.next().map(|(timestamp, data)| (*timestamp, Row::ref_cast(data)))
            }
        }
        impl<'a> DoubleEndedIterator for Iter<'a> {
            fn next_back(&mut self) -> Option<Self::Item> {
                self.0
                    .next_back()
                    .map(|(timestamp, data)| (*timestamp, Row::ref_cast(data)))
            }
        }
        impl Index<usize> for Row {
            type Output = u32;
            fn index(&self, i: usize) -> &Self::Output {
                &self.0[i]
            }
        }
        impl<'a> IntoIterator for &'a Row {
            type Item = u32;
            type IntoIter = Copied<slice::Iter<'a, u32>>;
            fn into_iter(self) -> Self::IntoIter {
                self.0.iter().copied()
            }
        }
        impl Deref for Row {
            type Target = [u32];
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }
        pub struct RelativeRow<'a> {
            row: &'a Row,
            total: u32,
        }
        impl<'a> Div<u32> for &'a Row {
            type Output = RelativeRow<'a>;
            fn div(self, rhs: u32) -> Self::Output {
                RelativeRow {
                    row: self,
                    total: rhs,
                }
            }
        }
        impl Debug for Row {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.debug_list().entries(&self.0).finish()
            }
        }
        impl<'a> Debug for RelativeRow<'a> {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                let mut list = formatter.debug_list();
                for value in self.row {
                    list.entry(&(value as f32 / self.total as f32));
                }
                list.finish()
            }
        }
    }
    pub(crate) mod max {
        use crate::hint::TypeHint;
        use crate::present::Present;
        use differential_dataflow::collection::Collection;
        use differential_dataflow::difference::Semigroup;
        use differential_dataflow::lattice::Lattice;
        use differential_dataflow::operators::CountTotal;
        use differential_dataflow::ExchangeData;
        use std::fmt::Debug;
        use std::hash::Hash;
        use std::iter::once;
        use std::ops::{AddAssign, Mul};
        use timely::dataflow::Scope;
        use timely::order::TotalOrder;
        pub(crate) trait MaxByKey<G, K, V, R>
        where
            G: Scope,
        {
            fn max_by_key(&self) -> Collection<G, (K, V), isize>;
        }
        impl<G, K, V, R> MaxByKey<G, K, V, R> for Collection<G, (K, V), R>
        where
            G: Scope,
            K: Clone + ExchangeData + Hash,
            V: Clone + Ord + ExchangeData + Debug,
            R: Semigroup,
            Max<V>: Mul<R, Output = Max<V>>,
            G::Timestamp: TotalOrder + Lattice,
        {
            fn max_by_key(&self) -> Collection<G, (K, V), isize> {
                self.explode(|(key, value)| once((key, Max { value })))
                    .T::<K>()
                    .count_total()
                    .KV::<K, Max<V>>()
                    .map(|(key, max)| (key, max.value))
            }
        }
        pub(crate) struct Max<T> {
            value: T,
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl<T: ::core::clone::Clone> ::core::clone::Clone for Max<T> {
            #[inline]
            fn clone(&self) -> Max<T> {
                match *self {
                    Self { value: ref __self_0_0 } => {
                        Max {
                            value: ::core::clone::Clone::clone(&(*__self_0_0)),
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl<T: ::core::cmp::Ord> ::core::cmp::Ord for Max<T> {
            #[inline]
            fn cmp(&self, other: &Max<T>) -> ::core::cmp::Ordering {
                match *other {
                    Self { value: ref __self_1_0 } => {
                        match *self {
                            Self { value: ref __self_0_0 } => {
                                match ::core::cmp::Ord::cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::cmp::Ordering::Equal => ::core::cmp::Ordering::Equal,
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl<T: ::core::cmp::PartialOrd> ::core::cmp::PartialOrd for Max<T> {
            #[inline]
            fn partial_cmp(
                &self,
                other: &Max<T>,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self { value: ref __self_1_0 } => {
                        match *self {
                            Self { value: ref __self_0_0 } => {
                                match ::core::cmp::PartialOrd::partial_cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::option::Option::Some(
                                        ::core::cmp::Ordering::Equal,
                                    ) => {
                                        ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        impl<T> ::core::marker::StructuralEq for Max<T> {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl<T: ::core::cmp::Eq> ::core::cmp::Eq for Max<T> {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<T>;
                }
            }
        }
        impl<T> ::core::marker::StructuralPartialEq for Max<T> {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl<T: ::core::cmp::PartialEq> ::core::cmp::PartialEq for Max<T> {
            #[inline]
            fn eq(&self, other: &Max<T>) -> bool {
                match *other {
                    Self { value: ref __self_1_0 } => {
                        match *self {
                            Self { value: ref __self_0_0 } => {
                                (*__self_0_0) == (*__self_1_0)
                            }
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &Max<T>) -> bool {
                match *other {
                    Self { value: ref __self_1_0 } => {
                        match *self {
                            Self { value: ref __self_0_0 } => {
                                (*__self_0_0) != (*__self_1_0)
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl<T: ::core::fmt::Debug> ::core::fmt::Debug for Max<T> {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match *self {
                    Self { value: ref __self_0_0 } => {
                        let debug_trait_builder = &mut ::core::fmt::Formatter::debug_struct(
                            f,
                            "Max",
                        );
                        let _ = ::core::fmt::DebugStruct::field(
                            debug_trait_builder,
                            "value",
                            &&(*__self_0_0),
                        );
                        ::core::fmt::DebugStruct::finish(debug_trait_builder)
                    }
                }
            }
        }
        impl<T> Mul<Present> for Max<T> {
            type Output = Self;
            fn mul(self, rhs: Present) -> Self::Output {
                let _ = rhs;
                self
            }
        }
        impl<T> AddAssign<&Self> for Max<T>
        where
            T: Ord + Clone,
        {
            fn add_assign(&mut self, rhs: &Self) {
                if self.value < rhs.value {
                    self.value = rhs.value.clone();
                }
            }
        }
        impl<T> Semigroup for Max<T>
        where
            T: Ord + Clone + Debug + 'static,
        {
            fn is_zero(&self) -> bool {
                false
            }
        }
    }
    pub(crate) mod present {
        use differential_dataflow::difference::Semigroup;
        use std::ops::{AddAssign, Mul};
        pub(crate) struct Present;
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for Present {
            #[inline]
            fn clone(&self) -> Present {
                match *self {
                    Self => Present,
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Ord for Present {
            #[inline]
            fn cmp(&self, other: &Present) -> ::core::cmp::Ordering {
                match *other {
                    Self => {
                        match *self {
                            Self => ::core::cmp::Ordering::Equal,
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialOrd for Present {
            #[inline]
            fn partial_cmp(
                &self,
                other: &Present,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self => {
                        match *self {
                            Self => {
                                ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                            }
                        }
                    }
                }
            }
        }
        impl ::core::marker::StructuralEq for Present {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Eq for Present {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {}
            }
        }
        impl ::core::marker::StructuralPartialEq for Present {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialEq for Present {
            #[inline]
            fn eq(&self, other: &Present) -> bool {
                match *other {
                    Self => {
                        match *self {
                            Self => true,
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::fmt::Debug for Present {
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match *self {
                    Self => ::core::fmt::Formatter::write_str(f, "Present"),
                }
            }
        }
        impl Semigroup for Present {
            fn is_zero(&self) -> bool {
                false
            }
        }
        impl AddAssign<&Present> for Present {
            fn add_assign(&mut self, rhs: &Present) {
                let _ = rhs;
            }
        }
        impl Mul<Present> for Present {
            type Output = Present;
            fn mul(self, rhs: Present) -> Self::Output {
                let _ = rhs;
                Present
            }
        }
        impl Mul<Present> for isize {
            type Output = isize;
            fn mul(self, rhs: Present) -> Self::Output {
                let _ = rhs;
                self
            }
        }
        impl Mul<isize> for Present {
            type Output = isize;
            fn mul(self, rhs: isize) -> Self::Output {
                rhs
            }
        }
    }
    pub mod timestamp {
        use chrono::{NaiveDate, NaiveTime, Utc};
        use differential_dataflow::lattice::Lattice;
        use std::cmp;
        use std::fmt::{self, Debug, Display};
        use timely::order::{PartialOrder, TotalOrder};
        use timely::progress::timestamp::{PathSummary, Refines, Timestamp};
        #[repr(transparent)]
        pub struct NaiveDateTime(chrono::NaiveDateTime);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::marker::Copy for NaiveDateTime {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for NaiveDateTime {
            #[inline]
            fn clone(&self) -> NaiveDateTime {
                {
                    let _: ::core::clone::AssertParamIsClone<chrono::NaiveDateTime>;
                    *self
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Ord for NaiveDateTime {
            #[inline]
            fn cmp(&self, other: &NaiveDateTime) -> ::core::cmp::Ordering {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::Ord::cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::cmp::Ordering::Equal => ::core::cmp::Ordering::Equal,
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialOrd for NaiveDateTime {
            #[inline]
            fn partial_cmp(
                &self,
                other: &NaiveDateTime,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::PartialOrd::partial_cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::option::Option::Some(
                                        ::core::cmp::Ordering::Equal,
                                    ) => {
                                        ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        impl ::core::marker::StructuralEq for NaiveDateTime {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Eq for NaiveDateTime {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<chrono::NaiveDateTime>;
                }
            }
        }
        impl ::core::marker::StructuralPartialEq for NaiveDateTime {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialEq for NaiveDateTime {
            #[inline]
            fn eq(&self, other: &NaiveDateTime) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) == (*__self_1_0),
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &NaiveDateTime) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) != (*__self_1_0),
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::hash::Hash for NaiveDateTime {
            fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) -> () {
                match *self {
                    Self(ref __self_0_0) => {
                        ::core::hash::Hash::hash(&(*__self_0_0), state)
                    }
                }
            }
        }
        #[repr(transparent)]
        pub struct Duration(chrono::Duration);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::marker::Copy for Duration {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for Duration {
            #[inline]
            fn clone(&self) -> Duration {
                {
                    let _: ::core::clone::AssertParamIsClone<chrono::Duration>;
                    *self
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Ord for Duration {
            #[inline]
            fn cmp(&self, other: &Duration) -> ::core::cmp::Ordering {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::Ord::cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::cmp::Ordering::Equal => ::core::cmp::Ordering::Equal,
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialOrd for Duration {
            #[inline]
            fn partial_cmp(
                &self,
                other: &Duration,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::PartialOrd::partial_cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::option::Option::Some(
                                        ::core::cmp::Ordering::Equal,
                                    ) => {
                                        ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        impl ::core::marker::StructuralEq for Duration {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Eq for Duration {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<chrono::Duration>;
                }
            }
        }
        impl ::core::marker::StructuralPartialEq for Duration {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialEq for Duration {
            #[inline]
            fn eq(&self, other: &Duration) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) == (*__self_1_0),
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &Duration) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) != (*__self_1_0),
                        }
                    }
                }
            }
        }
        impl NaiveDateTime {
            pub fn new(date: NaiveDate, time: NaiveTime) -> Self {
                NaiveDateTime(chrono::NaiveDateTime::new(date, time))
            }
            pub fn now() -> Self {
                NaiveDateTime(Utc::now().naive_utc())
            }
            pub fn seconds(&self) -> i64 {
                self.0.timestamp()
            }
            pub fn millis(&self) -> i64 {
                self.0.timestamp_millis()
            }
            pub fn subsec_nanos(&self) -> u32 {
                self.0.timestamp_subsec_nanos()
            }
            pub fn from_timestamp(secs: i64, nanos: u32) -> Self {
                NaiveDateTime(chrono::NaiveDateTime::from_timestamp(secs, nanos))
            }
        }
        impl From<chrono::NaiveDateTime> for NaiveDateTime {
            fn from(naive_date_time: chrono::NaiveDateTime) -> Self {
                NaiveDateTime(naive_date_time)
            }
        }
        impl Timestamp for NaiveDateTime {
            type Summary = Duration;
            fn minimum() -> Self {
                NaiveDateTime(chrono::NaiveDateTime::from_timestamp(0, 0))
            }
        }
        impl Lattice for NaiveDateTime {
            fn join(&self, other: &Self) -> Self {
                cmp::max(*self, *other)
            }
            fn meet(&self, other: &Self) -> Self {
                cmp::min(*self, *other)
            }
        }
        impl PartialOrder for NaiveDateTime {
            fn less_than(&self, other: &Self) -> bool {
                self < other
            }
            fn less_equal(&self, other: &Self) -> bool {
                self <= other
            }
        }
        impl TotalOrder for NaiveDateTime {}
        impl PathSummary<NaiveDateTime> for Duration {
            fn results_in(&self, src: &NaiveDateTime) -> Option<NaiveDateTime> {
                src.0.checked_add_signed(self.0).map(NaiveDateTime)
            }
            fn followed_by(&self, other: &Self) -> Option<Self> {
                self.0.checked_add(&other.0).map(Duration)
            }
        }
        impl Refines<()> for NaiveDateTime {
            fn to_inner(_other: ()) -> Self {
                Self::minimum()
            }
            #[allow(clippy::unused_unit)]
            fn to_outer(self) -> () {}
            #[allow(clippy::unused_unit)]
            fn summarize(_path: <Self as Timestamp>::Summary) -> () {}
        }
        impl PartialOrder for Duration {
            fn less_than(&self, other: &Self) -> bool {
                self < other
            }
            fn less_equal(&self, other: &Self) -> bool {
                self <= other
            }
        }
        impl Default for NaiveDateTime {
            fn default() -> Self {
                Self::minimum()
            }
        }
        impl Display for NaiveDateTime {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                Display::fmt(&self.0, formatter)
            }
        }
        impl Debug for NaiveDateTime {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                Debug::fmt(&self.0, formatter)
            }
        }
        impl Default for Duration {
            fn default() -> Self {
                Duration(chrono::Duration::nanoseconds(0))
            }
        }
        impl Debug for Duration {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                Debug::fmt(&self.0, formatter)
            }
        }
    }
    pub mod version {
        use crate::arena::Slice;
        use semver::{Comparator, Op};
        use std::cmp::Ordering;
        use std::fmt::{self, Debug, Display};
        use std::ops::{Deref, DerefMut};
        use std::str::FromStr;
        pub struct Version(pub semver::Version);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for Version {
            #[inline]
            fn clone(&self) -> Version {
                match *self {
                    Self(ref __self_0_0) => {
                        Version(::core::clone::Clone::clone(&(*__self_0_0)))
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Ord for Version {
            #[inline]
            fn cmp(&self, other: &Version) -> ::core::cmp::Ordering {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::Ord::cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::cmp::Ordering::Equal => ::core::cmp::Ordering::Equal,
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialOrd for Version {
            #[inline]
            fn partial_cmp(
                &self,
                other: &Version,
            ) -> ::core::option::Option<::core::cmp::Ordering> {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => {
                                match ::core::cmp::PartialOrd::partial_cmp(
                                    &(*__self_0_0),
                                    &(*__self_1_0),
                                ) {
                                    ::core::option::Option::Some(
                                        ::core::cmp::Ordering::Equal,
                                    ) => {
                                        ::core::option::Option::Some(::core::cmp::Ordering::Equal)
                                    }
                                    cmp => cmp,
                                }
                            }
                        }
                    }
                }
            }
        }
        impl ::core::marker::StructuralEq for Version {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Eq for Version {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<semver::Version>;
                }
            }
        }
        impl ::core::marker::StructuralPartialEq for Version {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialEq for Version {
            #[inline]
            fn eq(&self, other: &Version) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) == (*__self_1_0),
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &Version) -> bool {
                match *other {
                    Self(ref __self_1_0) => {
                        match *self {
                            Self(ref __self_0_0) => (*__self_0_0) != (*__self_1_0),
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::hash::Hash for Version {
            fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) -> () {
                match *self {
                    Self(ref __self_0_0) => {
                        ::core::hash::Hash::hash(&(*__self_0_0), state)
                    }
                }
            }
        }
        pub struct VersionReq {
            pub comparators: Slice<Comparator>,
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::marker::Copy for VersionReq {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::clone::Clone for VersionReq {
            #[inline]
            fn clone(&self) -> VersionReq {
                {
                    let _: ::core::clone::AssertParamIsClone<Slice<Comparator>>;
                    *self
                }
            }
        }
        impl ::core::marker::StructuralEq for VersionReq {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::Eq for VersionReq {
            #[inline]
            #[doc(hidden)]
            #[no_coverage]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::core::cmp::AssertParamIsEq<Slice<Comparator>>;
                }
            }
        }
        impl ::core::marker::StructuralPartialEq for VersionReq {}
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::cmp::PartialEq for VersionReq {
            #[inline]
            fn eq(&self, other: &VersionReq) -> bool {
                match *other {
                    Self { comparators: ref __self_1_0 } => {
                        match *self {
                            Self { comparators: ref __self_0_0 } => {
                                (*__self_0_0) == (*__self_1_0)
                            }
                        }
                    }
                }
            }
            #[inline]
            fn ne(&self, other: &VersionReq) -> bool {
                match *other {
                    Self { comparators: ref __self_1_0 } => {
                        match *self {
                            Self { comparators: ref __self_0_0 } => {
                                (*__self_0_0) != (*__self_1_0)
                            }
                        }
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::core::hash::Hash for VersionReq {
            fn hash<__H: ::core::hash::Hasher>(&self, state: &mut __H) -> () {
                match *self {
                    Self { comparators: ref __self_0_0 } => {
                        ::core::hash::Hash::hash(&(*__self_0_0), state)
                    }
                }
            }
        }
        impl VersionReq {
            pub fn matches(&self, version: &Version) -> bool {
                matches_req(self.comparators, version)
            }
        }
        impl Deref for Version {
            type Target = semver::Version;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }
        impl DerefMut for Version {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.0
            }
        }
        impl Display for Version {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                Display::fmt(&self.0, formatter)
            }
        }
        impl Debug for Version {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                {
                    let result = formatter
                        .write_fmt(
                            ::core::fmt::Arguments::new_v1(
                                &["Version(", ")"],
                                &[::core::fmt::ArgumentV1::new_display(&self)],
                            ),
                        );
                    result
                }
            }
        }
        impl Ord for VersionReq {
            fn cmp(&self, other: &Self) -> Ordering {
                let mut lhs = self.comparators.iter_ref();
                let mut rhs = other.comparators.iter_ref();
                loop {
                    let x = match lhs.next() {
                        None => {
                            return if rhs.next().is_none() {
                                Ordering::Equal
                            } else {
                                Ordering::Less
                            };
                        }
                        Some(val) => val,
                    };
                    let y = match rhs.next() {
                        None => return Ordering::Greater,
                        Some(val) => val,
                    };
                    match (x.op as usize, x.major, x.minor, x.patch, &x.pre)
                        .cmp(&(y.op as usize, y.major, y.minor, y.patch, &y.pre))
                    {
                        Ordering::Equal => {}
                        non_eq => return non_eq,
                    }
                }
            }
        }
        impl PartialOrd for VersionReq {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl From<semver::VersionReq> for VersionReq {
            fn from(req: semver::VersionReq) -> Self {
                let comparators = Slice::new(&req.comparators);
                VersionReq { comparators }
            }
        }
        impl FromStr for VersionReq {
            type Err = semver::Error;
            fn from_str(string: &str) -> Result<Self, Self::Err> {
                semver::VersionReq::from_str(string).map(VersionReq::from)
            }
        }
        impl Display for VersionReq {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                if self.comparators.is_empty() {
                    return formatter.write_str("*");
                }
                for (i, comparator) in self.comparators.iter_ref().enumerate() {
                    if i > 0 {
                        formatter.write_str(", ")?;
                    }
                    {
                        let result = formatter
                            .write_fmt(
                                ::core::fmt::Arguments::new_v1(
                                    &[""],
                                    &[::core::fmt::ArgumentV1::new_display(&comparator)],
                                ),
                            );
                        result
                    }?;
                }
                Ok(())
            }
        }
        impl Debug for VersionReq {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                {
                    let result = formatter
                        .write_fmt(
                            ::core::fmt::Arguments::new_v1(
                                &["VersionReq(", ")"],
                                &[::core::fmt::ArgumentV1::new_display(&self)],
                            ),
                        );
                    result
                }
            }
        }
        fn matches_req(comparators: Slice<Comparator>, ver: &Version) -> bool {
            for cmp in comparators.iter_ref() {
                if !matches_impl(cmp, ver) {
                    return false;
                }
            }
            if ver.pre.is_empty() {
                return true;
            }
            for cmp in comparators.iter_ref() {
                if pre_is_compatible(cmp, ver) {
                    return true;
                }
            }
            false
        }
        fn matches_impl(cmp: &Comparator, ver: &Version) -> bool {
            match cmp.op {
                Op::Exact | Op::Wildcard => matches_exact(cmp, ver),
                Op::Greater => matches_greater(cmp, ver),
                Op::GreaterEq => matches_exact(cmp, ver) || matches_greater(cmp, ver),
                Op::Less => matches_less(cmp, ver),
                Op::LessEq => matches_exact(cmp, ver) || matches_less(cmp, ver),
                Op::Tilde => matches_tilde(cmp, ver),
                Op::Caret => matches_caret(cmp, ver),
                _ => ::core::panicking::panic("not implemented"),
            }
        }
        fn matches_exact(cmp: &Comparator, ver: &Version) -> bool {
            if ver.major != cmp.major {
                return false;
            }
            if let Some(minor) = cmp.minor {
                if ver.minor != minor {
                    return false;
                }
            }
            if let Some(patch) = cmp.patch {
                if ver.patch != patch {
                    return false;
                }
            }
            ver.pre == cmp.pre
        }
        fn matches_greater(cmp: &Comparator, ver: &Version) -> bool {
            if ver.major != cmp.major {
                return ver.major > cmp.major;
            }
            match cmp.minor {
                None => return false,
                Some(minor) => {
                    if ver.minor != minor {
                        return ver.minor > minor;
                    }
                }
            }
            match cmp.patch {
                None => return false,
                Some(patch) => {
                    if ver.patch != patch {
                        return ver.patch > patch;
                    }
                }
            }
            ver.pre > cmp.pre
        }
        fn matches_less(cmp: &Comparator, ver: &Version) -> bool {
            if ver.major != cmp.major {
                return ver.major < cmp.major;
            }
            match cmp.minor {
                None => return false,
                Some(minor) => {
                    if ver.minor != minor {
                        return ver.minor < minor;
                    }
                }
            }
            match cmp.patch {
                None => return false,
                Some(patch) => {
                    if ver.patch != patch {
                        return ver.patch < patch;
                    }
                }
            }
            ver.pre < cmp.pre
        }
        fn matches_tilde(cmp: &Comparator, ver: &Version) -> bool {
            if ver.major != cmp.major {
                return false;
            }
            if let Some(minor) = cmp.minor {
                if ver.minor != minor {
                    return false;
                }
            }
            if let Some(patch) = cmp.patch {
                if ver.patch != patch {
                    return ver.patch > patch;
                }
            }
            ver.pre >= cmp.pre
        }
        fn matches_caret(cmp: &Comparator, ver: &Version) -> bool {
            if ver.major != cmp.major {
                return false;
            }
            let minor = match cmp.minor {
                None => return true,
                Some(minor) => minor,
            };
            let patch = match cmp.patch {
                None => {
                    return if cmp.major > 0 {
                        ver.minor >= minor
                    } else {
                        ver.minor == minor
                    };
                }
                Some(patch) => patch,
            };
            if cmp.major > 0 {
                if ver.minor != minor {
                    return ver.minor > minor;
                } else if ver.patch != patch {
                    return ver.patch > patch;
                }
            } else if minor > 0 {
                if ver.minor != minor {
                    return false;
                } else if ver.patch != patch {
                    return ver.patch > patch;
                }
            } else if ver.minor != minor || ver.patch != patch {
                return false;
            }
            ver.pre >= cmp.pre
        }
        fn pre_is_compatible(cmp: &Comparator, ver: &Version) -> bool {
            cmp.major == ver.major && cmp.minor == Some(ver.minor)
                && cmp.patch == Some(ver.patch) && !cmp.pre.is_empty()
        }
    }
    use crate::arena::Slice;
    use crate::collect::{Collect, ResultCollection};
    use crate::dependency::DependencyKind;
    use crate::feature::{
        CrateFeature, DefaultFeatures, FeatureId, FeatureIter, FeatureNames,
        VersionFeature,
    };
    use crate::hint::TypeHint;
    use crate::id::{CrateId, DependencyId, QueryId, VersionId};
    use crate::matrix::Matrix;
    use crate::max::MaxByKey;
    use crate::present::Present;
    use crate::timestamp::{Duration, NaiveDateTime};
    use crate::version::{Version, VersionReq};
    use differential_dataflow::input::InputSession;
    use differential_dataflow::operators::arrange::{ArrangeByKey, ArrangeBySelf};
    use differential_dataflow::operators::iterate::Variable;
    use differential_dataflow::operators::{Consolidate, Join, JoinCore, Threshold};
    use std::iter::once;
    use std::ops::Deref;
    use std::sync::{Mutex, PoisonError};
    use timely::dataflow::Scope;
    use timely::order::Product;
    use timely::progress::Timestamp;
    use timely::worker::Config as WorkerConfig;
    use timely::CommunicationConfig;
    pub struct DbDump {
        pub releases: Vec<Release>,
        pub dependencies: Vec<Dependency>,
        pub features: FeatureNames,
    }
    pub struct Release {
        pub id: VersionId,
        pub crate_id: CrateId,
        pub num: Version,
        pub created_at: NaiveDateTime,
        pub features: Slice<(FeatureId, Slice<CrateFeature>)>,
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::clone::Clone for Release {
        #[inline]
        fn clone(&self) -> Release {
            match *self {
                Self {
                    id: ref __self_0_0,
                    crate_id: ref __self_0_1,
                    num: ref __self_0_2,
                    created_at: ref __self_0_3,
                    features: ref __self_0_4,
                } => {
                    Release {
                        id: ::core::clone::Clone::clone(&(*__self_0_0)),
                        crate_id: ::core::clone::Clone::clone(&(*__self_0_1)),
                        num: ::core::clone::Clone::clone(&(*__self_0_2)),
                        created_at: ::core::clone::Clone::clone(&(*__self_0_3)),
                        features: ::core::clone::Clone::clone(&(*__self_0_4)),
                    }
                }
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::fmt::Debug for Release {
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match *self {
                Self {
                    id: ref __self_0_0,
                    crate_id: ref __self_0_1,
                    num: ref __self_0_2,
                    created_at: ref __self_0_3,
                    features: ref __self_0_4,
                } => {
                    let debug_trait_builder = &mut ::core::fmt::Formatter::debug_struct(
                        f,
                        "Release",
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "id",
                        &&(*__self_0_0),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "crate_id",
                        &&(*__self_0_1),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "num",
                        &&(*__self_0_2),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "created_at",
                        &&(*__self_0_3),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "features",
                        &&(*__self_0_4),
                    );
                    ::core::fmt::DebugStruct::finish(debug_trait_builder)
                }
            }
        }
    }
    pub struct Dependency {
        pub id: DependencyId,
        pub version_id: VersionId,
        pub crate_id: CrateId,
        pub req: VersionReq,
        pub feature_id: FeatureId,
        pub default_features: DefaultFeatures,
        pub features: Slice<FeatureId>,
        pub kind: DependencyKind,
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::marker::Copy for Dependency {}
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::clone::Clone for Dependency {
        #[inline]
        fn clone(&self) -> Dependency {
            {
                let _: ::core::clone::AssertParamIsClone<DependencyId>;
                let _: ::core::clone::AssertParamIsClone<VersionId>;
                let _: ::core::clone::AssertParamIsClone<CrateId>;
                let _: ::core::clone::AssertParamIsClone<VersionReq>;
                let _: ::core::clone::AssertParamIsClone<FeatureId>;
                let _: ::core::clone::AssertParamIsClone<DefaultFeatures>;
                let _: ::core::clone::AssertParamIsClone<Slice<FeatureId>>;
                let _: ::core::clone::AssertParamIsClone<DependencyKind>;
                *self
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::fmt::Debug for Dependency {
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match *self {
                Self {
                    id: ref __self_0_0,
                    version_id: ref __self_0_1,
                    crate_id: ref __self_0_2,
                    req: ref __self_0_3,
                    feature_id: ref __self_0_4,
                    default_features: ref __self_0_5,
                    features: ref __self_0_6,
                    kind: ref __self_0_7,
                } => {
                    let debug_trait_builder = &mut ::core::fmt::Formatter::debug_struct(
                        f,
                        "Dependency",
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "id",
                        &&(*__self_0_0),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "version_id",
                        &&(*__self_0_1),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "crate_id",
                        &&(*__self_0_2),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "req",
                        &&(*__self_0_3),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "feature_id",
                        &&(*__self_0_4),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "default_features",
                        &&(*__self_0_5),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "features",
                        &&(*__self_0_6),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "kind",
                        &&(*__self_0_7),
                    );
                    ::core::fmt::DebugStruct::finish(debug_trait_builder)
                }
            }
        }
    }
    pub struct Query {
        pub id: QueryId,
        pub predicates: Slice<Predicate>,
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::marker::Copy for Query {}
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::clone::Clone for Query {
        #[inline]
        fn clone(&self) -> Query {
            {
                let _: ::core::clone::AssertParamIsClone<QueryId>;
                let _: ::core::clone::AssertParamIsClone<Slice<Predicate>>;
                *self
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::fmt::Debug for Query {
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match *self {
                Self { id: ref __self_0_0, predicates: ref __self_0_1 } => {
                    let debug_trait_builder = &mut ::core::fmt::Formatter::debug_struct(
                        f,
                        "Query",
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "id",
                        &&(*__self_0_0),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "predicates",
                        &&(*__self_0_1),
                    );
                    ::core::fmt::DebugStruct::finish(debug_trait_builder)
                }
            }
        }
    }
    pub struct Predicate {
        pub crate_id: CrateId,
        pub req: Option<VersionReq>,
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::marker::Copy for Predicate {}
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::clone::Clone for Predicate {
        #[inline]
        fn clone(&self) -> Predicate {
            {
                let _: ::core::clone::AssertParamIsClone<CrateId>;
                let _: ::core::clone::AssertParamIsClone<Option<VersionReq>>;
                *self
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::core::fmt::Debug for Predicate {
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            match *self {
                Self { crate_id: ref __self_0_0, req: ref __self_0_1 } => {
                    let debug_trait_builder = &mut ::core::fmt::Formatter::debug_struct(
                        f,
                        "Predicate",
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "crate_id",
                        &&(*__self_0_0),
                    );
                    let _ = ::core::fmt::DebugStruct::field(
                        debug_trait_builder,
                        "req",
                        &&(*__self_0_1),
                    );
                    ::core::fmt::DebugStruct::finish(debug_trait_builder)
                }
            }
        }
    }
    struct Input {
        db_dump: DbDump,
        queries: Vec<Query>,
    }
    pub fn run(
        db_dump: DbDump,
        jobs: usize,
        transitive: bool,
        queries: &[Query],
    ) -> Matrix {
        let config = timely::Config {
            communication: CommunicationConfig::Process(jobs),
            worker: WorkerConfig::default(),
        };
        let num_queries = queries.len();
        let queries = queries.to_owned();
        let input = Mutex::new(Some(Input { db_dump, queries }));
        let collection = ResultCollection::<(QueryId, NaiveDateTime, isize)>::new();
        let results = collection.emitter();
        timely::execute(
                config,
                move |worker| {
                    let mut queries = InputSession::<
                        NaiveDateTime,
                        Query,
                        Present,
                    >::new();
                    let mut releases = InputSession::<
                        NaiveDateTime,
                        Release,
                        Present,
                    >::new();
                    let mut dependencies = InputSession::<
                        NaiveDateTime,
                        Dependency,
                        Present,
                    >::new();
                    worker
                        .dataflow(|scope| {
                            type queries<'a> = differential_dataflow::collection::Collection<
                                timely::dataflow::scopes::Child<
                                    'a,
                                    timely::worker::Worker<
                                        timely::communication::allocator::Generic,
                                    >,
                                    crate::timestamp::NaiveDateTime,
                                >,
                                Query,
                                Present,
                            >;
                            let queries: queries = queries.to_collection(scope);
                            type releases<'a> = differential_dataflow::collection::Collection<
                                timely::dataflow::scopes::Child<
                                    'a,
                                    timely::worker::Worker<
                                        timely::communication::allocator::Generic,
                                    >,
                                    crate::timestamp::NaiveDateTime,
                                >,
                                Release,
                                Present,
                            >;
                            let releases: releases = releases.to_collection(scope);
                            type dependencies<'a> = differential_dataflow::collection::Collection<
                                timely::dataflow::scopes::Child<
                                    'a,
                                    timely::worker::Worker<
                                        timely::communication::allocator::Generic,
                                    >,
                                    crate::timestamp::NaiveDateTime,
                                >,
                                Dependency,
                                Present,
                            >;
                            let dependencies: dependencies = dependencies
                                .to_collection(scope);
                            type releases_by_crate_id<'a> = differential_dataflow::collection::Collection<
                                timely::dataflow::scopes::Child<
                                    'a,
                                    timely::worker::Worker<
                                        timely::communication::allocator::Generic,
                                    >,
                                    crate::timestamp::NaiveDateTime,
                                >,
                                (CrateId, (VersionId, Version)),
                                Present,
                            >;
                            let releases_by_crate_id: releases_by_crate_id = releases
                                .map(|rel| (rel.crate_id, (rel.id, rel.num)));
                            let releases_by_crate_id = releases_by_crate_id
                                .arrange_by_key();
                            type resolved<'a> = differential_dataflow::collection::Collection<
                                timely::dataflow::scopes::Child<
                                    'a,
                                    timely::worker::Worker<
                                        timely::communication::allocator::Generic,
                                    >,
                                    crate::timestamp::NaiveDateTime,
                                >,
                                ((CrateId, VersionReq), VersionId),
                                isize,
                            >;
                            let resolved: resolved = dependencies
                                .map(|dep| (dep.crate_id, dep.req))
                                .KV::<CrateId, VersionReq>()
                                .join_core(
                                    &releases_by_crate_id,
                                    |crate_id, req, (version_id, version)| {
                                        req.matches(version)
                                            .then(|| (
                                                (*crate_id, *req),
                                                (version.clone(), *version_id),
                                            ))
                                    },
                                )
                                .KV::<(CrateId, VersionReq), (Version, VersionId)>()
                                .max_by_key()
                                .KV::<(CrateId, VersionReq), (Version, VersionId)>()
                                .map(|((crate_id, req), (_version, version_id))| (
                                    (crate_id, req),
                                    version_id,
                                ));
                            let resolved = resolved.arrange_by_key();
                            type dependency_edges<'a> = differential_dataflow::collection::Collection<
                                timely::dataflow::scopes::Child<
                                    'a,
                                    timely::worker::Worker<
                                        timely::communication::allocator::Generic,
                                    >,
                                    crate::timestamp::NaiveDateTime,
                                >,
                                (VersionId, VersionId),
                                isize,
                            >;
                            let direct_dependency_edges: dependency_edges = dependencies
                                .map(|dep| ((dep.crate_id, dep.req), dep.version_id))
                                .KV::<(CrateId, VersionReq), VersionId>()
                                .join_core(
                                    &resolved,
                                    |(_crate_id, _req), from_version_id, to_version_id| {
                                        once((*from_version_id, *to_version_id))
                                    },
                                );
                            type most_recent_crate_version<'a> = differential_dataflow::collection::Collection<
                                timely::dataflow::scopes::Child<
                                    'a,
                                    timely::worker::Worker<
                                        timely::communication::allocator::Generic,
                                    >,
                                    crate::timestamp::NaiveDateTime,
                                >,
                                VersionId,
                                isize,
                            >;
                            let most_recent_crate_version: most_recent_crate_version = releases
                                .map(|rel| (
                                    rel.crate_id,
                                    (rel.num.pre.is_empty(), rel.created_at, rel.id),
                                ))
                                .KV::<CrateId, (bool, NaiveDateTime, VersionId)>()
                                .max_by_key()
                                .KV::<CrateId, (bool, NaiveDateTime, VersionId)>()
                                .map(|
                                    (_crate_id, (_not_prerelease, _created_at, version_id))|
                                version_id);
                            let most_recent_crate_version = most_recent_crate_version
                                .arrange_by_self();
                            type match_releases<'a> = differential_dataflow::collection::Collection<
                                timely::dataflow::scopes::Child<
                                    'a,
                                    timely::worker::Worker<
                                        timely::communication::allocator::Generic,
                                    >,
                                    crate::timestamp::NaiveDateTime,
                                >,
                                (VersionId, QueryId),
                                Present,
                            >;
                            let match_releases: match_releases = queries
                                .flat_map(|query| {
                                    query
                                        .predicates
                                        .iter()
                                        .map(move |pred| (pred.crate_id, (query.id, pred.req)))
                                })
                                .KV::<CrateId, (QueryId, Option<VersionReq>)>()
                                .join_core(
                                    &releases_by_crate_id,
                                    |_crate_id, (query_id, version_req), (version_id, version)| {
                                        let matches = match version_req {
                                            None => true,
                                            Some(req) => req.matches(version),
                                        };
                                        matches.then(|| (*version_id, *query_id))
                                    },
                                );
                            type query_results<'a> = differential_dataflow::collection::Collection<
                                timely::dataflow::scopes::Child<
                                    'a,
                                    timely::worker::Worker<
                                        timely::communication::allocator::Generic,
                                    >,
                                    crate::timestamp::NaiveDateTime,
                                >,
                                (VersionId, QueryId),
                                isize,
                            >;
                            let mut query_results: query_results = direct_dependency_edges
                                .join_core(
                                    &most_recent_crate_version,
                                    |edge_from, edge_to, ()| { once((*edge_to, *edge_from)) },
                                )
                                .KV::<VersionId, VersionId>()
                                .join_map(
                                    &match_releases,
                                    |_edge_to, edge_from, query_id| { (*edge_from, *query_id) },
                                );
                            if transitive {
                                type dependency_edges<'a> = differential_dataflow::collection::Collection<
                                    timely::dataflow::scopes::Child<
                                        'a,
                                        timely::worker::Worker<
                                            timely::communication::allocator::Generic,
                                        >,
                                        crate::timestamp::NaiveDateTime,
                                    >,
                                    (VersionFeature, VersionFeature),
                                    isize,
                                >;
                                let dep_dependency_edges: dependency_edges = dependencies
                                    .flat_map(|dep| match dep.kind {
                                        DependencyKind::Normal | DependencyKind::Build => {
                                            Some((
                                                (dep.crate_id, dep.req),
                                                (
                                                    dep.version_id,
                                                    dep.feature_id,
                                                    dep.default_features,
                                                    dep.features,
                                                ),
                                            ))
                                        }
                                        DependencyKind::Dev => None,
                                    })
                                    .KV::<
                                        (CrateId, VersionReq),
                                        (VersionId, FeatureId, DefaultFeatures, Slice<FeatureId>),
                                    >()
                                    .join_core(
                                        &resolved,
                                        |
                                            (_crate_id, _req),
                                            (version_id, feature_id, default_features, features),
                                            resolved_version_id|
                                        {
                                            let edge_from = VersionFeature {
                                                version_id: *version_id,
                                                feature_id: *feature_id,
                                            };
                                            let resolved_version_id = *resolved_version_id;
                                            FeatureIter::new(*default_features, *features)
                                                .map(move |feature_id| {
                                                    let edge_to = VersionFeature {
                                                        version_id: resolved_version_id,
                                                        feature_id,
                                                    };
                                                    (edge_from, edge_to)
                                                })
                                        },
                                    );
                                let feature_intracrate_edges: dependency_edges = releases
                                    .explode(|rel| {
                                        let version_id = rel.id;
                                        let crate_id = rel.crate_id;
                                        rel.features
                                            .iter()
                                            .flat_map(move |(feature_id, depends_on)| {
                                                let edge_from = VersionFeature {
                                                    version_id,
                                                    feature_id,
                                                };
                                                depends_on
                                                    .into_iter()
                                                    .filter_map(move |crate_feature| {
                                                        if crate_feature.crate_id == crate_id {
                                                            let edge_to = VersionFeature {
                                                                version_id,
                                                                feature_id: crate_feature.feature_id,
                                                            };
                                                            Some((edge_from, edge_to))
                                                        } else {
                                                            None
                                                        }
                                                    })
                                                    .chain({
                                                        if feature_id == FeatureId::DEFAULT {
                                                            None
                                                        } else {
                                                            let edge_to = VersionFeature {
                                                                version_id,
                                                                feature_id: FeatureId::CRATE,
                                                            };
                                                            Some((edge_from, edge_to))
                                                        }
                                                    })
                                            })
                                            .chain({
                                                let edge_from = VersionFeature {
                                                    version_id,
                                                    feature_id: FeatureId::DEFAULT,
                                                };
                                                let edge_to = VersionFeature {
                                                    version_id,
                                                    feature_id: FeatureId::CRATE,
                                                };
                                                once((edge_from, edge_to))
                                            })
                                            .map(|(edge_from, edge_to)| ((edge_from, edge_to), 1))
                                    });
                                let feature_dependency_edges: dependency_edges = releases
                                    .flat_map(|rel| {
                                        let version_id = rel.id;
                                        let crate_id = rel.crate_id;
                                        rel.features
                                            .into_iter()
                                            .flat_map(move |(feature_id, depends_on)| {
                                                depends_on
                                                    .into_iter()
                                                    .filter_map(move |crate_feature| {
                                                        if crate_feature.crate_id == crate_id {
                                                            None
                                                        } else {
                                                            Some((
                                                                (version_id, crate_feature.crate_id),
                                                                (feature_id, crate_feature.feature_id),
                                                            ))
                                                        }
                                                    })
                                            })
                                    })
                                    .KV::<(VersionId, CrateId), (FeatureId, FeatureId)>()
                                    .join_map(
                                        &dependencies
                                            .map(|dep| ((dep.version_id, dep.crate_id), dep.req))
                                            .KV::<(VersionId, CrateId), VersionReq>(),
                                        |(version_id, crate_id), (from_feature, to_feature), req| {
                                            (
                                                (*crate_id, *req),
                                                (*version_id, *from_feature, *to_feature),
                                            )
                                        },
                                    )
                                    .KV::<
                                        (CrateId, VersionReq),
                                        (VersionId, FeatureId, FeatureId),
                                    >()
                                    .join_core(
                                        &resolved,
                                        |
                                            (_crate_id, _req),
                                            (from_version_id, from_feature_id, to_feature_id),
                                            to_version_id|
                                        {
                                            let edge_from = VersionFeature {
                                                version_id: *from_version_id,
                                                feature_id: *from_feature_id,
                                            };
                                            let edge_to = VersionFeature {
                                                version_id: *to_version_id,
                                                feature_id: *to_feature_id,
                                            };
                                            Some((edge_from, edge_to))
                                        },
                                    );
                                let incoming_transitive_dependency_edges = dep_dependency_edges
                                    .concat(&feature_intracrate_edges)
                                    .concat(&feature_dependency_edges)
                                    .KV::<VersionFeature, VersionFeature>()
                                    .map_in_place(|edge| {
                                        let (edge_from, edge_to) = *edge;
                                        *edge = (edge_to, edge_from);
                                    })
                                    .KV::<VersionFeature, VersionFeature>()
                                    .arrange_by_key();
                                type addend_transitive_releases<'a> = differential_dataflow::collection::Collection<
                                    timely::dataflow::scopes::Child<
                                        'a,
                                        timely::worker::Worker<
                                            timely::communication::allocator::Generic,
                                        >,
                                        crate::timestamp::NaiveDateTime,
                                    >,
                                    (VersionId, QueryId),
                                    isize,
                                >;
                                let addend_transitive_releases: addend_transitive_releases = scope
                                    .iterative::<
                                        u16,
                                        _,
                                        _,
                                    >(|nested| {
                                        let match_releases = match_releases
                                            .KV::<VersionId, QueryId>()
                                            .explode(|(version_id, query_id)| {
                                                let version_feature = VersionFeature {
                                                    version_id,
                                                    feature_id: FeatureId::CRATE,
                                                };
                                                once(((version_feature, query_id), 1))
                                            })
                                            .KV::<VersionFeature, QueryId>()
                                            .enter(nested);
                                        let summary = Product::new(Duration::default(), 1);
                                        let variable = Variable::new_from(match_releases, summary);
                                        let result = variable
                                            .deref()
                                            .KV::<VersionFeature, QueryId>()
                                            .join_core(
                                                &incoming_transitive_dependency_edges.enter(nested),
                                                |_edge_to, query_id, edge_from| Some((
                                                    *edge_from,
                                                    *query_id,
                                                )),
                                            )
                                            .KV::<VersionFeature, QueryId>()
                                            .concat(&variable)
                                            .KV::<VersionFeature, QueryId>()
                                            .distinct();
                                        variable.set(&result).leave()
                                    })
                                    .KV::<VersionFeature, QueryId>()
                                    .map(|(version_feature, query_id)| (
                                        version_feature.version_id,
                                        query_id,
                                    ));
                                query_results = addend_transitive_releases
                                    .join_core(
                                        &most_recent_crate_version,
                                        |version_id, query_id, ()| {
                                            Some((*version_id, *query_id))
                                        },
                                    )
                                    .KV::<VersionId, QueryId>()
                                    .concat(&query_results);
                            }
                            query_results
                                .distinct()
                                .map(|(_version_id, query_id)| query_id)
                                .consolidate()
                                .collect_into(&results);
                        });
                    let input = match input
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .take()
                    {
                        Some(input) => input,
                        None => return,
                    };
                    for query in input.queries {
                        queries.update(query, Present);
                    }
                    queries.close();
                    for dep in input.db_dump.dependencies {
                        dependencies.update(dep, Present);
                    }
                    dependencies.close();
                    for rel in input.db_dump.releases {
                        releases.advance_to(rel.created_at);
                        releases.update(rel, Present);
                    }
                },
            )
            .unwrap();
        let mut time = NaiveDateTime::minimum();
        let mut values = ::alloc::vec::from_elem(0u32, num_queries);
        let mut matrix = Matrix::new(num_queries);
        collection.sort();
        for (i, (query_id, timestamp, diff)) in collection.into_iter().enumerate() {
            if timestamp > time {
                if i > 0 {
                    matrix.push(time, values.clone());
                }
                time = timestamp;
            }
            let cell = &mut values[query_id.0 as usize];
            if diff > 0 {
                *cell += diff as u32;
            } else {
                *cell = cell.checked_sub(-diff as u32).expect("value went negative");
            }
        }
        if match matrix.iter().next_back() {
            Some((_timestamp, last)) => values != **last,
            None => values.iter().any(|&n| n != 0),
        } {
            matrix.push(time, values);
        }
        matrix
    }
}
#[doc(hidden)]
pub use crate::lib::*;
