#![feature(prelude_import)]
#![doc(html_root_url = "https://docs.rs/anyhow/1.0.58")]
#![feature(backtrace)]
#![deny(dead_code, unused_imports, unused_mut)]
#![allow(
    clippy::doc_markdown,
    clippy::enum_glob_use,
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::module_name_repetitions,
    clippy::must_use_candidate,
    clippy::needless_doctest_main,
    clippy::new_ret_no_self,
    clippy::redundant_else,
    clippy::return_self_not_must_use,
    clippy::unused_self,
    clippy::used_underscore_binding,
    clippy::wildcard_imports,
    clippy::wrong_self_convention
)]
#[prelude_import]
use std::prelude::rust_2018::*;
#[macro_use]
extern crate std;
extern crate alloc;
#[macro_use]
mod backtrace {
    #[cfg(backtrace)]
    pub(crate) use std::backtrace::{Backtrace, BacktraceStatus};
    fn _assert_send_sync() {
        fn _assert<T: Send + Sync>() {}
        _assert::<Backtrace>();
    }
}
mod chain {
    use self::ChainState::*;
    use crate::StdError;
    #[cfg(feature = "std")]
    use std::vec;
    #[cfg(feature = "std")]
    pub(crate) use crate::Chain;
    pub(crate) enum ChainState<'a> {
        Linked { next: Option<&'a (dyn StdError + 'static)> },
        #[cfg(feature = "std")]
        Buffered { rest: vec::IntoIter<&'a (dyn StdError + 'static)> },
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl<'a> ::core::clone::Clone for ChainState<'a> {
        #[inline]
        fn clone(&self) -> ChainState<'a> {
            match (&*self,) {
                (&ChainState::Linked { next: ref __self_0 },) => {
                    ChainState::Linked {
                        next: ::core::clone::Clone::clone(&(*__self_0)),
                    }
                }
                (&ChainState::Buffered { rest: ref __self_0 },) => {
                    ChainState::Buffered {
                        rest: ::core::clone::Clone::clone(&(*__self_0)),
                    }
                }
            }
        }
    }
    impl<'a> Chain<'a> {
        #[cold]
        pub fn new(head: &'a (dyn StdError + 'static)) -> Self {
            Chain {
                state: ChainState::Linked {
                    next: Some(head),
                },
            }
        }
    }
    impl<'a> Iterator for Chain<'a> {
        type Item = &'a (dyn StdError + 'static);
        fn next(&mut self) -> Option<Self::Item> {
            match &mut self.state {
                Linked { next } => {
                    let error = (*next)?;
                    *next = error.source();
                    Some(error)
                }
                #[cfg(feature = "std")]
                Buffered { rest } => rest.next(),
            }
        }
        fn size_hint(&self) -> (usize, Option<usize>) {
            let len = self.len();
            (len, Some(len))
        }
    }
    #[cfg(feature = "std")]
    impl DoubleEndedIterator for Chain<'_> {
        fn next_back(&mut self) -> Option<Self::Item> {
            match &mut self.state {
                Linked { mut next } => {
                    let mut rest = Vec::new();
                    while let Some(cause) = next {
                        next = cause.source();
                        rest.push(cause);
                    }
                    let mut rest = rest.into_iter();
                    let last = rest.next_back();
                    self.state = Buffered { rest };
                    last
                }
                Buffered { rest } => rest.next_back(),
            }
        }
    }
    impl ExactSizeIterator for Chain<'_> {
        fn len(&self) -> usize {
            match &self.state {
                Linked { mut next } => {
                    let mut len = 0;
                    while let Some(cause) = next {
                        next = cause.source();
                        len += 1;
                    }
                    len
                }
                #[cfg(feature = "std")]
                Buffered { rest } => rest.len(),
            }
        }
    }
    #[cfg(feature = "std")]
    impl Default for Chain<'_> {
        fn default() -> Self {
            Chain {
                state: ChainState::Buffered {
                    rest: Vec::new().into_iter(),
                },
            }
        }
    }
}
mod context {
    use crate::error::ContextError;
    use crate::{Context, Error, StdError};
    use core::convert::Infallible;
    use core::fmt::{self, Debug, Display, Write};
    #[cfg(backtrace)]
    use std::backtrace::Backtrace;
    mod ext {
        use super::*;
        pub trait StdError {
            fn ext_context<C>(self, context: C) -> Error
            where
                C: Display + Send + Sync + 'static;
        }
        #[cfg(feature = "std")]
        impl<E> StdError for E
        where
            E: std::error::Error + Send + Sync + 'static,
        {
            fn ext_context<C>(self, context: C) -> Error
            where
                C: Display + Send + Sync + 'static,
            {
                let backtrace = match self.backtrace() {
                    Some(_) => None,
                    None => Some(crate::backtrace::Backtrace::capture()),
                };
                Error::from_context(context, self, backtrace)
            }
        }
        impl StdError for Error {
            fn ext_context<C>(self, context: C) -> Error
            where
                C: Display + Send + Sync + 'static,
            {
                self.context(context)
            }
        }
    }
    impl<T, E> Context<T, E> for Result<T, E>
    where
        E: ext::StdError + Send + Sync + 'static,
    {
        fn context<C>(self, context: C) -> Result<T, Error>
        where
            C: Display + Send + Sync + 'static,
        {
            self.map_err(|error| error.ext_context(context))
        }
        fn with_context<C, F>(self, context: F) -> Result<T, Error>
        where
            C: Display + Send + Sync + 'static,
            F: FnOnce() -> C,
        {
            self.map_err(|error| error.ext_context(context()))
        }
    }
    impl<T> Context<T, Infallible> for Option<T> {
        fn context<C>(self, context: C) -> Result<T, Error>
        where
            C: Display + Send + Sync + 'static,
        {
            self.ok_or_else(|| Error::from_display(
                context,
                Some(crate::backtrace::Backtrace::capture()),
            ))
        }
        fn with_context<C, F>(self, context: F) -> Result<T, Error>
        where
            C: Display + Send + Sync + 'static,
            F: FnOnce() -> C,
        {
            self.ok_or_else(|| Error::from_display(
                context(),
                Some(crate::backtrace::Backtrace::capture()),
            ))
        }
    }
    impl<C, E> Debug for ContextError<C, E>
    where
        C: Display,
        E: Debug,
    {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            f.debug_struct("Error")
                .field("context", &Quoted(&self.context))
                .field("source", &self.error)
                .finish()
        }
    }
    impl<C, E> Display for ContextError<C, E>
    where
        C: Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            Display::fmt(&self.context, f)
        }
    }
    impl<C, E> StdError for ContextError<C, E>
    where
        C: Display,
        E: StdError + 'static,
    {
        #[cfg(backtrace)]
        fn backtrace(&self) -> Option<&Backtrace> {
            self.error.backtrace()
        }
        fn source(&self) -> Option<&(dyn StdError + 'static)> {
            Some(&self.error)
        }
    }
    impl<C> StdError for ContextError<C, Error>
    where
        C: Display,
    {
        #[cfg(backtrace)]
        fn backtrace(&self) -> Option<&Backtrace> {
            Some(self.error.backtrace())
        }
        fn source(&self) -> Option<&(dyn StdError + 'static)> {
            Some(unsafe { crate::ErrorImpl::error(self.error.inner.by_ref()) })
        }
    }
    struct Quoted<C>(C);
    impl<C> Debug for Quoted<C>
    where
        C: Display,
    {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_char('"')?;
            Quoted(&mut *formatter)
                .write_fmt(
                    ::core::fmt::Arguments::new_v1(
                        &[""],
                        &[::core::fmt::ArgumentV1::new_display(&self.0)],
                    ),
                )?;
            formatter.write_char('"')?;
            Ok(())
        }
    }
    impl Write for Quoted<&mut fmt::Formatter<'_>> {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            Display::fmt(&s.escape_debug(), self.0)
        }
    }
    pub(crate) mod private {
        use super::*;
        pub trait Sealed {}
        impl<T, E> Sealed for Result<T, E>
        where
            E: ext::StdError,
        {}
        impl<T> Sealed for Option<T> {}
    }
}
mod ensure {
    use crate::Error;
    use alloc::string::String;
    use core::fmt::{self, Debug, Write};
    use core::mem::MaybeUninit;
    use core::ptr;
    use core::slice;
    use core::str;
    #[doc(hidden)]
    pub trait BothDebug {
        fn __dispatch_ensure(self, msg: &'static str) -> Error;
    }
    impl<A, B> BothDebug for (A, B)
    where
        A: Debug,
        B: Debug,
    {
        fn __dispatch_ensure(self, msg: &'static str) -> Error {
            render(msg, &self.0, &self.1)
        }
    }
    #[doc(hidden)]
    pub trait NotBothDebug {
        fn __dispatch_ensure(self, msg: &'static str) -> Error;
    }
    impl<A, B> NotBothDebug for &(A, B) {
        fn __dispatch_ensure(self, msg: &'static str) -> Error {
            Error::msg(msg)
        }
    }
    struct Buf {
        bytes: [MaybeUninit<u8>; 40],
        written: usize,
    }
    impl Buf {
        fn new() -> Self {
            Buf {
                bytes: [MaybeUninit::uninit(); 40],
                written: 0,
            }
        }
        fn as_str(&self) -> &str {
            unsafe {
                str::from_utf8_unchecked(
                    slice::from_raw_parts(self.bytes.as_ptr().cast::<u8>(), self.written),
                )
            }
        }
    }
    impl Write for Buf {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            if s.bytes().any(|b| b == b' ' || b == b'\n') {
                return Err(fmt::Error);
            }
            let remaining = self.bytes.len() - self.written;
            if s.len() > remaining {
                return Err(fmt::Error);
            }
            unsafe {
                ptr::copy_nonoverlapping(
                    s.as_ptr(),
                    self.bytes.as_mut_ptr().add(self.written).cast::<u8>(),
                    s.len(),
                );
            }
            self.written += s.len();
            Ok(())
        }
    }
    fn render(msg: &'static str, lhs: &dyn Debug, rhs: &dyn Debug) -> Error {
        let mut lhs_buf = Buf::new();
        if fmt::write(
                &mut lhs_buf,
                ::core::fmt::Arguments::new_v1(
                    &[""],
                    &[::core::fmt::ArgumentV1::new_debug(&lhs)],
                ),
            )
            .is_ok()
        {
            let mut rhs_buf = Buf::new();
            if fmt::write(
                    &mut rhs_buf,
                    ::core::fmt::Arguments::new_v1(
                        &[""],
                        &[::core::fmt::ArgumentV1::new_debug(&rhs)],
                    ),
                )
                .is_ok()
            {
                let lhs_str = lhs_buf.as_str();
                let rhs_str = rhs_buf.as_str();
                let len = msg.len() + 2 + lhs_str.len() + 4 + rhs_str.len() + 1;
                let mut string = String::with_capacity(len);
                string.push_str(msg);
                string.push_str(" (");
                string.push_str(lhs_str);
                string.push_str(" vs ");
                string.push_str(rhs_str);
                string.push(')');
                return Error::msg(string);
            }
        }
        Error::msg(msg)
    }
}
mod error {
    use crate::backtrace::Backtrace;
    use crate::chain::Chain;
    #[cfg(any(feature = "std", anyhow_no_ptr_addr_of))]
    use crate::ptr::Mut;
    use crate::ptr::{Own, Ref};
    use crate::{Error, StdError};
    use alloc::boxed::Box;
    use core::any::TypeId;
    use core::fmt::{self, Debug, Display};
    use core::mem::ManuallyDrop;
    #[cfg(not(anyhow_no_ptr_addr_of))]
    use core::ptr;
    use core::ptr::NonNull;
    #[cfg(feature = "std")]
    use core::ops::{Deref, DerefMut};
    impl Error {
        #[cfg(feature = "std")]
        #[cold]
        #[must_use]
        pub fn new<E>(error: E) -> Self
        where
            E: StdError + Send + Sync + 'static,
        {
            let backtrace = match error.backtrace() {
                Some(_) => None,
                None => Some(crate::backtrace::Backtrace::capture()),
            };
            Error::from_std(error, backtrace)
        }
        #[cold]
        #[must_use]
        pub fn msg<M>(message: M) -> Self
        where
            M: Display + Debug + Send + Sync + 'static,
        {
            Error::from_adhoc(message, Some(crate::backtrace::Backtrace::capture()))
        }
        #[cfg(feature = "std")]
        #[cold]
        pub(crate) fn from_std<E>(error: E, backtrace: Option<Backtrace>) -> Self
        where
            E: StdError + Send + Sync + 'static,
        {
            let vtable = &ErrorVTable {
                object_drop: object_drop::<E>,
                object_ref: object_ref::<E>,
                object_boxed: object_boxed::<E>,
                object_downcast: object_downcast::<E>,
                object_drop_rest: object_drop_front::<E>,
            };
            unsafe { Error::construct(error, vtable, backtrace) }
        }
        #[cold]
        pub(crate) fn from_adhoc<M>(message: M, backtrace: Option<Backtrace>) -> Self
        where
            M: Display + Debug + Send + Sync + 'static,
        {
            use crate::wrapper::MessageError;
            let error: MessageError<M> = MessageError(message);
            let vtable = &ErrorVTable {
                object_drop: object_drop::<MessageError<M>>,
                object_ref: object_ref::<MessageError<M>>,
                object_boxed: object_boxed::<MessageError<M>>,
                object_downcast: object_downcast::<M>,
                object_drop_rest: object_drop_front::<M>,
            };
            unsafe { Error::construct(error, vtable, backtrace) }
        }
        #[cold]
        pub(crate) fn from_display<M>(message: M, backtrace: Option<Backtrace>) -> Self
        where
            M: Display + Send + Sync + 'static,
        {
            use crate::wrapper::DisplayError;
            let error: DisplayError<M> = DisplayError(message);
            let vtable = &ErrorVTable {
                object_drop: object_drop::<DisplayError<M>>,
                object_ref: object_ref::<DisplayError<M>>,
                object_boxed: object_boxed::<DisplayError<M>>,
                object_downcast: object_downcast::<M>,
                object_drop_rest: object_drop_front::<M>,
            };
            unsafe { Error::construct(error, vtable, backtrace) }
        }
        #[cfg(feature = "std")]
        #[cold]
        pub(crate) fn from_context<C, E>(
            context: C,
            error: E,
            backtrace: Option<Backtrace>,
        ) -> Self
        where
            C: Display + Send + Sync + 'static,
            E: StdError + Send + Sync + 'static,
        {
            let error: ContextError<C, E> = ContextError { context, error };
            let vtable = &ErrorVTable {
                object_drop: object_drop::<ContextError<C, E>>,
                object_ref: object_ref::<ContextError<C, E>>,
                object_boxed: object_boxed::<ContextError<C, E>>,
                object_downcast: context_downcast::<C, E>,
                object_drop_rest: context_drop_rest::<C, E>,
            };
            unsafe { Error::construct(error, vtable, backtrace) }
        }
        #[cfg(feature = "std")]
        #[cold]
        pub(crate) fn from_boxed(
            error: Box<dyn StdError + Send + Sync>,
            backtrace: Option<Backtrace>,
        ) -> Self {
            use crate::wrapper::BoxedError;
            let error = BoxedError(error);
            let vtable = &ErrorVTable {
                object_drop: object_drop::<BoxedError>,
                object_ref: object_ref::<BoxedError>,
                object_boxed: object_boxed::<BoxedError>,
                object_downcast: object_downcast::<Box<dyn StdError + Send + Sync>>,
                object_drop_rest: object_drop_front::<Box<dyn StdError + Send + Sync>>,
            };
            unsafe { Error::construct(error, vtable, backtrace) }
        }
        #[cold]
        unsafe fn construct<E>(
            error: E,
            vtable: &'static ErrorVTable,
            backtrace: Option<Backtrace>,
        ) -> Self
        where
            E: StdError + Send + Sync + 'static,
        {
            let inner: Box<ErrorImpl<E>> = Box::new(ErrorImpl {
                vtable,
                backtrace,
                _object: error,
            });
            let inner = Own::new(inner).cast::<ErrorImpl>();
            Error { inner }
        }
        #[cold]
        #[must_use]
        pub fn context<C>(self, context: C) -> Self
        where
            C: Display + Send + Sync + 'static,
        {
            let error: ContextError<C, Error> = ContextError {
                context,
                error: self,
            };
            let vtable = &ErrorVTable {
                object_drop: object_drop::<ContextError<C, Error>>,
                object_ref: object_ref::<ContextError<C, Error>>,
                object_boxed: object_boxed::<ContextError<C, Error>>,
                object_downcast: context_chain_downcast::<C>,
                object_drop_rest: context_chain_drop_rest::<C>,
            };
            let backtrace = None;
            unsafe { Error::construct(error, vtable, backtrace) }
        }
        #[cfg(any(backtrace, feature = "backtrace"))]
        pub fn backtrace(&self) -> &std::backtrace::Backtrace {
            unsafe { ErrorImpl::backtrace(self.inner.by_ref()) }
        }
        #[cfg(feature = "std")]
        #[cold]
        pub fn chain(&self) -> Chain {
            unsafe { ErrorImpl::chain(self.inner.by_ref()) }
        }
        #[cfg(feature = "std")]
        pub fn root_cause(&self) -> &(dyn StdError + 'static) {
            self.chain().last().unwrap()
        }
        pub fn is<E>(&self) -> bool
        where
            E: Display + Debug + Send + Sync + 'static,
        {
            self.downcast_ref::<E>().is_some()
        }
        pub fn downcast<E>(mut self) -> Result<E, Self>
        where
            E: Display + Debug + Send + Sync + 'static,
        {
            let target = TypeId::of::<E>();
            let inner = self.inner.by_mut();
            unsafe {
                #[cfg(not(anyhow_no_ptr_addr_of))]
                let addr = match (vtable(inner.ptr)
                    .object_downcast)(inner.by_ref(), target)
                {
                    Some(addr) => addr.by_mut().extend(),
                    None => return Err(self),
                };
                let outer = ManuallyDrop::new(self);
                let error = addr.cast::<E>().read();
                (vtable(outer.inner.ptr).object_drop_rest)(outer.inner, target);
                Ok(error)
            }
        }
        pub fn downcast_ref<E>(&self) -> Option<&E>
        where
            E: Display + Debug + Send + Sync + 'static,
        {
            let target = TypeId::of::<E>();
            unsafe {
                let addr = (vtable(self.inner.ptr)
                    .object_downcast)(self.inner.by_ref(), target)?;
                Some(addr.cast::<E>().deref())
            }
        }
        pub fn downcast_mut<E>(&mut self) -> Option<&mut E>
        where
            E: Display + Debug + Send + Sync + 'static,
        {
            let target = TypeId::of::<E>();
            unsafe {
                #[cfg(not(anyhow_no_ptr_addr_of))]
                let addr = (vtable(self.inner.ptr)
                    .object_downcast)(self.inner.by_ref(), target)?
                    .by_mut();
                Some(addr.cast::<E>().deref_mut())
            }
        }
    }
    #[cfg(feature = "std")]
    impl<E> From<E> for Error
    where
        E: StdError + Send + Sync + 'static,
    {
        #[cold]
        fn from(error: E) -> Self {
            let backtrace = match error.backtrace() {
                Some(_) => None,
                None => Some(crate::backtrace::Backtrace::capture()),
            };
            Error::from_std(error, backtrace)
        }
    }
    #[cfg(feature = "std")]
    impl Deref for Error {
        type Target = dyn StdError + Send + Sync + 'static;
        fn deref(&self) -> &Self::Target {
            unsafe { ErrorImpl::error(self.inner.by_ref()) }
        }
    }
    #[cfg(feature = "std")]
    impl DerefMut for Error {
        fn deref_mut(&mut self) -> &mut Self::Target {
            unsafe { ErrorImpl::error_mut(self.inner.by_mut()) }
        }
    }
    impl Display for Error {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            unsafe { ErrorImpl::display(self.inner.by_ref(), formatter) }
        }
    }
    impl Debug for Error {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            unsafe { ErrorImpl::debug(self.inner.by_ref(), formatter) }
        }
    }
    impl Drop for Error {
        fn drop(&mut self) {
            unsafe {
                (vtable(self.inner.ptr).object_drop)(self.inner);
            }
        }
    }
    struct ErrorVTable {
        object_drop: unsafe fn(Own<ErrorImpl>),
        object_ref: unsafe fn(
            Ref<ErrorImpl>,
        ) -> Ref<dyn StdError + Send + Sync + 'static>,
        object_boxed: unsafe fn(
            Own<ErrorImpl>,
        ) -> Box<dyn StdError + Send + Sync + 'static>,
        object_downcast: unsafe fn(Ref<ErrorImpl>, TypeId) -> Option<Ref<()>>,
        object_drop_rest: unsafe fn(Own<ErrorImpl>, TypeId),
    }
    unsafe fn object_drop<E>(e: Own<ErrorImpl>) {
        let unerased = e.cast::<ErrorImpl<E>>().boxed();
        drop(unerased);
    }
    unsafe fn object_drop_front<E>(e: Own<ErrorImpl>, target: TypeId) {
        let _ = target;
        let unerased = e.cast::<ErrorImpl<ManuallyDrop<E>>>().boxed();
        drop(unerased);
    }
    unsafe fn object_ref<E>(
        e: Ref<ErrorImpl>,
    ) -> Ref<dyn StdError + Send + Sync + 'static>
    where
        E: StdError + Send + Sync + 'static,
    {
        let unerased = e.cast::<ErrorImpl<E>>();
        #[cfg(not(anyhow_no_ptr_addr_of))]
        return Ref::from_raw(
            NonNull::new_unchecked(&raw const (*unerased.as_ptr())._object as *mut E),
        );
    }
    unsafe fn object_boxed<E>(
        e: Own<ErrorImpl>,
    ) -> Box<dyn StdError + Send + Sync + 'static>
    where
        E: StdError + Send + Sync + 'static,
    {
        e.cast::<ErrorImpl<E>>().boxed()
    }
    unsafe fn object_downcast<E>(e: Ref<ErrorImpl>, target: TypeId) -> Option<Ref<()>>
    where
        E: 'static,
    {
        if TypeId::of::<E>() == target {
            let unerased = e.cast::<ErrorImpl<E>>();
            #[cfg(not(anyhow_no_ptr_addr_of))]
            return Some(
                Ref::from_raw(
                        NonNull::new_unchecked(
                            &raw const (*unerased.as_ptr())._object as *mut E,
                        ),
                    )
                    .cast::<()>(),
            );
        } else {
            None
        }
    }
    #[cfg(feature = "std")]
    unsafe fn context_downcast<C, E>(
        e: Ref<ErrorImpl>,
        target: TypeId,
    ) -> Option<Ref<()>>
    where
        C: 'static,
        E: 'static,
    {
        if TypeId::of::<C>() == target {
            let unerased = e.cast::<ErrorImpl<ContextError<C, E>>>().deref();
            Some(Ref::new(&unerased._object.context).cast::<()>())
        } else if TypeId::of::<E>() == target {
            let unerased = e.cast::<ErrorImpl<ContextError<C, E>>>().deref();
            Some(Ref::new(&unerased._object.error).cast::<()>())
        } else {
            None
        }
    }
    #[cfg(feature = "std")]
    unsafe fn context_drop_rest<C, E>(e: Own<ErrorImpl>, target: TypeId)
    where
        C: 'static,
        E: 'static,
    {
        if TypeId::of::<C>() == target {
            let unerased = e
                .cast::<ErrorImpl<ContextError<ManuallyDrop<C>, E>>>()
                .boxed();
            drop(unerased);
        } else {
            let unerased = e
                .cast::<ErrorImpl<ContextError<C, ManuallyDrop<E>>>>()
                .boxed();
            drop(unerased);
        }
    }
    unsafe fn context_chain_downcast<C>(
        e: Ref<ErrorImpl>,
        target: TypeId,
    ) -> Option<Ref<()>>
    where
        C: 'static,
    {
        let unerased = e.cast::<ErrorImpl<ContextError<C, Error>>>().deref();
        if TypeId::of::<C>() == target {
            Some(Ref::new(&unerased._object.context).cast::<()>())
        } else {
            let source = &unerased._object.error;
            (vtable(source.inner.ptr).object_downcast)(source.inner.by_ref(), target)
        }
    }
    unsafe fn context_chain_drop_rest<C>(e: Own<ErrorImpl>, target: TypeId)
    where
        C: 'static,
    {
        if TypeId::of::<C>() == target {
            let unerased = e
                .cast::<ErrorImpl<ContextError<ManuallyDrop<C>, Error>>>()
                .boxed();
            drop(unerased);
        } else {
            let unerased = e
                .cast::<ErrorImpl<ContextError<C, ManuallyDrop<Error>>>>()
                .boxed();
            let inner = unerased._object.error.inner;
            drop(unerased);
            let vtable = vtable(inner.ptr);
            (vtable.object_drop_rest)(inner, target);
        }
    }
    #[repr(C)]
    pub(crate) struct ErrorImpl<E = ()> {
        vtable: &'static ErrorVTable,
        backtrace: Option<Backtrace>,
        _object: E,
    }
    unsafe fn vtable(p: NonNull<ErrorImpl>) -> &'static ErrorVTable {
        *(p.as_ptr() as *const &'static ErrorVTable)
    }
    #[repr(C)]
    pub(crate) struct ContextError<C, E> {
        pub context: C,
        pub error: E,
    }
    impl<E> ErrorImpl<E> {
        fn erase(&self) -> Ref<ErrorImpl> {
            Ref::new(self).cast::<ErrorImpl>()
        }
    }
    impl ErrorImpl {
        pub(crate) unsafe fn error(
            this: Ref<Self>,
        ) -> &(dyn StdError + Send + Sync + 'static) {
            (vtable(this.ptr).object_ref)(this).deref()
        }
        #[cfg(feature = "std")]
        pub(crate) unsafe fn error_mut(
            this: Mut<Self>,
        ) -> &mut (dyn StdError + Send + Sync + 'static) {
            #[cfg(not(anyhow_no_ptr_addr_of))]
            return (vtable(this.ptr).object_ref)(this.by_ref()).by_mut().deref_mut();
        }
        #[cfg(any(backtrace, feature = "backtrace"))]
        pub(crate) unsafe fn backtrace(this: Ref<Self>) -> &Backtrace {
            this.deref()
                .backtrace
                .as_ref()
                .or_else(|| {
                    #[cfg(backtrace)] return Self::error(this).backtrace();
                })
                .expect("backtrace capture failed")
        }
        #[cold]
        pub(crate) unsafe fn chain(this: Ref<Self>) -> Chain {
            Chain::new(Self::error(this))
        }
    }
    impl<E> StdError for ErrorImpl<E>
    where
        E: StdError,
    {
        #[cfg(backtrace)]
        fn backtrace(&self) -> Option<&Backtrace> {
            Some(unsafe { ErrorImpl::backtrace(self.erase()) })
        }
        fn source(&self) -> Option<&(dyn StdError + 'static)> {
            unsafe { ErrorImpl::error(self.erase()).source() }
        }
    }
    impl<E> Debug for ErrorImpl<E>
    where
        E: Debug,
    {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            unsafe { ErrorImpl::debug(self.erase(), formatter) }
        }
    }
    impl<E> Display for ErrorImpl<E>
    where
        E: Display,
    {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            unsafe { Display::fmt(ErrorImpl::error(self.erase()), formatter) }
        }
    }
    impl From<Error> for Box<dyn StdError + Send + Sync + 'static> {
        #[cold]
        fn from(error: Error) -> Self {
            let outer = ManuallyDrop::new(error);
            unsafe { (vtable(outer.inner.ptr).object_boxed)(outer.inner) }
        }
    }
    impl From<Error> for Box<dyn StdError + Send + 'static> {
        fn from(error: Error) -> Self {
            Box::<dyn StdError + Send + Sync>::from(error)
        }
    }
    impl From<Error> for Box<dyn StdError + 'static> {
        fn from(error: Error) -> Self {
            Box::<dyn StdError + Send + Sync>::from(error)
        }
    }
    #[cfg(feature = "std")]
    impl AsRef<dyn StdError + Send + Sync> for Error {
        fn as_ref(&self) -> &(dyn StdError + Send + Sync + 'static) {
            &**self
        }
    }
    #[cfg(feature = "std")]
    impl AsRef<dyn StdError> for Error {
        fn as_ref(&self) -> &(dyn StdError + 'static) {
            &**self
        }
    }
}
mod fmt {
    use crate::chain::Chain;
    use crate::error::ErrorImpl;
    use crate::ptr::Ref;
    use core::fmt::{self, Debug, Write};
    impl ErrorImpl {
        pub(crate) unsafe fn display(
            this: Ref<Self>,
            f: &mut fmt::Formatter,
        ) -> fmt::Result {
            {
                let result = f
                    .write_fmt(
                        ::core::fmt::Arguments::new_v1(
                            &[""],
                            &[::core::fmt::ArgumentV1::new_display(&Self::error(this))],
                        ),
                    );
                result
            }?;
            if f.alternate() {
                for cause in Self::chain(this).skip(1) {
                    {
                        let result = f
                            .write_fmt(
                                ::core::fmt::Arguments::new_v1(
                                    &[": "],
                                    &[::core::fmt::ArgumentV1::new_display(&cause)],
                                ),
                            );
                        result
                    }?;
                }
            }
            Ok(())
        }
        pub(crate) unsafe fn debug(
            this: Ref<Self>,
            f: &mut fmt::Formatter,
        ) -> fmt::Result {
            let error = Self::error(this);
            if f.alternate() {
                return Debug::fmt(error, f);
            }
            {
                let result = f
                    .write_fmt(
                        ::core::fmt::Arguments::new_v1(
                            &[""],
                            &[::core::fmt::ArgumentV1::new_display(&error)],
                        ),
                    );
                result
            }?;
            if let Some(cause) = error.source() {
                {
                    let result = f
                        .write_fmt(
                            ::core::fmt::Arguments::new_v1(&["\n\nCaused by:"], &[]),
                        );
                    result
                }?;
                let multiple = cause.source().is_some();
                for (n, error) in Chain::new(cause).enumerate() {
                    {
                        let result = f
                            .write_fmt(::core::fmt::Arguments::new_v1(&["\n"], &[]));
                        result
                    }?;
                    let mut indented = Indented {
                        inner: f,
                        number: if multiple { Some(n) } else { None },
                        started: false,
                    };
                    {
                        let result = indented
                            .write_fmt(
                                ::core::fmt::Arguments::new_v1(
                                    &[""],
                                    &[::core::fmt::ArgumentV1::new_display(&error)],
                                ),
                            );
                        result
                    }?;
                }
            }
            #[cfg(any(backtrace, feature = "backtrace"))]
            {
                use crate::backtrace::BacktraceStatus;
                let backtrace = Self::backtrace(this);
                if let BacktraceStatus::Captured = backtrace.status() {
                    let mut backtrace = backtrace.to_string();
                    {
                        let result = f
                            .write_fmt(::core::fmt::Arguments::new_v1(&["\n\n"], &[]));
                        result
                    }?;
                    if backtrace.starts_with("stack backtrace:") {
                        backtrace.replace_range(0..1, "S");
                    } else {
                        {
                            let result = f
                                .write_fmt(
                                    ::core::fmt::Arguments::new_v1(&["Stack backtrace:\n"], &[]),
                                );
                            result
                        }?;
                    }
                    backtrace.truncate(backtrace.trim_end().len());
                    {
                        let result = f
                            .write_fmt(
                                ::core::fmt::Arguments::new_v1(
                                    &[""],
                                    &[::core::fmt::ArgumentV1::new_display(&backtrace)],
                                ),
                            );
                        result
                    }?;
                }
            }
            Ok(())
        }
    }
    struct Indented<'a, D> {
        inner: &'a mut D,
        number: Option<usize>,
        started: bool,
    }
    impl<T> Write for Indented<'_, T>
    where
        T: Write,
    {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            for (i, line) in s.split('\n').enumerate() {
                if !self.started {
                    self.started = true;
                    match self.number {
                        Some(number) => {
                            {
                                let result = self
                                    .inner
                                    .write_fmt(
                                        ::core::fmt::Arguments::new_v1_formatted(
                                            &["", ": "],
                                            &[::core::fmt::ArgumentV1::new_display(&number)],
                                            &[
                                                ::core::fmt::rt::v1::Argument {
                                                    position: 0usize,
                                                    format: ::core::fmt::rt::v1::FormatSpec {
                                                        fill: ' ',
                                                        align: ::core::fmt::rt::v1::Alignment::Right,
                                                        flags: 0u32,
                                                        precision: ::core::fmt::rt::v1::Count::Implied,
                                                        width: ::core::fmt::rt::v1::Count::Is(5usize),
                                                    },
                                                },
                                            ],
                                            unsafe { ::core::fmt::UnsafeArg::new() },
                                        ),
                                    );
                                result
                            }?
                        }
                        None => self.inner.write_str("    ")?,
                    }
                } else if i > 0 {
                    self.inner.write_char('\n')?;
                    if self.number.is_some() {
                        self.inner.write_str("       ")?;
                    } else {
                        self.inner.write_str("    ")?;
                    }
                }
                self.inner.write_str(line)?;
            }
            Ok(())
        }
    }
}
mod kind {
    use crate::Error;
    use core::fmt::{Debug, Display};
    #[cfg(feature = "std")]
    use crate::StdError;
    pub struct Adhoc;
    pub trait AdhocKind: Sized {
        #[inline]
        fn anyhow_kind(&self) -> Adhoc {
            Adhoc
        }
    }
    impl<T> AdhocKind for &T
    where
        T: ?Sized + Display + Debug + Send + Sync + 'static,
    {}
    impl Adhoc {
        #[cold]
        pub fn new<M>(self, message: M) -> Error
        where
            M: Display + Debug + Send + Sync + 'static,
        {
            Error::from_adhoc(message, Some(crate::backtrace::Backtrace::capture()))
        }
    }
    pub struct Trait;
    pub trait TraitKind: Sized {
        #[inline]
        fn anyhow_kind(&self) -> Trait {
            Trait
        }
    }
    impl<E> TraitKind for E
    where
        E: Into<Error>,
    {}
    impl Trait {
        #[cold]
        pub fn new<E>(self, error: E) -> Error
        where
            E: Into<Error>,
        {
            error.into()
        }
    }
    #[cfg(feature = "std")]
    pub struct Boxed;
    #[cfg(feature = "std")]
    pub trait BoxedKind: Sized {
        #[inline]
        fn anyhow_kind(&self) -> Boxed {
            Boxed
        }
    }
    #[cfg(feature = "std")]
    impl BoxedKind for Box<dyn StdError + Send + Sync> {}
    #[cfg(feature = "std")]
    impl Boxed {
        #[cold]
        pub fn new(self, error: Box<dyn StdError + Send + Sync>) -> Error {
            let backtrace = match error.backtrace() {
                Some(_) => None,
                None => Some(crate::backtrace::Backtrace::capture()),
            };
            Error::from_boxed(error, backtrace)
        }
    }
}
mod macros {}
mod ptr {
    use alloc::boxed::Box;
    use core::marker::PhantomData;
    use core::ptr::NonNull;
    #[repr(transparent)]
    pub struct Own<T>
    where
        T: ?Sized,
    {
        pub ptr: NonNull<T>,
    }
    unsafe impl<T> Send for Own<T>
    where
        T: ?Sized,
    {}
    unsafe impl<T> Sync for Own<T>
    where
        T: ?Sized,
    {}
    impl<T> Copy for Own<T>
    where
        T: ?Sized,
    {}
    impl<T> Clone for Own<T>
    where
        T: ?Sized,
    {
        fn clone(&self) -> Self {
            *self
        }
    }
    impl<T> Own<T>
    where
        T: ?Sized,
    {
        pub fn new(ptr: Box<T>) -> Self {
            Own {
                ptr: unsafe { NonNull::new_unchecked(Box::into_raw(ptr)) },
            }
        }
        pub fn cast<U: CastTo>(self) -> Own<U::Target> {
            Own { ptr: self.ptr.cast() }
        }
        pub unsafe fn boxed(self) -> Box<T> {
            Box::from_raw(self.ptr.as_ptr())
        }
        pub fn by_ref(&self) -> Ref<T> {
            Ref {
                ptr: self.ptr,
                lifetime: PhantomData,
            }
        }
        pub fn by_mut(&mut self) -> Mut<T> {
            Mut {
                ptr: self.ptr,
                lifetime: PhantomData,
            }
        }
    }
    #[repr(transparent)]
    pub struct Ref<'a, T>
    where
        T: ?Sized,
    {
        pub ptr: NonNull<T>,
        lifetime: PhantomData<&'a T>,
    }
    impl<'a, T> Copy for Ref<'a, T>
    where
        T: ?Sized,
    {}
    impl<'a, T> Clone for Ref<'a, T>
    where
        T: ?Sized,
    {
        fn clone(&self) -> Self {
            *self
        }
    }
    impl<'a, T> Ref<'a, T>
    where
        T: ?Sized,
    {
        pub fn new(ptr: &'a T) -> Self {
            Ref {
                ptr: NonNull::from(ptr),
                lifetime: PhantomData,
            }
        }
        #[cfg(not(anyhow_no_ptr_addr_of))]
        pub fn from_raw(ptr: NonNull<T>) -> Self {
            Ref { ptr, lifetime: PhantomData }
        }
        pub fn cast<U: CastTo>(self) -> Ref<'a, U::Target> {
            Ref {
                ptr: self.ptr.cast(),
                lifetime: PhantomData,
            }
        }
        #[cfg(not(anyhow_no_ptr_addr_of))]
        pub fn by_mut(self) -> Mut<'a, T> {
            Mut {
                ptr: self.ptr,
                lifetime: PhantomData,
            }
        }
        #[cfg(not(anyhow_no_ptr_addr_of))]
        pub fn as_ptr(self) -> *const T {
            self.ptr.as_ptr() as *const T
        }
        pub unsafe fn deref(self) -> &'a T {
            &*self.ptr.as_ptr()
        }
    }
    #[repr(transparent)]
    pub struct Mut<'a, T>
    where
        T: ?Sized,
    {
        pub ptr: NonNull<T>,
        lifetime: PhantomData<&'a mut T>,
    }
    impl<'a, T> Copy for Mut<'a, T>
    where
        T: ?Sized,
    {}
    impl<'a, T> Clone for Mut<'a, T>
    where
        T: ?Sized,
    {
        fn clone(&self) -> Self {
            *self
        }
    }
    impl<'a, T> Mut<'a, T>
    where
        T: ?Sized,
    {
        pub fn cast<U: CastTo>(self) -> Mut<'a, U::Target> {
            Mut {
                ptr: self.ptr.cast(),
                lifetime: PhantomData,
            }
        }
        #[cfg(not(anyhow_no_ptr_addr_of))]
        pub fn by_ref(self) -> Ref<'a, T> {
            Ref {
                ptr: self.ptr,
                lifetime: PhantomData,
            }
        }
        pub fn extend<'b>(self) -> Mut<'b, T> {
            Mut {
                ptr: self.ptr,
                lifetime: PhantomData,
            }
        }
        pub unsafe fn deref_mut(self) -> &'a mut T {
            &mut *self.ptr.as_ptr()
        }
    }
    impl<'a, T> Mut<'a, T> {
        pub unsafe fn read(self) -> T {
            self.ptr.as_ptr().read()
        }
    }
    pub trait CastTo {
        type Target;
    }
    impl<T> CastTo for T {
        type Target = T;
    }
}
mod wrapper {
    use crate::StdError;
    use core::fmt::{self, Debug, Display};
    #[repr(transparent)]
    pub struct MessageError<M>(pub M);
    impl<M> Debug for MessageError<M>
    where
        M: Display + Debug,
    {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            Debug::fmt(&self.0, f)
        }
    }
    impl<M> Display for MessageError<M>
    where
        M: Display + Debug,
    {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            Display::fmt(&self.0, f)
        }
    }
    impl<M> StdError for MessageError<M>
    where
        M: Display + Debug + 'static,
    {}
    #[repr(transparent)]
    pub struct DisplayError<M>(pub M);
    impl<M> Debug for DisplayError<M>
    where
        M: Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            Display::fmt(&self.0, f)
        }
    }
    impl<M> Display for DisplayError<M>
    where
        M: Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            Display::fmt(&self.0, f)
        }
    }
    impl<M> StdError for DisplayError<M>
    where
        M: Display + 'static,
    {}
    #[cfg(feature = "std")]
    #[repr(transparent)]
    pub struct BoxedError(pub Box<dyn StdError + Send + Sync>);
    #[cfg(feature = "std")]
    impl Debug for BoxedError {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            Debug::fmt(&self.0, f)
        }
    }
    #[cfg(feature = "std")]
    impl Display for BoxedError {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            Display::fmt(&self.0, f)
        }
    }
    #[cfg(feature = "std")]
    impl StdError for BoxedError {
        #[cfg(backtrace)]
        fn backtrace(&self) -> Option<&crate::backtrace::Backtrace> {
            self.0.backtrace()
        }
        fn source(&self) -> Option<&(dyn StdError + 'static)> {
            self.0.source()
        }
    }
}
use crate::error::ErrorImpl;
use crate::ptr::Own;
use core::fmt::Display;
#[cfg(feature = "std")]
use std::error::Error as StdError;
pub use anyhow as format_err;
#[repr(transparent)]
pub struct Error {
    inner: Own<ErrorImpl>,
}
#[cfg(feature = "std")]
pub struct Chain<'a> {
    state: crate::chain::ChainState<'a>,
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl<'a> ::core::clone::Clone for Chain<'a> {
    #[inline]
    fn clone(&self) -> Chain<'a> {
        match *self {
            Self { state: ref __self_0_0 } => {
                Chain {
                    state: ::core::clone::Clone::clone(&(*__self_0_0)),
                }
            }
        }
    }
}
pub type Result<T, E = Error> = core::result::Result<T, E>;
pub trait Context<T, E>: context::private::Sealed {
    fn context<C>(self, context: C) -> Result<T, Error>
    where
        C: Display + Send + Sync + 'static;
    fn with_context<C, F>(self, f: F) -> Result<T, Error>
    where
        C: Display + Send + Sync + 'static,
        F: FnOnce() -> C;
}
#[allow(non_snake_case)]
pub fn Ok<T>(t: T) -> Result<T> {
    Result::Ok(t)
}
#[doc(hidden)]
pub mod private {
    use crate::Error;
    use alloc::fmt;
    use core::fmt::Arguments;
    pub use crate::ensure::{BothDebug, NotBothDebug};
    pub use alloc::format;
    pub use core::result::Result::Err;
    pub use core::{concat, format_args, stringify};
    #[doc(hidden)]
    pub mod kind {
        pub use crate::kind::{AdhocKind, TraitKind};
        #[cfg(feature = "std")]
        pub use crate::kind::BoxedKind;
    }
    #[doc(hidden)]
    #[inline]
    #[cold]
    pub fn format_err(args: Arguments) -> Error {
        #[cfg(not(anyhow_no_fmt_arguments_as_str))]
        let fmt_arguments_as_str = args.as_str();
        if let Some(message) = fmt_arguments_as_str {
            Error::msg(message)
        } else {
            Error::msg(fmt::format(args))
        }
    }
    #[doc(hidden)]
    #[inline]
    #[cold]
    #[must_use]
    pub fn must_use(error: Error) -> Error {
        error
    }
}
