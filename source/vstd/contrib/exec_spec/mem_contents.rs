//! This module contains the exec mirror of [`crate::raw_ptr::MemContents`],
//! the abstract memory-state view of the `PointsTo` permission family
//! (`raw_ptr::PointsTo`, `simple_pptr::PointsTo`, `cell::PointsTo`).
//!
//! Unlike `Option<T>` (whose exec mirror is itself), `MemContents` needs a
//! distinct exec type: it is a `ghost enum`, so its constructors don't
//! exist in exec code under `cargo verus verify`.
use crate::contrib::exec_spec::*;
use crate::prelude::*;
use crate::raw_ptr::MemContents;

verus! {

/// `MemContents<T>` is compiled to `ExecMemContents<T>`
#[derive(Eq, Hash, PartialEq, Debug)]
pub enum ExecMemContents<T> {
    /// Mirror of [`MemContents::Uninit`]
    Uninit,
    /// Mirror of [`MemContents::Init`]
    Init(T),
}

#[allow(non_snake_case)]
impl<T: DeepView> ExecMemContents<T> {
    #[inline(always)]
    pub fn exec_is_Init(&self) -> (res: bool)
        ensures
            res == self.deep_view() is Init,
    {
        match self {
            ExecMemContents::Init(_) => true,
            ExecMemContents::Uninit => false,
        }
    }

    #[inline(always)]
    pub fn exec_is_Uninit(&self) -> (res: bool)
        ensures
            res == self.deep_view() is Uninit,
    {
        match self {
            ExecMemContents::Uninit => true,
            ExecMemContents::Init(_) => false,
        }
    }

    #[inline(always)]
    pub fn exec_arrow_Init_0(&self) -> (res: &T)
        requires
            self.deep_view() is Init,
        ensures
            res.deep_view() == self.deep_view()->Init_0,
    {
        match self {
            ExecMemContents::Init(t) => t,
            ExecMemContents::Uninit => crate::pervasive::unreached(),
        }
    }

    #[inline(always)]
    pub fn exec_arrow_0(&self) -> (res: &T)
        requires
            self.deep_view() is Init,
        ensures
            res.deep_view() == self.deep_view()->0,
    {
        match self {
            ExecMemContents::Init(t) => t,
            ExecMemContents::Uninit => crate::pervasive::unreached(),
        }
    }
}

/// Implementations for shared traits
impl<T: DeepView> DeepView for ExecMemContents<T> {
    type V = MemContents<<T as DeepView>::V>;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            ExecMemContents::Uninit => MemContents::Uninit,
            ExecMemContents::Init(t) => MemContents::Init(t.deep_view()),
        }
    }
}

impl<'a, T: DeepView> ToRef<&'a ExecMemContents<T>> for &'a ExecMemContents<T> {
    #[inline(always)]
    fn get_ref(self) -> &'a ExecMemContents<T> {
        self
    }
}

impl<'a, T: DeepView + DeepViewClone> ToOwned<ExecMemContents<T>> for &'a ExecMemContents<T> {
    #[inline(always)]
    fn get_owned(self) -> ExecMemContents<T> {
        self.deep_clone()
    }
}

impl<T: DeepViewClone> DeepViewClone for ExecMemContents<T> {
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        match self {
            ExecMemContents::Uninit => ExecMemContents::Uninit,
            ExecMemContents::Init(t) => ExecMemContents::Init(t.deep_clone()),
        }
    }
}

impl<'a, T: DeepView> ExecSpecEq<'a> for &'a ExecMemContents<T> where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
 {
    type Other = &'a ExecMemContents<T>;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        match (this, other) {
            (ExecMemContents::Init(t1), ExecMemContents::Init(t2)) => <&'a T>::exec_eq(t1, t2),
            (ExecMemContents::Uninit, ExecMemContents::Uninit) => true,
            _ => false,
        }
    }
}

/// Traits for MemContents methods
/// Spec for executable versions of [`MemContents::is_init`],
/// [`MemContents::is_uninit`], and [`MemContents::value`].
pub trait ExecSpecMemContents<'a>: Sized + DeepView {
    type Elem: DeepView + DeepViewClone;

    spec fn is_init_spec(&self) -> bool;

    fn exec_is_init(self) -> bool;

    fn exec_is_uninit(self) -> bool;

    fn exec_value(self) -> Self::Elem
        requires
            self.is_init_spec(),
    ;
}

/// Impls for MemContents methods
impl<'a, T> ExecSpecMemContents<'a> for &'a ExecMemContents<T> where T: DeepView + DeepViewClone {
    type Elem = T;

    open spec fn is_init_spec(&self) -> bool {
        self.deep_view() is Init
    }

    #[inline(always)]
    fn exec_is_init(self) -> (res: bool)
        ensures
            res == self.deep_view().is_init(),
    {
        match self {
            ExecMemContents::Init(_) => true,
            ExecMemContents::Uninit => false,
        }
    }

    #[inline(always)]
    fn exec_is_uninit(self) -> (res: bool)
        ensures
            res == self.deep_view().is_uninit(),
    {
        match self {
            ExecMemContents::Uninit => true,
            ExecMemContents::Init(_) => false,
        }
    }

    #[inline(always)]
    fn exec_value(self) -> (res: Self::Elem)
        ensures
            res.deep_view() == self.deep_view()->0,
    {
        match self {
            ExecMemContents::Init(t) => t.deep_clone(),
            ExecMemContents::Uninit => {
                // Unreachable under the `is_init_spec` requires.
                crate::pervasive::unreached()
            },
        }
    }
}

} // verus!
