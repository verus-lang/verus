use crate::contrib::exec_spec::*;
use crate::prelude::*;

verus! {

impl<'a, T: Sized + DeepView, E: Sized + DeepView> ToRef<&'a Result<T, E>> for &'a Result<T, E> {
    #[inline(always)]
    fn get_ref(self) -> &'a Result<T, E> {
        self
    }
}

impl<'a, T: DeepView + DeepViewClone, E: DeepView + DeepViewClone> ToOwned<
    Result<T, E>,
> for &'a Result<T, E> {
    #[inline(always)]
    fn get_owned(self) -> Result<T, E> {
        self.deep_clone()
    }
}

impl<T: DeepViewClone, E: DeepViewClone> DeepViewClone for Result<T, E> {
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        match self {
            Ok(t) => Ok(t.deep_clone()),
            Err(e) => Err(e.deep_clone()),
        }
    }
}

impl<'a, T: DeepView, E: DeepView> ExecSpecEq<'a> for &'a Result<T, E> where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
    &'a E: ExecSpecEq<'a, Other = &'a E>,
 {
    type Other = &'a Result<T, E>;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        match (this, other) {
            (Ok(t1), Ok(t2)) => <&'a T>::exec_eq(t1, t2),
            (Err(e1), Err(e2)) => <&'a E>::exec_eq(e1, e2),
            _ => false,
        }
    }
}

pub trait ExecSpecResultArrow<T, E>: Sized {
    spec fn is_ok_variant_spec(&self) -> bool;

    spec fn is_err_variant_spec(&self) -> bool;

    #[allow(non_snake_case)]
    fn exec_arrow_Ok_0(&self) -> &T
        requires
            self.is_ok_variant_spec(),
    ;

    #[allow(non_snake_case)]
    fn exec_arrow_Err_0(&self) -> &E
        requires
            self.is_err_variant_spec(),
    ;
}

impl<T: DeepView, E: DeepView> ExecSpecResultArrow<T, E> for Result<T, E> {
    open spec fn is_ok_variant_spec(&self) -> bool {
        *self is Ok
    }

    open spec fn is_err_variant_spec(&self) -> bool {
        *self is Err
    }

    #[inline(always)]
    fn exec_arrow_Ok_0(&self) -> (res: &T)
        ensures
            res.deep_view() == self.deep_view()->Ok_0,
    {
        match self {
            Ok(t) => t,
            Err(_) => crate::pervasive::unreached(),
        }
    }

    #[inline(always)]
    fn exec_arrow_Err_0(&self) -> (res: &E)
        ensures
            res.deep_view() == self.deep_view()->Err_0,
    {
        match self {
            Err(e) => e,
            Ok(_) => crate::pervasive::unreached(),
        }
    }
}

} // verus!
