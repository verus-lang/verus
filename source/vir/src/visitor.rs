use std::sync::Arc;

pub(crate) trait Returner {
    type Ret<A>;
    type Vec<A>;
    type Opt<A>;
    fn get<A>(r: Self::Ret<A>) -> A;
    fn get_vec<A>(r: Self::Vec<A>) -> Vec<A>;
    fn get_vec_a<A>(r: Self::Vec<A>) -> Arc<Vec<A>>;
    fn get_vec_or<'a, A>(r: &'a Self::Vec<A>, or: &'a Vec<A>) -> &'a Vec<A>;
    fn get_opt<A>(r: Self::Opt<A>) -> Option<A>;
    fn vec<A>() -> Self::Vec<A>;
    fn push<A>(v: &mut Self::Vec<A>, a: Self::Ret<A>);
    fn map_vec<A, B, Err>(
        v: &Vec<A>,
        f: &mut impl FnMut(&A) -> Result<Self::Ret<B>, Err>,
    ) -> Result<Self::Vec<B>, Err>;
    fn map_opt<A, B, Err>(
        o: &Option<A>,
        f: &mut impl FnMut(&A) -> Result<Self::Ret<B>, Err>,
    ) -> Result<Self::Opt<B>, Err>;
    fn ret<A, Err>(f: impl FnOnce() -> A) -> Result<Self::Ret<A>, Err>;
}

pub(crate) struct Walk;
pub(crate) struct Rewrite;

impl Returner for Walk {
    type Ret<A> = ();
    type Vec<A> = ();
    type Opt<A> = ();
    fn get<A>(_: Self::Ret<A>) -> A {
        panic!("cannot use Returner::get in Walk");
    }
    fn get_vec<A>(_: Self::Vec<A>) -> Vec<A> {
        panic!("cannot use Returner::get_vec in Walk");
    }
    fn get_vec_a<A>(_: Self::Vec<A>) -> Arc<Vec<A>> {
        panic!("cannot use Returner::get_vec_a in Walk");
    }
    fn get_vec_or<'a, A>(_r: &'a Self::Vec<A>, or: &'a Vec<A>) -> &'a Vec<A> {
        or
    }
    fn get_opt<A>(_: Self::Opt<A>) -> Option<A> {
        panic!("cannot use Returner::get_opt in Walk");
    }
    fn vec<A>() -> Self::Vec<A> {
        ()
    }
    fn push<A>(_: &mut Self::Vec<A>, _: Self::Ret<A>) {}
    fn map_vec<A, B, Err>(
        v: &Vec<A>,
        f: &mut impl FnMut(&A) -> Result<Self::Ret<B>, Err>,
    ) -> Result<Self::Vec<B>, Err> {
        for a in v {
            f(a)?;
        }
        Ok(())
    }
    fn map_opt<A, B, Err>(
        o: &Option<A>,
        f: &mut impl FnMut(&A) -> Result<Self::Ret<B>, Err>,
    ) -> Result<Self::Opt<B>, Err> {
        if let Some(a) = o {
            f(a)?;
        }
        Ok(())
    }
    fn ret<A, Err>(_: impl FnOnce() -> A) -> Result<Self::Ret<A>, Err> {
        Ok(())
    }
}

impl Returner for Rewrite {
    type Ret<A> = A;
    type Vec<A> = Vec<A>;
    type Opt<A> = Option<A>;
    fn get<A>(r: Self::Ret<A>) -> A {
        r
    }
    fn get_vec<A>(r: Self::Vec<A>) -> Vec<A> {
        r
    }
    fn get_vec_a<A>(r: Self::Vec<A>) -> Arc<Vec<A>> {
        Arc::new(r)
    }
    fn get_vec_or<'a, A>(r: &'a Self::Vec<A>, _or: &'a Vec<A>) -> &'a Vec<A> {
        r
    }
    fn get_opt<A>(o: Self::Opt<A>) -> Option<A> {
        o
    }
    fn vec<A>() -> Self::Vec<A> {
        Vec::new()
    }
    fn push<A>(v: &mut Self::Vec<A>, a: Self::Ret<A>) {
        v.push(a);
    }
    fn map_vec<A, B, Err>(
        v: &Vec<A>,
        f: &mut impl FnMut(&A) -> Result<Self::Ret<B>, Err>,
    ) -> Result<Self::Vec<B>, Err> {
        let mut vec = Vec::new();
        for a in v {
            vec.push(f(a)?);
        }
        Ok(vec)
    }
    fn map_opt<A, B, Err>(
        o: &Option<A>,
        f: &mut impl FnMut(&A) -> Result<Self::Ret<B>, Err>,
    ) -> Result<Self::Opt<B>, Err> {
        if let Some(a) = o { Ok(Some(f(a)?)) } else { Ok(None) }
    }
    fn ret<A, Err>(f: impl FnOnce() -> A) -> Result<Self::Ret<A>, Err> {
        Ok(f())
    }
}

#[derive(PartialEq, Eq, Debug)]
pub(crate) enum VisitorControlFlow<T> {
    Recurse,
    Return,
    Stop(T),
}

macro_rules! expr_visitor_control_flow {
    ($cf:expr) => {
        match $cf {
            crate::ast_visitor::VisitorControlFlow::Recurse => (),
            crate::ast_visitor::VisitorControlFlow::Return => (),
            crate::ast_visitor::VisitorControlFlow::Stop(val) => {
                return crate::ast_visitor::VisitorControlFlow::Stop(val);
            }
        }
    };
}

pub(crate) use expr_visitor_control_flow;
