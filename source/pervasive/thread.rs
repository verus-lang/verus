#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::result::*;

verus!{

pub trait Spawnable<Ret: Sized> : Sized {
    spec fn pre(self) -> bool;

    spec fn post(self, ret: Ret) -> bool;
    
    exec fn run(self) -> (r: Ret)
        requires self.pre(),
        ensures self.post(r);
}

}

#[verifier(external_body)]
pub struct JoinHandle<#[verifier(maybe_negative)] Ret>
{
    handle: std::thread::JoinHandle<Ret>,
}

impl<Ret> JoinHandle<Ret>
{
    fndecl!(pub fn predicate(&self, ret: Ret) -> bool);

    #[verifier(external_body)]
    pub fn join(self) -> Result<Ret, ()>
    {
        ensures(|r: Result<Ret, ()>|
            r.is_Ok() >>= self.predicate(r.get_Ok_0()));

        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            match self.handle.join() {
                Ok(r) => Result::Ok(r),
                Err(_) => Result::Err(()),
            }
        }));
        match res {
            Ok(res) => res,
            Err(_) => {
                println!("panic on join");
                std::process::abort();
            }
        }
    }
}

#[verifier(external_body)]
pub fn spawn<Param: Spawnable<Ret> + Send + 'static, Ret: Send + 'static>(p: Param) -> JoinHandle<Ret> 
{
    requires(p.pre());
    ensures(|handle: JoinHandle<Ret>|
        forall(|ret: Ret| handle.predicate(ret) >>= p.post(ret)));

    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let handle = std::thread::spawn(move || p.run());
        JoinHandle { handle }
    }));
    match res {
        Ok(res) => res,
        Err(_) => {
            println!("panic on spawn");
            std::process::abort();
        }
    }
}

