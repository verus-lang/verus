#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::result::*;

trait Spawnable<Ret: Sized> : Sized {
    #[spec]
    fn pre(self) -> bool { no_method_body() }

    #[spec]
    fn post(self, ret: Ret) -> bool { no_method_body() }
    
    fn run(self) -> Ret {
        requires(self.pre());
        ensures(|r: Ret| self.post(r));
        no_method_body()
    }
}

#[verifier(external_body)]
pub struct JoinHandle<#[verifier(maybe_negative)] Ret>
{
    handle: std::thread::JoinHandle<Ret>,
}

impl<Ret> JoinHandle<Ret>
{
    fndecl!(fn predicate(&self, ret: Ret) -> bool);

    // TODO note that std::thread::JoinHandle::join is allowed to panic
    #[verifier(external_body)]
    fn join(self) -> Result<Ret, ()>
    {
        ensures(|r: Result<Ret, ()>|
            r.is_Ok() >>= self.predicate(r.get_Ok_0()));

        match self.handle.join() {
            Ok(r) => Result::Ok(r),
            Err(_) => Result::Err(()),
        }
    }
}

#[verifier(external_body)]
pub fn spawn<Param: Spawnable<Ret> + Send + 'static, Ret: Send + 'static>(p: Param) -> JoinHandle<Ret> 
{
    requires(p.pre());
    ensures(|handle: JoinHandle<Ret>|
        forall(|ret: Ret| handle.predicate(ret) >>= p.post(ret)));

    let handle = std::thread::spawn(move || p.run());
    JoinHandle { handle }
}
