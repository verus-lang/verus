#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::result::*;

verus! {

#[verifier(external_body)]
pub struct JoinHandle<#[verifier(maybe_negative)] Ret>
{
    handle: std::thread::JoinHandle<Ret>,
}

impl<Ret> JoinHandle<Ret> {
    pub spec fn predicate(&self, ret: Ret) -> bool;

    #[verifier(external_body)]
    pub fn join(self) -> Result<Ret, ()>
    {
        ensures(|r: Result<Ret, ()>|
            r.is_Ok() ==> self.predicate(r.get_Ok_0()));

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
pub fn spawn<F, Ret>(f: F) -> (handle: JoinHandle<Ret>)
    where F: FnOnce() -> Ret,
          F: Send + 'static,
          Ret: Send + 'static,
    requires f.requires(()),
    ensures forall |ret: Ret| #[trigger] handle.predicate(ret) ==> f.ensures((), ret),
{
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let handle = std::thread::spawn(move || f());
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

} // verus!
