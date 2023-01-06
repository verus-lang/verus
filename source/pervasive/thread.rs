#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::result::*;

verus! {

/// Object returned by [`spawn()`](spawn) to allow thread joining.
/// (Wrapper around [`std::thread::JoinHandle`](https://doc.rust-lang.org/std/thread/struct.JoinHandle.html).)
///
/// See the documentation of [`spawn()`](spawn) for more details.

#[verifier(external_body)]
pub struct JoinHandle<#[verifier(maybe_negative)] Ret>
{
    handle: std::thread::JoinHandle<Ret>,
}

impl<Ret> JoinHandle<Ret> {
    /// Predicate restricting the possible return values. This is determined by the
    /// postcondition of the closure provided when calling `spawn()`.

    pub spec fn predicate(&self, ret: Ret) -> bool;

    /// Wait for a thread to complete.

    #[verifier(external_body)]
    pub fn join(self) -> (r_result: Result<Ret, ()>)
        ensures match r_result {
            Result::Ok(r) => self.predicate(r),
            Result::Err(_) => true,
        },
    {
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

/// Spawns a thread. (Wrapper around [`std::thread::spawn`](https://doc.rust-lang.org/std/thread/fn.spawn.html).)
///
/// This takes as input a `FnOnce` closure with no arguments.
/// The `spawn` returns a [`JoinHandle`], on which the client can call
/// [`join()`](JoinHandle::join) to wait
/// for the thread to complete. The return value of the closure is returned via `join()`.
///
/// The closure must be callable (i.e., its precondition must be satisfied)
/// but it may have an arbitrary postcondition. The postcondition is passed through
/// the `JoinHandle` via [`JoinHandle::predicate()`](JoinHandle::predicate).
///
/// ### Example
///
/// ```rust,ignore
/// struct MyInteger {
///     u: u64,
/// }
/// 
/// fn main() {
///     // Construct an object to pass into the thread.
///     let my_int = MyInteger { u: 5 };
/// 
///     // Spawn a new thread.
///     let join_handle = spawn(move || {
///         ensures(|return_value: MyInteger|
///             return_value.u == 20);
/// 
///         // Move the `my_int` object into the closure.
///         let mut my_int_on_another_thread = my_int;
/// 
///         // Update its value.
///         my_int_on_another_thread.u = 20;
/// 
///         // Return it.
///         my_int_on_another_thread
///     });
/// 
///     // Wait for the thread to finish its work.
///     let result_my_int = join_handle.join();
/// 
///     match result_my_int {
///         Result::Ok(my_int) => {
///             // Obtain the `MyInteger` object that was passed
///             // back from the spawned thread.
///             // Assert that it has the right value.
///             assert(my_int.u == 20);
///         }
///         Result::Err(_) => { }
///     }
/// }
/// ```

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
