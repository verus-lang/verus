#![allow(unused_imports)]

use super::pervasive::*;
use core::marker;
use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

/// Runs `f`, aborting the process if it panics, so that unwinding never
/// reaches verified code.
#[verifier::external]
fn abort_on_panic<R, F: FnOnce() -> R>(msg: &str, f: F) -> R {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(res) => res,
        Err(_) => {
            println!("{}", msg);
            std::process::abort();
        },
    }
}

/// Object returned by [`spawn()`](spawn) to allow thread joining.
/// (Wrapper around [`std::thread::JoinHandle`](https://doc.rust-lang.org/std/thread/struct.JoinHandle.html).)
///
/// See the documentation of [`spawn()`](spawn) for more details.
#[verifier::external_body]
#[verifier::reject_recursive_types(Ret)]
pub struct JoinHandle<Ret> {
    handle: std::thread::JoinHandle<Ret>,
}

impl<Ret> JoinHandle<Ret> {
    /// Predicate restricting the possible return values. This is determined by the
    /// postcondition of the closure provided when calling `spawn()`.
    pub uninterp spec fn predicate(&self, ret: Ret) -> bool;

    /// Wait for a thread to complete.
    #[verifier::external_body]
    pub fn join(self) -> (r_result: Result<Ret, ()>)
        ensures
            match r_result {
                Result::Ok(r) => self.predicate(r),
                Result::Err(_) => true,
            },
    {
        abort_on_panic(
            "panic on join",
            ||
                {
                    match self.handle.join() {
                        Ok(v) => Ok(v),
                        Err(_) => Err(()),
                    }
                },
        )
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
#[verifier::external_body]
pub fn spawn<F, Ret>(f: F) -> (handle: JoinHandle<Ret>) where
    F: FnOnce() -> Ret,
    F: Send + 'static,
    Ret: Send + 'static,

    requires
        f.requires(()),
    ensures
        forall|ret: Ret| #[trigger] handle.predicate(ret) ==> f.ensures((), ret),
{
    abort_on_panic(
        "panic on spawn",
        ||
            {
                let handle = std::thread::spawn(move || f());
                JoinHandle { handle }
            },
    )
}

/// A scope to spawn scoped threads in, created by [`scope()`](scope).
/// (Wrapper around [`std::thread::Scope`](https://doc.rust-lang.org/std/thread/struct.Scope.html).)
///
/// See the documentation of [`scope()`](scope) for more details.
#[verifier::external_body]
#[repr(transparent)]
pub struct Scope<'scope, 'env: 'scope> {
    inner: std::thread::Scope<'scope, 'env>,
}

/// Object returned by [`Scope::spawn()`](Scope::spawn) to allow joining a scoped thread.
/// (Wrapper around [`std::thread::ScopedJoinHandle`](https://doc.rust-lang.org/std/thread/struct.ScopedJoinHandle.html).)
///
/// See the documentation of [`scope()`](scope) for more details.
#[verifier::external_body]
#[verifier::reject_recursive_types(Ret)]
pub struct ScopedJoinHandle<'scope, Ret> {
    handle: std::thread::ScopedJoinHandle<'scope, Ret>,
}

impl<'scope, Ret> ScopedJoinHandle<'scope, Ret> {
    /// Predicate restricting the possible return values. This is determined by the
    /// postcondition of the closure provided when calling `Scope::spawn()`.
    pub uninterp spec fn predicate(&self, ret: Ret) -> bool;

    /// Wait for a scoped thread to complete.
    #[verifier::external_body]
    pub fn join(self) -> (r_result: Result<Ret, ()>)
        ensures
            match r_result {
                Result::Ok(r) => self.predicate(r),
                Result::Err(_) => true,
            },
    {
        abort_on_panic(
            "panic on join",
            ||
                {
                    match self.handle.join() {
                        Ok(v) => Ok(v),
                        Err(_) => Err(()),
                    }
                },
        )
    }
}

impl<'scope, 'env> Scope<'scope, 'env> {
    /// Spawns a scoped thread. (Wrapper around
    /// [`std::thread::Scope::spawn`](https://doc.rust-lang.org/std/thread/struct.Scope.html#method.spawn).)
    ///
    /// Unlike [`spawn()`](spawn), the closure may borrow non-`'static` data from
    /// outside the scope. The precondition and postcondition behave as for
    /// [`spawn()`](spawn): the closure must be callable, and its postcondition is
    /// passed through the [`ScopedJoinHandle`] via
    /// [`ScopedJoinHandle::predicate()`](ScopedJoinHandle::predicate).
    #[verifier::external_body]
    pub fn spawn<F, Ret>(&'scope self, f: F) -> (handle: ScopedJoinHandle<'scope, Ret>) where
        F: FnOnce() -> Ret,
        F: Send + 'scope,
        Ret: Send + 'scope,

        requires
            f.requires(()),
        ensures
            forall|ret: Ret| #[trigger] handle.predicate(ret) ==> f.ensures((), ret),
    {
        abort_on_panic(
            "panic on spawn",
            ||
                {
                    let handle = self.inner.spawn(move || f());
                    ScopedJoinHandle { handle }
                },
        )
    }
}

/// Creates a scope for spawning scoped threads.
/// (Wrapper around [`std::thread::scope`](https://doc.rust-lang.org/std/thread/fn.scope.html).)
///
/// This takes as input a `FnOnce` closure that receives a [`Scope`].
/// Inside the closure, [`Scope::spawn()`](Scope::spawn) spawns threads that, unlike
/// threads created by [`spawn()`](spawn), may borrow non-`'static` data from the
/// enclosing function. All threads spawned in the scope are automatically joined
/// before `scope` returns. The return value of the closure is returned by `scope`.
///
/// The closure must be callable (i.e., its precondition must be satisfied) for any
/// `Scope`, and the return value satisfies the closure's postcondition.
/// Since `Scope` has no specification-level information, closure specifications normally
/// do not mention the `Scope` argument.
///
/// The postcondition of a scoped thread is only available if the thread is explicitly
/// joined with [`ScopedJoinHandle::join()`](ScopedJoinHandle::join).
///
/// ### Example
///
/// ```rust,ignore
/// fn main() {
///     let mut v: Vec<u64> = Vec::new();
///     v.push(10);
///     v.push(20);
///     assert(v@ =~= seq![10u64, 20u64]);
///
///     let sum = scope(|s| -> (r: u64)
///         requires v@ == seq![10u64, 20u64],
///         ensures r == 30,
///     {
///         // Borrow the non-'static `v` from a scoped thread.
///         let handle = s.spawn(|| -> (r: u64)
///             requires v@ == seq![10u64, 20u64],
///             ensures r == 30,
///         {
///             v[0] + v[1]
///         });
///
///         // The thread's postcondition is available through `join()`.
///         match handle.join() {
///             Result::Ok(r) => r,
///             Result::Err(_) => 30,
///         }
///     });
///
///     assert(sum == 30);
///
///     // `v` can be mutated again once the scope ends.
///     v.push(30);
/// }
/// ```
#[verifier::external_body]
pub fn scope<'env, F, T>(f: F) -> (r: T) where
    F: for <'scope>FnOnce(&'scope Scope<'scope, 'env>) -> T,

    requires
        forall|s: &Scope<'_, 'env>| f.requires((s,)),
    ensures
        exists|s: &Scope<'_, 'env>| f.ensures((s,), r),
{
    abort_on_panic(
        "panic on scope",
        ||
            {
                std::thread::scope(
                    |s|
                        {
                            let s: &Scope<'_, 'env> = unsafe {
                                &*(s as *const std::thread::Scope<'_, 'env> as *const Scope<
                                    '_,
                                    'env,
                                >)
                            };
                            f(s)
                        },
                )
            },
    )
}

/// Wrapper around Rust's
/// [`ThreadId`](https://doc.rust-lang.org/std/thread/struct.ThreadId.html)
/// object. This is an opaque type.
// Note: Rust defines ThreadId as an opaque type. Rust guarantees that ThreadIds
// will never be reused. There's also an `as_u64()` method, but it's unstable,
// and right now it's not clear if it's going to have the same guarantee.
// Regardless, it seems best to stick with Rust's opaque type here.
#[verifier::external_body]
pub struct ThreadId {
    thread_id: std::thread::ThreadId,
}

/// Proof object that guarantees the owning thread has the given ThreadId.
#[cfg(verus_keep_ghost)]
#[verifier::external_body]
pub tracked struct IsThread {}

#[cfg(verus_keep_ghost)]
impl !Sync for IsThread {

}

#[cfg(verus_keep_ghost)]
impl !Send for IsThread {

}

// TODO: remove this when !Sync, !Send are supported by stable Rust
#[cfg(not(verus_keep_ghost))]
#[verifier::external_body]
pub tracked struct IsThread {
    _no_send_sync: core::marker::PhantomData<*const ()>,
}

impl IsThread {
    pub uninterp spec fn view(&self) -> ThreadId;

    /// Guarantees that any two `IsThread` objects on the same thread
    /// will have the same ID.
    pub axiom fn agrees(tracked self, tracked other: IsThread)
        ensures
            self@ == other@,
    ;
}

#[verifier::external]
impl Clone for IsThread {
    #[cfg(verus_keep_ghost)]
    fn clone(&self) -> Self {
        IsThread {  }
    }

    #[cfg(not(verus_keep_ghost))]
    fn clone(&self) -> Self {
        IsThread { _no_send_sync: Default::default() }
    }
}

impl Copy for IsThread {

}

/// Gets the current thread ID using Rust's [`Thread::id()`](https://doc.rust-lang.org/std/thread/struct.Thread.html#method.id)
/// under the hood. Also returns a ghost object representing proof of being on this thread.
#[verifier::external_body]
pub fn thread_id() -> (res: (ThreadId, Tracked<IsThread>))
    ensures
        res.1@@ == res.0,
{
    let id: std::thread::ThreadId = std::thread::current().id();
    let id = ThreadId { thread_id: id };
    (id, Tracked::assume_new())
}

/// Returns _just_ the ghost object, without physically obtaining the thread ID.
pub axiom fn ghost_thread_id() -> (tracked res: IsThread);

/// Tracked object that makes any tracked object `Send` or `Sync`.
/// Requires the client to prove that they are the correct thread in order to
/// access the underlying object.
#[verifier::external_body]
#[verifier::accept_recursive_types(V)]
tracked struct ThreadShareable<V> {
    phantom: marker::PhantomData<V>,
}

#[verifier::external]
unsafe impl<V> Sync for ThreadShareable<V> {

}

#[verifier::external]
unsafe impl<V> Send for ThreadShareable<V> {

}

impl<V> ThreadShareable<V> {
    pub uninterp spec fn view(&self) -> V;

    pub uninterp spec fn id(&self) -> ThreadId;

    /// Recover the inner value provide we are on the same thread.
    pub axiom fn into(tracked self, tracked is_thread: IsThread) -> (tracked res: V)
        requires
            self.id() == is_thread@,
        ensures
            res == self@,
    ;

    /// Borrow the inner value provide we are on the same thread.
    pub axiom fn borrow(tracked &self, tracked is_thread: IsThread) -> (tracked res: &V)
        requires
            self.id() == is_thread@,
        ensures
            *res == self@,
    ;
}

impl<V: Send> ThreadShareable<V> {
    /// Recover the inner value.
    /// Unlike `into`, this has no thread requirement, but it does
    /// require the inner type to be `Send`.
    pub axiom fn send_into(tracked self) -> (tracked res: V)
        ensures
            res == self@,
    ;
}

impl<V: Sync> ThreadShareable<V> {
    /// Borrow the inner value.
    /// Unlike `borrow`, this has no thread requirement, but it does
    /// require the inner type to be `Sync`.
    pub axiom fn sync_borrow(tracked &self) -> (tracked res: &V)
        ensures
            *res == self@,
    ;
}

} // verus!
