#![allow(unused_imports)]

use super::pervasive::*;
use builtin::*;
use builtin_macros::*;
use core::marker;

verus! {

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
    pub spec fn predicate(&self, ret: Ret) -> bool;

    /// Wait for a thread to complete.
    #[verifier::external_body]
    pub fn join(self) -> (r_result: Result<Ret, ()>)
        ensures
            match r_result {
                Result::Ok(r) => self.predicate(r),
                Result::Err(_) => true,
            },
    {
        let res = std::panic::catch_unwind(
            std::panic::AssertUnwindSafe(
                ||
                    {
                        match self.handle.join() {
                            Ok(v) => Ok(v),
                            Err(_) => Err(()),
                        }
                    },
            ),
        );
        match res {
            Ok(res) => res,
            Err(_) => {
                println!("panic on join");
                std::process::abort();
            },
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
    let res = std::panic::catch_unwind(
        std::panic::AssertUnwindSafe(
            ||
                {
                    let handle = std::thread::spawn(move || f());
                    JoinHandle { handle }
                },
        ),
    );
    match res {
        Ok(res) => res,
        Err(_) => {
            println!("panic on spawn");
            std::process::abort();
        },
    }
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
    pub spec fn view(&self) -> ThreadId;

    /// Guarantees that any two `IsThread` objects on the same thread
    /// will have the same ID.
    #[verifier::external_body]
    pub proof fn agrees(tracked self, tracked other: IsThread)
        ensures
            self@ == other@,
    {
        unimplemented!();
    }
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
#[verifier::external_body]
pub proof fn ghost_thread_id() -> (tracked res: IsThread) {
    unimplemented!();
}

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
    pub spec fn view(&self) -> V;

    pub spec fn id(&self) -> ThreadId;

    /// Recover the inner value provide we are on the same thread.
    #[verifier::external_body]
    pub proof fn into(tracked self, tracked is_thread: IsThread) -> (tracked res: V)
        requires
            self.id() == is_thread@,
        ensures
            res == self@,
    {
        unimplemented!();
    }

    /// Borrow the inner value provide we are on the same thread.
    #[verifier::external_body]
    pub proof fn borrow(tracked &self, tracked is_thread: IsThread) -> (tracked res: &V)
        requires
            self.id() == is_thread@,
        ensures
            *res == self@,
    {
        unimplemented!();
    }
}

impl<V: Send> ThreadShareable<V> {
    /// Recover the inner value.
    /// Unlike `into`, this has no thread requirement, but it does
    /// require the inner type to be `Send`.
    #[verifier::external_body]
    pub proof fn send_into(tracked self) -> (tracked res: V)
        ensures
            res == self@,
    {
        unimplemented!();
    }
}

impl<V: Sync> ThreadShareable<V> {
    /// Borrow the inner value.
    /// Unlike `borrow`, this has no thread requirement, but it does
    /// require the inner type to be `Sync`.
    #[verifier::external_body]
    pub proof fn sync_borrow(tracked &self) -> (tracked res: &V)
        ensures
            *res == self@,
    {
        unimplemented!();
    }
}

} // verus!
