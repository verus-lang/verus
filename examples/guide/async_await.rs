#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use verus_builtin_macros::*;
#[allow(unused_imports)]
use vstd::seq::*;

verus! {

// ANCHOR: basic_async_ensures
async fn add1(x: u64) -> (result: u64)
    requires x < u64::MAX,
    ensures result == x + 1,
{
    x + 1
}
// ANCHOR_END: basic_async_ensures

// ANCHOR: basic_async_caller
async fn async_call(x: u64)
{
    let result = add1(41).await;
    assert(result == 42);
    let future = add1(41);
    // ^ This future has not yet executed, so the following
    // assertion would fail; the value of a future can be obtained
    // via `.view()` or `@`.

    // assert(future@ == 42);
}
// ANCHOR_END: basic_async_caller

// ANCHOR: basic_async_caller_awaited
use vstd::future::FutureAdditionalSpecFns;
async fn async_call2(x: u64)
{
    let future = add1(41);
    assert(future.awaited() ==> future@ == 42);
    future.await;
    assert(future.awaited());
}
// ANCHOR_END: basic_async_caller_awaited

// ANCHOR: async_future_branch
use std::future::Future;
async fn branch_and_await<T>(
    run_first: bool,
    f1: impl Future<Output = T>,
    f2: impl Future<Output = T>,
) -> (result: T)
    ensures
        run_first ==> f1.awaited() && result == f1@,
        !run_first ==> f2.awaited() && result == f2@,
{
    if run_first {
        f1.await
    } else {
        f2.await
    }
}

async fn call_branch() {
    let f1 = add1(22);
    let f2 = add1(41);
    let result = branch_and_await(true, f1, f2).await;
    assert(result == 23 && f1.awaited());
}
// ANCHOR_END: async_future_branch

// ANCHOR: async_mut
async fn mutating_arg(x: &mut usize) -> (result: ())
    requires *old(x) < usize::MAX,
    ensures *x == *old(x) + 1
{
    *x += 1;
}

async fn using_async_mutation() {
    let mut x = 42;
    let f = mutating_arg(&mut x);
    // assert(x == 42); // should fail
    // assert(x == 43); // should fail
    f.await;
    assert(x == 43);
}
// ANCHOR_END: async_mut

}