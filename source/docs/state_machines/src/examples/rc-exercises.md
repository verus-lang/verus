# Exerises

 1. Implement a thread-safe reference-counted pointer, `Arc`.
    The `Arc<T>` typed should satisfy the `Send` and `Sync` marker traits.

    Answer the following:

      (a) In terms of _executable_ code, which part of `Rc` is not thread-safe?
          How does it need to change?

      (b) In terms of _ghost_ code, which component prevents `Rc` from satisfying
         `Send` or `Sync`? What should it be changed to to support `Send` and `Sync`?

      (c) In order to make change (b), it is necessary to also make change (a).  Why?

 2. Augment the verified `Rc` to allow weak pointers.
    The allocation should include 2 counts: a strong reference count (as before)
    and a weak reference count. The inner `T` is dropped when the strong reference
    count hits 0, but the memory is not freed until both counts hit 0.
    Upgrading a weak pointer should fail in the case that the strong count has already hit 0.

    Implement the above and verify a spec like the following:

```rust
type Rc<T>
type Weak<T>

impl<T> Rc<T> {
    pub spec fn view(&self) -> T;

    pub fn new(t: T) -> (rc: Self)
        ensures rc@ === t

    pub fn clone(&self) -> (rc: Self)
        ensures rc@ === self@

    pub fn drop(self)

    pub fn borrow(&self) -> (t: &T)
        ensures *t === self@

    pub fn downgrade(&self) -> (weak: Weak<T>)
        ensures weak@ === self@
}

impl<T> Weak<T> {
    pub spec fn view(&self) -> T;

    pub fn clone(&self) -> (weak: Self)
        ensures weak@ === self@

    pub fn drop(self)

    pub fn upgrade(&self) -> (rc_opt: Option<Rc<T>>)
        ensures match rc_opt {
            None => true,
            Some(rc) => rc@ === self@,
        }
}
```
