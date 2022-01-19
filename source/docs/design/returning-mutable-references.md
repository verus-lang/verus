## Support for returning mutable references

This concerns functions that return mutable references (e.g. `fn index_mut(&mut self, idx: usize) -> &mut u64`); it does not yet consider support for borrows without a function call (e.g. `let a = &mut adt.field`).

### Verification conditions for the callers

Similarly to calling functions with an `&mut` parameter, we can treat (a) returning a mutable reference and (b) the borrow expiring as two "moves" of the borrowed value: once (a) out of and once (b) back to the lender (the lender is the `&mut` parameter with the same lifetime as the returned reference). The intuition is to treat the caller's code from the call site to the end of the borrow roughly as if it was a function that takes the mutable reference as an `&mut` parameter. The specification of this ficticious function is provided in an `after<'lifetime>` block in the header of the borrowing function. In other words,

* regular `requires` and `ensures` apply to the function call site, and have the same semantics as for functions that don't return a mutable reference;
* an `after<'lifetime>` block is used to introduce a second pair of `requires`/`ensures` that refer to the point at which the borrow expires: `requires` expresses constraints on the borrowed value before the borrow ends (i.e. before it's returned to its lender), `ensures` is what's true after the end of the borrow. `before(ref)` where `ref` is the reference can be used to refer to the value of the borrowed references just after the call (at the very start of the borrow), whereas `old` has the same meaning as regular `requires`/`ensures`

In its unsugared form, `after` requires an explicit lifetime, to tie it to a specific lifetime being returned by the function. Despite being initially unsupported, a rust function may return multiple mutable references with different lifetimes. We can provide a version of `after` with an implicit lifetime, when only one lifetime is (implicitly or explicitly) declared for the function signature.

```rust
struct Vec<V>

impl<V> View for Vec<V> {
  type View = Seq<V>;
  
  #[spec]
  fn view(&self) -> Seq<V> { .. }
}

impl<V> Vec<V> {
  #[verifier(external_body)]
  pub fn index_mut_increasing<'a>(&'a mut self, idx: usize) -> &'a mut V {
    requires(idx < self.len());
    ensures(|ref: &mut V| *ref == old(self).index(idx));
    after<'a>(|ref: &mut V| {
      requires(*ref > *before(ref)); // what needs to be true of *ref at the end of the borrow
                      // before(ref) is the value of ref at the beginning of the borrow
      ensures([ // after the end of the borrow
        forall(|i: nat| i < self.len() >>= if i != idx {
          self.index(j) == old(self).index(j) // old(self) is the value of self before the call
        } else {
          self.index(j) == *ref // ref is the value of ref at the end of the borrow
        },
        sum(self.view()) > sum(old(self).view()),
      ]);
    });
  }
}
```

The mutably borrowed value (the lender) is treated as "moved" for the duration of the borrow (the borrow-checker would prevent access to it): referencing its value in spec code results in the value before the move (i.e. the call). It is havoc-ed when the borrow ends.

One language design issue is the fact that generally speaking there's no code that directly corresponds to the end of a borrow, as show in Example 3 and Example 4. To start (and in order to avoid having to extract information from the borrow checker), we can require the user to explicitly expire the borrow (with an `expire`/`drop` function), like in Example 4.

Example 1. Correct usage:

```rust
fn caller(v: Vec<u64>, v2: Vec<u64>) {
  requires([sum(v) >= 20, v.len() > 10, v2.len() == v1.len()]);
  #[spec] let v_prev = v;
  let e: &'a mut u64 = v.index_mut_increasing(4);
  e = e + v2.index(4);
  // mutable borrow 'a expires here
  // `v` havoc-ed, and after ensures clause applies
  sort(&'b mut v); // ensures elements are the same
  assert(sum(v) > 20);
  assert(exists(|i: nat| i < v.len() && v.index(i) == v_prev.index(i) + v2.index(4)));
}
```

Example 2. Error, `after` `requires` not satisfied:

```rust
fn caller(v: Vec<u64>, v2: Vec<u64>) {
  requires([sum(v) >= 20, v.len() > 10, v2.len() == v1.len()]);
  #[spec] let v_prev = v;
  let e: &'a mut u64 = v.index_mut_increasing(4);
  // mutable borrow 'a expires here
  // error: requires condition after the expiry of the borrow
  sort(&'b mut v); // ensures elements are the same
  assert(sum(v) >= 20);
  assert(exists(|i: nat| i < v.len() && v.index(i) == v_prev.index(i) + v2.index(4)));
}
```

Example 3. Error, `after` `ensures` only takes hold at the end of the borrow:

```rust
fn caller(v: Vec<u64>, v2: Vec<u64>) {
  requires([sum(v) >= 20, v.len() > 10, v2.len() == v1.len()]);
  #[spec] let v_prev = v;
  let e: &'a mut u64 = v.index_mut_increasing(4);
  e = e + v2.index(4);
  assert(sum(v) > 20); // error: v still has the old value (before the borrow)
                       // emit warning that there's a live mutable borrow?
  // mutable borrow 'a expires here
  sort(&'b mut v); // ensures elements are the same
  assert(exists(|i: nat| i < v.len() && v.index(i) == v_prev.index(i) + v2.index(4)));
}
```

Example 4. Example 3 fixed: explicitly drop the borrowing variable to terminate the borrow:

```rust
fn caller(v: Vec<u64>, v2: Vec<u64>) {
  requires([sum(v) >= 20, v.len() > 10, v2.len() == v1.len()]);
  #[spec] let v_prev = v;
  let e: &'a mut u64 = v.index_mut_increasing(4);
  e = e + v2.index(4);
  expire(e); // force the end of the borrow here
  assert(sum(v) > 20); // now verifies
  sort(&'b mut v); // ensures elements are the same
  assert(exists(|i: nat| i < v.len() && v.index(i) == v_prev.index(i) + v2.index(4)));
}
```

This discussed the general case of a borrow extending for potentially multiple statements. The special case of a single direct assignment to the mutable reference in the same statement as the function call can be handled using the same semantics as described above (but without the need for an explicit `expire`).

Example 5.

```rust
fn caller(v: Vec<u64>, v2: Vec<u64>) {
  requires([sum(v) >= 20, v.len() > 10, v2.len() == v1.len()]);
  let e = *v.index(4);
  #[spec] let v_prev = v;
  *v.index_mut_increasing(4) = e + v2.index(4); // single statement with direct assigment
  assert(sum(v) > 20);
  sort(&'b mut v);
  assert(exists(|i: nat| i < v.len() && v.index(i) == v_prev.index(i) + v2.index(4)));
}
```

Example 6. `Option<&mut>` brought up by @tjhance. A function on a hashtable to optionally obtain a mutable reference to a value, if the key is present:

```rust
impl HashTable<K, V> {
  pub fn borrow_mut<'a>(&'a mut self, key: K) -> Option<&'a mut V> {
    ensures(|ref: &mut V| if self.contains(key) {
      ref.is_some() && ref.value() == old(self).get(key)
    } else {
      equal(*ref, None)
    }));
    after<'a>(|ref: &mut V| {
      ensures([
        // forall(|k: K| equal(self.contains(k), old(self).contains(k)) && (self.contains(k) >>= (
        // 	 self.get(k) == (if k == key { ref.value() } else { old(self).get(k) })
        // ))),
        self.view() == old(self).view().set(key, *ref.value()),
      ])
    })
    
    // ...
  }
}
```

This example depends on implementing `enum` `.is_variant()` and `.field()` , similar to Dafny's `.Variant?` (e.g. `.Some?`) and Dafny's field accessors (for `enum`s).

Example 6b. Caller, without reborrows, but with helper functions on `Option`:

```rust
fn increment(ht: &mut HashTable<u64, i64>, key: u64) {
  requires(ht.contains(key));
  ensures(ht.view() == old(ht).view().set(key, old(ht).view().get(key) + 1),
  let val = ht.borrow_mut(key);
  if val.is_some() {
    val.put(val.value() + 1);
  }
  expire(val);
}
```

Example 6c. Caller, with reborrows

* [ ] do we want to support re-borrows right away? It's more complex, due to the relationship between the returned mutable reference and `val` bound in the match pattern:

```rust
fn increment(ht: &mut HashTable<u64, i64>, key: u64) {
  requires(ht.contains(key));
  ensures(ht.view() == old(ht).view().set(key, old(ht).view().get(key) + 1),
  if let Some(ref mut val) = ht.borrow_mut(key) {
    *val = *val + 1;
  }
}
```

### Verification conditions for the function body

Given a

```rust
struct A {
  m: u64,
  n: u64,
}
```

we can write a function

```rust
impl A {
  pub fn borrow_either(&mut self, which: bool) -> &mut u64 {
    ensures(|ref: &mut u64| *ref == if which { self.m } else { self.n });
    after<'a>(|ref: &mut V| {
      ensures([ // after the end of the borrow
        if which [
          self.m == *ref && self.n == old(self).n
        ] else {
          self.m == old(self).m && self.n == *ref
        }
      ]);
    });

    if which {
      &mut self.m
    } else {
      &mut self.n
    }
  }
}
```

* [ ] only allow directly returning a borrow to avoid the issue of handling pointer variables?

### Open questions

* [ ] allow re-assigning the pointer variable? What to do then? Phrophecy variables a-la RustHorn?