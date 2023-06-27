# Spec Closures

Verus supports anonymous funcitons in ghost code.

In the examples for `Set` in the [specification libraries](spec_lib.md):
```
proof fn test_seq2() {
    let s: Seq<int> = Seq::new(5, |i: int| 10 * i);
    assert(s.len() == 5);
    assert(s[2] == 20);
    assert(s[3] == 30);
}
```
Since ghost code can only contain ghost code, the closure `|i: int| 10 * i` passed into `Seq::new` is a spec closures, which has type `FnSpec(int -> bool)`. You can declare these closures as normal rust Code.

Spec Closures have the [same restrictions](modes.md) as normal sepc functions.

## FnSpec is a type

It is worth noticing that `FnSpec` is not a trait as Rust does for `Fn`. Therefore, ghost code can return a spec closure without [a lot of trouble](https://doc.rust-lang.org/book/ch19-05-advanced-functions-and-closures.html#:~:text=clearer%20to%20you.-,Returning%20Closures,return%20value%20of%20the%20function.).


<!--https://github.com/verus-lang/verus/wiki/Status%3A-currently-supported-Rust-features>

<!--https://github.com/verus-lang/verus/blob/main/CONTRIBUTING.md>