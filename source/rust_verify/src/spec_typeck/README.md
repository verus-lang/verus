# Type-Checking Ghost code

Normally, the way Rust does type-checking in two passes:

 - **Resolution** - resolves all identifiers and paths,
    so you know what locals or top-level items they point to
 - **Type checking** - infer the type of every expression, resolve trait obligations,
    identify auto-derefs, that kind of thing

For ghost code, we want the results of resolution, but **not** type-checking, in order to tailor
type-checking to the needs of ghost code. (For example, we don't really want auto-derefs,
or Sized bound checking, but we also want to do smarter conversions with int and nat.)

Thus, we run **resolution** on the crate with all the ghost code included, then excise the ghost
code from the tree before running rustc's type-checker. Then we run **our own type-checking pass**
on ghost code, which is what this module is devoted to.

### The results of resolution

The main thing we get from resolution is a [`rustc_hir::QPath`](https://doc.rust-lang.org/1.76.0/nightly-rustc/rustc_hir/enum.QPath.html), which looks like this:

```rust
pub enum QPath<'hir> {
    Resolved(Option<&'hir Ty<'hir>>, &'hir Path<'hir>),
    TypeRelative(&'hir Ty<'hir>, &'hir PathSegment<'hir>),
    LangItem(LangItem, Span),
}
```

Having a `QPath::Resolve` is the ideal case, since it gives a direct link to the relevant
local variable or a top-level item (via `DefId`).

The `QPath::TypeRelative` is a more complicated case, as this means we need to do type-directed
lookup. For example if you have `SomeType::foo` we have to look for an ImplItem called `foo`
in all the impls of type `SomeType`. Of course, `SomeType` in the source-code might be
given in a non-normalized form, requiring us to resolve projection types in order to find `foo`.

An even more complicated case is method lookup, as in `something.foo()`. Again, this is
type-directed lookup depending on the type of the receiver `something`. However, this can
_also_ resolve to trait methods, so it depends on the trait bounds that are in scope for
`something`.

## Components of `spec_typeck`

### High level structure

The main type-checking pass traverses the entire expression (`check_expr`),
creating type inference variables where necessary and acculumating constraints.
The constraints are solved via unification (`unifier.rs`).
The output of `check_expr` is a VIR `Expr` whose types may include inference variables.

Then (if we successfully resolve all inference vars), we "finalize" the expression
(`finalize_expr.rs`) by replacing all inference vars with their concrete, resolved forms.
We also run some additional checks, including all the trait obligations at this point.

### The `check_expr` pass

This is the good part, the part we _want_ to write, where we can decide on the rules
for how `+` and `*` typecheck as so forth. Type constraints can be added by calling
`self.expect_exact` or `self.expect_allowing_coercion` (the latter allows auto-casting to `int`).

To handle a call, we either instantiate the generic type ares the types provided by the
user or we create type inference vars to instantiate the generic type args.
For example, if `foo` takes one generic arg then:

 * If the user writes `foo::<SomeType>(x)` instantiate the arg with `SomeType`
 * If the user writes `foo::<Pair<_, _>>(x)` then we create 2 inference vars `?1` and `?2`
    and instantiate the arg with `Pair<?1, ?2>`.
 * if the user write `foo(x)` or equivalently `foo::<_>(x)` then we instantiate one inference var.

Types are translated in `check_ty.rs`.

### Handling paths, type-directed lookup, method calls

The `QPath` type described above is handled in `check_path.rs`.
Again, the ideal case is that we have a `QPath::Resolved`, which already gives us the `DefId`.
In that case, all we have to do is instantiate the generic args as described above
(though this is still a little complicated because these args are spread out across the
`PathSegments`).

For type-directed lookup (`TypeRelative` paths and `MethodCall` expressions),
we fork code from rustc, specifically we fork `probe.rs`:
<https://doc.rust-lang.org/1.79.0/nightly-rustc/src/rustc_hir_typeck/method/probe.rs.html>.
This is a private module in `rustc_typeck`, about 2000 lines. We modify it slightly to not rely on
the rest of `rustc_typeck`. The forked version is in `method_probe.rs`.
This module doesn't include the complex code
for offering suggestions when the given item isn't found.

The module does include code for the fairly complex auto-deref procedure; however, I think
this can be removed as it isn't useful in spec code. (In principle, we could implement
auto-_view_ as has been discussed aspirationally before.)

In order to call into `method_probe.rs`, we have to map our VIR types back to rustc types
(see `reverse_type_map.rs`). The result of a method probe is a `DefId` which lets us move on.
If resolution doesn't succeed, then we error.

Though hackish, this approach mostly seems to "just work".

### Trait obligations

Rustc exports nice public interfaces for its trait-solving machinery, so this part is pretty easy
(once all types have been inferred). In `finalize_expr.rs` we establish trait obligations for all
the method calls and try to resolve them, and we can get rust's nice looking error messages this way as well.

### Unification, normalization, projection types

Without projection types, unification is fairly straightforward: create inference vars
in a union-find data structure, map each var to either 'known' or 'unknown', and write
a recursive `unify` procedure.

With projection types, things become more complicated. We usually want to reduce
projection types as much as possible, for type-directed lookup or other type-based decisions,
but projection types might be blocked on inference. Thus the unification table
needs to support non-normalized projection types, and it needs to smartly make progress on them.
(TODO The "making smart progress" part isn't implemented right now.)

Finally, we need to handle the actual reduction operation.
Unfortunately, this is only easy to do with rust's machinery *when there are no unsolve inference variables*.
By contrast, if there _are_ inference variables, then rustc's `normalize` procedure will
end up doing complicated things in the rustc `InferCtxt` internal state, which is not great for us.

To implement reduction, we can use the rustc `SelectionCtxt` to look for the right trait impl.
Once we have the right trait impl, we can instantiate inference variables for the impl type
args and do substitution on the associated type item (all very similar to what we do
for function calls). See `reduce_projection.rs`.

### Handling integers

The unification table supports an `UnknownInteger` type which we can use for integer literals.
If, at the end of inference, there are any `UnknownInteger` types that
haven't been concretized to a specific integer type, we defaults to `int`.

# Alternatives

There are at least 2 kinda awkward things we might consider changing.

**Type representations**
Type inference is mostly done with VIR Typs, which I chose because I figured it would
make it easier to write Verus-specific type checking logic. However, this does
mean we need to a "reverse map" whenever we call into Rustc machinery.
An alternative might be to do all the type-checking with rustc_middle::ty::Ty and then
lower to VIR Typs at the end.

**Rolling our own type inference**

Rustc obviously has a lot of machinery for doing type inference, mostly found in its
`InferCtxt` object. We create a few of these contexts when we need to call rustc stuff, 
but we never use them "properly", i.e., we never actually use its unification procedures
or do anything complicated with InferTy values.
An alternative would be to use the `InferCtxt` "properly" and actually use it for
unification and normalization.

I made this choice because I thought relying on rustc's InferCtxt too deeply would be a bad
idea because it's probably very unstable and would make maintenance difficult. On the other hand,
it's probably highly well-tuned for corner cases like cycle checking and everything.
So this question really comes down to: do we want to maintain compatability with some evolving APIs
(more than we already are) or do we want to maintain our own unifiers and normalizers?

# Benefits

Writing our own ghost-code type checkers unlock a number of useful possibilities:

 * Auto-Coercing integer types to `nat` or `int`
 * Automatically typing a spec function as `fn_spec(...) -> _`
 * Better inference for arguments to a spec closure
 * No unnecessary `Sized` trait bounds
 * Recursive Spec-mode ADTs without `Box`
 * Better diagnostics and suggestions specific to spec/proof code
