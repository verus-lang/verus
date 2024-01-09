# Static items

Verus supports static items, similar to `const` items. Unlike `const` items, though,
`static` items are only usable in `exec` mode. Note that this requires them to be
_explicitly_ marked as `exec`:

```
exec static x: u64 = 0;
```

The reason for this is consistency with `const`; for `const` items, the default mode
for an unmarked const item is the [dual `spec`-`exec` mode](./const.md).
However, this mode is not supported for `static` items; therefore, static items
need to be explicitly marked `exec`.

Note there are some **limitations** to the current support for `static` items.
Currently, a static item cannot be referenced from a spec expression. This means, for example,
that you can't prove that two uses of the same static item give the same value
if those uses are in different functions. We expect this limitation will be lifted
in the future.
