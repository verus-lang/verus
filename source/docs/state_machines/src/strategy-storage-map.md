# The `storage_map` strategy

The `storage_map` strategy can be applied to fields of type <code><a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html">Map&lt;K, <span style="font-style: italic; color: #c08080">Tok</span>&gt;</a></code>
for any types `K` and <code><span style="font-style: italic; color: #c08080">Tok</span></code>.

```rust
fields {
    #[sharding(storage_map)]
    pub field: Map<K, Tok>,
}
```

**Tokens.**
Usually <code><span style="font-style: italic; color: #c08080">Tok</span></code> is itself some "token" type intended for tracked
contexts---e.g., the token created by a different VerusSync system
(or even the same VerusSync system, as recursive types _are_ permitted),
a [`PointsTo`](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/struct.PointsTo.html),
or a datatype/tuple combining multiple of these.

VerusSync does not create any _additional_ tokens for the field.

**Relationship between global field value and the token.**
When a field is declared `storage_map`, the VerusSync gains the ability to "store"
tokens of the given type <code><span style="font-style: italic; color: #c08080">Tok</span></code>. Multiple such tokens can be stored,
and they are indexed by keys of type `K`.

For example, if the field has value `[1 => tok1, 4 => tok2]`, then that means `tok1` and `tok2` are stored.

## Manipulation of the field

### Quick Reference

In the following table, `k: K`, <code>tok: <span style="font-style: italic; color: #c08080">Tok</span></code>, and <code>map_toks: <a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html">Map&lt;K, <span style="font-style: italic; color: #c08080">Tok</span>&gt;</a></code>.

<div class="table-wrapper" style="font-size: 13px"><table>
  <colgroup>
     <col span="1" style="width: 40%;">
     <col span="1" style="width: 45%;">
     <col span="1" style="width: 15%;">
  </colgroup>
  <thead>
    <tr>
      <th>Command</th>
      <th>Meaning in transition</th>
      <th>Exchange Fn Parameter</th>
    </tr>
  </thead>
  <tbody>
    <tr><td></td><td></td><td></td></tr>
    <tr>
      <td><code>init field = map_toks;</code></td>
      <td><code>init field = map_toks;</code></td>
      <td>Input <code><a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html">Map&lt;K, <span style="font-style: italic; color: #c08080">Tok</span>&gt;</a></code></td>
    </tr> <tr>
      <td><code>deposit field += [ k => tok ];</code></td>
      <td><code>assert !field.dom().contains(k);</code><br><code>update field = field.insert(k, tok);</code></td>
      <td>Input <code><span style="font-style: italic; color: #c08080">Tok</span></code></td>
    </tr> <tr>
      <td><code>guard field &gt;= [ k => tok ];</code></td>
      <td><code>assert field.dom().contains(k) && field[k] == tok;</code></td>
      <td>Output <code>&amp;<span style="font-style: italic; color: #c08080">Tok</span></code></td>
    </tr> <tr>
      <td><code>withdraw field -= [ k => tok ];</code></td>
      <td><code>assert field.dom().contains(k) && field[k] == tok;</code><br><code>update field = field.remove(k);</code></td>
      <td>Output <code><span style="font-style: italic; color: #c08080">Tok</span></code></td>
    </tr> <tr>
      <td><code>deposit field += map_toks;</code></td>
      <td><code style="white-space: pre">assert field.dom().<a href="https://verus-lang.github.io/verus/verusdoc/vstd/set/struct.Set.html#method.disjoint">disjoint</a>(map_toks.dom());</code><br>
        <code style="white-space: pre">update field = field.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.union_prefer_right">union_prefer_right</a>(map_toks);</code>
      </td>
      <td>Input <code><a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html">Map&lt;K, <span style="font-style: italic; color: #c08080">Tok</span>&gt;</a></code></td>
    </tr> <tr>
      <td><code>guard field &gt;= map_toks;</code></td>
      <td><code style="white-space: pre">assert map_toks.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.submap_of">submap_of</a>(field);</code></td>
      <td>Output <code>&amp;<a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html">Map&lt;K, <span style="font-style: italic; color: #c08080">Tok</span>&gt;</a></code></td>
    </tr> <tr>
      <td><code>withdraw field -= map_toks;</code></td>
      <td><code style="white-space: pre">assert map_toks.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.submap_of">submap_of</a>(field);</code><br>
          <code>update field = field.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.remove_keys">remove_keys</a>(map_toks.dom());</code></td>
      <td>Output <code><a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html">Map&lt;K, <span style="font-style: italic; color: #c08080">Tok</span>&gt;</a></code></td>
    </tr>
  </tbody>
</table></div>

### Initializing the field

Initializing the field is done with the usual `init` statement (as it for all strategies).

```rust
init field = map_toks;
```

The instance-init function will take _as input_ a token of type <code><a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html">Map&lt;K, <span style="font-style: italic; color: #c08080">Tok</span>&gt;</a></code>,
equal to the value of `map_toks`.

### Performing a deposit

To deposit a token <code>tok: <span style="font-style: italic; color: #c08080">Tok</span></code>, use the `deposit` statement in any `transition!` operation:

```
deposit field += [ k => tok ];
```

This sets the map value at key `k` to `tok`. The resulting token operation then takes a token equal to `tok` as input.

The `deposit` instruction has an inherent safety condition that key is not already present in the pre-state. (Note: this is not strictly necessary, and the restriction may be removed later.)

If you require manual proof to prove the inherent safety condition, you can add
an optional `by` clause:

```rust
deposit field += [ k => tok ];
by {
    // proof goes here
};
```

### Performing a withdraw

To withdraw a token <code>tok: <span style="font-style: italic; color: #c08080">Tok</span></code>, use the `withdraw` statement in any `transition!` operation:

```
withdraw field -= [ k => tok ];
```

This sets the field value to `None`. The resulting token operation then returns a token
equal to `tok` in its output.

The `withdraw` instruction has an inherent safety condition that `field` contains the key-value pair `k`, `tok` in the pre-state.

**Manual proofs.** If you require manual proof to prove the inherent safety condition, you can add
an optional `by` clause:

```rust
withdraw field -= [ k => tok ];
by {
    // proof goes here
};
```

**Using patterns.** Instead of specifying `tok` as an exact expression, you can also pattern-match
by using the `let` keyword.

```
withdraw field -= [ k => let $pat ];
```

In this case, the inherent safety condition is that the `field` map contains the key `k` and that
the corresponding value matches `$pat`. In this case, note that the value matched on `$pat` is
_not_ deterministic in the input arguments of the token operation. Therefore,
VerusSync considers any variables bound in `$pat` to implicitly be [`birds_eye`](./birds_eye.md)
binders. Specifically, the pattern-matching variant is equivalent to:

```
birds_eye let stored_value = pre.field[k];
withdraw field -= [ k => stored_value ];
birds_eye let $pat = stored_value;
```

### Performing a guard (obtaining a shared reference to the stored object)

To guard a token <code>tok: <span style="font-style: italic; color: #c08080">Tok</span></code>, use the `guard` statement in any `property!` operation:

```
guard field >= [ k => tok ];
```

The resulting token operation then returns a _shared reference_ to the token
equal to `tok` in its output. The shared reference has a lifetime bounded by the lifetimes
of the input references.

The `guard` instruction has an inherent safety condition that `field` contains the key-value pair `k`, `tok` in the pre-state.

**Manual proofs.** If you require manual proof to prove the inherent safety condition, you can add
an optional `by` clause:

```rust
guard field >= [ k => tok ];
by {
    // proof goes here
};
```

### Operations that manipulate collections of tokens

You can also write versions of the above operations that operate on optional tokens.
The operations below are equivalent to the above versions whenever `map_toks == [ k => tok ]`,
and they are all no-ops when `map_toks == map![]`.

To deposit an <code><a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html">Map&lt;K, <span style="font-style: italic; color: #c08080">Tok</span>&gt;</a></code>:

```rust
deposit field += (map_toks);
```

To withdraw an <code><a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html">Map&lt;K, <span style="font-style: italic; color: #c08080">Tok</span>&gt;</a></code>:

```rust
remove field -= (map_toks);
```

To obtain an <code>&amp;<a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html">Map&lt;K, <span style="font-style: italic; color: #c08080">Tok</span>&gt;</a></code>:

```rust
guard field >= (map_toks);
```

## Example

TODO
