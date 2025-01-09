# The `map` strategy

The `map` strategy can be applied to fields of type [`Map<K, V>`](https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html) for any types `K` and `V`.

```rust
fields {
    #[sharding(map)]
    pub field: Map<K, V>,
}
```

**Tokens.**
VerusSync creates a fresh token type, <code style="font-style: italic; color: #408040">tok</code>,
named `State::field` where `State` is the name of the VerusSync system and `field` is the name of the field.

The token type <code style="font-style: italic; color: #408040">tok</code> implements the
[`UniqueKeyValueToken<V>`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.UniqueKeyValueToken.html) trait.

For dealing with _collections_ of tokens, VerusSync uses
<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html"><code>MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a>. It also creates a type alias for this type by appending `_map` to the field name, e.g., `State::field_map`.

**Relationship between global field value and the token.**
Every token represents a _single_ key-value pair (given by the `.key()` and `.value()`
functions on the [`UniqueKeyValueToken<V>`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.UniqueKeyValueToken.html) trait).
The value of the field on the global state is the map given by the collection of key-value pairs.

## Manipulation of the field

### Quick Reference

In the following table, `k: K`, `v: v`, and `m: Map<K, V>`.

<div class="table-wrapper" style="font-size: 13px"><table>
  <colgroup>
     <col span="1" style="width: 35%;">
     <col span="1" style="width: 40%;">
     <col span="1" style="width: 25%;">
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
      <td><code>init field = m;</code></td>
      <td><code>init field = m;</code></td>
      <td>Output <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html"><code>MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a></td>
    </tr> <tr>
      <td><code>remove field -= [k => v];</code></td>
      <td><code>require field.dom().contains(k) && field[k] == v;</code><br><code>update field = field.remove(k);</code></td>
      <td>Input <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>have field &gt;= [k => v];</code></td>
      <td><code>require field.dom().contains(k) && field[k] == v;</code></td>
      <td>Input <code>&amp;<span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>add field += [k => v];</code></td>
      <td><code>assert !field.dom().contains(k);</code><br><code>update field = field.insert(k, v);</code></td>
      <td>Output <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>remove field -= (m);</code></td>
      <td><code style="white-space: pre">require m.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.submap_of">submap_of</a>(field);</code><br>
          <code>update field = field.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.remove_keys">remove_keys</a>(m.dom());</code></td>
      <td>Input <code><a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html">MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a></code></td>
    </tr> <tr>
      <td><code>have field &gt;= (m);</code></td>
      <td><code style="white-space: pre">require m.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.submap_of">submap_of</a>(field);</code></td>
      <td>Input <code>&amp;<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html">MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a></code></td>
    </tr> <tr>
      <td><code>add field += (m);</code></td>
      <td><code style="white-space: pre">assert field.dom().<a href="https://verus-lang.github.io/verus/verusdoc/vstd/set/struct.Set.html#method.disjoint">disjoint</a>(m.dom());</code><br>
        <code style="white-space: pre">update field = field.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.union_prefer_right">union_prefer_right</a>(m);</code>
      </td>
      <td>Output <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html"><code>MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a></td>
    </tr>
  </tbody>
</table></div>

### Initializing the field

Initializing the field is done with the usual `init` statement (as it for all strategies).

```rust
init field = m;
```

The instance-init function will return a token `token` of type
<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html"><code>MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a>, where <code>token.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html#method.map">map()</a> == m</code>.

### Adding a token

To write an operation that _creates_ a token with key-value pair `k, v`,
equivalently, inserting the pair `k, v` into the map, write, inside any `transition!` operation:

```rust
add field += [k => v];
```

This operation has an inherent safety condition that `k` is not in the domain of the pre-state value of the map.
The resulting token exchange function will return a token of type <code><span style="font-style: italic; color: #408040">tok</span></code>
and with `key()` equal to `k` and `value()` equal to `v`.

If you require manual proof to prove the inherent safety condition, you can add
an optional `by` clause:

```rust
add field += [k => v]
by {
    // proof goes here
};
```

### Removing a token

To write an operation that _removes_ a token with key-value pair `k, v`,
equivalently, removing the pair `k, v` from the map, write, inside any `transition!` operation:

```rust
remove field -= [k => v];
```

The resulting exchange function will consume a <code><span style="font-style: italic; color: #408040">tok</span></code> token with `key()` equal to `k` and `value()` equal to `v`.

Instead of specifying `v` as an exact expression, you can also pattern-match
by using the `let` keyword.

```rust
remove field -= [k => let $pat];
```

This will require the prior value of `field[k]` to match `$pat`,
and this statement binds all the variables in `$pat` for use later in the transition.

### Checking the value of the token

To check the key and value of the token without removing it,
write, inside any `transition!`, `readonly!` or `property!` operation:

```rust
have field >= [k => v];
```

The resulting exchange function will accept an immutable reference
<code>&amp;<span style="font-style: italic; color: #408040">tok</span></code> (that is, it takes the token as input but does not consume it).

Instead of specifying `v` as an exact expression, you can also pattern-match
by using the `let` keyword.

```rust
have field >= [k => let $pat];
```

This will require the prior value of `field` to match `$pat`,
and this statement binds all the variables in `$pat` for use later in the transition.

### Updating a token

To update the value of a `map` token, first `remove` it, then `add` it,
in sequence.

```rust
remove field -= [k => let _];
add field += [k => v];
```

### Operations that manipulate collections of tokens

You can also write versions of the above operations that operate on variable-sized collections of tokens
rather than singleton key-value pairs.
Such token collections are managed as <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html"><code>MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a> objects.

The operations below are equivalent to the above versions whenever `m == map![k => v]`,
and they are all no-ops when `m == map![]`.

To create a <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html"><code>MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a> where `tok.map() == m`:

```rust
add field += (m);
```

To consume a <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html"><code>MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a> where `tok.map() == m`:

```rust
remove field -= (m);
```

To check the value of a <code>&amp;<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html">MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</a></code> where `tok.map() == m`:

```rust
have field >= (m);
```

## Example

TODO
