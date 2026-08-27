# The `persistent_map` strategy

The `persistent_map` strategy can be applied to fields of type [`Map<K, V>`](https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html) for any types `K` and `V`.

```rust
fields {
    #[sharding(persistent_map)]
    pub field: Map<K, V>,
}
```

**Tokens.**
VerusSync creates a fresh token type, <code style="font-style: italic; color: #408040">tok</code>,
named `State::field` where `State` is the name of the VerusSync system and `field` is the name of the field.

The token type <code style="font-style: italic; color: #408040">tok</code> implements the
[`KeyValueToken<V>`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.KeyValueToken.html) trait.

For dealing with _collections_ of tokens, VerusSync uses
<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html"><code>MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a>. It also creates a type alias for this type by appending `_map` to the field name, e.g., `State::field_map`.

**Relationship between global field value and the token.**
Every token represents a _single_ key-value pair (given by the `.key()` and `.value()`
functions on the [`KeyValueToken<V>`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.KeyValueToken.html) trait).
The value of the field on the global state is the map given by the collection of key-value pairs.
Since the tokens are `Copy`, there can be any number of such tokens for any given key.

Of course, all such tokens for the same key will agree on the value as well.
Once a key is set to a given value, this cannot be changed or removed.

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
      <td><code>have field &gt;= [k => v];</code></td>
      <td><code>require field.dom().contains(k) && field[k] == v;</code></td>
      <td>Input <code>&amp;<span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>add field (union)= [k => v];</code></td>
      <td><code>assert field.dom().contains(k) ==> field[k] == v;</code><br><code>update field = field.insert(k, v);</code></td>
      <td>Output <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>have field &gt;= (m);</code></td>
      <td><code style="white-space: pre">require m.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.submap_of">submap_of</a>(field);</code></td>
      <td>Input <code>&amp;<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html">MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</a></code></td>
    </tr> <tr>
      <td><code>add field (union)= (m);</code></td>
      <td><code style="white-space: pre">assert field.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.agrees">agrees</a>(m);</code><br>
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
write, inside any `transition!` operation:

```rust
add field (union)= [k => v];
```

This operation has an inherent safety condition that, _if_ `k` is in the domain of the pre-state value of the map, then it has the same value `v`.
The resulting token exchange function will return a token of type <code><span style="font-style: italic; color: #408040">tok</span></code>
and with `key()` equal to `k` and `value()` equal to `v`.

If you require manual proof to prove the inherent safety condition, you can add
an optional `by` clause:

```rust
add field (union)= [k => v]
by {
    // proof goes here
};
```

### Checking the value of the token

To check the key and value of the token,
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

### Operations that manipulate collections of tokens

You can also write versions of the above operations that operate on variable-sized collections of tokens
rather than singleton key-value pairs.
Such token collections are managed as <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html"><code>MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a> objects.

The operations below are equivalent to the above versions whenever `m == map![k => v]`,
and they are all no-ops when `m == map![]`.

To create a <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html"><code>MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a> where `tok.map() == m`:

```rust
add field (union)= (m);
```

To check the value of a <code>&amp;<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MapToken.html">MapToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</a></code> where `tok.map() == m`:

```rust
have field >= (m);
```

## Example

TODO
