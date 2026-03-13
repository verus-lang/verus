# The `set` strategy

The `set` strategy can be applied to fields of type [`Set<E>`](https://verus-lang.github.io/verus/verusdoc/vstd/set/struct.Set.html) for any types `E`.

```rust
fields {
    #[sharding(set)]
    pub field: Set<E>,
}
```

**Tokens.**
VerusSync creates a fresh token type, <code style="font-style: italic; color: #408040">tok</code>,
named `State::field` where `State` is the name of the VerusSync system and `field` is the name of the field.

The token type <code style="font-style: italic; color: #408040">tok</code> implements the
[`UniqueElementToken<V>`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.UniqueElementToken.html) trait.

For dealing with _collections_ of tokens, VerusSync uses
<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.SetToken.html"><code>SetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a>. It also creates a type alias for this type by appending `_set` to the field name, e.g., `State::field_set`.

**Relationship between global field value and the token.**
Every token represents a _single_ element of the set (given by the `.element()`
function on the [`UniqueElementToken<V>`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.UniqueElementToken.html) trait).
The value of the field on the global state is the set given by the collection of all such elements.

## Manipulation of the field

### Quick Reference

In the following table, `e: E` and `s: Set<E>`.

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
      <td><code>init field = s;</code></td>
      <td><code>init field = s;</code></td>
      <td>Output <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.SetToken.html"><code>SetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a></td>
    </tr> <tr>
      <td><code>remove field -= set { e };</code></td>
      <td><code>require field.contains(e);</code><br><code>update field = field.remove(e);</code></td>
      <td>Input <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>have field &gt;= set { e };</code></td>
      <td><code>require field.contains(e);</code></td>
      <td>Input <code>&amp;<span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>add field += set { e };</code></td>
      <td><code>assert !field.contains(e);</code><br><code>update field = field.insert(e);</code></td>
      <td>Output <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>remove field -= (s);</code></td>
      <td><code style="white-space: pre">require s.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/set/struct.Set.html#method.subset_of">subset_of</a>(field);</code><br>
          <code>update field = field.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/set/struct.Set.html#method.difference">difference</a>(s);</code></td>
      <td>Input <code><a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.SetToken.html">SetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</a></code></td>
    </tr> <tr>
      <td><code>have field &gt;= (s);</code></td>
      <td><code style="white-space: pre">require s.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/set/struct.Set.html#method.subset_of">subset_of</a>(field);</code></td>
      <td>Input <code>&amp;<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.SetToken.html">SetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</a></code></td>
    </tr> <tr>
      <td><code>add field += (s);</code></td>
      <td><code style="white-space: pre">assert field.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/set/struct.Set.html#method.disjoint">disjoint</a>(s);</code><br>
        <code style="white-space: pre">update field = field.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/set/struct.Set.html#method.union">union</a>(s);</code>
      </td>
      <td>Output <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.SetToken.html"><code>SetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a></td>
    </tr>
  </tbody>
</table></div>

### Initializing the field

Initializing the field is done with the usual `init` statement (as it for all strategies).

```rust
init field = s;
```

The instance-init function will return a token `token` of type
<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.SetToken.html"><code>SetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a>, where <code>token.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.SetToken.html#method.set">set()</a> == s</code>.

### Adding a token

To write an operation that _creates_ a token with element `e`,
equivalently, inserting the element `e` into the set, write, inside any `transition!` operation:

```rust
add field += set { e };
```

This operation has an inherent safety condition that `e` is not in the pre-state value of the set.
The resulting token exchange function will return a token of type <code><span style="font-style: italic; color: #408040">tok</span></code>
and with `element()` equal to `e`.

If you require manual proof to prove the inherent safety condition, you can add
an optional `by` clause:

```rust
add field += set { e } by {
    // proof goes here
};
```

### Removing a token

To write an operation that _removes_ a token with element `e`,
equivalently, removing the element `e` from the set, write, inside any `transition!` operation:

```rust
remove field -= set { e };
```

The resulting exchange function will consume a <code><span style="font-style: italic; color: #408040">tok</span></code> token with `element()` equal to `e`.

### Checking the value of the token

To check the element of the token without removing it,
write, inside any `transition!`, `readonly!` or `property!` operation:

```rust
have field >= set { e };
```

The resulting exchange function will accept an immutable reference
<code>&amp;<span style="font-style: italic; color: #408040">tok</span></code> (that is, it takes the token as input but does not consume it).

### Operations that manipulate collections of tokens

You can also write versions of the above operations that operate on sets of tokens
rather than singleton elements.
Such token collections are managed as <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.SetToken.html"><code>SetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a> objects.

The operations below are equivalent to the above versions whenever `s == set![e]`,
and they are all no-ops when `s == set![]`.

To create a <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.SetToken.html"><code>SetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a> where `tok.set() == s`:

```rust
add field += (s);
```

To consume a <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.SetToken.html"><code>SetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a> where `tok.set() == s`:

```rust
remove field -= (s);
```

To check the value of a <code>&amp;<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.SetToken.html">SetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</a></code> where `tok.set() == s`:

```rust
have field >= (s);
```

## Example

TODO
