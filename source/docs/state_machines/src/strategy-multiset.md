# The `multiset` strategy

The `multiset` strategy can be applied to fields of type [`Multiset<E>`](https://verus-lang.github.io/verus/verusdoc/vstd/multiset/struct.Multiset.html) for any types `E`.

```rust
fields {
    #[sharding(multiset)]
    pub field: Multiset<E>,
}
```

**Tokens.**
VerusSync creates a fresh token type, <code style="font-style: italic; color: #408040">tok</code>,
named `State::field` where `State` is the name of the VerusSync system and `field` is the name of the field.

The token type <code style="font-style: italic; color: #408040">tok</code> implements the
[`UniqueElementToken<V>`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.UniqueElementToken.html) trait.

For dealing with _collections_ of tokens, VerusSync uses
<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MultisetToken.html"><code>MultisetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a>. It also creates a type alias for this type by appending `_set` to the field name, e.g., `State::field_set`.

**Relationship between global field value and the token.**
Every token represents a _single_ element of the multiset (given by the `.element()`
function on the [`UniqueElementToken<V>`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.UniqueElementToken.html) trait).
The value of the field on the global state is the multiset given by the collection of all such elements.

## Manipulation of the field

### Quick Reference

In the following table, `e: E` and `m: Multiset<E>`.

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
      <td>Output <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MultisetToken.html"><code>MultisetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a></td>
    </tr> <tr>
      <td><code>remove field -= { e };</code></td>
      <td><code>require field.contains(e);</code><br><code>update field = field.remove(e);</code></td>
      <td>Input <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>have field &gt;= { e };</code></td>
      <td><code>require field.contains(e);</code></td>
      <td>Input <code>&amp;<span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>add field += { e };</code></td>
      <td><code>update field = field.insert(e);</code></td>
      <td>Output <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>remove field -= (m);</code></td>
      <td><code style="white-space: pre">require m.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/multiset/struct.Multiset.html#method.subset_of">subset_of</a>(field);</code><br>
          <code>update field = field.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/multiset/struct.Multiset.html#method.difference_with">difference_with</a>(m);</code></td>
      <td>Input <code><a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MultisetToken.html">MultisetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</a></code></td>
    </tr> <tr>
      <td><code>have field &gt;= (m);</code></td>
      <td><code style="white-space: pre">require m.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/multiset/struct.Multiset.html#method.subset_of">subset_of</a>(field);</code></td>
      <td>Input <code>&amp;<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MultisetToken.html">MultisetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</a></code></td>
    </tr> <tr>
      <td><code>add field += (m);</code></td>
      <td><code style="white-space: pre">update field = field.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/multiset/struct.Multiset.html#method.add">add</a>(m);</code>
      </td>
      <td>Output <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MultisetToken.html"><code>MultisetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a></td>
    </tr>
  </tbody>
</table></div>

### Initializing the field

Initializing the field is done with the usual `init` statement (as it for all strategies).

```rust
init field = m;
```

The instance-init function will return a token `token` of type
<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MultisetToken.html"><code>MultisetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a>, where <code>token.<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MultisetToken.html#method.multiset">multiset()</a> == m</code>.

### Adding a token

To write an operation that _creates_ a token with element `e`,
equivalently, inserting the element `e` into the multiset, write, inside any `transition!` operation:

```rust
add field += { e };
```

This operation has an inherent safety condition that `e` is not in the pre-state value of the multiset.
The resulting token exchange function will return a token of type <code><span style="font-style: italic; color: #408040">tok</span></code>
and with `element()` equal to `e`.

If you require manual proof to prove the inherent safety condition, you can add
an optional `by` clause:

```rust
add field += { e } by {
    // proof goes here
};
```

### Removing a token

To write an operation that _removes_ a token with element `e`,
equivalently, removing the element `e` from the multiset, write, inside any `transition!` operation:

```rust
remove field -= { e };
```

The resulting exchange function will consume a <code><span style="font-style: italic; color: #408040">tok</span></code> token with `element()` equal to `e`.

### Checking the value of the token

To check the element of the token without removing it,
write, inside any `transition!`, `readonly!` or `property!` operation:

```rust
have field >= { e };
```

The resulting exchange function will accept an immutable reference
<code>&amp;<span style="font-style: italic; color: #408040">tok</span></code> (that is, it takes the token as input but does not consume it).

### Operations that manipulate collections of tokens

You can also write versions of the above operations that operate on variable-sized collections of tokens
rather than singleton elements.
Such token collections are managed as <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MultisetToken.html"><code>MultisetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a> objects.

The operations below are equivalent to the above versions whenever `m == multiset![e]`,
and they are all no-ops when `m == multiset![]`.

To create a <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MultisetToken.html"><code>MultisetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a> where `tok.multiset() == m`:

```rust
add field += (m);
```

To consume a <a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MultisetToken.html"><code>MultisetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</code></a> where `tok.multiset() == m`:

```rust
remove field -= (m);
```

To check the value of a <code>&amp;<a href="https://verus-lang.github.io/verus/verusdoc/vstd/tokens/struct.MultisetToken.html">MultisetToken&lt;K, V, <span style="font-style: italic; color: #408040">tok</span>&gt;</a></code> where `tok.multiset() == m`:

```rust
have field >= (m);
```

## Example

TODO
