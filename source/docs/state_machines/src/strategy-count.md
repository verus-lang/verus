# The `count` strategy

The `count` strategy can be applied to fields of type `nat`.

```rust
fields {
    #[sharding(count)]
    pub field: nat,
}
```

**Tokens.**
VerusSync creates a fresh token type, <code style="font-style: italic; color: #408040">tok</code>,
named `State::field` where `State` is the name of the VerusSync system and `field` is the name of the field.

The token type <code style="font-style: italic; color: #408040">tok</code> implements the
[`CountToken`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.CountToken.html) trait.
Each token has a `count()` value, and these tokens
"fungible" in the sense that they can be combined and split, numbers
combining additively.

**Relationship between global field value and the token.**
The global value of the `field` is the sum of the counts of all the tokens.

## Manipulation of the field

### Quick Reference

In the following table, `n: nat`.

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
      <td><code>init field = n;</code></td>
      <td><code>init field = n;</code></td>
      <td>Output <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>remove field -= (n);</code></td>
      <td><code>require field >= n;</code><br><code>update field = field - n;</code></td>
      <td>Input <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>have field &gt;= n;</code></td>
      <td><code>require field >= n;</code></td>
      <td>Input <code>&amp;<span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>add field += n;</code></td>
      <td><code>update field = field + n;</code></td>
      <td>Output <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr>
  </tbody>
</table></div>

### Initializing the field

Initializing the field is done with the usual `init` statement (as it for all strategies).

```rust
init field = n;
```

The instance-init function will return a token of type <code><span style="font-style: italic; color: #408040">tok</span></code>
with `count()` equal to `n`.

### Adding a token (increasing the count)

To write an operation that _creates_ a token,
equivalently, adding to the total count, write,

```rust
add field += (n);
```

The resulting token exchange function will return a token of type <code><span style="font-style: italic; color: #408040">tok</span></code>
with `count()` equal to `n`.

### Removing a token

To write an operation that _removes_ a token,
equivalently, decreasing the total count,
updating the field's value from `true` to `false`, write, inside any `transition!`
operation:

```rust
remove field -= (n);
```

The resulting exchange function will consume a <code><span style="font-style: italic; color: #408040">tok</span></code> token
with `count()` equal to `n`
as a parameter.

### Checking the value of the token

To check the value of the token without removing it,
write, inside any `transition!`, `readonly!` or `property!` operation:

```rust
have field >= (n);
```

The resulting exchange function will accept an immutable reference
<code>&amp;<span style="font-style: italic; color: #408040">tok</span></code> (that is, it takes the token as input but does not consume it).

## Example

TODO
