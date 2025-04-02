# The `persistent_bool` strategy

The `persistent_bool` strategy can be applied to fields of type `bool`.

```rust
fields {
    #[sharding(bool)]
    pub field: bool,
}
```

**Tokens.**
VerusSync creates a fresh token type, <code style="font-style: italic; color: #408040">tok</code>,
named `State::field` where `State` is the name of the VerusSync system and `field` is the name of the field.

The token type <code style="font-style: italic; color: #408040">tok</code> implements the
[`SimpleToken<V>`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.SimpleToken.html) trait.

**Relationship between global field value and the token.**
When `field` is `false`, this corresponds to no token existing, while
when `field` is `true`, this corresponds to at least one token existing.
The token doesn't contain any additional data.
Having multiple such tokens at the same time is an impossible state.

Since the tokens are `Copy`, there can be any number of such tokens for any given key.

## Manipulation of the field

### Quick Reference

In the following table, `b: bool`.

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
      <td><code>init field = b;</code></td>
      <td><code>init field = b;</code></td>
      <td>Output <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code></td>
    </tr> <tr>
      <td><code>have field &gt;= true;</code></td>
      <td><code>require field == true;</code></td>
      <td>Input <code>&amp;<span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>add field (union)= true;</code></td>
      <td><code>update field = true;</code></td>
      <td>Output <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>have field &gt;= (b);</code></td>
      <td><code>require b ==> field;</code></td>
      <td>Input <code>&amp;Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code></td>
    </tr> <tr>
      <td><code>add field (union)= (b);</code></td>
      <td><code>update field = field || b;</code></td>
      <td>Output <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code></td>
    </tr>
  </tbody>
</table></div>

### Initializing the field

Initializing the field is done with the usual `init` statement (as it for all strategies).

```rust
init field = b;
```

The instance-init function will return a token of type <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>,
related as follows:

<table>
  <tr>
    <th>value of <code>b: bool</code></th>
    <th>&nbsp;&nbsp;&nbsp;value of optional token <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>></code></th>
  </tr>
  <tr>
    <td><code>false</code></td>
    <td><code>None</code></td>
  </tr>
  <tr>
    <td><code>true</code></td>
    <td><code>Some(tok)</code></td>
  </tr>
</table>

### Adding a token

To write an operation that _creates_ a token,
write, inside any `transition!` operation:

```rust
add field (union)= true;
```

The resulting token exchange function will return a token of type <code><span style="font-style: italic; color: #408040">tok</span></code>
and with value `v`.

In other words, you can create a token at any time, regardless of the current value of the field.
The only requirement is that (as always) the invariants of the system must be preserved.

### Observing that the token exists

To observe that the token exists,
write, inside any `transition!`, `readonly!` or `property!` operation:

```rust
have field >= true;
```

The resulting exchange function will accept an immutable reference
<code>&amp;<span style="font-style: italic; color: #408040">tok</span></code> (that is, it takes the token as input but does not consume it).

### Operations that manipulate optional tokens

You can also write versions of the above operations that operate on optional tokens.
The operations below are equivalent to the above versions whenever `opt_v == Some(v)`,
and they are all no-ops when `opt_v == None`.

To create an <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>:

```rust
add field (union)= (b);
```

To observe the token <code>&amp;Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>:

```rust
have field >= (b);
```

The value of `b` is related to the value of
<code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>
as [they are for initialization](#initializing-the-field).

## Example

TODO
