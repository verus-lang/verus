# The `bool` strategy

The `bool` strategy can be applied to fields of type `bool`.

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
[`UniqueSimpleToken`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.UniqueSimpleToken.html) trait.

**Relationship between global field value and the token.**
When `field` is `false`, this corresponds to no token existing, while
when `field` is `true`, this corresponds to a token existing.
The token doesn't contain any additional data.
Having multiple such tokens at the same time is an impossible state.

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
      <td><code>remove field -= true;</code></td>
      <td><code>require field == true;</code><br><code>update field = false;</code></td>
      <td>Input <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>have field &gt;= true;</code></td>
      <td><code>require field == true;</code></td>
      <td>Input <code>&amp;<span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>add field += true;</code></td>
      <td><code>assert field == false;</code><br><code>update field = true;</code></td>
      <td>Output <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>remove field -= (b);</code></td>
      <td><code style="white-space: pre">require (b ==> field);
update field = field && !b;</code></td>
      <td>Input <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code></td>
    </tr> <tr>
      <td><code>have field &gt;= (b);</code></td>
      <td><code>require (b ==> field);</code></td>
      <td>Input <code>&amp;Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code></td>
    </tr> <tr>
      <td><code>add field += (b);</code></td>
      <td><code style="white-space: pre">assert !(field && b);
update field = field || b;</code></td>
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
    <td><code>Some(tok)</code> where <code>tok.value() == v</code></td>
  </tr>
</table>

### Adding a token

To write an operation that _creates_ a token,
equivalently,
updating the field's value from `false` to `true`, write, inside any `transition!`
operation:

```rust
add field += true;
```

This operation has an inherent safety condition that the prior value of `field` is `false`.
The resulting token exchange function will return a token of type <code><span style="font-style: italic; color: #408040">tok</span></code>.

### Removing a token

To write an operation that _removes_ a token,
equivalently,
updating the field's value from `true` to `false`, write, inside any `transition!`
operation:

```rust
remove field -= true;
```

The resulting exchange function will consume a <code><span style="font-style: italic; color: #408040">tok</span></code> token
as a parameter.

### Checking the value of the token

To check the value of the token without removing it,
write, inside any `transition!`, `readonly!` or `property!` operation:

```rust
have field >= true;
```

The resulting exchange function will accept an immutable reference
<code>&amp;<span style="font-style: italic; color: #408040">tok</span></code> (that is, it takes the token as input but does not consume it).

### Operations that manipulate optional tokens

You can also write versions of the above operations that operate on optional tokens.
The operations below are equivalent to the above versions whenever `b == true`,
and they are all no-ops when `b == false`.

To create an <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>:

```rust
add field += (b);
```

To consume an <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>:

```rust
remove field -= (b);
```

To check the value of an <code>&amp;Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>:

```rust
have field >= (b);
```


The value of `b` is related to the value of
<code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>
as [they are for initialization](#initializing-the-field).

## Example

TODO
