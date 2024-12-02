# The `option` strategy

The `option` strategy can be applied to fields of type `Option<V>` for any type `V`.

```rust
fields {
    #[sharding(option)]
    pub field: Option<V>,
}
```

**Tokens.**
VerusSync creates a fresh token type, <code style="font-style: italic; color: #408040">tok</code>,
named `State::field` where `State` is the name of the VerusSync system and `field` is the name of the field.

The token type <code style="font-style: italic; color: #408040">tok</code> implements the
[`UniqueValueToken<V>`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.UniqueValueToken.html) trait.

**Relationship between global field value and the token.**
When `field` is `None`, this corresponds to no token existing, while
when `field` is `Some(v)`, this corresponds to a token of value `v` existing.
Having multiple such tokens at the same time is an impossible state.

## Manipulation of the field

### Quick Reference

In the following table, `v: V` and `v_opt: Option<V>`.

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
      <td><code>init field = v_opt;</code></td>
      <td><code>init field = v_opt;</code></td>
      <td>Output <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code></td>
    </tr> <tr>
      <td><code>remove field -= Some(v);</code></td>
      <td><code>require field == Some(v);</code><br><code>update field = None;</code></td>
      <td>Input <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>have field &gt;= Some(v);</code></td>
      <td><code>require field == Some(v);</code></td>
      <td>Input <code>&amp;<span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>add field += Some(v);</code></td>
      <td><code>assert field == None;</code><br><code>update field = Some(v);</code></td>
      <td>Output <code><span style="font-style: italic; color: #408040">tok</span></code></td>
    </tr> <tr>
      <td><code>remove field -= (v_opt);</code></td>
      <td><code style="white-space: pre">require v_opt == None || field == v_opt;
update field = if v_opt == None { field }
               else { None };</code></td>
      <td>Input <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code></td>
    </tr> <tr>
      <td><code>have field &gt;= (v_opt);</code></td>
      <td><code>require v_opt == None || field == v_opt;</code></td>
      <td>Input <code>&amp;Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code></td>
    </tr> <tr>
      <td><code>add field += (v_opt);</code></td>
      <td><code style="white-space: pre">assert field == None || v_opt == None;
update field = if v_opt == None { field }
               else { v_opt };</code></td>
      <td>Output <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code></td>
    </tr>
  </tbody>
</table></div>

### Initializing the field

Initializing the field is done with the usual `init` statement (as it for all strategies).

```rust
init field = opt_v;
```

The instance-init function will return a token of type <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>,
related as follows:

<table>
  <tr>
    <th>value of <code>opt_v: V</code></th>
    <th>&nbsp;&nbsp;&nbsp;value of optional token <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>></code></th>
  </tr>
  <tr>
    <td><code>None</code></td>
    <td><code>None</code></td>
  </tr>
  <tr>
    <td><code>Some(v)</code></td>
    <td><code>Some(tok)</code> where <code>tok.value() == v</code></td>
  </tr>
</table>

### Adding a token

To write an operation that _creates_ a token with value `v`,
equivalently,
updating the field's value from `None` to `Some(v)`, write, inside any `transition!`
operation:

```rust
add field += Some(v);
```

This operation has an inherent safety condition that the prior value of `field` is `None`.
The resulting token exchange function will return a token of type <code><span style="font-style: italic; color: #408040">tok</span></code>
and with value `v`.

If you require manual proof to prove the inherent safety condition, you can add
an optional `by` clause:

```rust
add field += Some(v)
by {
    // proof goes here
};
```

### Removing a token

To write an operation that _removes_ a token with value `v`,
equivalently,
updating the field's value from `Some(v)` to `None`, write, inside any `transition!`
operation:

```rust
remove field -= Some(v);
```

The resulting exchange function will consume a <code><span style="font-style: italic; color: #408040">tok</span></code> token with value `v`
as a parameter.

Instead of specifying `v` as an exact expression, you can also pattern-match
by using the `let` keyword.

```rust
remove field -= Some(let $pat);
```

This will require the prior value of `field` to match `Some($pat)`,
and this statement binds all the variables in `$pat` for use later in the transition.

### Checking the value of the token

To check the value of the token without removing it,
write, inside any `transition!`, `readonly!` or `property!` operation:

```rust
have field >= Some(v);
```

The resulting exchange function will accept an immutable reference
<code>&amp;<span style="font-style: italic; color: #408040">tok</span></code> (that is, it takes the token as input but does not consume it).

Instead of specifying `v` as an exact expression, you can also pattern-match
by using the `let` keyword.

```rust
have field >= Some(let $pat);
```

This will require the prior value of `field` to match `Some($pat)`,
and this statement binds all the variables in `$pat` for use later in the transition.

### Updating a token

To update the value of an `option` token, first `remove` it, then `add` it,
in sequence.

```rust
remove field -= Some(let _);
add field += Some(new_v);
```

### Operations that manipulate optional tokens

You can also write versions of the above operations that operate on optional tokens.
The operations below are equivalent to the above versions whenever `opt_v == Some(v)`,
and they are all no-ops when `opt_v == None`.

To create an <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>:

```rust
add field += (opt_v);
```

To consume an <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>:

```rust
remove field -= (opt_v);
```

To check the value of an <code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>:

```rust
have field >= (opt_v);
```


The value of `opt_v` is related to the value of
<code>Option&lt;<span style="font-style: italic; color: #408040">tok</span>&gt;</code>
as [they are for initialization](#initializing-the-field).

## Example

```rust,ignore
{{#include ../../../rust_verify/example/state_machines/reference-examples/strategy_option.rs:full}}
```
