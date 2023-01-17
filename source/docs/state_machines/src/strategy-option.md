# The `option` strategy

The `option` strategy can be applied to fields of type `Option<V>` for any type `V`.

```rust
fields {
    #[sharding(option)]
    pub field: Option<V>,
}
```

This creates a token type, `State::field`, which a field `value: V`.
When `field` is `None`, this corresponds to no token existing, while
when `field` is `Some(v)`, this corresponds to a token of value `v` existing.
Having multiple such tokens at the same time is an impossible state.

### Quick Reference

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
      <td>Output <code>Option&lt;State::field&gt;</code></td>
    </tr> <tr>
      <td><code>remove field -= Some(v);</code></td>
      <td><code>require field === Some(v);</code><br><code>update field = None;</code></td>
      <td>Input <code>State::field</code></td>
    </tr> <tr>
      <td><code>have field &gt;= Some(v);</code></td>
      <td><code>require field === Some(v);</code></td>
      <td>Input <code>&amp;State::field</code></td>
    </tr> <tr>
      <td><code>add field += Some(v);</code></td>
      <td><code>assert field === None;</code><br><code>update field = Some(v);</code></td>
      <td>Output <code>State::field</code></td>
    </tr> <tr>
      <td><code>remove field -= (v_opt);</code></td>
      <td><code style="white-space: pre">require v_opt === None || field === v_opt;
update field = if v_opt === None { field }
               else { None };</code></td>
      <td>Input <code>Option&lt;State::field&gt;</code></td>
    </tr> <tr>
      <td><code>have field &gt;= (v_opt);</code></td>
      <td><code>require v_opt === None || field === v_opt;</code></td>
      <td>Input <code>&amp;Option&lt;State::field&gt;</code></td>
    </tr> <tr>
      <td><code>add field += (v_opt);</code></td>
      <td><code style="white-space: pre">assert field === None || v_opt === None;
update field = if v_opt === None { field }
               else { v_opt };</code></td>
      <td>Output <code>Option&lt;State::field&gt;</code></td>
    </tr>
  </tbody>
</table></div>

### Initializing the field

Initializing the field is done with the usual `init` statement (as it for all strategies).

```rust
init field = opt_v;
```

The instance-init function will return a token of type `Option<State::field>`,
related as follows:

<table>
  <tr>
    <th>value of <code>opt_v: V</code></th>
    <th>&nbsp;&nbsp;&nbsp;value of optional token <code>Option&lt;State::field></code></th>
  </tr>
  <tr>
    <td><code>None</code></td>
    <td><code>None</code></td>
  </tr>
  <tr>
    <td><code>Some(v)</code></td>
    <td><code>Some(tok)</code> where <code>tok@.value === v</code></td>
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
The resulting token exchange function will return a token of type `State::field`
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

The resulting exchange function will consume a `State::field` token with value `v`
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
`&State::field` (that is, it takes the token as input but does not consume it).

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
These operations are equivalent to above versions whenever `opt_v = Some(v)`,
and they are all no-ops when `opt_v = None`.

To create an `Option<State::field>`:

```rust
add field += (opt_v);
```

To consume an `Option<State::field>`:

```rust
remove field -= (opt_v);
```

To check the value of an `Option<State::field>`:

```rust
have field >= (opt_v);
```


The value of `opt_v` is related to the value of `Option<State::field>`
as [they are for initialization](#initializing-the-field).

## Example

```rust,ignore
{{#include ../../../rust_verify/example/state_machines/reference-examples/strategy_option.rs:full}}
```
