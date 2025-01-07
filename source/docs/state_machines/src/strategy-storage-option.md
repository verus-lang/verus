# The `storage_option` strategy

The `storage_option` strategy can be applied to fields of type <code>Option&lt;<span style="font-style: italic; color: #c08080">Tok</span>&gt;</code>
for any type <code><span style="font-style: italic; color: #c08080">Tok</span></code>.

```rust
fields {
    #[sharding(storage_option)]
    pub field: Option<Tok>,
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
When a field is declared `storage_option`, the VerusSync gains the ability to "store"
tokens of the given type <code><span style="font-style: italic; color: #c08080">Tok</span></code>. A field value of `None` means nothing is stored;
a field value of `Some(tok)` means the token `tok` is stored.

## Manipulation of the field

### Quick Reference

In the following table, <code>tok: <span style="font-style: italic; color: #c08080">Tok</span></code>, and <code>opt_token: Option&lt;<span style="font-style: italic; color: #c08080">Tok</span>&gt;</code>.

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
      <td><code>init field = opt_tok;</code></td>
      <td><code>init field = opt_tok;</code></td>
      <td>Input <code>Option&lt;<span style="font-style: italic; color: #c08080">Tok</span>&gt;</code></td>
    </tr> <tr>
      <td><code>deposit field += Some(tok);</code></td>
      <td><code>assert field == None;</code><br><code>update field = Some(tok);</code></td>
      <td>Input <code><span style="font-style: italic; color: #c08080">Tok</span></code></td>
    </tr> <tr>
      <td><code>guard field &gt;= Some(tok);</code></td>
      <td><code>assert field == Some(tok);</code></td>
      <td>Output <code>&amp;<span style="font-style: italic; color: #c08080">Tok</span></code></td>
    </tr> <tr>
      <td><code>withdraw field -= Some(tok);</code></td>
      <td><code>assert field == Some(tok);</code><br><code>update field = None;</code></td>
      <td>Output <code><span style="font-style: italic; color: #c08080">Tok</span></code></td>
    </tr> <tr>
      <td><code>deposit field += opt_tok;</code></td>
      <td><code>assert field == None || opt_tok == None;</code><br><code>update field = opt_tok;</code></td>
      <td>Input <code>Option&lt;<span style="font-style: italic; color: #c08080">Tok</span>&gt;</code></td>
    </tr> <tr>
      <td><code>guard field &gt;= opt_tok;</code></td>
      <td><code>assert opt_tok.is_some() ==> field == opt_tok;</code></td>
      <td>Output <code>&amp;Option&lt;<span style="font-style: italic; color: #c08080">Tok</span>&gt;</code></td>
    </tr> <tr>
      <td><code>withdraw field -= opt_tok;</code></td>
      <td><code>assert opt_tok.is_some() ==> field == opt_tok;</code><br><code>update field = if opt_tok == None { field } else { None };</code></td>
      <td>Output <code>Option&lt;<span style="font-style: italic; color: #c08080">Tok</span>&gt;</code></td>
    </tr>
  </tbody>
</table></div>

### Initializing the field

Initializing the field is done with the usual `init` statement (as it for all strategies).

```rust
init field = opt_tok;
```

The instance-init function will take _as input_ a token of type <code>Option&lt;<span style="font-style: italic; color: #c08080">Tok</span>&gt;</code>,
equal to the value of `opt_tok`.

That is, if `opt_tok` is `None`, then the initial state has nothing "stored" and passing `None` to the constructor is trivial;
if `opt_tok` is `Some(tok)`, then the initial state has `tok` "stored" and it must be supplied via the input argument for the constructor.

### Performing a deposit

To deposit a token <code>tok: <span style="font-style: italic; color: #c08080">Tok</span></code>, use the `deposit` statement in any `transition!` operation:

```
deposit field += Some(tok);
```

This sets the field value to `Some(tok)`. The resulting token operation then takes a token equal to `tok` as input.

The `deposit` instruction has an inherent safety condition that `field` is `None` in the pre-state. (Note: this is not strictly necessary, and the restriction may be removed later.)

If you require manual proof to prove the inherent safety condition, you can add
an optional `by` clause:

```rust
deposit field += Some(v)
by {
    // proof goes here
};
```

### Performing a withdraw

To withdraw a token <code>tok: <span style="font-style: italic; color: #c08080">Tok</span></code>, use the `withdraw` statement in any `transition!` operation:

```
withdraw field -= Some(tok);
```

This sets the field value to `None`. The resulting token operation then returns a token
equal to `tok` in its output.

The `withdraw` instruction has an inherent safety condition that `field` is `Some(tok)` in the pre-state.

**Manual proofs.** If you require manual proof to prove the inherent safety condition, you can add
an optional `by` clause:

```rust
withdraw field -= Some(tok)
by {
    // proof goes here
};
```

**Using patterns.** Instead of specifying `tok` as an exact expression, you can also pattern-match
by using the `let` keyword.

```
withdraw field -= Some(let $pat);
```

In this case, the inherent safety condition is that the `field` value is `Some` and that
the inner value matches `$pat`. In this case, note that the value matched on `$pat` is
_not_ deterministic in the input arguments of the token operation. Therefore,
VerusSync considers any variables bound in `$pat` to implicitly be [`birds_eye`](./birds_eye.md)
binders. Specifically, the pattern-matching variant is equivalent to:

```
birds_eye let stored_value = pre.field.unwrap();
withdraw field -= Some(stored_value);
birds_eye let $pat = stored_value;
```

### Performing a guard (obtaining a shared reference to the stored object)

To guard a token <code>tok: <span style="font-style: italic; color: #c08080">Tok</span></code>, use the `guard` statement in any `property!` operation:

```
guard field >= Some(tok);
```

The resulting token operation then returns a _shared reference_ to the token
equal to `tok` in its output. The shared reference has a lifetime bounded by the lifetimes
of the input references.

The `guard` instruction has an inherent safety condition that `field` is `Some(tok)` in the pre-state.

**Manual proofs.** If you require manual proof to prove the inherent safety condition, you can add
an optional `by` clause:

```rust
guard field >= Some(tok)
by {
    // proof goes here
};
```

### Operations that manipulate optional tokens

You can also write versions of the above operations that operate on optional tokens.
The operations below are equivalent to the above versions whenever `opt_tok == Some(tok)`,
and they are all no-ops when `opt_tok == None`.

To deposit an <code>Option&lt;<span style="font-style: italic; color: #c08080">Tok</span>&gt;</code>:

```rust
deposit field += (opt_tok);
```

To withdraw an <code>Option&lt;<span style="font-style: italic; color: #c08080">Tok</span>&gt;</code>:

```rust
remove field -= (opt_tok);
```

To obtain an <code>&amp;Option&lt;<span style="font-style: italic; color: #c08080">Tok</span>&gt;</code>:

```rust
guard field >= (opt_v);
```

## Example

TODO
