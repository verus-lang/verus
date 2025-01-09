# The `variable` strategy

The `variable` strategy can be applied to fields of any type `V`.

```rust
fields {
    #[sharding(variable)]
    pub field: V,
}
```

**Tokens.**
VerusSync creates a fresh token type, <code style="font-style: italic; color: #408040">tok</code>,
named `State::field` where `State` is the name of the VerusSync system and `field` is the name of the field.

The token type <code style="font-style: italic; color: #408040">tok</code> implements the
[`UniqueValueToken<V>`](https://verus-lang.github.io/verus/verusdoc/vstd/tokens/trait.UniqueValueToken.html) trait.

**Relationship between global field value and the token.**
The value of the token is the same as the value of the field.
Having multiple such tokens at the same time (for the same field) is an impossible state.

## Manipulation of the field

### Overview

Unlike with most strategies,
fields of strategy `variable` are manipulated in the same way as fields of "normal" non-tokenized
state machines, using `init` and `update` instructions, and by referring to the value using
`pre.field`. These fields do _not_ have special associated "tokenized" instructions.

### Initializing the field

Initializing the field is done with the usual `init` statement (as it for all strategies).

```rust
init field = v;
```

The instance-init function will return a token of type <code><span style="font-style: italic; color: #408040">tok</span></code>.

### Reading the field

Reading the field can be done by writing `pre.field`. If the variable is read but not modified,
it will be input as a 
<code>&amp;<span style="font-style: italic; color: #408040">tok</span></code>.
If it's read _and_ modified, it will be input as a 
<code>&amp;mut <span style="font-style: italic; color: #408040">tok</span></code>.

### Updating the field

Updating the field is done with the `update` statement in any `transition!` operation:

```rust
update field = v;
```

The token will be input and modified via an argument of type
<code>&amp;mut <span style="font-style: italic; color: #408040">tok</span></code>.

## Example

TODO
