# The `constant` strategy

The `constant` strategy can be applied to fields of any type `V`.

```rust
fields {
    #[sharding(constant)]
    pub field: V,
}
```

**Tokens.**
VerusSync doesn't create a new token type this field; instead, the constant goes on
the `Instance` token.
It can be accessed by writing `instance.field()`
(where `field` is the field name). Thus, the value of the constant is always accessible
in any token operation.

(If for some reason you really need a separate token type that isn't on the `Instance` field,
you can use the [`persisent_option` strategy](./strategy-persistent-option.md).

## Manipulation of the field

### Overview

Unlike with most strategies,
fields of strategy `constant` are manipulated in the same way as fields of "normal" non-tokenized,
except you can't `update` them.
They are initialized using `init`, and you can read the value in transitions or other operations
by referring to the value using `pre.field`. These fields do _not_ have special associated "tokenized" instructions.

### Initializing the field

Initializing the field is done with the usual `init` statement (as it for all strategies).

```rust
init field = v;
```

The instance-init function will return an instance whose value of the constant
(`instance.field()`) has value `v`.

### Reading the field

Reading the field can be done by writing `pre.field`.

## Example

TODO
