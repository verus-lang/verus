# Token exchanges as transitions

The aim of the framework of tokenized state machines is to marry the power and ergonomics of general transition systems with the token-based approach to concurrency reasoning.

To make this work, the developer has to do two special things when describing their transitions system:

 * First, they must annotate each field of their state datatype with what we call a _strategy_: the the strategy tells Verus how the state should break down into tokens.
 * Second, they must define their transitions using special commands so that the transitions can be interpretted simultaneously as [transitions on the state](./components.md)  _and_ as [token exchange functions](./thinking-tokens.md).

TODO write an explanation for why we need special transitions
