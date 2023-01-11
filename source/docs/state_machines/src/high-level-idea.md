# High-Level Concepts

The approach we follow for each of the examples follows roughly this high-level recipe:

 1. Consider the program you want to verify.
 2. Create an "abstraction" of the program as a tokenized state machine.
 3. Verus will automatically produce for you a bunch of ghost "token types" that make up the
    tokenized state machine.
 4. Implement a verified program using the token types

That doesn't sound too bad, but there's a bit of an art to it, especially in step (2).
To build a proper abstraction, one needs to choose an abstraction which is both abstract
enough that it's easy to prove the relevant properties about, but still concrete enough
that it can be properly connected back to the implementation in step (4).
Choosing this abstraction requires one to identify which pieces of state need to be
in the abstraction, as well as which "tokenization strategy" to use---that's a concept
we'll be introducing soon.

In the upcoming examples, we'll look at a variety of scenarios and the techniques
we can use to tackle them.
