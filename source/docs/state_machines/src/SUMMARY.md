# Summary

[Intro](./intro.md)

# User Guide

  - [Tokenized State Machines](./tokenized.md)

    - [High-Level Idea](high-level-idea.md)

    - [Guide by example](tutorial-by-example.md)

      - [Counting to 2](./examples/counting-to-2.md)
        - [Unverified Source](./examples/rust-counting-to-2.md)
        - [Verified Source](./examples/src-counting-to-2.md)

      - [Counting to _n_](./examples/counting-to-n.md)
        - [Unverified Source](./examples/rust-counting-to-n.md)
        - [Verified Source](./examples/src-counting-to-n.md)

      - [Producer-consumer queue](./examples/producer-consumer-queue.md)
        - [Unverified Source](./examples/rust-producer-consumer-queue.md)
        - [Verified Source](./examples/src-producer-consumer-queue.md)

      - [Reference-counted smart pointer](./examples/rc.md)
        - [Unverified Source](./examples/rust-rc.md)
        - [Verified Source](./examples/src-rc.md)
        - [Exerises](./examples/rc-exercises.md)

    - [Guide TODO](tutorial-by-example.md)

      - [Counting to _n_ (again) (TODO)](./examples/counting-to-n-again.md)
      - [Hash table (TODO)](./examples/hash-table.md)
      - [Reader-writer lock (TODO)](./examples/rwlock.md)

# Reference

  - [State Machines](./state-machine-reference.md)
    - [State Machine Basics](./components.md)
    - [State Machine Macro Syntax (TODO)](./macro-high-level-reference.md)
    - [Transition Language](./transition-language.md)
    - [Invariants and Inductive Proofs](./invariants.md)
    - [Macro-generated code (TODO)](./macro-generated-reference.md)
    - [State Machine Refinements (TODO)](./refinements-reference.md)

  - [Tokenization](./tokenization-reference.md)
    - [Strategy Reference](strategy-reference.md)
      - [`option`](strategy-option.md)
    - [Formalism of Tokenization by monoids (TODO)](./monoid-formalism.md)
