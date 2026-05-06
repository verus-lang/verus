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
        - [Exercises](./examples/rc-exercises.md)

    - [Guide (TODO)](tutorial-again.md)
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

  - [VerusSync](./tokenization-reference.md)
    - [Strategy Reference](./strategy-reference.md)
      - [`variable`](./strategy-variable.md)
      - [`constant`](./strategy-constant.md)
      - [`option`](./strategy-option.md)
      - [`map`](./strategy-map.md)
      - [`set`](./strategy-set.md)
      - [`multiset`](./strategy-multiset.md)
      - [`bool`](./strategy-bool.md)
      - [`count`](./strategy-count.md)
      - [`persistent_option`](./strategy-persistent-option.md)
      - [`persistent_map`](./strategy-persistent-map.md)
      - [`persistent_set`]()
      - [`persistent_bool`](./strategy-persistent-bool.md)
      - [`persistent_count`]()
      - [`not_tokenized`](./strategy-not-tokenized.md)
      - [`storage_option`](./strategy-storage-option.md)
      - [`storage_map`](./strategy-storage-map.md)
    - [Properties](./properties.md)
    - [Operation definitions](./operations.md)
      - [`birds_eye`](./birds-eye.md)
    - [Formalism of Tokenization by monoids (TODO)](./monoid-formalism.md)
