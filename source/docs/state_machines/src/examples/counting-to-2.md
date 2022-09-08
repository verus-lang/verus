# Counting to 2

Suppose we want to verify a program like the following:

 * The main thread instantiates a counter to 0.
 * The main thread forks two child threads.
   * Each child thread (atomically) increments the counter.
 * The main thread joins the two threads (i.e., waits for them to complete).
 * The main thread reads the counter.

**Our objective:** Prove the counter read in the final step has value 2.

```rust,ignore
{{#include ../../../../rust_verify/example/state_machines/tutorial/unverified_counting_to_2.rs:full}}
```

We'll walk through the verification of this snippet, starting with the planning stage.

In general, the verification of a concurrent program will look something like the following:

 * Devise an abstraction of the concurrent program. We want an abstraction that is both easy to reason about on its own, but which is “shardable” enough to capture the concurrent execution of the code.
 * Formalize the abstraction as a `tokenized_state_machine!` system. Use Verus to check that it is well-formed.
 * Implement the desired code, “annotating” it with ghost tokens provided by `tokenized_state_machine!`.

### Devising the abstraction

We'll explain our abstraction using a (possibly overwrought) analogy.

Let's imagine that the program is taking place in a classroom, with threads and other concepts personified as students.

To start, we'll use the chalkboard to represent the counter, so we'll start by writing a 0 on the chalkboard. Then we'll ask the student council president to watch the chalkboard and make sure that everybody accessing the chalkboard follows the rules.

The rule is simple: the student can walk up to the chalkboard, and if they have a ticket, they can erase the value and increment it by 1. The student council president will stamp the ticket so the same ticket can't be used again.

Now: suppose you create two tickets and give them to Alice and Bob. Then, you go take a nap, and when you come back, Alice and Bob both give you two _stamped_ tickets. Now, you go look at the chalkboard. Is it possible to see anything than 2?

No, of course not. It must say 2, since both tickets got stamped, so the chalkboard counter must have incremented 2 times.

There are some implicit assumptions here, naturally. For example, we have to assume that nobody could have forged their own ticket, or their own stamp, or remove stamps...

On the other hand—subject to the players playing by the rules of the game as we laid out—our conclusion that the chalkboard holds the number 2 holds without even making any assumptions about what Alice and Bob did while we were away. For all we know, Alice handed the ticket off to Carol who gave it to Dave, who incremented the counter, who then gave it back to Alice. Maybe Alice and Bob switched tickets. Who knows? It's all implementation details.

### Formalizing the abstraction

It's time to formalize the above intuition with a `tokenized_state_machine!`.

The machine is going to have two pieces of state: the `counter: int` (“the number on the chalkboard”) and the state representing the “tickets”. For the latter, since our example is fixed to the number `2`, we'll represent these as two separate fields, `ticket_a: bool` and `ticket_b: bool`, where `false` means an “unstamped ticket” (i.e., has not incremented the counter) and `true` represents a “stamped ticket” (i.e., _has_ incremented the counter).

(In [the next section](./counting-to-n.md) we'll see how to generalize to 2 to `n`, so we won't need a separate field for each ticket, but we'll keep things simple for now.)

Here's our first (incomplete) attempt at a definition:

```rust,ignore
tokenized_state_machine!{
    X {
        fields {
            #[sharding(variable)]
            pub counter: int,

            #[sharding(variable)]
            pub ticket_a: bool,

            #[sharding(variable)]
            pub ticket_b: bool,
        }

        init!{
            initialize() {
                init counter = 0;                   // Initialize “chalkboard” to 0
                init ticket_a = false;              // Create one “unstamped ticket”
                init ticket_b = false;              // Create another “unstamped ticket”
            }
        }

        transition!{
            do_increment_a() {
                require(!pre.ticket_a);             // Require the client to provide an “unstamped ticket”
                update counter = pre.counter + 1;   // Increment the chalkboard counter by 1
                update ticket_a = true;             // Stamp the ticket
            }
        }

        transition!{
            do_increment_b() {
                require(!pre.ticket_b);             // Require the client to provide an “unstamped ticket”
                update counter = pre.counter + 1;   // Increment the chalkboard counter by 1
                update ticket_b = true;             // Stamp the ticket
            }
        }

        readonly!{
            finalize() {
                require(pre.ticket_a);              // Given that both tickets are stamped
                require(pre.ticket_b);              // ...
                assert(pre.counter == 2);           // one can conclude the chalkboard value is 2.
            }
        }
    }
}
```

Let's take this definition one piece at a time. In the `fields` block, we declared our three states. Note that each one is tagged with a _sharding strategy_, which tells Verus how to break the state into pieces—we'll talk about that below. We'll talk more about the strategies in the next section; right now, all three of our fields use the `variable` strategy, so we don't have anything to compare to.

Now we defined four operations on the state machine. The first one is an initialization procedure, named `initialize`: It lets instantiate the protocol with the counter at 0 and with two unstamped tickets.

The transition `do_increment_a` lets the client trade in an unstamped ticket for a stamped ticket, while incrementing the counter. The transition `do_increment_b` is similar, for the `ticket_b` ticket.

Lastly, we come to the `finalize` operation. This one is `readonly!`, as it doesn't actually update any state. Instead, it lets the client _conclude_ something about the state that we read: just by having the two stamped tickets, we can conclude that the `counter` value is 2.

Let's run and see what happens.

```ignore
error: unable to prove assertion safety condition
  --> y.rs:50:17
   |
50 |                 assert(pre.counter == 2);
   |                 ^^^^^^^^^^^^^^^^^^^^^^^^^

error: aborting due to previous error; 1 warning emitted
```

Uh-oh. Verus wasn't able to prove the safety condition. Of course not—we didn't provide any invariant for our system! For all Verus knows, the state `{counter: 1, ticket_a: true, ticket_b: true}` is valid. Let's fix this up:

```rust,ignore
{{#include ../../../../rust_verify/example/state_machines/tutorial/counting_to_2.rs:inv}}
```

Our invariant is pretty straightforward: The value of the counter should be equal to the number of stamps. Now, we need to supply stub lemmas to prove that the invariant is preserved by every transition. In this case, Verus completes the proofs easily, so we don't need to supply any proofs in the lemma bodies to help out Verus.

```rust,ignore
{{#include ../../../../rust_verify/example/state_machines/tutorial/counting_to_2.rs:inv_proof}}
```

Now that we've completed our abstraction, let's turn towards the implementation.

### The Auto-generated Token API

Given a `tokenized_state_machine!` like the above, Verus will analyze it and produce a series of _token types_ representing pieces of the state, and a series of _exchange functions_ that perform the transitions on the tokens.

(TODO provide instructions for the user to get this information themselves)

Let's take a look at the tokens that Verus generates here. First, Verus generates an _Instance_ type for instances of the protocol. For the simple state machine here, this doesn't do very much other than serve as a unique identifier for each instantiation.

```rust,ignore
#[proof]
#[verifier(unforgeable)]
pub struct Instance { ... }
```

Next, we have token types that represent the actual fields of the state machine. We get one token for each field:

```rust,ignore
#[proof]
#[verifier(unforgeable)]
pub struct counter {
    #[spec] pub instance: X::Instance,
    #[spec] pub value: int,
}

#[proof]
#[verifier(unforgeable)]
pub struct ticket_a {
    #[spec] pub instance: X::Instance,
    #[spec] pub value: bool,
}

#[proof]
#[verifier(unforgeable)]
pub struct ticket_b {
    #[spec] pub instance: X::Instance,
    #[spec] pub value: bool,
}
```

For example, ownership of a token `X::counter { instance: inst, value: 5 }` represents proof that the instance `inst` of the protocol currently has its `counter` state set to `5`. With all three tokens for a given instance taken altogether, we recover the full state.

Now, let's take a look at the exchange functions. We start with `X::Instance::initialize`, generated from our declared `initialize` operation.  This function returns a fresh instance of the protocol (`X::Instance`) and tokens for each field (`X::counter`, `X::ticket_a`, and `X::ticket_b`) all initialized to the values as we declared them (`0`, `false`, and `false`).

```rust,ignore
impl Instance {
    // init!{
    //      initialize() {
    //          init counter = 0;
    //          init ticket_a = false;
    //          init ticket_b = false;
    //      }
    //  }

    #[proof]
    #[verifier(returns(proof))]
    pub fn initialize() -> (X::Instance, X::counter, X::ticket_a, X::ticket_b) {
        ensures(|tmp_tuple: (X::Instance, X::counter, X::ticket_a, X::ticket_b)| {
            [{
                let (instance, token_counter, token_ticket_a, token_ticket_b) = tmp_tuple;
                (equal(token_counter.instance, instance))
                    && (equal(token_ticket_a.instance, instance))
                    && (equal(token_ticket_b.instance, instance))
                    && (equal(token_counter.value, 0))            // init counter = 0;
                    && (equal(token_ticket_a.value, false))       // init ticket_a = false;
                    && (equal(token_ticket_b.value, false))       // init ticket_b = false;
            }]
        });
        ...
    }
```

Next, the function for the `do_increment_a` transition. Note that enabling condition in the user's declared transition
becomes a precondition for calling of `do_increment_a`. The exchange function takes a `X::counter` and `X::ticket_a` token as input,
and since the transition modifies both fields, the exchange function takes the tokens as `&mut`.

Also note, crucially, that _it does not take a `X::ticket_b` token at all_ because the transition doesn't depend on the `ticket_b` field.
The transition can be performed entirely without reference to it.

```rust,ignore
    //  transition!{
    //      do_increment_a() {
    //          require(!pre.ticket_a);
    //          update counter = pre.counter + 1;
    //          update ticket_a = true;
    //      }
    //  }

    #[proof]
    pub fn do_increment_a(
        #[proof] &self,
        #[proof] token_counter: &mut X::counter,
        #[proof] token_ticket_a: &mut X::ticket_a,
    ) {
        requires([
            equal(old(token_counter).instance, (*self)),
            equal(old(token_ticket_a).instance, (*self)),
            (!old(token_ticket_a).value),                        // require(!pre.ticket_a)
        ]);
        ensures([
            equal(token_counter.instance, (*self)),
            equal(token_ticket_a.instance, (*self)),
            equal(token_counter.value, old(token_counter).value + 1),   // update counter = pre.counter + 1
            equal(token_ticket_a.value, true),                          // update ticket_a = true
        ]);
        ...
    }
```

The function for the `do_increment_b` transition is similar:

```rust,ignore
    //  transition!{
    //      do_increment_b() {
    //          require(!pre.ticket_b);
    //          update counter = pre.counter + 1;
    //          update ticket_b = true;
    //      }
    //  }

    #[proof]
    pub fn do_increment_b(
        #[proof] &self,
        #[proof] token_counter: &mut X::counter,
        #[proof] token_ticket_b: &mut X::ticket_b,
    ) {
        requires([
            equal(old(token_counter).instance, (*self)),
            equal(old(token_ticket_b).instance, (*self)),
            (!old(token_ticket_b).value),                        // require(!pre.ticket_b)
        ]);
        ensures([
            equal(token_counter.instance, (*self)),
            equal(token_ticket_b.instance, (*self)),
            equal(token_counter.value, old(token_counter).value + 1),   // update counter = pre.counter + 1
            equal(token_ticket_b.value, true),                          // update ticket_b = true
        ]);
        ...
    }
```

Finally, we come to the `finalize` operation. Again this is a “no-op” transition that doesn't update any fields, so the generated exchange method takes the tokens as readonly parameters (non-mutable borrows).  Here, we observe that the `assert` becomes a post-condition, that is, by performing this operation, though it does not update any state, causes us to learn something about that state.

```rust,ignore
    //  readonly!{
    //      finalize() {
    //          require(pre.ticket_a);
    //          require(pre.ticket_b);
    //          assert(pre.counter == 2);
    //      }
    //  }

    #[proof]
    pub fn finalize(
        #[proof] &self,
        #[proof] token_counter: &X::counter,
        #[proof] token_ticket_a: &X::ticket_a,
        #[proof] token_ticket_b: &X::,
    ) {
        requires([
            equal(token_counter.instance, (*self)),
            equal(token_ticket_a.instance, (*self)),
            equal(token_ticket_b.instance, (*self)),
            (token_ticket_a.value),                     // require(pre.ticket_a)
            (token_ticket_b.value),                     // require(pre.ticket_b)
        ]);
        ensures([token_counter.value == 2]);            // assert(pre.counter == 2)
        ...
    }
}
```

### Writing the verified implementation

To verify the implementation, our plan is to instantiate this ghost protocol and associate
the `counter` field of the protocol to the atomic memory location we use in our code.

To do this, we'll use the Verus library `atomic_ghost`.
Specifically, we'll use the type `atomic_ghost::AtomicU32<X::counter>`.
This is a wrapper around an `AtomicU32` location which associates it to a `tracked`
ghost token `X::counter`.

More specifically, all threads will share this global state:

```rust,ignore
{{#include ../../../../rust_verify/example/state_machines/tutorial/counting_to_2.rs:global_struct}}
```

Note that we track `instance` as a separate field. This ensures that all threads agree
on which instance of the protocol they are running.

(Keep in mind that whenever we perform a transition on the ghost tokens, all the tokens
have to have the same instance. Why does Verus enforce restriction? Because if it did not,
then the programmer could instantiate two instances of the protocol, the mix-and-match to get
into an invalid state. For example, they could increment the counter twice, using up
both "tickets" of that instance, and then use the ticket of another instance to increment
it a third time.)

TODO finish writing the explanation
