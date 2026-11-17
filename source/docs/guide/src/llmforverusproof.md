# Using LLMs to Help Write Verus Proofs

## Quick Start: Recommended Setup

For best results, we recommend this setup:

1. **Use a coding agent**, not direct model API calls
2. **Provide Verus resources (vstd and others)** for the model to reference
3. **Provide a Verus binary** for the model to run and see error messages
4. **Use a cheat checker** to catch invalid proof shortcuts

With these in place, you don't need complicated prompts; a simple prompt like the following often works well:

```
The file X.rs cannot be verified by Verus yet.
Please add proof annotations so that it can be successfully verified by Verus.
The vstd folder contains Verus standard library definitions and helper lemmas.
Keep editing your proof until Verus shows no errors.
Do NOT change existing specifications (requires/ensures) or executable code.
Do NOT use assume(...) or admit(...).
Before you finish, run the cheat checker to make sure you haven't cheated.
```

## Use a Coding Agent

**Why a coding agent?** Writing code and writing proofs about code have many similarities. Both require a good understanding of the existing code base and both can beneift from tool support, such as testing tools for code synthesis and verifiers for proof synthesis. Practice has shown that state-of-the-art LLMs work best when they can explore the code base, run tools, and iterate at their own pace, which is well supported by existing coding agents like [GitHub Copilot CLI](https://githubnext.com/projects/copilot-cli).

**Practical tips:**
- We recommend running the agent in a secure container or sandbox, so that you can safely give it the freedom to run Verus and other available tools, without requiring repeated human intervention, e.g., via `--allow-all-tools` (Copilot CLI) or similar options.

## Provide Verus Resources

Giving the LLM access to existing Verus resources, such as the Verus standard library ([`vstd`](https://github.com/verus-lang/verus/tree/main/source/vstd)), the Verus test suite ([`rust_verify_test`](https://github.com/verus-lang/verus/tree/main/source/rust_verify_test)), and the Verus [Guide](https://github.com/verus-lang/verus/tree/main/source/docs/guide/src/), offers several benefits:

1. **Learning Verus syntax**: By examining these resources, LLMs can learn correct Verus idioms. This is especially helpful for models that occasionally produce syntax errors.

2. **Finding helper lemmas**: The `vstd` library contains many useful lemmas that can simplify or enable proofs. If you don't give LLMs access to `vstd`, they may hallucinate about what lemmas are available.

3. **Learning latest features**: `rust_verify_test` is a great resource for LLMs to learn about the most recent features added to Verus.

Here is a snippet of GPT-5-mini's reasoning log, when provided with the [`lemma_len_intersect`](./assert_assume.md) lemma to prove:

```
● Web Search (MCP: github-mcp-server) · Verus set len subset injective_map "Verus" "Set" len subset…
  └ ...

● Edit lemma_len_intersect.rs +1 -1

● Run verus on modified lemma_len_intersect.rs to see if pervasive::set::len_mono exists (shell)
  └ ...

● Edit lemma_len_intersect.rs +1 -1

● Run verus on modified lemma_len_intersect.rs to see if vstd::set::len_mono exists (shell)
  └ ...

● Edit lemma_len_intersect.rs +1 -1

● Run verus to check if subset_len exists (shell)
  └ ...

● Edit lemma_len_intersect.rs +1 -1

● Run verus to check if len_le_of_subset exists (shell)
  └ ...
```

As you can see, when `vstd` is not provided, models can struggle and hallucinate.

## Provide a Verus Binary

LLMs should be able to invoke Verus and see its error output. Verus error messages are informative and help guide the proof-development process. When you are facing a complicated proof task, even the most capable model today can rarely generate a correct and sufficient proof in one attempt. Without seeing the error report from Verus, the model will rely on luck to fix an incomplete or incorrect proof.

Here is a snippet of the reasoning log from Claude Opus 4.5, a very powerful reasoning model, when we ask it to verify a very difficult lemma function in `test.rs`:
```
Let me run Verus to see what the errors are:

● Run Verus to see initial errors (shell)
  │ cd /usr/src/work && verus test.rs --rlimit 100 2>&1 | head -200
  └ 46 lines...

Now I need to add proof annotations to help Verus verify this lemma. Let me look at the vstd folder for any useful lemmas:
...
... 

● Run Verus to check proof (shell)
  │ cd /usr/src/tmp && verus test.rs --rlimit 150 2>&1 | head -400
  └ 94 lines...

There are several issues. Let me take a more careful approach by understanding what needs to be proven. Let me simplify the proof and add the necessary assertions more carefully:

... 
...

● Run Verus to check proof (shell)
  │ cd /usr/src/tmp && verus test.rs --rlimit 150 2>&1 | head -400
  └ 16 lines...

I see there are issues with imports. Let me look at the file structure more carefully:

...
```

This workflow of repeatedly running Verus, reflecting on the resulting Verus error report, and then editing proof annotations accordingly is a good practice for both human developers and LLMs.

**Key points:**
- Provide a simple command to run Verus (e.g., `verus file.rs`)
- Let the model see the complete error output, not just success/failure (this is the case by default if you use coding agents)
- The `--expand-errors` flag can provide even more detailed feedback

## Use a Cheat Checker

Without explicit guardrails, LLMs will sometimes "cheat" to make proofs pass. This happens a lot when the proof task is difficult.

There are many ways that LLMs cheat. Here are just some typical cheating methods:

| Cheat Type | What It Looks Like |
|------------|-------------------|
| Using `assume()` or `admit()` | Assumes properties without proof |
| Adding `external_body` tags | Skips verification of function bodies |
| Adding `axiom` tags | Assumes lemmas without proof |
| Changing specifications | Strengthens preconditions or weakens postconditions |
| Changing executable code | Changes Rust code to make verification easier, which may change program semantics, reduce performance, or harm code readability |

A simple tool that compares the model's output against the original file can catch most of these. The first three cheating methods can be easily identified by searching for strings like ```assume```, ```admit```, ```external_body```, and ```axiom```, in the added content of LLMs. Precisely checking specification or executable code changes would require parser support.


## Understand Model Capabilities and Costs

Different models have different strengths, costs, and speed. Here's what to expect:

### Success Rates

Proof-synthesis capability differs a lot across different models. Older models like GPT-4o and GPT o4-mini are poor at Verus syntax and general verification skills. Sophisticated prompting beyond a generic coding agent is likely needed to make them work in non-trivial proof tasks. Newer models are doing much better. Practice has shown that models like Claude Sonnet 4.5 and Claude Opus 4.5 can successfully fill in proof annotations for most proof lemmas in existing Verus-verified system projects.


### Time and Money

Before using LLMs, you should be aware of their cost.

There are several factors that may affect the cost:
- Using a coding agent in general costs more than directly calling the model API, as the coding agent may make many model API calls before getting back to the user;
- Applying an LLM to a proof task in a big project could cost much more than applying it to the same proof task extracted out of the project, as the LLM will inevitably explore the code base before settling down on the problem it should solve;
- More advanced models, naturally, cost more, sometimes much more. Based on our experience, it is possible to cost a few hundred dollars to generate a proof, sometimes incomplete, for just one function. Users may want to decompose a big proof task into smaller ones before using LLMs, and potentially set token limits for each run.
- The reasoning time varies a lot across different models. Claude Opus 4.5 noticeably takes much longer to generate proof annotations than Claude Sonnet 4.5. Some older models like GPT-5 seem to know their own limits and give up very easily, which could be an appealing feature depending on the usage scenario. Some models (e.g., Opus series models) tend to give Verus huge resource limits (e.g., 2000), via the --rlimit command-line option, for complicated proof tasks and hence wait for many hours for Verus to finish. Users should be aware of this trend and actively prompt the model to avoid doing this and to instead focus on breaking the proof into smaller steps.
- More advanced models sometimes fail to finish the whole proof after a lot of time and money spent, but can help shrink the proof target. This is not true for all models. It is good practice to urge models to output intermediate results and to explain their reasoning, so that it is possible for human experts to take over incomplete proofs.

**Note**: If cost is a major concern, consider:
- Starting with a cheaper model and escalating to more capable ones if needed
- Breaking complex proofs into smaller pieces first
- Prompting the model directly rather than via a generic coding agent (but this will entail a lot of manual work)

### When Models Struggle

LLMs tend to fail on:

1. **Inductive invariants**: Proving that a state machine maintains an invariant by finding a stronger inductive property is still difficult
2. **Procedural macro expansion**: Code generated by procedural macros may confuse models
3. **Heavy abstraction**: Proof writing is challenging when it requires understanding closed/opaque spec functions and selecting the right lemmas to reveal their properties
4. **Very large tasks**: Success correlates negatively with task size (lines of code)

## LLM Proofs May Be Verbose

Expect LLM-generated proofs to be longer than human-written ones; often 2–3× as long on average. This happens because:

1. LLMs don't always know what the theorem prover can handle automatically
2. They tend to add "safety" assertions that turn out to be unnecessary
3. They may use more explicit reasoning steps and care less about proof maintenance

**Example**: 
When we provided the following proof function to Sonnet 4.5, 
```rust
pub proof fn myseq_lemma<A>()
    ensures
        forall|s: Seq<A>, v: A, x: A| !s.contains(x) && v != x ==> !s.push(v).contains(x),
{
}
```

it came up with the following proof body:

```rust
    // Prove the postcondition: if s doesn't contain x and v != x, then s.push(v) doesn't contain x
    assert forall|s: Seq<A>, v: A, x: A| !s.contains(x) && v != x implies !s.push(v).contains(x) by {
        if !s.contains(x) && v != x {
            // Proof by contradiction: assume s.push(v) contains x
            if s.push(v).contains(x) {
                // Then there exists an index j where s.push(v)[j] == x
                let j = choose|j: int| 0 <= j < s.push(v).len() && s.push(v)[j] == x;

                // Case analysis on j
                if j < s.len() {
                    // By axiom_seq_push_index_different: s.push(v)[j] == s[j]
                    assert(s.push(v)[j] == s[j]);
                    // So s[j] == x, which means s contains x - contradiction!
                    assert(s.contains(x));
                    assert(false);
                } else if j == s.len() {
                    // By axiom_seq_push_index_same: s.push(v)[j] == v
                    assert(s.push(v)[j] == v);
                    // So v == x - contradiction with v != x!
                    assert(v == x);
                    assert(false);
                } else {
                    // j >= s.push(v).len(), which contradicts 0 <= j < s.push(v).len()
                    assert(false);
                }
                assert(false);
            }
        }
    };
```

There is nothing wrong with this, except that an empty proof would have worked just as well!

**This verbosity is usually harmless** for correctness but does increase:
- Token costs (more output = more money)
- Proof maintenance burden
- Verification time (slightly)

Users can try asking LLMs to clean up the proof annotations after the verification succeeds.


## LLMs as Collaborators

Of course, we do not have to let LLMs write all the proofs by themselves. LLMs work well as collaborators with human proof developers:

- **Starting from partial proofs**: A human proof developer can write a skeleton of a proof, and let an LLM complete all the detailed proof annotations. This is particularly helpful since LLMs are good at filling in the routine proof obligations which may be tedious for human proof developers
- **Adjusting lemma specification**: When human proof developers struggle with decomposing a big proof task into smaller lemmas, LLMs can be helpful in adjusting lemma specifications
- **Suggesting library usage**: When asked, LLMs are good at finding relevant `vstd` or project-specific lemmas that can be used to simplify proofs

For verified system development, an LLM is a powerful assistant but not a replacement for human judgment about design, specification, and proof architecture.

## Summary

| Best Practice | Why |
|--------------|-----|
| Use a coding agent | Enables the observe-adjust loop essential for proof development |
| Provide vstd access | Helps find lemmas and learn syntax |
| Let model run Verus | Error feedback is crucial for iterative refinement |
| Use a cheat checker | Prevents invalid proof shortcuts |
| Start with Sonnet 4.5 if budget allows | Highest success rate |
| Expect verbose proofs | LLMs over-explain; can be trimmed later |
| Human + LLM collaboration | Combine human insight with LLM thoroughness |

