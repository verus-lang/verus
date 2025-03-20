# Proof fn signature

The general form of a `proof` function signature takes the form:

<pre>
<code class="hljs">proof fn <span style="color: #800000; font-style: italic">function_name</span> <span style="color: #800000; font-style: italic">generics</span><sup>?</sup>(<span style="color: #800000; font-style: italic">args...</span>) -&gt; <span style="color: #800000; font-style: italic">return_type_and_name</span><sup>?</sup>
    <span style="color: #800000; font-style: italic">where_clause</span><sup>?</sup>
    <span style="color: #000080; font-style: italic">requires_clause</span><sup>?</sup>
    <span style="color: #000080; font-style: italic">ensures_clause</span><sup>?</sup>
    <span style="color: #000080; font-style: italic">returns_clause</span><sup>?</sup>
    <span style="color: #000080; font-style: italic">invariants_clause</span><sup>?</sup>
</code>
</pre>

## Function specification

The elements of the function specification are given by the signature clauses.

**The precondition.**
The <code class="hljs"><span style="color: #000080; font-style: italic">requires_clause</span></code> is the precondition.

**The postcondition.**
The <code class="hljs"><span style="color: #000080; font-style: italic">ensures_clause</span></code>
and the
<code class="hljs"><span style="color: #000080; font-style: italic">returns_clause</span></code>
together form the postcondition.

**The invariants.**
The <code class="hljs"><span style="color: #000080; font-style: italic">invariants_clause</span></code> specifies what invariants can be opened by the function.
For proof functions, the default is `open_invariants none`.
See [this page](./reference-opens-invariants.md) for more details.

## Function arguments

All arguments and return values need to have `ghost` or `tracked` mode.
Arguments are `ghost` by default, and they can be declared `tracked` with the `tracked` keyword.

See [here](./reference-var-modes.md#cheat-sheet) for more information.
