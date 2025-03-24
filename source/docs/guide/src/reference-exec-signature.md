# Exec fn signature

The general form of an `exec` function signature takes the form:

<pre>
<code class="hljs">fn <span style="color: #800000; font-style: italic">function_name</span> <span style="color: #800000; font-style: italic">generics</span><sup>?</sup>(<span style="color: #800000; font-style: italic">args...</span>) -&gt; <span style="color: #800000; font-style: italic">return_type_and_name</span><sup>?</sup>
    <span style="color: #800000; font-style: italic">where_clause</span><sup>?</sup>
    <span style="color: #000080; font-style: italic">requires_clause</span><sup>?</sup>
    <span style="color: #000080; font-style: italic">ensures_clause</span><sup>?</sup>
    <span style="color: #000080; font-style: italic">returns_clause</span><sup>?</sup>
    <span style="color: #000080; font-style: italic">invariants_clause</span><sup>?</sup>
    <span style="color: #000080; font-style: italic">unwind_clause</span><sup>?</sup>
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
For exec functions, the default is `open_invariants any`.
See [this page](./reference-opens-invariants.md) for more details.

**Unwinding.**
The <code class="hljs"><span style="color: #000080; font-style: italic">unwind_clause</span></code> specifies whether the function might exit "abnormally" by unwinding,
and under what conditions that can happen.
See [this page](./reference-unwind-sig.md) for more details.

## Function arguments

All arguments and return values need to have `exec` mode. To embed ghost/tracked variables into the signature, use the `Tracked` and `Ghost` types.

See [here](./reference-var-modes.md#cheat-sheet) for more information.
