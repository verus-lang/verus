# Spec fn signature

The general form of a `spec` function signature takes the form:

<pre>
<code class="hljs">spec fn <span style="color: #800000; font-style: italic">function_name</span> <span style="color: #800000; font-style: italic">generics</span><sup>?</sup>(<span style="color: #800000; font-style: italic">args...</span>) -&gt; <span style="color: #800000; font-style: italic">return_type</span><sup>?</sup>
    <span style="color: #800000; font-style: italic">where_clause</span><sup>?</sup>
    <span style="color: #000080; font-style: italic">recommends_clause</span><sup>?</sup>
    <span style="color: #000080; font-style: italic">decreases_clause</span><sup>?</sup>
</code>
</pre>

## The `recommends` clause

The `recommends` clauses is a "soft precondition", which is sometimes checked for the sake
of diagnostics, but is not a hard requirement for the function to be well-defined.

See [this guide page](./spec_vs_proof.md#recommends) for motivation and overview.

## The `decreases` clause

The `decreases` clause is used to ensure that recursive definitions are well-formed.
Note that if the `decreases` clauses has a `when`-subclause, it will restrict the function definition
to the domain.

See [the reference page for `decreases`](./reference-decreases.md) for more information,
or see [the guide page on recursive functions](./recursion.md) for motivation and overview.
