# Implication (==&gt;, &lt;==, and &lt;==&gt;)

The operator `P ==> Q`, read _P implies Q_, is equivalent to `!P || Q`.

This can also be written backwards: `Q <== P` is equivalent to `P ==> Q`.

Finally, `P <==> Q` is equivalent to `P == Q`. It is sometimes useful for readability,
and because `<==>` has the same syntactic precedence as `==>`
rather than the precedence of `==`.
