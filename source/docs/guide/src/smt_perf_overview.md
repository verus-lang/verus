# Managing proof performance and why it's critical

Sometimes your proof succeeds, but it takes too long. It's tempting to simply
tolerate the longer verification time and move on.  However, we urge you to
take the time to improve the verification performance.  Slow verification
performance typically has an underlying cause.  Diagnosing and fixing the cause
is much easier to do as the problems arise; waiting until you have multiple
performance problems compounds the challenges of diagnosis and repair.  Plus,
if the proof later breaks, you'll appreciate having a short code-prove
development cycle.  Keeping verification times short also makes it easier to
check for regressions.

This chapter describes various ways to measure the performance of your
proofs and steps you can take to improve it.
