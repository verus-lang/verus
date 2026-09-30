# Verus build/verification

To build vstd and run Verus verification with expanded error output, run:

```
source/tools/build-expand-errors.sh
```

This script `cd`s into `source/` and sources `../tools/activate` itself, then runs
`vargo build --release --vstd-expand-errors`. Do not manually run `../tools/activate`
or `chmod +x` on it beforehand — just invoke the script directly.
