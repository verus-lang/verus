The `record-history` feature records every invocation of Verus with the current source of the crate it was invoked on, and the Verus verification results and outputs.

To enable, re-build vargo, then compile Verus with `--features record-history`:

```
vargo build --release --features record-history
```

Then you need a per-project opt-in.
To opt-in place an empty directory named `.record-history` in the same directory as the file that acts as the crate root. That is, if you normally run Verus as

```
verus path/to/foo.rs
```

Add an empty folder named `path/to/.record-history`.

The next time Verus is run, it will create `path/to/.record-history/git`, which will contain a bare repo with the recordings.