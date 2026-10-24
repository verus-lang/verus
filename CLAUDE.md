# Verus build/verification

To build vstd and run Verus verification with expanded error output, run:

```
source/tools/build-expand-errors.sh
```

This script `cd`s into `source/` and sources `../tools/activate` itself, then runs
`vargo build --release --vstd-expand-errors`. Do not manually run `../tools/activate`
or `chmod +x` on it beforehand — just invoke the script directly.

# Bash commands: avoid approval prompts where possible

Some commands will need the user's approval, and that's fine. But whenever a way exists
to do something without a prompt, use it: prefer a single, simple command that matches
an allow rule in `.claude/settings.local.json`, or a dedicated tool. In particular:

- One command per call. No `;`, `&&`, `||`, pipes (`|`), `cd ... &&`, `git -C`,
  shell variables, heredocs, or `$(...)`. Use absolute paths instead of `cd`.
  Several independent commands go in several parallel Bash calls.
- Read files with the Read tool (offset/limit), not `cat`/`head`/`tail`/`sed`.
- Edit files with Edit/Write, never with `sed -i`, `perl -i`, or Python scripts.
- Search with a plain `grep -n ...` (allowed); list with plain `ls` or `wc -l`.
- Run a build wrapper exactly as `source/tools/build-expand-errors.sh`, alone,
  with no redirection or extra arguments (the allow rule is an exact match).
- For an old version of a file: `git show HEAD:path`, alone, then read the output.
