# Meausuring verification performance

To see a more detailed breakdown of where Verus is spending time, you can pass
`--time` on the command line.  For even more details, try `--time-expanded`.
For a machine-readable output, add `--output-json`.  These flags will also
report on the SMT resources (rlimit) used.  SMT resources are an advanced topic;
they give a *very rough* estimate of how hard the SMT solver worked on the provided
query (or queries).

See `verus --help` for more information about these options.
