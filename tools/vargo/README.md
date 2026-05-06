A tool to build `verus`.

It acts as a `cargo` shim layer, with a subset of `cargo` commands available.


Currently supported commands (as reported by `vargo help`).
In most cases, cargo flags also apply to vargo.
```
Usage: vargo [OPTIONS] <COMMAND>

Commands:
  build     Build Verus
  clean     Clean current build
  cmd       Run an arbitrary command in vargo's environment
  fmt       Run the formatter on the codebase
  metadata  Get metadata from cargo
  nextest   Run Verus tests with nextest
  run       Run a binary package
  test      Run Verus tests
  update    Update dependencies
  help      Print this message or the help of the given subcommand(s)

Options:
      --offline                  Run without accessing the network
  -v, --verbose...               Use verbose output
      --color <COLOR>            Coloring [default: auto] [possible values: always, auto, never]
      --vargo-verbose            Turn on `vargo`s verbose logging
      --no-solver-version-check  Skip checking that the server's solver version is correct
  -h, --help                     Print help
```
