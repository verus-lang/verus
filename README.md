![Quick Start](https://img.shields.io/badge/tutorial-quick%20start-informational?link=https://verus-lang.github.io/verus/guide/getting_started.html) ![Library Documentation](https://img.shields.io/badge/docs-vstd-informational?link=https://verus-lang.github.io/verus/verusdoc/lib/)

Verus is a tool for verifying the correctness of code written in Rust.
Developers write specifications of what their code should do,
and Verus statically checks that the executable Rust code will always 
satisfy the specifications for all possible executions of the code.
Rather than adding run-time checks, Verus instead relies on powerful solvers to
prove the code is correct.  Furthermore, Verus allows developers to go beyond
the standard Rust type system and statically check the correctness of code that,
for example, manipulates [raw pointers](https://verus-lang.github.io/verus/state_machines/examples/rc.html).

![VS Code Demo](source/docs/verus-demo.gif)

Verus supports a large and growing [set of Rust features](https://verus-lang.github.io/verus/guide/features.html).  It also includes support for [user-defined specifications](https://verus-lang.github.io/verus/guide/spec_functions.html), which can be written in terms of pre-eixsting [specification libraries](https://verus-lang.github.io/verus/guide/spec_lib.html).

# Try Verus

Please follow our [installation instructions](INSTALL.md).

# Documentation
Our (work-in-progress) documentation resources include:
 * [Project Goals](../../wiki/Goals)
 * [📖 Tutorial and reference](https://verus-lang.github.io/verus/guide/)
 * [📖 API documentation for Verus's standard library](https://verus-lang.github.io/verus/verusdoc/lib/)
 * [📖 Guide for verifying concurrent code](https://verus-lang.github.io/verus/state_machines/)
 * [📖 Contributing to Verus](CONTRIBUTING.md)
 * [License](LICENSE)
