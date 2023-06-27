[![Quick Start](https://img.shields.io/badge/tutorial-quick%20start-informational)](https://verus-lang.github.io/verus/guide/getting_started.html) [![Library Documentation](https://img.shields.io/badge/docs-vstd-informational)](https://verus-lang.github.io/verus/verusdoc/vstd/)

Verus is a tool for verifying the correctness of code written in Rust.
Developers write specifications of what their code should do,
and Verus statically checks that the executable Rust code will always 
satisfy the specifications for all possible executions of the code.
Rather than adding run-time checks, Verus instead relies on powerful solvers to
prove the code is correct.  Verus currently supports a subset of Rust (which we
are working to expand), and in some cases, it allows developers to go beyond
the standard Rust type system and statically check the correctness of code
that, for example, manipulates raw pointers.  

![VS Code Demo](source/docs/verus-demo.png)

## Status

Verus is under *active development*. Features may be broken and/or missing, and
the documentation is still incomplete. If you want to try Verus, please be
prepared to ask for help by filing GitHub issues.

## Try Verus

To try Verus in your browser, please visit the [Verus Playground](https://play.verus-lang.org/).
For more involved development, please follow our [installation instructions](INSTALL.md).
Then you can dive into the documentation below, starting
with the [📖 Tutorial and reference](https://verus-lang.github.io/verus/guide/).

## Documentation
Our (work-in-progress) documentation resources include:
 * [📖 Tutorial and reference](https://verus-lang.github.io/verus/guide/)
 * [📖 API documentation for Verus's standard library](https://verus-lang.github.io/verus/verusdoc/vstd/)
 * [📖 Guide for verifying concurrent code](https://verus-lang.github.io/verus/state_machines/)
 * [Project Goals](../../wiki/Goals)
 * [Contributing to Verus](CONTRIBUTING.md)
 * [License](LICENSE)

## Reporting issues, and starting discussions

Thanks for contributing to Verus! Please report issues or start discussions here on GitHub.

We use GitHub discussions for feature requests and more open-ended conversations about
upcoming features, and we reserve GitHub issues for actionable issues (bugs) with
existing features. Don't worry though: if we think an issue should be a discussion (or
viceversa) we can always move it later.

We welcome contributions! If you'd like to contribute code, have a look at the tips in
[Contributing to Verus](CONTRIBUTING.md).
