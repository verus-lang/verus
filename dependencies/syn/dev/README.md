A little project skeleton for troubleshooting Syn's parsers during development,
especially when adding support for new Rust syntax.

Place a sample of the syntax you are working on into main.rs and then run `cargo
check` to try parsing it, revealing the resulting syntax tree or else showing
the position and error message if the input fails to parse.
