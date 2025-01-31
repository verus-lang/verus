#[cfg(debug_assertions)]
build_alert::yellow! {"
NOTE:  use --release
  Syn's test suite has some tests that run on every source file
  and test case in the rust-lang/rust repo, which can be pretty
  slow in debug mode. Consider running cargo test with `--release`
  to speed things up.
"}

#[cfg(not(feature = "all-features"))]
build_alert::red! {"
ERROR:  use --all-features
  Syn's test suite normally only works with all-features enabled.
  Run again with `--all-features`, or run with `--features test`
  to bypass this check.
"}
