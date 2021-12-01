#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

#[test]
fn verify_pervasive() {
    let files = vec![(
        "test.rs".to_string(),
        code! {
            mod pervasive;
            #[allow(unused_import)]
            use pervasive::*;
        },
    )];
    let result = verify_files_and_pervasive(files, "test.rs".to_string(), true);
    assert!(result.is_ok());
}
