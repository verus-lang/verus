#![no_main]

use libfuzzer_sys::fuzz_target;
use std::str;

fuzz_target!(|data: &[u8]| {
    let ..=299 = data.len() else { return };
    let Ok(string) = str::from_utf8(data) else {
        return;
    };
    let Ok(syntax_tree) = syn::parse_file(string) else {
        return;
    };
    let _ = prettyplease::unparse(&syntax_tree);
});
