#![no_main]

use libfuzzer_sys::fuzz_target;
use std::str;

fuzz_target!(|data: &[u8]| {
    if data.len() < 24 {
        if let Ok(string) = str::from_utf8(data) {
            let _ = syn::Lit::from_str_for_fuzzing(string);
        }
    }
});
