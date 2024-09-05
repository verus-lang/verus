// ACKNOWLEDGEMENT: adapted from Mara Bos' (@m_ou_se) https://blog.m-ou.se/writing-python-inside-rust-2/

use proc_macro::TokenStream;

pub(crate) fn rust_code_core(input: TokenStream) -> String {
    let mut tokens = input.into_iter();
    let mut span = tokens.next().unwrap().span();
    while let Some(token) = tokens.next() {
        span = span.join(token.span()).unwrap();
    }

    if let Some(src) = span.source_text() {
        let n = span.start().column() - 1;
        let original_src = src;
        let mut src = String::new();
        let mut lines = original_src.lines();
        src += lines.next().unwrap();
        src += "\n";
        for line in lines {
            let (indent, line) = line.split_at(n.min(line.len()));
            assert!(!indent.contains(|c| c != ' '), "Invalid indentation");
            src += line;
            src += "\n";
        }
        src
    } else {
        "panic!(\"source_text() returned None\")".to_string()
    }
}
