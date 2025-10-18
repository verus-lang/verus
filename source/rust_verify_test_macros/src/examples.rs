use proc_macro::{Span, TokenStream};
use quote::quote;
use std::path::Path;

pub fn examples_in_dir(input: TokenStream) -> TokenStream {
    let arg = syn::parse_macro_input!(input as syn::LitStr);

    // relative to rust_verify
    let relative_path_string = arg.value();
    let relative_path = Path::new(&relative_path_string);
    let dir_underscores =
        relative_path_string.replace("../../", "").replace("/", "_").replace("-", "_");

    // relative to current working directory
    let dir_path = Path::new("rust_verify").join(Path::new(&relative_path));

    let entries = std::fs::read_dir(dir_path).expect("cannot find examples directory");

    let mut res = proc_macro2::TokenStream::new();

    for entry in entries {
        let entry = entry.expect("invalid path");
        let path = entry.path();

        if path.extension() != Some(std::ffi::OsStr::new("rs")) {
            continue;
        }

        let test_name = dir_underscores.clone()
            + "_"
            + &path.file_prefix().unwrap().to_str().unwrap().replace("-", "_");
        let test_name_ident = syn::Ident::new(&test_name, arg.span());

        // path to the file, relative to rust_verify/
        let file_name = path.file_name().unwrap();
        let path_to_file = relative_path.join(Path::new(file_name));
        let path_to_file_string = path_to_file.to_str().unwrap();

        res.extend(quote! {
            #[test]
            fn #test_name_ident() {
                run_example_for_file(#path_to_file_string);
            }
        });
    }

    res.into()
}

pub fn cargo_examples(input: TokenStream) -> TokenStream {
    let verified = syn::parse_macro_input!(input as syn::LitBool).value();
    let name = if verified { "verified" } else { "unverified" };

    // relative to current working directory
    let folder_path = Path::new("rust_verify_test/tests/cargo-tests/");
    let folder_path = folder_path.join(name);

    let entries = std::fs::read_dir(&folder_path).expect("cannot find cargo-tests directory");

    let mut res = proc_macro2::TokenStream::new();

    for entry in entries {
        let entry = entry.expect("invalid path");
        let path = entry.path();

        let test_name = name.to_string() + "_"
            + &path.file_prefix().unwrap().to_str().unwrap().replace("-", "_");
        let test_name_ident = syn::Ident::new(&test_name, Span::call_site().into());

        // path to the test directory, relative to folder_path
        let dir_name = path.file_name().unwrap();
        let path_to_dir = folder_path.join(Path::new(dir_name));
        let path_to_dir_string = path_to_dir.to_str().unwrap();

        if verified {
            res.extend(quote! {
                #[test]
                fn #test_name_ident() {
                    run_cargo_verus_for_dir(#path_to_dir_string);
                }
            });
        } else {
            res.extend(quote! {
                #[test]
                fn #test_name_ident() {
                    run_vanilla_cargo_for_dir(#path_to_dir_string);
                }
            });
        }
    }

    res.into()
}