// TODO: Migrate to using the rustc_diagnostic_item instead of string 
// comparison for the identifier. We have a compiler guarantee this way 
// that what we are checking for is exactly equal, no such guarantee exists with a string
// comparision.

// #![feature(rustc_attrs)]

#[verifier(external_body)]
pub struct String {
    inner: std::string::String,
}

// #[rustc_diagnostic_item ="pervasive::string::StrSlice"]
#[verifier(external_body)]
pub struct StrSlice<'a> {
    inner: &'a str,
}

impl<'a> StrSlice<'a> {
    #[verifier(external_body)]
    pub fn new(s: &'a str, verify: bool) -> Self {
        Self { inner: s }
    }
}

