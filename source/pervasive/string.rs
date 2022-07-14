#![feature(rustc_attrs)]

#[verifier(external_body)]
pub struct String {
    inner: std::string::String,
}

#[rustc_diagnostic_item = "pervasive::string::StrSlice"]
#[verifier(external_body)]
pub struct StrSlice<'a> {
    inner: &'a str,
}

impl<'a> StrSlice<'a> {
    #[rustc_diagnostic_item = "pervasive::string::StrSlice::new"]
    #[verifier(external_body)]
    pub const fn new(s: &'a str) -> Self {
        Self { inner: s }
    }

    #[rustc_diagnostic_item = "pervasive::string::StrSlice::reveal"]
    #[verifier(external_body)]
    pub const fn reveal(&self) {}
}
