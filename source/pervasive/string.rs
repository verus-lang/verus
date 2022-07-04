

#[verifier(external_body)]
pub struct String {
    inner: std::string::String,
}

#[verifier(external_body)]
pub struct StrSlice<'a> {
    inner: &'a str,
}

impl<'a> StrSlice<'a> {
    #[verifier(external_body)]
    pub fn new(s: &'a str) -> Self {
        Self { inner: s }
    }
}

