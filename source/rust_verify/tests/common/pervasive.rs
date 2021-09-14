pub const LIB: &str = crate::common::code_str! {
    extern crate builtin;
    extern crate builtin_macros;
};

pub const PERVASIVE: &str = crate::common::code_str! {
    use builtin::*;

    #[proof]
    pub fn assume(b: bool) {
        ensures(b);

        admit();
    }

    #[proof]
    #[verifier(custom_req_err, "Assertion failure")]
    pub fn assert(b: bool) {
        requires(b);
        ensures(b);
    }

    #[proof]
    pub fn affirm(b: bool) {
        requires(b);
    }
};

pub const PERVASIVE_IMPORT_PRELUDE: &str = crate::common::code_str! {
    extern crate builtin;
    extern crate builtin_macros;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use builtin_macros::*;
    mod pervasive;
    #[allow(unused_imports)]
    use pervasive::*;
};
