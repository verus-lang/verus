pub const PERVASIVE: &str = crate::common::code_str! {
    extern crate builtin;
    use builtin::*;

    #[proof]
    pub fn assume(b: bool) {
        ensures(b);

        admit();
    }

    #[proof]
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
    use builtin::*;
    mod pervasive;
    use pervasive::*;
};
