#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] set_axiom_01 verus_code! {
        use vstd::set::*;
        // This verified lemma used to be an axiom in the Dafny prelude
        /// If set `s` already contains element `a`, the inserting `a` into `s` does not change the length of `s`.
        pub proof fn lemma_set_insert_same_len<A>(s: Set<A>, a: A)
            requires
                s.finite(),
            ensures
                s.contains(a) ==> s.insert(a).len() =~= s.len(),
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] set_axiom_02 verus_code! {
        use vstd::set::*;
        // This verified lemma used to be an axiom in the Dafny prelude
        /// If set `s` does not contain element `a`, then inserting `a` into `s` increases the length of `s` by 1.
        pub proof fn lemma_set_insert_diff_len<A>(s: Set<A>, a: A)
            requires
                s.finite(),
            ensures
                !s.contains(a) ==> s.insert(a).len() == s.len() + 1,
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] set_axiom_03 verus_code! {
        use vstd::set::*;
        // This verified lemma used to be an axiom in the Dafny prelude
        /// If set `s` contains element `a`, then removing `a` from `s` decreases the length of `s` by 1.
        /// If set `s` does not contain element `a`, then removing `a` from `s` does not change the length of `s`.
        pub proof fn lemma_set_remove_len_contains<A>(s: Set<A>, a: A)
            requires
                s.finite(),
            ensures
                (s.contains(a) ==> (s.remove(a).len() == s.len() -1))
                    && (!s.contains(a) ==> s.len() == s.remove(a).len()),
        {}
    } => Ok(())
}
