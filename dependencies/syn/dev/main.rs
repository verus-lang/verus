syn_dev::r#mod! {
    // Write Rust code here and run `cargo check` to have Syn parse it.

    pub proof fn foo()
        opens_invariants any
    {
    }

    pub proof fn foo2()
        requires true,
        opens_invariants none
    {
    }

    pub proof fn foo2()
        opens_invariants none
    {
    }

    pub proof fn foo3()
    {
    }
}
