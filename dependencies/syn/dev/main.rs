syn_dev::r#mod! {
    // Write Rust code here and run `cargo check` to have Syn parse it.

    pub proof fn foo<T: FnOnce(u8) -> ()>()
    {
    }

    pub proof fn foo2(f: fn(u8) -> ())
    {
    }

    pub proof fn foo<T: FnOnce(u8) -> ()>()
        -> (stuff: u8)
    {
    }

    pub proof fn foo<T: FnOnce(u8) -> ()>()
        -> (stuff: ::Blah)
    {
    }

    pub proof fn foo<T: FnOnce(u8) -> ()>()
        -> ((stuff): ::Blah)
    {
    }



}
