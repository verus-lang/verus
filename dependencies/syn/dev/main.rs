syn_dev::r#mod! {
    // Write Rust code here and run `cargo check` to have Syn parse it.

    pub fn foo<T: FnOnce(u8) -> ()>()
        no_unwind when i >= 0
    {
    }


    pub fn foo<T: FnOnce(u8) -> ()>()
        no_unwind
    {
    }

}
