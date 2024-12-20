syn_dev::r#mod! {
    // Write Rust code here and run `cargo check` to have Syn parse it.

    pub assume_specification [foo::moo](&self, x: u8) -> (ret: u16)
        requires x == 5;

}
