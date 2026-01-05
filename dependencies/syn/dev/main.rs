syn_dev::r#mod! {
    // Write Rust code here and run `cargo check` to have Syn parse it.

    fn t() {
        let x = &mut y;
        let x = &mut exec y;
        let x = &mut tracked y;
    }
}
