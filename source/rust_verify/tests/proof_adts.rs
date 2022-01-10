#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Error: #[verifier(unforgeable)] should be marked #[proof]

test_verify_one_file! {
    #[test] spec_unforgeable_err code! {
        #[verifier(unforgeable)]
        #[spec]
        struct X { // FAILS
          #[spec] pub u: int,
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] exec_unforgeable_err code! {
        #[verifier(unforgeable)]
        struct X { // FAILS
          #[spec] pub u: int,
        }
    } => Err(err) => assert_vir_error(err)
}

// The fields of a unforgeable datatype must be 'spec'

test_verify_one_file! {
    #[test] unforgeable_fields_must_be_spec1 code! {
        #[verifier(unforgeable)]
        #[proof]
        struct X { // FAILS
          pub u: int,
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] unforgeable_fields_must_be_spec2 code! {
        #[verifier(unforgeable)]
        #[proof]
        struct X { // FAILS
          #[proof] pub u: int,
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] unforgeable_ok code! {
        #[verifier(unforgeable)]
        #[proof]
        struct X { // FAILS
          #[spec] pub u: u8,
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unforgeable_cant_construct code! {
        #[verifier(unforgeable)]
        #[proof]
        struct X { // FAILS
          #[spec] pub u: u8,
        }

        pub fn X() {
          #[proof] let x = X{u: 8};
        }
    } => Err(err) => assert_vir_error(err)
}
