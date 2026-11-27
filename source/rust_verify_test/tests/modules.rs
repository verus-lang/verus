#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const M1: &str = verus_code_str! {
    mod M1 {
        #[derive(PartialEq, Eq)]
        pub struct Car {
            pub four_doors: bool,
        }

        pub open spec fn is_four_doors(c: Car) -> bool {
            c.four_doors
        }
    }
};

test_verify_one_file! {
    #[test] test_mod_adt_0 M1.to_string() + verus_code_str! {
        mod M2 {
            use crate::M1::Car;
            use verus_builtin::*;

            fn mod_adt_0() {
                assert(!Car { four_doors: false }.four_doors);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mod_adt_1 M1.to_string() + verus_code_str! {
        mod M2 {
            use crate::M1::{is_four_doors, Car};
            use verus_builtin::*;

            fn test() {
                let c = Car { four_doors: true };
                assert(is_four_doors(c));
            }
        }
    } => Ok(())
}

const M1_OPAQUE: &str = verus_code_str! {
    mod M1 {
        #[derive(PartialEq, Eq)]
        pub struct Car {
            pub four_doors: bool,
        }

        #[verifier(opaque_outside_module)] /* vattr */
        pub open spec fn is_four_doors(c: Car) -> bool {
            c.four_doors
        }
    }
};

test_verify_one_file! {
    #[test] test_mod_fn_publish_opaque_no_reveal M1_OPAQUE.to_string() + verus_code_str! {
        mod M2 {
            use crate::M1::{is_four_doors, Car};
            use verus_builtin::*;

            fn test() {
                let c = Car { four_doors: true };
                assert(is_four_doors(c)); // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_mod_fn_publish_opaque_reveal M1_OPAQUE.to_string() + verus_code_str! {
        mod M2 {
            use crate::M1::{is_four_doors, Car};
            use verus_builtin::*;

            fn test() {
                let c = Car { four_doors: true };
                proof {
                    reveal(is_four_doors);
                }
                assert(is_four_doors(c));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mod_adt_no_verify verus_code! {
        #[verifier(external_body)] /* vattr */
        #[derive(PartialEq, Eq)]
        pub struct Car {
            pub four_doors: bool,
        }

        fn mod_adt_no_verify() {
            assert(!Car { four_doors: false }.four_doors);
        }
    } => Err(err) => assert_vir_error_msg(err, "disallowed: field expression for an opaque datatype")
}

test_verify_one_file! {
    #[test] test_mod_child_ok verus_code! {
        spec fn f() -> bool {
            true
        }

        mod M1 {
            fn test()
                ensures crate::f()
            {
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mod_sibling_fail verus_code! {
        mod M0 {
            pub closed spec fn f() -> bool {
                true
            }
        }

        mod M1 {
            fn test()
                ensures crate::M0::f() // FAILS
            {
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_requires_private verus_code! {
        mod M1 {
            spec fn f() -> bool { true }

            pub fn g()
                requires f()
            {
            }
        }

        mod M2 {
            fn h() {
                crate::M1::g();
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "in `requires` clause of public function, cannot refer to private function")
}

test_verify_one_file! {
    #[test] test_publish_but_not_marked_pub verus_code! {
        open spec fn bar() -> u64 {
            7
        }
    } => Err(err) => assert_vir_error_msg(err, "function is marked `open` but not marked `pub`")
}

test_verify_one_file! {
    #[test] publish_proof_fail verus_code! {
        pub open proof fn bar() {
        }
    } => Err(err) => assert_vir_error_msg(err, "only `spec` functions can be marked `open`, `closed`, or `uninterp`")
}

test_verify_one_file! {
    #[test] publish_exec_fail verus_code! {
        pub open fn bar() {
        }
    } => Err(err) => assert_vir_error_msg(err, "only `spec` functions can be marked `open`, `closed`, or `uninterp`")
}

test_verify_one_file! {
    #[test] main_proof_fail verus_code! {
        pub proof fn main() {
        }
    } => Err(err) => assert_vir_error_msg(err, "`main` function must be `exec`")
}

test_verify_one_file! {
    #[test] main_spec_fail verus_code! {
        pub closed spec fn main() {
            ()
        }
    } => Err(err) => assert_vir_error_msg(err, "`main` function must be `exec`")
}

test_verify_one_file! {
    #[test] open_fn_refers_to_private_const_fail verus_code! {
        mod A {
            spec const X: usize = 1;
            pub open spec fn f() -> usize {
                X
            }
        }

        mod B {
            use crate::A;
            pub open spec fn g() -> bool {
                A::f() == 1
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "in pub open spec function, cannot refer to private const")
}

test_verify_one_file! {
    #[test] open_qualified_refers_to_private verus_code! {
        mod m {
            pub mod n {
                use verus_builtin::*;

                spec fn stuff() -> bool { true }

                pub open(in crate::m) spec fn foo() -> bool {
                    stuff()
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "in pub open spec function, cannot refer to private function")
}

test_verify_one_file! {
    #[test] open_crate verus_code! {
        mod m {
            pub mod n {
                use verus_builtin::*;

                pub open(crate) spec fn foo() -> bool {
                    true
                }

                proof fn test() {
                    assert(foo() == true);
                }
            }

            proof fn test2() {
                assert(n::foo() == true);
            }
        }

        proof fn test3() {
            assert(m::n::foo() == true);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] open_super verus_code! {
        mod m {
            pub mod n {
                use verus_builtin::*;

                pub open(super) spec fn foo() -> bool {
                    true
                }

                proof fn test() {
                    assert(foo() == true);
                }
            }

            proof fn test2() {
                assert(n::foo() == true);
            }
        }

        proof fn test3() {
            assert(m::n::foo() == true); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] open_path verus_code! {
        mod m {
            pub mod n {
                use verus_builtin::*;

                pub open(in crate::m) spec fn foo() -> bool {
                    true
                }

                proof fn test() {
                    assert(foo() == true);
                }
            }

            proof fn test2() {
                assert(n::foo() == true);
            }
        }

        proof fn test3() {
            assert(m::n::foo() == true); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] open_more_public_than_function verus_code! {
        mod m {
            pub mod n {
                use verus_builtin::*;

                pub(in crate::m) open(crate) spec fn foo() -> bool {
                    true
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "the function body is declared `open` to a wider scope than the function itself")
}

test_verify_one_file! {
    #[test] uninterp_exec_fail verus_code! {
        pub uninterp fn bar() {
        }
    } => Err(err) => assert_vir_error_msg(err, "only `spec` functions can be marked `open`, `closed`, or `uninterp`")
}

test_verify_one_file! {
    #[test] uninterp_spec_body_free_fail verus_code! {
        pub uninterp spec fn bar() -> bool {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "function is marked `uninterp` but it has a body")
}

test_verify_one_file! {
    #[test] uninterp_spec_body_assoc_fail verus_code! {
        struct G {
            v: bool,
        }

        impl G {
            pub uninterp spec fn bar(&self) -> bool {
                self.v
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "function is marked `uninterp` but it has a body")
}

test_verify_one_file! {
    #[test] uninterp_spec_body_trait_fail verus_code! {
        trait T {
            uninterp spec fn bar(&self) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "function is marked `uninterp` but it has a body")
}

test_verify_one_file! {
    #[test] uninterp_spec_body_trait_impl_fail verus_code! {
        trait T {
            uninterp spec fn bar(&self) -> bool;

            #[verifier::external_body]
            proof fn a(&self)
                ensures self.bar()
            {
            }
        }

        impl T for bool {
            spec fn bar(&self) -> bool { // this should be rejected
                *self
            }
        }

        proof fn a() {
            let t = false;
            t.a();
            assert(t.bar());
        }
    } => Err(err) => assert_vir_error_msg(err, "trait method implementation cannot be marked as `uninterp`")
}

test_verify_one_file! {
    // TODO reject this code
    #[ignore] #[test] closed_spec_trait_fail verus_code! {
        trait T {
            closed spec fn bar(&self) -> bool {
                true
            }
        }
    } => Err(_err) => todo!()
}

test_verify_one_file! {
    #[ignore] #[test] uninterp_spec_fn_warning verus_code! {
        spec fn bar(i: nat) -> bool;
    } => Ok(err) => {
        assert!(err.errors.is_empty());
        assert!(err.warnings.iter().find(|w| w.message.contains("uninterpreted functions")).iter().next().is_some());
    }
}

test_verify_one_file! {
    #[test] uninterp_open_fail verus_code! {
        pub uninterp open fn bar();
    } => Err(err) => assert_vir_error_msg(err, "expected `fn`")
}
// Cross-module recursive spec functions and decreases checks.
// These tests exercise verification outcomes; SST structure needs separate validation.
test_verify_one_file! {
    #[test] cross_module_recursive_open_spec_visible verus_code! {
        mod A {
            use verus_builtin::{nat, SpecAdd, SpecSub};

            pub open spec fn count(n: nat) -> nat
                decreases n
            {
                if n == 0 { 0 } else { 1 + count((n - 1) as nat) }
            }
        }

        mod B {
            use crate::A::count;

            proof fn check() {
                assert(count(0) == 0);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] cross_module_recursive_closed_spec_hidden verus_code! {
        mod A {
            use verus_builtin::{nat, SpecAdd, SpecSub};

            pub closed spec fn count(n: nat) -> nat
                decreases n
            {
                if n == 0 { 0 } else { 1 + count((n - 1) as nat) }
            }
        }

        mod B {
            use crate::A::count;

            proof fn check() {
                assert(count(0) == 0); // FAILS: sibling cannot unfold a closed spec.
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cross_module_recursive_invalid_decrease_rejected verus_code! {
        mod A {
            use verus_builtin::{nat, SpecAdd, SpecSub};

            pub open spec fn count(n: nat) -> nat
                decreases n
            {
                count(n) // FAILS: recursion does not decrease.
            }
        }

        mod B {
            use crate::A::count;

            proof fn check() {
                let _observed = count(0);
            }
        }
    } => Err(err) => assert_one_fails(err)
}

// A private decreases_by proof is checked in the defining module.
test_verify_one_file! {
    #[test] cross_module_recursive_decreases_by verus_code! {
        mod A {
            use verus_builtin::{nat, SpecAdd, SpecSub};
            use verus_builtin::decreases_by;

            pub open spec fn count(n: nat) -> nat
                decreases n
            {
                decreases_by(check_count);
                if n == 0 { 0 } else { 1 + count((n - 1) as nat) }
            }

            #[verifier(decreases_by)]
            proof fn check_count(n: nat) {
            }
        }

        mod B {
            use crate::A::count;

            proof fn check() {
                assert(count(0) == 0);
            }
        }
    } => Ok(())
}

// A recursive SCC spanning two modules must verify in both owning buckets.
test_verify_one_file! {
    #[test] cross_module_mutual_recursive_decrease verus_code! {
        mod A {
            use verus_builtin::{nat, SpecAdd, SpecSub};

            pub open spec fn even(n: nat) -> nat
                decreases n
            {
                if n == 0 { 0 } else { crate::B::odd((n - 1) as nat) }
            }
        }

        mod B {
            use verus_builtin::{nat, SpecAdd, SpecSub};

            pub open spec fn odd(n: nat) -> nat
                decreases n
            {
                if n == 0 { 0 } else { crate::A::even((n - 1) as nat) }
            }
        }

        mod C {
            use crate::A::even;

            proof fn check() {
                assert(even(0) == 0);
            }
        }
    } => Ok(())
}

// Check the exported SST directly. Verification verdict tests alone pass on
// unmodified Verus and do not establish the cross-bucket export contract.
#[test]
fn cross_module_recursive_sst_export_preserves_ownership() {
    let temp = tempfile::tempdir().expect("temporary SST log directory");
    let test_name = "cross_module_recursive_sst_export_preserves_ownership";
    let log_dir = if let Some(root) = std::env::var_os("VERUS_TEST_LOG_DIR") {
        let binary = std::env::current_exe()
            .expect("test executable")
            .file_name()
            .expect("test binary name")
            .to_string_lossy()
            .into_owned();
        let binary = match binary.rsplit_once('-') {
            Some((stem, hash)) if hash.chars().all(|c| c.is_ascii_hexdigit()) => stem,
            _ => binary.as_str(),
        };
        std::path::PathBuf::from(root).join(binary).join(test_name).join("log")
    } else {
        let dir = temp.path().join("log");
        std::fs::create_dir(&dir).expect("create SST log directory");
        THREAD_LOCAL_TEST_LOG_DIR.with(|slot| *slot.borrow_mut() = Some(dir.clone()));
        dir
    };

    let source = verus_code! {
        mod A {
            use verus_builtin::{nat, SpecAdd, SpecSub};

            pub open spec fn count(n: nat) -> nat
                decreases n
            {
                if n == 0 { 0 } else { 1 + count((n - 1) as nat) }
            }
        }

        mod B {
            use crate::A::count;

            proof fn check() {
                assert(count(0) == 0);
            }
        }
    };
    let result = verify_one_file(test_name, source, &[]);
    assert!(result.is_ok(), "native verification failed: {:?}", result);

    for (bucket, owning) in [("A", true), ("B", false)] {
        let file = log_dir.join(format!("t%{bucket}-sst.vir"));
        let sst = std::fs::read_to_string(&file)
            .unwrap_or_else(|e| panic!("missing SST at {}: {}", file.display(), e));
        let implicit = ":kind (PostConditionKind DecreasesImplicitLemma)";
        assert_eq!(sst.matches(implicit).count(), 1, "SST: {}", file.display());
        let owner_flag = format!(":verify_termination_in_this_bucket {owning}");
        assert!(sst.contains(&owner_flag), "incorrect owner provenance in {}", file.display());
    }
}
