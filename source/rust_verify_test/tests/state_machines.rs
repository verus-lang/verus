#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    #[allow(unused_imports)] use vstd::{atomic::*};
    #[allow(unused_imports)] use vstd::{modes::*};
    #[allow(unused_imports)] use vstd::prelude::*;
    #[allow(unused_imports)] use vstd::imap::*;
    #[allow(unused_imports)] use vstd::map::*;
    #[allow(unused_imports)] use vstd::set::*;
    #[allow(unused_imports)] use vstd::multiset::*;
    #[allow(unused_imports)] use vstd::pervasive::*;
    #[allow(unused_imports)] use verus_builtin::*;
    #[allow(unused_imports)] use verus_builtin_macros::*;
    #[allow(unused_imports)] use verus_state_machines_macros::*;
    // With `--cfg verus_verified_tsm` (test_verify_tsm!'s `verified` run, or VERUS_TSM=verified)
    // these explicit imports shadow the glob-imported trusted macros.
    #[cfg(verus_verified_tsm)] #[allow(unused_imports)]
    use verus_state_machines_macros::verified_tokenized_state_machine as tokenized_state_machine;
    #[cfg(verus_verified_tsm)] #[allow(unused_imports)]
    use verus_state_machines_macros::verified_state_machine_model as state_machine;

    verus!{

    pub ghost enum Foo {
        Bar(int),
        Qax(int),
        Duck(int),
    }

    }
};

test_verify_tsm! {
    #[test] dupe_name_fail IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub v: IMap<int, int>,
            }

            transition!{
                some_name() {
                }
            }

            transition!{
                some_name() {
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "duplicate item name")
}

test_verify_tsm! {
    #[test] test_birds_eye_init_error IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields { #[sharding(variable)] pub t: int }

            init!{
                initialize() {
                    birds_eye let x = 5; // error
                    init t = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "`birds_eye` has no effect in an init!")
}

test_verify_tsm! {
    #[test] test_birds_eye_nontokenized_error IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields { pub t: int }

            transition!{
                tr() {
                    birds_eye let x = 5; // error
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "`birds_eye` only makes sense for tokenized state machines")
}

test_verify_one_file_with_options! {
    #[test] test_custom_err_on_subexpression_is_inert ["--expand-errors"] => verus_code! {
        spec fn custom_requires(a: bool, b: bool) -> bool {
            (#[verifier::custom_err("Custom error on subexpression")] a) && b
        }

        fn caller() {
            assert(custom_requires(1 == 2, true));
        }
    } => Err(err) => {
        assert!(err.errors[0].message.contains("assertion failed"));
        assert!(!err.errors.iter().any(|diag| {
            diag.message.contains("Custom error on subexpression")
                || diag.rendered.contains("Custom error on subexpression")
        }));
    }
}

test_verify_tsm_with_options! {
    #[test] test_state_machine_req_custom_err_is_inert ["--expand-errors"] => IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub i: int,
            }

            transition!{
                tr() {
                    require(pre.i > 0);
                    update i = pre.i + 1;
                }
            }
        }}

        proof fn assert_tr() {
            let pre = X::State { i: 0 };
            let post = X::State { i: 1 };
            X::show::tr(pre, post);
            assert(X::State::tr(pre, post));
        }
    } => Err(err) => {
        assert!(err.errors[0].message.contains("precondition not satisfied"));
        assert!(err.errors[1].message.contains("assertion failed"));
        assert!(!err.errors.iter().any(|diag| {
            diag.message.contains("cannot prove this condition holds")
                || diag.rendered.contains("cannot prove this condition holds")
        }));
    }
}

test_verify_tsm! {
    #[test] test_birds_eye_guard IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            property!{
                tr() {
                    birds_eye let x = 5;
                    guard so >= Some(x); // error: guard depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "a guard value must be a deterministic function")
}

test_verify_tsm! {
    #[test] test_withdraw_bind_guard IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            property!{
                tr() {
                    withdraw so -= Some(let y);
                    guard so >= Some(x); // error: guard depends on withdraw binding
                }
            }
        }}
    } => Err(e) => assert_any_vir_error_msg(e, "a guard value must be a deterministic function")
}

test_verify_tsm! {
    #[test] test_birds_eye_req IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            property!{
                tr() {
                    birds_eye let x = 5;
                    require(x == 5); // error: require depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'require' statements should not be in the scope of a `birds_eye` let-binding")
}

test_verify_tsm! {
    #[test] require_let_birds_eye_fail IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(variable)]
                pub opt: Option<int>,
            }

            transition!{
                tr1() {
                    require birds_eye let x = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'require' statements should not be in the scope of a `birds_eye` let-binding")
}

test_verify_tsm! {
    #[test] test_withdraw_bind_req IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            property!{
                tr() {
                    withdraw so -= Some(let x);
                    require(x == 5); // error: require depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_any_vir_error_msg(e, "'require' statements should not be in the scope of a `withdraw` let-binding")
}

test_verify_tsm! {
    #[test] test_birds_eye_req2 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            property!{
                tr() {
                    if 0 == 0 {
                        birds_eye let x = 5;
                        assert(x == 5);
                    }
                    require(x == 5); // error: require depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'require' statements should not be preceeded by an assert which is in the scope of")
}

test_verify_tsm! {
    #[test] test_withdraw_bind_req2 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            transition!{
                tr() {
                    if 0 == 0 {
                        withdraw so -= Some(let x);
                        assert(x == 5);
                    }
                    require(x == 5); // error: require depends on withdraw binding
                }
            }
        }}
    } => Err(e) => assert_any_vir_error_msg(e, "'require' statements should not be preceeded by an assert which is in the scope of")
}

test_verify_tsm! {
    #[test] test_birds_eye_special IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)] pub so: Option<int>
            }

            transition!{
                tr() {
                    birds_eye let x = 5;
                    remove so -= Some(x); // error: depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'remove' statements should not be in the scope of a `birds_eye` let-binding")
}

test_verify_tsm! {
    #[test] test_withdraw_binding_remove IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)] pub so: Option<int>
            }

            transition!{
                tr() {
                    withdraw so -= Some(let x);
                    remove so -= Some(x); // error: depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_any_vir_error_msg(e, "'remove' statements should not be in the scope of a `withdraw` let-binding")
}

test_verify_tsm! {
    #[test] test_birds_eye_special2 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)] pub so: Option<int>
            }

            transition!{
                tr() {
                    if 0 == 0 {
                        birds_eye let x = 5;
                        assert(x == 5);
                    }
                    remove so -= Some(0); // error: depends on birds_eye variable
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'remove' statements should not be preceeded by an assert which is in the scope of")
}

test_verify_tsm! {
    #[test] test_update_constant IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(constant)] pub t: int
            }

            transition!{
                tr() {
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'update' statement not allowed for field with sharding strategy 'constant'")
}

test_verify_tsm! {
    #[test] test_add_constant IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(constant)] pub t: int
            }

            transition!{
                tr() {
                    add t += (5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'add' statement not allowed for field with sharding strategy 'constant'")
}

test_verify_tsm! {
    #[test] test_have_constant IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(constant)] pub t: int
            }

            transition!{
                tr() {
                    have t >= (5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'have' statement not allowed for field with sharding strategy 'constant'")
}

test_verify_tsm! {
    #[test] test_use_option_directly IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)] pub t: Option<int>,
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.t->Some_0;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "cannot be directly referenced here")
}

test_verify_tsm! {
    #[test] test_use_map_directly IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)] pub t: Map<int, int>,
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.t.index(0);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "cannot be directly referenced here")
}

test_verify_tsm! {
    #[test] test_use_imap_directly IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(imap)] pub t: IMap<int, int>,
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.t.index(0);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "cannot be directly referenced here")
}

test_verify_tsm! {
    #[test] test_use_multiset_directly IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)] pub t: Multiset<int>,
                #[sharding(variable)] pub v: Multiset<int>,
            }

            transition!{
                tr() {
                    update v = pre.t;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "cannot be directly referenced here")
}

test_verify_tsm! {
    #[test] test_use_storage_option_directly IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub t: Option<int>,
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.t->Some_0;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "cannot be directly referenced here")
}

test_verify_tsm! {
    #[test] test_use_nottokenized_directly IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(not_tokenized)] pub t: int,
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.t;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "cannot be directly referenced here")
}

test_verify_tsm! {
    #[test] test_use_pre_no_field IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = { let s = pre; s.v };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "cannot be used opaquely")
}

test_verify_tsm! {
    #[test] test_use_pre_no_field_withdraw_kv_value IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_imap)] pub v: IMap<int, int>,
            }

            transition!{
                tr() {
                    withdraw v -= [5 => { let s = pre; s.v } ];
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "cannot be used opaquely")
}

test_verify_tsm! {
    #[test] test_use_pre_no_field_remove_kv_key IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)] pub v: Map<int, int>,
            }

            transition!{
                tr() {
                    remove v -= [5 => { let s = pre; s.v } ];
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "cannot be used opaquely")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field_withdraw_kv_key IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_imap)] pub v: IMap<int, int>,
            }

            init!{
                initialize() {
                    init v = IMap::empty();
                }
            }

            transition!{
                tr() {
                    // this is ok:
                    withdraw v -= [{ let s = pre; s.v.index(0) } => 5]
                          by { assume(false); };
                }
            }
        }}

        verus!{

        proof fn foo(tracked m: IMap<int, int>) {
            requires(equal(m, IMap::empty()));

            let tracked inst = X::Instance::initialize(m);
            let tracked t = (inst).tr();
            assert(t == 5);
        }

        }
    } => Ok(())
}

// Checked-macro version of test_use_pre_no_field_withdraw_kv_key. API difference: in a machine
// with storage, an operation that consumes no token takes a `Unit` (here from
// `<init>_with_unit`, as the machine has no field token).
test_verify_one_file! {
    #[test] test_use_pre_no_field_withdraw_kv_key_verified IMPORTS.to_string() + verus_code_str! {
        verified_tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_imap)] pub v: IMap<int, int>,
            }

            init!{
                initialize() {
                    init v = IMap::empty();
                }
            }

            transition!{
                tr() {
                    // this is ok:
                    withdraw v -= [{ let s = pre; s.v.index(0) } => 5]
                          by { assume(false); };
                }
            }
        }}

        verus!{

        proof fn foo(tracked m: IMap<int, int>) {
            requires(equal(m, IMap::empty()));

            let tracked (Tracked(inst), Tracked(unit)) = X::Instance::initialize_with_unit(m);
            let tracked t = (inst).tr(unit);
            assert(t == 5);
        }

        }
    } => Ok(())
}

test_verify_tsm! {
    #[test] test_use_pre_no_field2 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.some_fn();
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "`pre` cannot be used opaquely")
}

test_verify_tsm! {
    #[test] test_use_pre_no_field3 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.not_a_field;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "any field access must be a state field")
}

test_verify_tsm! {
    #[test] test_use_pre_no_field4 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.0;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "expected a named field")
}

test_verify_tsm! {
    #[test] field_name_reserved_ident1 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub instance: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "reserved identifier")
}

test_verify_tsm! {
    #[test] field_name_reserved_ident2 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub param_token_a: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "reserved identifier")
}

test_verify_tsm! {
    #[test] sm_name_reserved_ident1 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ instance {
            fields {
                #[sharding(variable)] pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "reserved identifier")
}

test_verify_tsm! {
    #[test] sm_name_reserved_ident2 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ param_token_a {
            fields {
                #[sharding(variable)] pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "reserved identifier")
}

test_verify_tsm! {
    #[test] let_name_reserved_ident1 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr() {
                    let instance = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "reserved identifier")
}

test_verify_tsm! {
    #[test] let_name_reserved_ident2 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr() {
                    let param_token_a = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "reserved identifier")
}

test_verify_tsm! {
    #[test] arg_reserved_ident1 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(instance: int) {
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "reserved identifier")
}

test_verify_tsm! {
    #[test] arg_reserved_ident2 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(param_token_a: int) {
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "reserved identifier")
}

test_verify_tsm! {
    #[test] binding_reserved_ident1 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)] pub t: Option<int>,
            }

            transition!{
                tr() {
                    remove t -= Some(let instance);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "reserved identifier")
}

test_verify_tsm! {
    #[test] duplicate_inductive_lemma IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                    update t = x;
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) {
            }

            #[inductive(tr)]
            pub fn lemma_tr2(pre: Self, post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "duplicate 'inductive' lemma")
}

test_verify_tsm! {
    #[test] missing_inductive_lemma IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                    update t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool {
                self.t == 5
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "missing inductiveness proofs for")
}

test_verify_tsm! {
    #[test] missing_inductive_lemma_init IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool {
                self.t == 5
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "missing inductiveness proofs for")
}

test_verify_tsm! {
    #[test] inductive_lemma_readonly IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            readonly!{
                tr(x: int) {
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'inductive' lemma does not make sense for a 'readonly' transition")
}

test_verify_tsm! {
    #[test] inductive_lemma_property IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            property!{
                tr(x: int) {
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'inductive' lemma does not make sense for a 'property' definition")
}

test_verify_tsm! {
    #[test] lemma_wrong_args IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, y: int) {
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "params for 'inductive' lemma should be")
}

test_verify_tsm! {
    #[test] lemma_bad_transition_name IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                }
            }

            #[inductive(tro)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "could not find transition")
}

test_verify_tsm! {
    #[test] lemma_bad_generic_params IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1<T>(pre: Self, post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "should have no generic parameters")
}

test_verify_tsm! {
    #[test] lemma_bad_return_type IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) -> bool {
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "should have no return type")
}

test_verify_tsm! {
    #[test] lemma_bad_header IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                }
            }

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) {
                requires(true);
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "the precondition and postcondition are implicit")
}

test_verify_tsm! {
    #[test] lemma_doesnt_verify IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(x: int) {
                    update t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool {
                self.t == 5
            }

            #[inductive(tr)] // FAILS
            pub fn lemma_tr1(pre: Self, post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] lemma_doesnt_verify_init IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool {
                self.t == 5
            }

            #[inductive(tr)] // FAILS
            pub fn lemma_tr1(post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] sm_generic_param_not_type IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X<'a> {
            fields {
                #[sharding(variable)] pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "Only generic type parameters are supported")
}

test_verify_tsm! {
    #[test] multiple_fields IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            fields {
                #[sharding(variable)] pub x: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "Expected only one declaration of `fields` block")
}

test_verify_tsm! {
    #[test] no_fields IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
        }}
    } => Err(e) => assert_vir_error_msg(e, "'fields' declaration was not found")
}

test_verify_tsm! {
    #[test] conflicting_attrs IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            #[inductive(tr)]
            pub fn the_inv(self) -> bool {
                self.t == 5
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "conflicting attributes")
}

test_verify_tsm! {
    #[test] explicit_mode_inv IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            #[verifier::spec]
            pub fn the_inv(self) -> bool {
                true
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "should not be explicitly labelled")
}

test_verify_tsm! {
    #[test] wrong_mode_inv IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub proof fn the_inv(self) -> bool {
                true
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "an invariant function should be `spec`")
}

test_verify_tsm! {
    #[test] wrong_mode_inductive IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool {
                true
            }

            #[inductive(tr)]
            pub spec fn lemma_tr1(post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "an inductiveness lemma should be `proof`")
}

test_verify_tsm! {
    #[test] explicit_mode_field IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] #[verifier::spec] pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "should not be explicitly labelled")
}

test_verify_tsm! {
    #[test] explicit_mode_proof IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool {
                true
            }

            #[inductive(tr)]
            #[verifier::proof]
            pub fn lemma_tr1(post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "should not be explicitly labelled")
}

test_verify_tsm! {
    #[test] inv_wrong_params IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv(x: int) -> bool {
                true
            }

            #[inductive(tr)]
            #[verifier::proof]
            pub fn lemma_tr1(post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_vir_error_msg(e, "an invariant function must take 1 argument (self)")
}

test_verify_tsm! {
    #[test] inv_wrong_ret IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv(self) -> int {
                5
            }

            #[inductive(tr)]
            #[verifier::proof]
            pub fn lemma_tr1(post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_vir_error_msg(e, "an invariant function must return a bool")
}

test_verify_tsm! {
    #[test] inv_wrong_generics IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            init!{
                tr(x: int) {
                    init t = x;
                }
            }

            #[invariant]
            pub fn the_inv<V>(self) -> bool {
                true
            }

            #[inductive(tr)]
            #[verifier::proof]
            pub fn lemma_tr1(post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_vir_error_msg(e, "an invariant function must take 0 type arguments")
}

test_verify_tsm! {
    #[test] normal_sm_sharding IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "sharding strategy only makes sense for tokenized state machines")
    // verified_state_machine_model! accepts (and ignores) sharding annotations by design.
    ; verified => Ok(())
}

test_verify_tsm! {
    #[test] tokenized_sm_no_sharding IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "tokenized state machine requires a sharding strategy")
}

test_verify_tsm! {
    #[test] unrecognized_sharding_strategy_name IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(foo)] pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "unrecognized sharding strategy")
}

test_verify_tsm! {
    #[test] duplicate_sharding_attr IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)]
                #[sharding(variable)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "duplicate sharding attribute")
}

test_verify_tsm! {
    #[test] wrong_form_option IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "must be of the form Option<_>")
}

test_verify_tsm! {
    #[test] wrong_form_option2 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Multiset<int>,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "must be of the form Option<_>")
}

test_verify_tsm! {
    #[test] wrong_form_option3 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: IMap<int, int>,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "must be of the form Option<_>")
}

test_verify_tsm! {
    #[test] wrong_form_storage_option IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "must be of the form Option<_>")
}

test_verify_tsm! {
    #[test] wrong_form_map IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "must be of the form Map<_, _>")
}

test_verify_tsm! {
    #[test] wrong_form_storage_map IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "must be of the form Map<_, _>")
}

test_verify_tsm! {
    #[test] wrong_form_storage_imap IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_imap)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "must be of the form IMap<_, _>")
}

test_verify_tsm! {
    #[test] wrong_form_multiset IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "must be of the form Multiset<_>")
}

test_verify_tsm! {
    #[test] wrong_form_set IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(set)]
                pub t: Multiset<int>,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "must be of the form Set<_>")
}

test_verify_tsm! {
    #[test] wrong_form_iset IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(iset)]
                pub t: Multiset<int>,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "must be of the form ISet<_>")
}

test_verify_tsm! {
    #[test] wrong_form_count IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(count)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "must be nat")
}

test_verify_tsm! {
    #[test] wrong_form_bool IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(bool)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "must be bool")
}

test_verify_tsm! {
    #[test] special_op_conditional IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    if true {
                        add t += Some(5);
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statements are not supported inside conditionals")
}

test_verify_tsm! {
    #[test] special_op_binding_conditional IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    if true {
                        remove t -= Some(let x);
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statements are not supported inside conditionals")
}

test_verify_tsm! {
    #[test] special_op_match IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr(foo: Foo) {
                    match foo {
                        Foo::Bar(x) => {
                            add t += Some(5);
                        }
                        Foo::Qax(y) => { }
                        Foo::Duck(z) => { }
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statements are not supported inside conditionals")
}

test_verify_tsm! {
    #[test] remove_after_have IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    have t >= Some(5);
                    remove t -= Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "remove -> have -> add")
}

test_verify_tsm! {
    #[test] remove_after_have_with_binding IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    have t >= Some(let z);
                    remove t -= Some(let x);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "remove -> have -> add")
}

test_verify_tsm! {
    #[test] have_after_add IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    add t += Some(5);
                    have t >= Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "remove -> have -> add")
}

test_verify_tsm! {
    #[test] remove_after_add IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    add t += Some(5);
                    remove t -= Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "remove -> have -> add")
}

test_verify_tsm! {
    #[test] init_wf_init_missing IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "procedure does not initialize")
}

test_verify_tsm! {
    #[test] init_wf_init_dupe IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    init t = 5;
                    init t = 6;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "might be initialized multiple times")
}

test_verify_tsm! {
    #[test] init_wf_init_dupe_conditional IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    init t = 5;
                    if 1 + 2 == 3 {
                        init t = 6;
                    } else {
                        init t = 7;
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "might be initialized multiple times")
}

test_verify_tsm! {
    #[test] init_wf_init_if IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    if 1 + 2 == 3 {
                        init t = 6;
                    } else {
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "the else-branch does not initialize")
}

test_verify_tsm! {
    #[test] init_wf_init_dupe_match IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init(foo: Foo) {
                    init t = 5;
                    match foo {
                        Foo::Bar(x) => { init t = 6; }
                        Foo::Qax(y) => { init t = 7; }
                        Foo::Duck(z) => { init t = 8; }
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "might be initialized multiple times")
}

test_verify_tsm! {
    #[test] init_wf_init_else IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    if 1 + 2 == 3 {
                    } else {
                        init t = 6;
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "the if-branch does not initialize")
}

test_verify_tsm! {
    #[test] init_wf_init_match IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    match foo {
                        Foo::Bar(x) => {
                            init t = 6;
                        }
                        Foo::Qax(y) => {
                        }
                        Foo::Duck(z) => {
                            init t = 7;
                        }
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "all branches of a match-statement must initialize")
}

test_verify_tsm! {
    #[test] init_wf_init_match2 IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    match foo {
                        Foo::Bar(x) => {
                        }
                        Foo::Qax(y) => {
                            init t = 6;
                        }
                        Foo::Duck(z) => {
                        }
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "all branches of a match-statement must initialize")
}

test_verify_tsm! {
    #[test] init_wf_update IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    init t = 6;
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'update' statement not allowed in initialization")
}

test_verify_tsm! {
    #[test] init_wf_update2 IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'update' statement not allowed in initialization")
}

test_verify_tsm! {
    #[test] init_wf_special IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            init!{
                init() {
                    add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "use 'init' instead")
}

test_verify_tsm! {
    #[test] init_wf_special_with_binding IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            init!{
                init() {
                    remove t -= Some(let x);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "use 'init' instead")
}

test_verify_tsm! {
    #[test] init_wf_assert IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    assert(true);
                    init t = 6;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'assert' statement not allowed in initialization")
}

test_verify_tsm! {
    #[test] normal_wf_update_dupe IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update t = 5;
                    update t = 6;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "might be updated multiple times")
}

test_verify_tsm! {
    #[test] normal_wf_update_dupe_conditional IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update t = 5;
                    if true {
                        update t = 6;
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "might be updated multiple times")
}

test_verify_tsm! {
    #[test] normal_wf_update_dupe_conditional2 IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update t = 5;
                    if true {
                    } else {
                        update t = 6;
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "might be updated multiple times")
}

test_verify_tsm! {
    #[test] normal_wf_update_dupe_match IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update t = 5;
                    match foo {
                        Foo::Bar(x) => {
                            update t = 6;
                        }
                        Foo::Qax(y) => { }
                        Foo::Duck(z) => { }
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "might be updated multiple times")
}

test_verify_tsm! {
    #[test] normal_wf_update_init IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    init t = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'init' statement not allowed")
}

test_verify_tsm! {
    #[test] normal_wf_update_guard IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    guard t >= Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "'guard' statement only allowed in 'readonly' transition or 'property' definition")
}

test_verify_tsm! {
    #[test] readonly_wf_update IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            readonly!{
                tr() {
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_tsm! {
    #[test] property_wf_update IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            property!{
                tr() {
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statement not allowed in property definition")
}

test_verify_tsm! {
    #[test] readonly_wf_init IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            readonly!{
                tr() {
                    init t = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statement not allowed outside 'init' routine")
}

test_verify_tsm! {
    #[test] property_wf_init IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            property!{
                tr() {
                    init t = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statement not allowed outside 'init' routine")
}

test_verify_tsm! {
    #[test] readonly_wf_add IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            readonly!{
                tr() {
                    add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_tsm! {
    #[test] property_wf_add IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            property!{
                tr() {
                    add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statement not allowed in 'property' definition")
}

test_verify_tsm! {
    #[test] readonly_wf_remove_with_binding IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            readonly!{
                tr() {
                    remove t -= Some(let x);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_tsm! {
    #[test] readonly_wf_remove IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            readonly!{
                tr() {
                    remove t -= Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_tsm! {
    #[test] readonly_wf_deposit IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>,
            }

            readonly!{
                tr() {
                    deposit t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_tsm! {
    #[test] readonly_wf_withdraw IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>,
            }

            readonly!{
                tr() {
                    withdraw t -= Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_tsm! {
    #[test] field_not_found IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update whats_this = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "field 'whats_this' not found")
}

test_verify_tsm! {
    #[test] inherent_safety_condition_option_remove IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    remove t -= Some(5) by { };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "adding a proof body is meaningless")
}

test_verify_tsm! {
    #[test] inherent_safety_condition_option_remove_with_binding IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    remove t -= Some(let y) by { };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "adding a proof body is meaningless")
}

test_verify_tsm! {
    #[test] inherent_safety_condition_map_remove IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    remove t -= [5 => 7] by { };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "adding a proof body is meaningless")
}

test_verify_tsm! {
    #[test] inherent_safety_condition_multiset_remove IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>
            }

            transition!{
                tr() {
                    remove t -= { 5 } by { };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "adding a proof body is meaningless")
}

test_verify_tsm! {
    #[test] inherent_safety_condition_option_add IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    add t += Some(5) by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t is None);
                assert(post.t is Some);
                assert(post.t->Some_0 == 5);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_option_general_add IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    add t += (Option::Some(5)) by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t is None);
                assert(post.t is Some);
                assert(post.t->Some_0 == 5);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_map_add IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    add t += [5 => 7] by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(!pre.t.dom().contains(5));
                assert(post.t.dom().contains(5));
                assert(post.t.index(5) == 7);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_map_general_add IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    add t += (Map::<int, int>::empty().insert(5, 7)) by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(!pre.t.dom().contains(5));
                assert(post.t.dom().contains(5));
                assert(post.t.index(5) == 7);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_multiset_add IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>
            }

            transition!{
                tr() {
                    add t += { 5 } by { };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "adding a proof body is meaningless")
}

test_verify_tsm! {
    #[test] inherent_safety_condition_multiset_general_add IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>
            }

            transition!{
                tr() {
                    add t += ({ 5 }) by { };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "adding a proof body is meaningless")
}

test_verify_tsm! {
    #[test] inherent_safety_condition_option_have IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    have t >= Some(5) by { };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "adding a proof body is meaningless")
}

test_verify_tsm! {
    #[test] inherent_safety_condition_map_have IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    have t >= [5 => 7] by { };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "adding a proof body is meaningless")
}

test_verify_tsm! {
    #[test] inherent_safety_condition_multiset_have IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>
            }

            transition!{
                tr() {
                    have t >= { 5 } by { };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "adding a proof body is meaningless")
}

test_verify_tsm! {
    #[test] inherent_safety_condition_option_withdraw IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    withdraw t -= Some(5) by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t is Some);
                assert(pre.t->Some_0 == 5);
                assert(post.t is None);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_map_withdraw IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_imap)]
                pub t: IMap<int, int>
            }

            transition!{
                tr() {
                    withdraw t -= [5 => 7] by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t.dom().contains(5));
                assert(pre.t.index(5) == 7);
                assert(!post.t.dom().contains(5));
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_map_withdraw_with_binding IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_imap)]
                pub t: IMap<int, int>
            }

            transition!{
                tr() {
                    withdraw t -= [5 => let z] by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t.dom().contains(5));
                assert(!post.t.dom().contains(5));
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_multiset_withdraw IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_multiset)]
                pub t: Multiset<int>
            }

            transition!{
                tr() {
                    withdraw t -= { 5 } by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t.count(5) >= 1);
                assert(equal(post.t, pre.t.remove(5)));
            }
        }}
    // not supported right now:
    } => Err(e) => assert_vir_error_msg(e, "storage_multiset strategy not implemented")
    //} => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_option_guard IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>
            }

            property!{
                tr() {
                    guard t >= Some(5) by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t is Some && t->0 == 5);
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_map_guard IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_imap)]
                pub t: IMap<int, int>
            }

            property!{
                tr() {
                    guard t >= [5 => 7] by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.dom().contains(5) && t.index(5) == 7);
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_option_general_guard IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>
            }

            property!{
                tr() {
                    guard t >= (Option::Some(5)) by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t is Some && t->0 == 5);
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_map_general_guard IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_imap)]
                pub t: IMap<int, int>
            }

            property!{
                tr() {
                    guard t >= (IMap::<int,int>::empty().insert(5, 7)) by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.dom().contains(5)) by {
                        assert(IMap::<int,int>::empty().insert(5, 7).dom().contains(5));
                        assert(IMap::<int,int>::empty().insert(5, 7).index(5) == 7);
                    };
                    assert(t.index(5) == 7) by {
                        assert(IMap::<int,int>::empty().insert(5, 7).dom().contains(5));
                        assert(IMap::<int,int>::empty().insert(5, 7).index(5) == 7);
                    };
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

// The `by` blocks are needed (the invariant is opaque): they prove the
// operations' inherent safety conditions.
test_verify_tsm! {
    #[test] inherent_safety_condition_by_block_needed IMPORTS.to_string() + verus_code_str! {
        #[verifier::opaque]
        pub open spec fn full(v: int) -> bool { v == 0 }

        tokenized_state_machine!{ X {
            fields {
                #[sharding(constant)]
                pub k: int,

                #[sharding(variable)]
                pub v: int,

                #[sharding(storage_option)]
                pub s: Option<int>,

                #[sharding(storage_map)]
                pub m: Map<int, int>,
            }

            #[invariant]
            pub fn inv(&self) -> bool {
                &&& (self.s is Some <==> full(self.v))
                &&& (full(self.v) ==> self.s == Some(self.k))
                &&& (self.m.dom().contains(1) <==> full(self.v))
                &&& (full(self.v) ==> self.m[1] == self.k)
            }

            init!{
                initialize(k: int) {
                    init k = k;
                    init v = 0;
                    init s = Option::Some(k);
                    init m = Map::empty().insert(1, k);
                }
            }

            transition!{
                take() {
                    require pre.v == 0;
                    update v = 1;
                    withdraw s -= Some(pre.k) by { reveal(full); };
                    withdraw m -= [1 => pre.k] by { reveal(full); };
                }
            }

            transition!{
                give() {
                    require pre.v == 1;
                    update v = 0;
                    deposit s += Some(pre.k) by { reveal(full); };
                    deposit m += [1 => pre.k] by { reveal(full); };
                }
            }

            property!{
                peek() {
                    require pre.v == 0;
                    guard s >= Some(pre.k) by { reveal(full); };
                    guard m >= [1 => pre.k] by { reveal(full); };
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self, k: int) { reveal(full); }

            #[inductive(take)]
            fn take_inductive(pre: Self, post: Self) { reveal(full); }

            #[inductive(give)]
            fn give_inductive(pre: Self, post: Self) { reveal(full); }
        }}
    } => Ok(())
}

test_verify_tsm! {
    #[test] inherent_safety_condition_by_block_missing IMPORTS.to_string() + verus_code_str! {
        #[verifier::opaque]
        pub open spec fn full(v: int) -> bool { v == 0 }

        tokenized_state_machine!{ X {
            fields {
                #[sharding(constant)]
                pub k: int,

                #[sharding(variable)]
                pub v: int,

                #[sharding(storage_option)]
                pub s: Option<int>,
            }

            #[invariant]
            pub fn inv(&self) -> bool {
                &&& (self.s is Some <==> full(self.v))
                &&& (full(self.v) ==> self.s == Some(self.k))
            }

            init!{
                initialize(k: int) {
                    init k = k;
                    init v = 0;
                    init s = Option::Some(k);
                }
            }

            transition!{
                take() {
                    require pre.v == 0;
                    update v = 1;
                    withdraw s -= Some(pre.k); // FAILS
                }
            }

            transition!{
                give() {
                    require pre.v == 1;
                    update v = 0;
                    deposit s += Some(pre.k); // FAILS
                }
            }

            property!{
                peek() {
                    require pre.v == 0;
                    guard s >= Some(pre.k); // FAILS
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self, k: int) { reveal(full); }

            #[inductive(take)]
            fn take_inductive(pre: Self, post: Self) { reveal(full); }

            #[inductive(give)]
            fn give_inductive(pre: Self, post: Self) { reveal(full); }
        }}
    } => Err(e) => assert_fails(e, 3)
    // (the checked macro reports the three conditions, which have no `by`
    // block, at the macro invocation: one diagnostic)
    ; verified => Err(e) => assert_fails_anywhere(e, 1)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_multiset_guard IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_multiset)]
                pub t: Multiset<int>
            }

            property!{
                tr() {
                    guard t >= { 5 } by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.count(5) >= 1);
                }
            }
        }}
    // not supported right now:
    } => Err(e) => assert_vir_error_msg(e, "storage_multiset strategy not implemented")
    //} => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_multiset_general_guard IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_multiset)]
                pub t: Multiset<int>
            }

            property!{
                tr() {
                    guard t >= (Multiset::singleton(5)) by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.count(5) >= 1);
                }
            }
        }}
    // not supported right now:
    } => Err(e) => assert_vir_error_msg(e, "unrecognized sharding strategy: 'storage_multiset'")
    //} => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_option_deposit IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    deposit t += Some(5) by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(pre.t is None);
                assert(post.t is Some);
                assert(post.t->0 == 5);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_map_deposit IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_imap)]
                pub t: IMap<int, int>
            }

            transition!{
                tr() {
                    deposit t += [5 => 7] by { }; // FAILS
                }
            }

            #[inductive(tr)]
            pub fn is_inductive(pre: Self, post: Self) {
                assert(!pre.t.dom().contains(5));
                assert(post.t.dom().contains(5));
                assert(post.t.index(5) == 7);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] inherent_safety_condition_multiset_deposit IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_multiset)]
                pub t: Multiset<int>
            }

            transition!{
                tr() {
                    deposit t += { 5 } by { };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "storage_multiset strategy not implemented")
}

test_verify_tsm! {
    #[test] assert_safety_condition_fail IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    assert(pre.t == 0); // FAILS
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] assert_safety_condition_readonly_fail IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            readonly!{
                tr() {
                    assert(pre.t == 0); // FAILS
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] assert_safety_condition_property_fail IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            property!{
                tr() {
                    assert(pre.t == 0); // FAILS
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] wrong_op_var_add_option IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                    add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "statement not allowed for field with sharding strategy")
}

test_verify_tsm! {
    #[test] wrong_op_multiset_add_option IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>,
            }

            transition!{
                tr() {
                    add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "element but the given field has sharding strategy 'multiset'")
}

test_verify_tsm! {
    #[test] wrong_op_multiset_add_set IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>,
            }

            transition!{
                tr() {
                    add t += set { 5 };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "element but the given field has sharding strategy 'multiset'")
}

test_verify_tsm! {
    #[test] wrong_op_set_add_multiset IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(set)]
                pub t: Set<int>,
            }

            transition!{
                tr() {
                    add t += { 5 };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "element but the given field has sharding strategy 'set'")
}

test_verify_tsm! {
    #[test] wrong_op_multiset_add_option_with_binding IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>,
            }

            transition!{
                tr() {
                    add t += Some(let z);
                }
            }
        }}
    } => Err(e) => assert_any_vir_error_msg(e, "element but the given field has sharding strategy 'multiset'")
}

test_verify_tsm! {
    #[test] wrong_op_map_add_option IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>,
            }

            transition!{
                tr() {
                    add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "element but the given field has sharding strategy 'map'")
}

test_verify_tsm! {
    #[test] wrong_op_option_add_map IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    add t += [5 => 5];
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "element but the given field has sharding strategy 'option'")
}

test_verify_tsm! {
    #[test] wrong_op_option_add_multiset IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>
            }

            transition!{
                tr() {
                    add t += {5};
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "element but the given field has sharding strategy 'option'")
}

test_verify_tsm! {
    #[test] wrong_op_map_add_multiset IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    add t += {5};
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "element but the given field has sharding strategy 'map'")
}

test_verify_tsm! {
    #[test] wrong_op_multiset_add_map IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: Multiset<int>,
            }

            transition!{
                tr() {
                    add t += [5 => 5];
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "element but the given field has sharding strategy 'multiset'")
}

test_verify_tsm! {
    #[test] wrong_op_map_guard_option IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: Map<int, int>
            }

            property!{
                tr() {
                    guard t >= Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "element but the given field has sharding strategy 'map'")
}

test_verify_tsm! {
    #[test] wrong_op_count_add_option IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(count)]
                pub t: nat,
            }

            transition!{
                tr() {
                    add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "element but the given field has sharding strategy 'count'")
}

test_verify_tsm! {
    #[test] wrong_op_option_deposit_option IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                   deposit t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "is only for storage types")
}

test_verify_tsm! {
    #[test] wrong_op_storage_option_add_option IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>,
            }

            transition!{
                tr() {
                   add t += Some(5);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "use deposit/withdraw/guard statements for storage strategies")
}

test_verify_tsm! {
    #[test] no_let_repeated_idents IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: IMap<int, int>
            }

            transition!{
                tr() {
                    if true {
                        let x = 5;
                    } else {
                        let x = 5;
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "bound variables with the same name")
}

test_verify_tsm! {
    #[test] no_let_repeated_idents2 IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: IMap<int, int>
            }

            transition!{
                tr() {
                    let x = 5;
                    let x = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "bound variables with the same name")
}

test_verify_tsm! {
    #[test] no_let_repeated_idents3 IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: IMap<int, int>
            }

            transition!{
                tr(x: int) {
                    let x = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "bound variables with the same name")
}

test_verify_tsm! {
    #[test] no_let_repeated_idents4 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Option<int>,
            }

            transition!{
                tr(x: int) {
                    remove t -= Some(let x);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "bound variables with the same name")
}

test_verify_tsm! {
    #[test] type_recursion_ok IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)]
                pub t: X::Instance,
            }
        }}
    } => Ok(())
}

test_verify_tsm! {
    #[test] type_recursion_fail_negative IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                // this should fail because IMap has a reject_recursive_types first param

                #[sharding(variable)]
                pub t: IMap<X::Instance, int>
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "non-positive position")
    // The checked Instance of this machine holds only a location (it does not mention State),
    // so there is no recursion through IMap's rejected parameter.
    ; verified => Ok(())
}

test_verify_tsm! {
    #[test] lemma_recursion_fail IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)]
                pub t: int,
            }

            init!{
                initialize() {
                    init t = 1;
                }
            }

            property!{
                ro() {
                    assert(pre.t == 2);
                }
            }

            #[invariant]
            pub fn inv_2(self) -> bool {
                self.t == 2
            }

            #[inductive(initialize)]
            fn inductive_init(post: Self) {
                let tracked (Tracked(inst), Tracked(token)) = X::Instance::initialize();
                inst.ro(&token);
                // this should derive a contradiction if not for the recursion checking
            }
        }}
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
    // The checked macro reports the cycle twice (lemma and its use in a generated proof).
    ; verified => Err(err) => assert_any_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_tsm! {
    #[ignore] #[test] lemma_recursion_assert_fail IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)]
                pub t: int,
            }

            init!{
                initialize() {
                    init t = 1;
                }
            }

            property!{
                ro() {
                    assert(pre.t == 2) by {
                        foo_lemma();
                    };
                }
            }
        }}

        verus!{
        proof fn foo_lemma() {
            let tracked (Tracked(inst), Tracked(token)) = X::Instance::initialize();
            inst.ro(&token);
        }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_tsm! {
    #[test] relation_codegen IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub x: int,
                pub y: int,
                pub z: int,
            }

            init!{
                initialize(x: int, y: int, z: int) {
                    init x = x;
                    init y = y;
                    require(y <= z);
                    if x == y {
                        init z = z;
                    } else {
                        init z = z + 1;
                    }
                }
            }

            transition!{
                tr1(b: bool, c: bool) {
                    require(b);
                    assert(pre.y <= pre.z);
                    require(c);
                    update z = pre.z + 1;
                }
            }

            transition!{
                tr2(b: bool, c: bool) {
                    if b {
                        update z = pre.z + 1;
                    } else {
                        assert(pre.y <= pre.z);
                    }
                    require(c);
                }
            }

            transition!{
                tr3(b: bool, c: bool) {
                    if b {
                        assert(pre.y <= pre.z);
                    } else {
                        let j = pre.z + 1;
                        update z = j;
                    }
                    require(c);
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool { self.y <= self.z }

            #[inductive(initialize)]
            fn init_inductive(post: Self, x: int, y: int, z: int) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self, b: bool, c: bool) { }

            #[inductive(tr2)]
            fn tr2_inductive(pre: Self, post: Self, b: bool, c: bool) { }

            #[inductive(tr3)]
            fn tr3_inductive(pre: Self, post: Self, b: bool, c: bool) { }

        }}

        verus! {

        spec fn rel_init(post: X::State, x: int, y: int, z: int) -> bool {
            post.x == x && post.y == y && y <= z &&
            if x == y { post.z == z } else { post.z == z + 1 }
        }

        spec fn rel_tr1(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
            &&& b
            &&& pre.y <= pre.z ==> {
                &&& c
                &&& post.z == pre.z + 1
                &&& post.x == pre.x
                &&& post.y == pre.y
            }
        }

        spec fn rel_tr1_strong(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
            &&& b
            &&& pre.y <= pre.z && {
                &&& c
                &&& post.z == pre.z + 1
                &&& post.x == pre.x
                &&& post.y == pre.y
            }
        }

        spec fn rel_tr2(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
            &&& (if b { post.z == pre.z + 1 } else { pre.y <= pre.z ==> post.z == pre.z })
            &&& (!b ==> pre.y <= pre.z) ==> {
                &&& c
                &&& pre.x == post.x
                &&& pre.y == post.y
            }
        }

        spec fn rel_tr2_strong(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
            &&& (if b { post.z == pre.z + 1 } else { post.z == pre.z })
            &&& (!b ==> pre.y <= pre.z) && {
                &&& c
                &&& pre.x == post.x
                &&& pre.y == post.y
            }
        }

        spec fn rel_tr3(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
            &&& (if !b { post.z == pre.z + 1 } else { pre.y <= pre.z ==> post.z == pre.z })
            &&& (b ==> pre.y <= pre.z) ==> {
                &&& c
                &&& pre.x == post.x
                &&& pre.y == post.y
            }
        }

        spec fn rel_tr3_strong(pre: X::State, post: X::State, b: bool, c: bool) -> bool {
            &&& (if !b { post.z == pre.z + 1 } else { post.z == pre.z })
            &&& (b ==> pre.y <= pre.z) && {
                &&& c
                &&& pre.x == post.x
                &&& pre.y == post.y
            }
        }

        proof fn correct_init(post: X::State, x: int, y: int, z: int) {
            requires(X::State::initialize(post, x, y, z));
            ensures(rel_init(post, x, y, z));
        }

        proof fn rev_init(post: X::State, x: int, y: int, z: int) {
            requires(rel_init(post, x, y, z));
            ensures(X::State::initialize(post, x, y, z));
        }

        proof fn correct_tr1(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(X::State::tr1(pre, post, b, c));
            ensures(rel_tr1(pre, post, b, c));
        }

        proof fn rev_tr1(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(rel_tr1(pre, post, b, c));
            ensures(X::State::tr1(pre, post, b, c));
        }

        proof fn correct_tr1_strong(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(X::State::tr1_strong(pre, post, b, c));
            ensures(rel_tr1_strong(pre, post, b, c));
        }

        proof fn rev_tr1_strong(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(rel_tr1_strong(pre, post, b, c));
            ensures(X::State::tr1_strong(pre, post, b, c));
        }

        proof fn correct_tr2(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(X::State::tr2(pre, post, b, c));
            ensures(rel_tr2(pre, post, b, c));
        }

        proof fn rev_tr2(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(rel_tr2(pre, post, b, c));
            ensures(X::State::tr2(pre, post, b, c));
        }

        proof fn correct_tr2_strong(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(X::State::tr2_strong(pre, post, b, c));
            ensures(rel_tr2_strong(pre, post, b, c));
        }

        proof fn rev_tr2_strong(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(rel_tr2_strong(pre, post, b, c));
            ensures(X::State::tr2_strong(pre, post, b, c));
        }

        proof fn correct_tr3(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(X::State::tr3(pre, post, b, c));
            ensures(rel_tr3(pre, post, b, c));
        }

        proof fn rev_tr3(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(rel_tr3(pre, post, b, c));
            ensures(X::State::tr3(pre, post, b, c));
        }

        proof fn correct_tr3_strong(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(X::State::tr3_strong(pre, post, b, c));
            ensures(rel_tr3_strong(pre, post, b, c));
        }

        proof fn rev_tr3_strong(pre: X::State, post: X::State, b: bool, c: bool) {
            requires(rel_tr3_strong(pre, post, b, c));
            ensures(X::State::tr3_strong(pre, post, b, c));
        }

        } // verus!
    } => Ok(())
}

test_verify_tsm! {
    #[test] relation_codegen_match IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub x: int,
                pub y: int,
                pub z: int,
            }

            init!{
                initialize(x: int, y: int, z: int, foo: Foo) {
                    init x = x;
                    init y = y;
                    require(y <= z);
                    match foo {
                        Foo::Bar(a) => { init z = z; }
                        Foo::Qax(b) => { init z = z + 1; }
                        Foo::Duck(d) => { init z = z + 2; }
                    }
                }
            }

            transition!{
                tr1(foo: Foo, c: bool) {
                    match foo {
                        Foo::Bar(a) => { update z = pre.z + 1; }
                        Foo::Qax(b) if b == 20 => { assert(pre.y <= pre.z); }
                        Foo::Duck(d) => { assert(foo is Duck); }
                        _ => { }
                    }
                    require(c);
                }
            }

            #[invariant]
            pub fn the_inv(self) -> bool { self.y <= self.z }

            #[inductive(initialize)]
            fn init_inductive(post: Self, x: int, y: int, z: int, foo: Foo) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self, foo: Foo, c: bool) { }
        }}

        verus! {

        spec fn rel_init(post: X::State, x: int, y: int, z: int, foo: Foo) -> bool {
            &&& post.x == x
            &&& post.y == y
            &&& y <= z
            &&& match foo {
                Foo::Bar(a) => { post.z == z }
                Foo::Qax(b) => { post.z == z + 1 }
                Foo::Duck(d) => { post.z == z + 2 }
            }
        }

        spec fn rel_tr1(pre: X::State, post: X::State, foo: Foo, c: bool) -> bool {
            &&& (match foo {
                Foo::Bar(a) => { post.z == pre.z + 1 }
                Foo::Qax(b) if b == 20 => { pre.y <= pre.z ==> post.z == pre.z }
                Foo::Duck(d) => { post.z == pre.z }
                _ => { post.z == pre.z }
            })
            &&& ((match foo {
                Foo::Bar(a) => { true }
                Foo::Qax(b) if b == 20 => { pre.y <= pre.z }
                Foo::Duck(d) => { true }
                _ => { true }
            }) ==> {
                &&& c
                &&& pre.x == post.x
                &&& pre.y == post.y
            })
        }

        spec fn rel_tr1_strong(pre: X::State, post: X::State, foo: Foo, c: bool) -> bool {
            &&& (match foo {
                Foo::Bar(a) => { post.z == pre.z + 1 }
                Foo::Qax(b) if b == 20 => { post.z == pre.z && pre.y <= pre.z }
                Foo::Duck(d) => { post.z == pre.z }
                _ => { post.z == pre.z }
            })
            &&& (c && pre.x == post.x && pre.y == post.y)
        }

        proof fn correct_init(post: X::State, x: int, y: int, z: int, foo: Foo) {
            requires(X::State::initialize(post, x, y, z, foo));
            ensures(rel_init(post, x, y, z, foo));
        }

        proof fn rev_init(post: X::State, x: int, y: int, z: int, foo: Foo) {
            requires(rel_init(post, x, y, z, foo));
            ensures(X::State::initialize(post, x, y, z, foo));
        }

        proof fn correct_tr1(pre: X::State, post: X::State, foo: Foo, c: bool) {
            requires(X::State::tr1(pre, post, foo, c));
            ensures(rel_tr1(pre, post, foo, c));
        }

        proof fn rev_tr1(pre: X::State, post: X::State, foo: Foo, c: bool) {
            requires(rel_tr1(pre, post, foo, c));
            ensures(X::State::tr1(pre, post, foo, c));
        }

        proof fn correct_tr1_strong(pre: X::State, post: X::State, foo: Foo, c: bool) {
            requires(X::State::tr1_strong(pre, post, foo, c));
            ensures(rel_tr1_strong(pre, post, foo, c));
        }

        proof fn rev_tr1_strong(pre: X::State, post: X::State, foo: Foo, c: bool) {
            requires(rel_tr1_strong(pre, post, foo, c));
            ensures(X::State::tr1_strong(pre, post, foo, c));
        }

        } // verus!

    } => Ok(())
}

test_verify_tsm! {
    #[test] relation_codegen_special_finite IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,

                #[sharding(map)]
                pub map: Map<int, int>,

                #[sharding(multiset)]
                pub mset: Multiset<int>,

                #[sharding(storage_option)]
                pub storage_opt: Option<int>,

                #[sharding(storage_map)]
                pub storage_map: Map<int, int>,
            }

            transition!{
                tr1() {
                    remove opt -= Some(5);
                    add opt += Some(8);

                    remove map -= [0 => 1];
                    have map >= [2 => 3];
                    add map += [4 => 5] by { assume(false); };

                    remove mset -= {10};
                    have mset >= {11};
                    add mset += {12};

                    withdraw storage_opt -= Some(13) by { assume(false); };
                    deposit storage_opt += Some(14);

                    withdraw storage_map -= [15 => 16] by { assume(false); };
                    deposit storage_map += [17 => 18] by { assume(false); };
                }
            }

            transition!{
                tr2() {
                    have opt >= Some(7);
                    add map += [4 => 5] by { assume(false); };
                }
            }

            transition!{
                tr3() {
                    remove opt -= Some(7);
                    withdraw storage_opt -= Some(12) by { assume(false); };
                }
            }

            transition!{
                tr4() {
                    add opt += Some(7) by { assume(false); };
                    deposit storage_opt += Some(12) by { assume(false); };
                }
            }
        }}

        verus! {

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(5)
            &&& pre.map.contains_pair(0, 1)
            &&& pre.map.remove(0).contains_pair(2, 3)
            &&& !pre.map.remove(0).dom().contains(4)
              ==> pre.mset.count(10) >= 1
              && pre.mset.remove(10).count(11) >= 1
              && (pre.storage_opt == Option::Some(13)
                ==> (pre.storage_map.contains_pair(15, 16)
                  ==> (!pre.storage_map.remove(15).dom().contains(17)
                    ==> post.storage_map == pre.storage_map.remove(15).insert(17, 18)
                     && post.opt == Option::Some(8)
                     && post.map == pre.map.remove(0).insert(4, 5)
                     && post.mset == pre.mset.remove(10).insert(12)
                     && post.storage_opt == Option::Some(14)
                  )))
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(5)
            &&& post.opt == Option::Some(8)

            &&& pre.map.contains_pair(0, 1)
            &&& pre.map.remove(0).contains_pair(2, 3)
            &&& !pre.map.remove(0).dom().contains(4)
            &&& post.map == pre.map.remove(0).insert(4, 5)

            &&& pre.mset.count(10) >= 1
            &&& pre.mset.remove(10).count(11) >= 1
            &&& post.mset == pre.mset.remove(10).insert(12)

            &&& pre.storage_opt == Option::Some(13)
            &&& post.storage_opt == Option::Some(14)

            &&& pre.storage_map.contains_pair(15, 16)
            &&& !pre.storage_map.remove(15).dom().contains(17)
            &&& post.storage_map == pre.storage_map.remove(15).insert(17, 18)
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& !pre.map.dom().contains(4) ==> {
                &&& post.map == pre.map.insert(4, 5)
                &&& post.opt == pre.opt
                &&& post.storage_opt == pre.storage_opt
                &&& post.storage_map == pre.storage_map
                &&& post.mset == pre.mset
            }
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& !pre.map.dom().contains(4)
            &&& post.map == pre.map.insert(4, 5)
            &&& post.opt == pre.opt
            &&& post.storage_opt == pre.storage_opt
            &&& post.storage_map == pre.storage_map
            &&& post.mset == pre.mset
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& pre.storage_opt == Option::Some(12)
              ==> post.storage_opt == Option::None
                && post.map == pre.map
                && post.storage_map == pre.storage_map
                && post.mset == pre.mset
                && post.opt == Option::None
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& post.opt == Option::None
            &&& pre.storage_opt == Option::Some(12)
            &&& post.storage_opt == Option::None
            &&& post.map == pre.map
            &&& post.storage_map == pre.storage_map
            &&& post.mset == pre.mset
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            pre.opt == Option::None ==> (
              (pre.storage_opt == Option::None ==> {
                &&& post.storage_opt == Option::Some(12)
                &&& post.map == pre.map
                &&& post.storage_map == pre.storage_map
                &&& post.mset == pre.mset
                &&& post.opt == Option::Some(7)
              })
            )
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::None
            &&& post.opt == Option::Some(7)
            &&& pre.storage_opt == Option::None
            &&& post.storage_opt == Option::Some(12)
            &&& post.map == pre.map
            &&& post.storage_map == pre.storage_map
            &&& post.mset == pre.mset
        }

        proof fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        proof fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        proof fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        proof fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        proof fn correct_tr2(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2(pre, post));
            ensures(rel_tr2(pre, post));
        }

        proof fn rev_tr2(pre: Y::State, post: Y::State) {
            requires(rel_tr2(pre, post));
            ensures(Y::State::tr2(pre, post));
        }

        proof fn correct_tr2_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2_strong(pre, post));
            ensures(rel_tr2_strong(pre, post));
        }

        proof fn rev_tr2_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr2_strong(pre, post));
            ensures(Y::State::tr2_strong(pre, post));
        }

        proof fn correct_tr3(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3(pre, post));
            ensures(rel_tr3(pre, post));
        }

        proof fn rev_tr3(pre: Y::State, post: Y::State) {
            requires(rel_tr3(pre, post));
            ensures(Y::State::tr3(pre, post));
        }

        proof fn correct_tr3_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3_strong(pre, post));
            ensures(rel_tr3_strong(pre, post));
        }

        proof fn rev_tr3_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr3_strong(pre, post));
            ensures(Y::State::tr3_strong(pre, post));
        }

        proof fn correct_tr4(pre: Y::State, post: Y::State) {
            requires(Y::State::tr4(pre, post));
            ensures(rel_tr4(pre, post));
        }

        proof fn rev_tr4(pre: Y::State, post: Y::State) {
            requires(rel_tr4(pre, post));
            ensures(Y::State::tr4(pre, post));
        }

        proof fn correct_tr4_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr4_strong(pre, post));
            ensures(rel_tr4_strong(pre, post));
        }

        proof fn rev_tr4_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr4_strong(pre, post));
            ensures(Y::State::tr4_strong(pre, post));
        }

        } // verus!

    } => Ok(())
    // checked macro: tr1 withdraws from and then deposits into `storage_opt` (a replace), which
    // the checked macro rejects at the deposit (workaround: two transitions)
    ; verified => Err(err) => assert_vir_error_msg(err, "verified storage cannot deposit into a location withdrawn earlier in the same transition (one storage exchange cannot replace a stored value: its deposit must be disjoint from the pre-state storage); split the transition in two, with the intermediate state explicit: see examples/verified_tsm/storage_replace_in_two_transitions.rs")
}

test_verify_tsm! {
    #[test] relation_codegen_special_infinite IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,

                #[sharding(imap)]
                pub map: IMap<int, int>,

                #[sharding(multiset)]
                pub mset: Multiset<int>,

                #[sharding(storage_option)]
                pub storage_opt: Option<int>,

                #[sharding(storage_imap)]
                pub storage_map: IMap<int, int>,
            }

            transition!{
                tr1() {
                    remove opt -= Some(5);
                    add opt += Some(8);

                    remove map -= [0 => 1];
                    have map >= [2 => 3];
                    add map += [4 => 5] by { assume(false); };

                    remove mset -= {10};
                    have mset >= {11};
                    add mset += {12};

                    withdraw storage_opt -= Some(13) by { assume(false); };
                    deposit storage_opt += Some(14);

                    withdraw storage_map -= [15 => 16] by { assume(false); };
                    deposit storage_map += [17 => 18] by { assume(false); };
                }
            }

            transition!{
                tr2() {
                    have opt >= Some(7);
                    add map += [4 => 5] by { assume(false); };
                }
            }

            transition!{
                tr3() {
                    remove opt -= Some(7);
                    withdraw storage_opt -= Some(12) by { assume(false); };
                }
            }

            transition!{
                tr4() {
                    add opt += Some(7) by { assume(false); };
                    deposit storage_opt += Some(12) by { assume(false); };
                }
            }
        }}

        verus! {

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(5)
            &&& pre.map.contains_pair(0, 1)
            &&& pre.map.remove(0).contains_pair(2, 3)
            &&& !pre.map.remove(0).dom().contains(4)
              ==> pre.mset.count(10) >= 1
              && pre.mset.remove(10).count(11) >= 1
              && (pre.storage_opt == Option::Some(13)
                ==> (pre.storage_map.contains_pair(15, 16)
                  ==> (!pre.storage_map.remove(15).dom().contains(17)
                    ==> post.storage_map == pre.storage_map.remove(15).insert(17, 18)
                     && post.opt == Option::Some(8)
                     && post.map == pre.map.remove(0).insert(4, 5)
                     && post.mset == pre.mset.remove(10).insert(12)
                     && post.storage_opt == Option::Some(14)
                  )))
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(5)
            &&& post.opt == Option::Some(8)

            &&& pre.map.contains_pair(0, 1)
            &&& pre.map.remove(0).contains_pair(2, 3)
            &&& !pre.map.remove(0).dom().contains(4)
            &&& post.map == pre.map.remove(0).insert(4, 5)

            &&& pre.mset.count(10) >= 1
            &&& pre.mset.remove(10).count(11) >= 1
            &&& post.mset == pre.mset.remove(10).insert(12)

            &&& pre.storage_opt == Option::Some(13)
            &&& post.storage_opt == Option::Some(14)

            &&& pre.storage_map.contains_pair(15, 16)
            &&& !pre.storage_map.remove(15).dom().contains(17)
            &&& post.storage_map == pre.storage_map.remove(15).insert(17, 18)
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& !pre.map.dom().contains(4) ==> {
                &&& post.map == pre.map.insert(4, 5)
                &&& post.opt == pre.opt
                &&& post.storage_opt == pre.storage_opt
                &&& post.storage_map == pre.storage_map
                &&& post.mset == pre.mset
            }
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& !pre.map.dom().contains(4)
            &&& post.map == pre.map.insert(4, 5)
            &&& post.opt == pre.opt
            &&& post.storage_opt == pre.storage_opt
            &&& post.storage_map == pre.storage_map
            &&& post.mset == pre.mset
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& pre.storage_opt == Option::Some(12)
              ==> post.storage_opt == Option::None
                && post.map == pre.map
                && post.storage_map == pre.storage_map
                && post.mset == pre.mset
                && post.opt == Option::None
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& post.opt == Option::None
            &&& pre.storage_opt == Option::Some(12)
            &&& post.storage_opt == Option::None
            &&& post.map == pre.map
            &&& post.storage_map == pre.storage_map
            &&& post.mset == pre.mset
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            pre.opt == Option::None ==> (
              (pre.storage_opt == Option::None ==> {
                &&& post.storage_opt == Option::Some(12)
                &&& post.map == pre.map
                &&& post.storage_map == pre.storage_map
                &&& post.mset == pre.mset
                &&& post.opt == Option::Some(7)
              })
            )
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::None
            &&& post.opt == Option::Some(7)
            &&& pre.storage_opt == Option::None
            &&& post.storage_opt == Option::Some(12)
            &&& post.map == pre.map
            &&& post.storage_map == pre.storage_map
            &&& post.mset == pre.mset
        }

        proof fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        proof fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        proof fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        proof fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        proof fn correct_tr2(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2(pre, post));
            ensures(rel_tr2(pre, post));
        }

        proof fn rev_tr2(pre: Y::State, post: Y::State) {
            requires(rel_tr2(pre, post));
            ensures(Y::State::tr2(pre, post));
        }

        proof fn correct_tr2_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2_strong(pre, post));
            ensures(rel_tr2_strong(pre, post));
        }

        proof fn rev_tr2_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr2_strong(pre, post));
            ensures(Y::State::tr2_strong(pre, post));
        }

        proof fn correct_tr3(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3(pre, post));
            ensures(rel_tr3(pre, post));
        }

        proof fn rev_tr3(pre: Y::State, post: Y::State) {
            requires(rel_tr3(pre, post));
            ensures(Y::State::tr3(pre, post));
        }

        proof fn correct_tr3_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3_strong(pre, post));
            ensures(rel_tr3_strong(pre, post));
        }

        proof fn rev_tr3_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr3_strong(pre, post));
            ensures(Y::State::tr3_strong(pre, post));
        }

        proof fn correct_tr4(pre: Y::State, post: Y::State) {
            requires(Y::State::tr4(pre, post));
            ensures(rel_tr4(pre, post));
        }

        proof fn rev_tr4(pre: Y::State, post: Y::State) {
            requires(rel_tr4(pre, post));
            ensures(Y::State::tr4(pre, post));
        }

        proof fn correct_tr4_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr4_strong(pre, post));
            ensures(rel_tr4_strong(pre, post));
        }

        proof fn rev_tr4_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr4_strong(pre, post));
            ensures(Y::State::tr4_strong(pre, post));
        }

        } // verus!

    } => Ok(())
    // checked macro: tr1 withdraws from and then deposits into `storage_opt` (a replace), which
    // the checked macro rejects at the deposit (workaround: two transitions)
    ; verified => Err(err) => assert_vir_error_msg(err, "verified storage cannot deposit into a location withdrawn earlier in the same transition (one storage exchange cannot replace a stored value: its deposit must be disjoint from the pre-state storage); split the transition in two, with the intermediate state explicit: see examples/verified_tsm/storage_replace_in_two_transitions.rs")
}

test_verify_tsm! {
    #[test] relation_codegen_special_general_finite IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,

                #[sharding(map)]
                pub map: Map<int, int>,

                #[sharding(multiset)]
                pub mset: Multiset<int>,

                #[sharding(storage_option)]
                pub storage_opt: Option<int>,

                #[sharding(storage_map)]
                pub storage_map: Map<int, int>,
            }

            transition!{
                tr1() {
                    remove opt -= ( Option::Some(5) );
                    add opt += ( Option::Some(8) );

                    remove map -= ( Map::<int, int>::empty().insert(0, 1) );
                    have map >= ( Map::<int, int>::empty().insert(2, 3) );
                    add map += ( Map::<int, int>::empty().insert(4, 5) ) by { assume(false); };

                    remove mset -= ( Multiset::<int>::singleton(10) );
                    have mset >= ( Multiset::<int>::singleton(11) );
                    add mset += ( Multiset::<int>::singleton(12) );

                    withdraw storage_opt -= ( Option::Some(13) ) by { assume(false); };
                    deposit storage_opt += ( Option::Some(14) );

                    withdraw storage_map -= ( Map::<int, int>::empty().insert(15, 16) ) by { assume(false); };
                    deposit storage_map += ( Map::<int, int>::empty().insert(17, 18) ) by { assume(false); };
                }
            }

            transition!{
                tr2() {
                    have opt >= (Option::Some(7));
                    add map += (Map::<int, int>::empty().insert(4, 5)) by { assume(false); };
                }
            }

            transition!{
                tr3() {
                    remove opt -= (Option::Some(7));
                    withdraw storage_opt -= (Option::Some(12)) by { assume(false); };
                }
            }

            transition!{
                tr4() {
                    add opt += (Option::Some(7)) by { assume(false); };
                    deposit storage_opt += (Option::Some(12)) by { assume(false); };
                }
            }
        }}

        verus! {

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(5)

            &&& map![0 => 1].submap_of(pre.map)
            &&& map![2 => 3].submap_of(pre.map.remove_keys(map![0 => 1int].dom()))
            &&& pre.map.remove_keys(map![0 => 1int].dom()).dom().disjoint(map![4 => 5int].dom())

            ==> {

            &&& Multiset::singleton(10).subset_of(pre.mset)
            &&& Multiset::singleton(11).subset_of(pre.mset.sub(Multiset::singleton(10)))

            &&& (pre.storage_opt == Option::Some(13)

            ==>

            (map![15 => 16].submap_of(pre.storage_map)

            ==>

            (pre.storage_map.remove_keys(map![15 => 16int].dom()).dom().disjoint(map![17 => 18int].dom())

            ==> {

            &&& post.opt == Option::Some(8)
            &&& post.map == pre.map.remove_keys(map![0 => 1int].dom()).union_prefer_right(map![4 => 5])
            &&& post.mset ==
                pre.mset.sub(Multiset::singleton(10)).add(Multiset::singleton(12))
            &&& post.storage_opt == Option::Some(14)
            &&& post.storage_map ==
                pre.storage_map.remove_keys(map![15 => 16int].dom()).union_prefer_right(map![17 => 18])
            })))}
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(5)
            &&& post.opt == Option::Some(8)

            &&& map![0 => 1].submap_of(pre.map)
            &&& map![2 => 3].submap_of(pre.map.remove_keys(map![0 => 1int].dom()))
            &&& pre.map.remove_keys(map![0 => 1int].dom()).dom().disjoint(map![4 => 5int].dom())
            &&& post.map == pre.map.remove_keys(map![0 => 1int].dom()).union_prefer_right(map![4 => 5])

            &&& Multiset::singleton(10).subset_of(pre.mset)
            &&& Multiset::singleton(11).subset_of(pre.mset.sub(Multiset::singleton(10)))
            &&& post.mset ==
                pre.mset.sub(Multiset::singleton(10)).add(Multiset::singleton(12))

            &&& pre.storage_opt == Option::Some(13)
            &&& post.storage_opt == Option::Some(14)

            &&& map![15 => 16].submap_of(pre.storage_map)
            &&& pre.storage_map.remove_keys(map![15 => 16int].dom()).dom().disjoint(map![17 => 18int].dom())
            &&& post.storage_map ==
                pre.storage_map.remove_keys(map![15 => 16int].dom()).union_prefer_right(map![17 => 18])
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& !pre.map.dom().contains(4) ==> {
                &&& post.map == pre.map.union_prefer_right(map![4 => 5])
                &&& post.opt == pre.opt
                &&& post.storage_opt == pre.storage_opt
                &&& post.storage_map == pre.storage_map
                &&& post.mset == pre.mset
            }
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& !pre.map.dom().contains(4)
            &&& post.map == pre.map.union_prefer_right(map![4 => 5])
            &&& post.opt == pre.opt
            &&& post.storage_opt == pre.storage_opt
            &&& post.storage_map == pre.storage_map
            &&& post.mset == pre.mset
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& pre.storage_opt == Option::Some(12) ==> {
                &&& post.storage_opt == Option::None
                &&& post.map == pre.map
                &&& post.storage_map == pre.storage_map
                &&& post.mset == pre.mset
                &&& post.opt == Option::None
            }
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& post.opt == Option::None
            &&& pre.storage_opt == Option::Some(12)
            &&& post.storage_opt == Option::None
            &&& post.map == pre.map
            &&& post.storage_map == pre.storage_map
            &&& post.mset == pre.mset
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            pre.opt == Option::None ==> (
              (pre.storage_opt == Option::None ==> {
                &&& post.storage_opt == Option::Some(12)
                &&& post.map == pre.map
                &&& post.storage_map == pre.storage_map
                &&& post.mset == pre.mset
                &&& post.opt == Option::Some(7)
              })
            )
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::None
            &&& post.opt == Option::Some(7)
            &&& pre.storage_opt == Option::None
            &&& post.storage_opt == Option::Some(12)
            &&& post.map == pre.map
            &&& post.storage_map == pre.storage_map
            &&& post.mset == pre.mset
        }

        proof fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        proof fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        proof fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        proof fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        proof fn correct_tr2(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2(pre, post));
            ensures(rel_tr2(pre, post));
        }

        proof fn rev_tr2(pre: Y::State, post: Y::State) {
            requires(rel_tr2(pre, post));
            ensures(Y::State::tr2(pre, post));
        }

        proof fn correct_tr2_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2_strong(pre, post));
            ensures(rel_tr2_strong(pre, post));
        }

        proof fn rev_tr2_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr2_strong(pre, post));
            ensures(Y::State::tr2_strong(pre, post));
        }

        proof fn correct_tr3(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3(pre, post));
            ensures(rel_tr3(pre, post));
        }

        proof fn rev_tr3(pre: Y::State, post: Y::State) {
            requires(rel_tr3(pre, post));
            ensures(Y::State::tr3(pre, post));
        }

        proof fn correct_tr3_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3_strong(pre, post));
            ensures(rel_tr3_strong(pre, post));
        }

        proof fn rev_tr3_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr3_strong(pre, post));
            ensures(Y::State::tr3_strong(pre, post));
        }

        proof fn correct_tr4(pre: Y::State, post: Y::State) {
            requires(Y::State::tr4(pre, post));
            ensures(rel_tr4(pre, post));
        }

        proof fn rev_tr4(pre: Y::State, post: Y::State) {
            requires(rel_tr4(pre, post));
            ensures(Y::State::tr4(pre, post));
        }

        proof fn correct_tr4_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr4_strong(pre, post));
            ensures(rel_tr4_strong(pre, post));
        }

        proof fn rev_tr4_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr4_strong(pre, post));
            ensures(Y::State::tr4_strong(pre, post));
        }

        } // verus!
    } => Ok(())
    // checked macro: tr1 withdraws from and then deposits into `storage_opt` (a replace, here
    // with general operands `(Option::Some(..))`), which the checked macro rejects at the
    // deposit (workaround: two transitions)
    ; verified => Err(err) => assert_vir_error_msg(err, "verified storage cannot deposit into a location withdrawn earlier in the same transition (one storage exchange cannot replace a stored value: its deposit must be disjoint from the pre-state storage); split the transition in two, with the intermediate state explicit: see examples/verified_tsm/storage_replace_in_two_transitions.rs")
}

test_verify_tsm! {
    #[test] relation_codegen_special_general_infinite IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,

                #[sharding(imap)]
                pub map: IMap<int, int>,

                #[sharding(multiset)]
                pub mset: Multiset<int>,

                #[sharding(storage_option)]
                pub storage_opt: Option<int>,

                #[sharding(storage_imap)]
                pub storage_map: IMap<int, int>,
            }

            transition!{
                tr1() {
                    remove opt -= ( Option::Some(5) );
                    add opt += ( Option::Some(8) );

                    remove map -= ( IMap::<int, int>::empty().insert(0, 1) );
                    have map >= ( IMap::<int, int>::empty().insert(2, 3) );
                    add map += ( IMap::<int, int>::empty().insert(4, 5) ) by { assume(false); };

                    remove mset -= ( Multiset::<int>::singleton(10) );
                    have mset >= ( Multiset::<int>::singleton(11) );
                    add mset += ( Multiset::<int>::singleton(12) );

                    withdraw storage_opt -= ( Option::Some(13) ) by { assume(false); };
                    deposit storage_opt += ( Option::Some(14) );

                    withdraw storage_map -= ( IMap::<int, int>::empty().insert(15, 16) ) by { assume(false); };
                    deposit storage_map += ( IMap::<int, int>::empty().insert(17, 18) ) by { assume(false); };
                }
            }

            transition!{
                tr2() {
                    have opt >= (Option::Some(7));
                    add map += (IMap::<int, int>::empty().insert(4, 5)) by { assume(false); };
                }
            }

            transition!{
                tr3() {
                    remove opt -= (Option::Some(7));
                    withdraw storage_opt -= (Option::Some(12)) by { assume(false); };
                }
            }

            transition!{
                tr4() {
                    add opt += (Option::Some(7)) by { assume(false); };
                    deposit storage_opt += (Option::Some(12)) by { assume(false); };
                }
            }
        }}

        verus! {

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(5)

            &&& imap![0 => 1].submap_of(pre.map)
            &&& imap![2 => 3].submap_of(pre.map.remove_keys(imap![0 => 1int].dom()))
            &&& pre.map.remove_keys(imap![0 => 1int].dom()).dom().disjoint(imap![4 => 5int].dom())

            ==> {

            &&& Multiset::singleton(10).subset_of(pre.mset)
            &&& Multiset::singleton(11).subset_of(pre.mset.sub(Multiset::singleton(10)))

            &&& (pre.storage_opt == Option::Some(13)

            ==>

            (imap![15 => 16].submap_of(pre.storage_map)

            ==>

            (pre.storage_map.remove_keys(imap![15 => 16int].dom()).dom().disjoint(imap![17 => 18int].dom())

            ==> {

            &&& post.opt == Option::Some(8)
            &&& post.map == pre.map.remove_keys(imap![0 => 1int].dom()).union_prefer_right(imap![4 => 5])
            &&& post.mset ==
                pre.mset.sub(Multiset::singleton(10)).add(Multiset::singleton(12))
            &&& post.storage_opt == Option::Some(14)
            &&& post.storage_map ==
                pre.storage_map.remove_keys(imap![15 => 16int].dom()).union_prefer_right(imap![17 => 18])
            })))}
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(5)
            &&& post.opt == Option::Some(8)

            &&& imap![0 => 1].submap_of(pre.map)
            &&& imap![2 => 3].submap_of(pre.map.remove_keys(imap![0 => 1int].dom()))
            &&& pre.map.remove_keys(imap![0 => 1int].dom()).dom().disjoint(imap![4 => 5int].dom())
            &&& post.map == pre.map.remove_keys(imap![0 => 1int].dom()).union_prefer_right(imap![4 => 5])

            &&& Multiset::singleton(10).subset_of(pre.mset)
            &&& Multiset::singleton(11).subset_of(pre.mset.sub(Multiset::singleton(10)))
            &&& post.mset ==
                pre.mset.sub(Multiset::singleton(10)).add(Multiset::singleton(12))

            &&& pre.storage_opt == Option::Some(13)
            &&& post.storage_opt == Option::Some(14)

            &&& imap![15 => 16].submap_of(pre.storage_map)
            &&& pre.storage_map.remove_keys(imap![15 => 16int].dom()).dom().disjoint(imap![17 => 18int].dom())
            &&& post.storage_map ==
                pre.storage_map.remove_keys(imap![15 => 16int].dom()).union_prefer_right(imap![17 => 18])
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& !pre.map.dom().contains(4) ==> {
                &&& post.map == pre.map.union_prefer_right(imap![4 => 5])
                &&& post.opt == pre.opt
                &&& post.storage_opt == pre.storage_opt
                &&& post.storage_map == pre.storage_map
                &&& post.mset == pre.mset
            }
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& !pre.map.dom().contains(4)
            &&& post.map == pre.map.union_prefer_right(imap![4 => 5])
            &&& post.opt == pre.opt
            &&& post.storage_opt == pre.storage_opt
            &&& post.storage_map == pre.storage_map
            &&& post.mset == pre.mset
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& pre.storage_opt == Option::Some(12) ==> {
                &&& post.storage_opt == Option::None
                &&& post.map == pre.map
                &&& post.storage_map == pre.storage_map
                &&& post.mset == pre.mset
                &&& post.opt == Option::None
            }
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(7)
            &&& post.opt == Option::None
            &&& pre.storage_opt == Option::Some(12)
            &&& post.storage_opt == Option::None
            &&& post.map == pre.map
            &&& post.storage_map == pre.storage_map
            &&& post.mset == pre.mset
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            pre.opt == Option::None ==> (
              (pre.storage_opt == Option::None ==> {
                &&& post.storage_opt == Option::Some(12)
                &&& post.map == pre.map
                &&& post.storage_map == pre.storage_map
                &&& post.mset == pre.mset
                &&& post.opt == Option::Some(7)
              })
            )
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::None
            &&& post.opt == Option::Some(7)
            &&& pre.storage_opt == Option::None
            &&& post.storage_opt == Option::Some(12)
            &&& post.map == pre.map
            &&& post.storage_map == pre.storage_map
            &&& post.mset == pre.mset
        }

        proof fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        proof fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        proof fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        proof fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        proof fn correct_tr2(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2(pre, post));
            ensures(rel_tr2(pre, post));
        }

        proof fn rev_tr2(pre: Y::State, post: Y::State) {
            requires(rel_tr2(pre, post));
            ensures(Y::State::tr2(pre, post));
        }

        proof fn correct_tr2_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2_strong(pre, post));
            ensures(rel_tr2_strong(pre, post));
        }

        proof fn rev_tr2_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr2_strong(pre, post));
            ensures(Y::State::tr2_strong(pre, post));
        }

        proof fn correct_tr3(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3(pre, post));
            ensures(rel_tr3(pre, post));
        }

        proof fn rev_tr3(pre: Y::State, post: Y::State) {
            requires(rel_tr3(pre, post));
            ensures(Y::State::tr3(pre, post));
        }

        proof fn correct_tr3_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3_strong(pre, post));
            ensures(rel_tr3_strong(pre, post));
        }

        proof fn rev_tr3_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr3_strong(pre, post));
            ensures(Y::State::tr3_strong(pre, post));
        }

        proof fn correct_tr4(pre: Y::State, post: Y::State) {
            requires(Y::State::tr4(pre, post));
            ensures(rel_tr4(pre, post));
        }

        proof fn rev_tr4(pre: Y::State, post: Y::State) {
            requires(rel_tr4(pre, post));
            ensures(Y::State::tr4(pre, post));
        }

        proof fn correct_tr4_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr4_strong(pre, post));
            ensures(rel_tr4_strong(pre, post));
        }

        proof fn rev_tr4_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr4_strong(pre, post));
            ensures(Y::State::tr4_strong(pre, post));
        }

        } // verus!
    } => Ok(())
    // checked macro: tr1 withdraws from and then deposits into `storage_opt` (a replace, here
    // with general operands `(Option::Some(..))`), which the checked macro rejects at the
    // deposit (workaround: two transitions)
    ; verified => Err(err) => assert_vir_error_msg(err, "verified storage cannot deposit into a location withdrawn earlier in the same transition (one storage exchange cannot replace a stored value: its deposit must be disjoint from the pre-state storage); split the transition in two, with the intermediate state explicit: see examples/verified_tsm/storage_replace_in_two_transitions.rs")
}

test_verify_tsm! {
    #[test] relation_codegen_opt_general IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,

                #[sharding(storage_option)]
                pub storage_opt: Option<int>,
            }

            property!{
                ro() {
                    guard storage_opt >= (Option::<int>::None);
                }
            }

            transition!{
                tr1() {
                    have opt >= (Option::<int>::None);
                }
            }

            transition!{
                tr2() {
                    add opt += (Option::<int>::None);
                    deposit storage_opt += (Option::<int>::None);
                }
            }

            transition!{
                tr3() {
                    remove opt -= (Option::<int>::None);
                    withdraw storage_opt -= (Option::<int>::None);
                }
            }
        }}

        verus!{

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
        }

        proof fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        proof fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        proof fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        proof fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        proof fn correct_tr2(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2(pre, post));
            ensures(rel_tr2(pre, post));
        }

        proof fn rev_tr2(pre: Y::State, post: Y::State) {
            requires(rel_tr2(pre, post));
            ensures(Y::State::tr2(pre, post));
        }

        proof fn correct_tr2_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr2_strong(pre, post));
            ensures(rel_tr2_strong(pre, post));
        }

        proof fn rev_tr2_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr2_strong(pre, post));
            ensures(Y::State::tr2_strong(pre, post));
        }

        proof fn correct_tr3(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3(pre, post));
            ensures(rel_tr3(pre, post));
        }

        proof fn rev_tr3(pre: Y::State, post: Y::State) {
            requires(rel_tr3(pre, post));
            ensures(Y::State::tr3(pre, post));
        }

        proof fn correct_tr3_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr3_strong(pre, post));
            ensures(rel_tr3_strong(pre, post));
        }

        proof fn rev_tr3_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr3_strong(pre, post));
            ensures(Y::State::tr3_strong(pre, post));
        }

        }
    } => Ok(())
}

test_verify_tsm! {
    #[test] nondet_tokenizing IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Z {
            fields {
                #[sharding(variable)]
                pub v1: int,

                #[sharding(variable)]
                pub v2: int,

                #[sharding(not_tokenized)]
                pub nt: int,

                #[sharding(constant)]
                pub c: int,
            }

            init!{
                initialize() {
                    init v1 = 0;
                    init v2 = 1;
                    init nt = 2;
                    init c = 3;
                }
            }

            transition!{
                tr1() {
                    update nt = pre.nt + 1; // this is ok because the exchange fn ignores this line
                    update v1 = pre.v1 + 2;
                }
            }

            transition!{
                tr2() {
                    // v1 should be passed in as tokens, v2 read nondeterministically
                    birds_eye let x = pre.nt + pre.c + pre.v1 - pre.v2;
                    update v1 = x;
                }
            }

            transition!{
                tr3() {
                    // v1, v2 both passed in as tokens
                    birds_eye let x = pre.nt + pre.c + pre.v1 - pre.v2;
                    update v1 = x + 4 * pre.v2;
                }
            }
        }}

        verus!{
        proof fn go() {
            let tracked (Tracked(instance), Tracked(mut v1), Tracked(v2)) = Z::Instance::initialize();
            assert(equal(v1.instance_id(), instance.id()));
            assert(equal(v2.instance_id(), instance.id()));
            assert(equal(v1.value(), 0));
            assert(equal(v2.value(), 1));
            assert(equal(instance.c(), 3));

            instance.tr1(&mut v1);
            assert(equal(v1.instance_id(), instance.id()));
            assert(equal(v1.value(), 2));

            let old_v1_value = v1.value();
            let tracked (Ghost(birds_eye_v2), Ghost(birds_eye_nt)) = instance.tr2(&mut v1);
            assert(equal(v1.instance_id(), instance.id()));
            assert(equal(v1.value(),
                birds_eye_nt + instance.c() + old_v1_value - birds_eye_v2));

            let old_v1_value = v1.value();
            let birds_eye_nt = instance.tr3(&mut v1, &v2);
            assert(equal(v1.instance_id(), instance.id()));
            assert(equal(v1.value(), birds_eye_nt + instance.c() + old_v1_value + 3 * v2.value()));
        }
        }
    } => Ok(())
}

test_verify_tsm! {
    #[test] pre_in_init IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                    update t = pre.t;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "no previous state to refer to")
}

test_verify_tsm! {
    #[test] self_in_transition IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update t = self.t;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "`self` is meaningless")
}

test_verify_tsm! {
    #[test] post_in_transition IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            transition!{
                tr() {
                    update t = post.t;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "cannot refer directly to `post`")
}

test_verify_tsm! {
    #[test] test_let_pattern IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields { #[sharding(variable)] pub t: (int, int) }

            init!{
                initialize() {
                    init t = (2, 2);
                }
            }

            transition!{
                tr() {
                    let (a, b) = pre.t;
                    update t = (a + 1, b + 1);
                }
            }

            #[invariant]
            pub fn inv(&self) -> bool {
                self.t.0 == self.t.1
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }

            #[inductive(tr)]
            fn tr_inductive(pre: Self, post: Self) { }
        }}
    } => Ok(())
}

test_verify_tsm! {
    #[test] super_error IMPORTS.to_string() + verus_code_str! {
        struct Bar { }

        state_machine!{ X {
            fields { pub t: int }

            transition!{
                // this is disallowed because the macro would try to copy the path into
                // an inner module
                tr(foo: super::Bar) {
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "`super::` path not allowed here")
}

test_verify_tsm! {
    #[test] if_let_fail IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            property!{
                tr() {
                    if let x = 5 {
                        assert(x == 5);
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "do not support if-let conditionals")
}

test_verify_tsm! {
    #[test] if_let_fail_with_else IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            property!{
                tr() {
                    if let x = 5 {
                        assert(x == 5);
                    } else {
                        assert(true);
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "do not support if-let conditionals")
}

test_verify_tsm! {
    #[test] if_let_fail_with_chain IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            property!{
                tr() {
                    if true && let x = 5 {
                        assert(x == 5);
                    } else {
                        assert(true);
                    }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "do not support if-let conditionals")
}

test_verify_tsm! {
    #[test] use_self_type IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(variable)]
                pub x: int,

                #[sharding(variable)]
                pub recursing: Option<Box<Self>>,
            }

            init!{
                ini(t: Self) {
                    let r: Self = t;
                    init x = r.x;
                    init recursing = t.recursing;
                }
            }

            pub open spec fn add1(x: int) -> int {
                x + 1
            }

            transition!{
                tr(a: int) {
                    update x = Self::add1(a);
                }
            }

            transition!{
                tr2(y: Option<Box<Self>>) {
                    let t: Option<Box<Self>> = y;
                    update recursing = t;
                }
            }

            transition!{
                tr3() {
                    update recursing = Option::<Box<Self>>::None;
                }
            }

        }}

        verus!{
        pub proof fn foo() {
            let tracked (Tracked(inst), Tracked(mut x_tok), Tracked(mut r_tok)) = Y::Instance::ini(
                Y::State { x: 5, recursing: Option::None }
            );
            inst.tr(19, &mut x_tok);
            assert(x_tok.value() == 20);

            inst.tr2(Option::<Box<Y::State>>::None, &mut r_tok);
            assert(equal(Option::<Box<Y::State>>::None, r_tok.value()));

            inst.tr3(&mut r_tok);
            assert(equal(Option::<Box<Y::State>>::None, r_tok.value()));
        }
        }
    } => Ok(())
}

test_verify_tsm! {
    #[test] bind_codegen_finite IMPORTS.to_string() + verus_code_str! {

        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,

                #[sharding(map)]
                pub map: Map<int, u64>,

                #[sharding(storage_map)]
                pub storage_map: Map<int, u64>,
            }

            init!{
                initialize() {
                    init opt = Option::Some(2);
                    init map = Map::<int,u64>::empty().insert(1, 5);
                    init storage_map = Map::<int,u64>::empty().insert(1, 6);
                }
            }

            #[invariant]
            pub fn maps_eq(&self) -> bool {
                equal(self.map.dom(), self.storage_map.dom())
            }

            #[invariant]
            pub fn maps_6(&self) -> bool {
                forall |k| imply(self.storage_map.dom().contains(k),
                    self.storage_map.index(k) == 6)
            }

            transition!{
                tr1() {
                    remove opt -= Some(let x);
                    require(x == 2);
                }
            }

            transition!{
                tr2(key: int) {
                    remove map -= [key => let x];
                    require(x == 5);

                    withdraw storage_map -= [key => let y];
                    assert(y == 6);
                }
            }

            readonly!{
                tr3(key: int) {
                    have map >= [key => let x];
                    require(x == 5);

                    guard storage_map >= [key => 6];
                }
            }

            property!{
                tr4(key: int) {
                    have map >= [key => let x];
                    require(x == 5);

                    guard storage_map >= [key => 6];
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self) { }

            #[inductive(tr2)]
            fn tr2_inductive(pre: Self, post: Self, key: int) { }
        }}

        verus! {
        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(2)
            &&& post.opt == Option::None
            &&& post.map == pre.map
            &&& post.storage_map == pre.storage_map
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(2)
            &&& post.opt == Option::None
            &&& post.map == pre.map
            &&& post.storage_map == pre.storage_map
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State, key: int) -> bool {
            &&& pre.map.dom().contains(key)
            &&& pre.map.index(key) == 5

            &&& (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              ==> {
                &&& post.map == pre.map.remove(key)
                &&& post.storage_map == pre.storage_map.remove(key)
                &&& post.opt == pre.opt
              }
           )
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            &&& pre.map.dom().contains(key)
            &&& pre.map.index(key) == 5
            &&& (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              && {
                &&& post.map == pre.map.remove(key)
                &&& post.storage_map == pre.storage_map.remove(key)
                &&& post.opt == pre.opt
              }
           )
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State, key: int) -> bool {
            &&& pre.map.dom().contains(key)
            &&& pre.map.index(key) == 5

            &&& (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              ==> {
                &&& post.map == pre.map
                &&& post.storage_map == pre.storage_map
                &&& post.opt == pre.opt
              }
           )
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            &&& pre.map.dom().contains(key)
            &&& pre.map.index(key) == 5

            &&& (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              && {
                &&& post.map == pre.map
                &&& post.storage_map == pre.storage_map
                &&& post.opt == pre.opt
              }
           )
        }

        proof fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        proof fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        proof fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        proof fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        proof fn correct_tr2(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr2(pre, post, key));
            ensures(rel_tr2(pre, post, key));
        }

        proof fn rev_tr2(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr2(pre, post, key));
            ensures(Y::State::tr2(pre, post, key));
        }

        proof fn correct_tr2_strong(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr2_strong(pre, post, key));
            ensures(rel_tr2_strong(pre, post, key));
        }

        proof fn rev_tr2_strong(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr2_strong(pre, post, key));
            ensures(Y::State::tr2_strong(pre, post, key));
        }

        proof fn correct_tr3(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr3(pre, post, key));
            ensures(rel_tr3(pre, post, key));
        }

        proof fn rev_tr3(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr3(pre, post, key));
            ensures(Y::State::tr3(pre, post, key));
        }

        proof fn correct_tr3_strong(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr3_strong(pre, post, key));
            ensures(rel_tr3_strong(pre, post, key));
        }

        proof fn rev_tr3_strong(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr3_strong(pre, post, key));
            ensures(Y::State::tr3_strong(pre, post, key));
        }

        proof fn do_tokens() {
            let tracked mut m: Map<int, u64> = Map::tracked_empty();
            m.tracked_insert(1, 6u64);
            let tracked (Tracked(inst), Tracked(opt_token), Tracked(mut map_tokens)) = Y::Instance::initialize(m);

            match opt_token {
                Option::None => { assert(false); }
                Option::Some(opt_token) => {
                    inst.tr1(opt_token);

                    assert(map_tokens.dom().contains(1));
                    let tracked map_token = map_tokens.remove(1);

                    let tracked the_guard = inst.tr4(1, &map_token);
                    assert(*the_guard == 6);

                    let tracked t = inst.tr2(1, map_token);
                    assert(t == 6);
                }
            };
        }

        } // verus!

    } => Ok(())
}

test_verify_tsm! {
    #[test] bind_codegen_infinite IMPORTS.to_string() + verus_code_str! {

        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,

                #[sharding(imap)]
                pub map: IMap<int, u64>,

                #[sharding(storage_imap)]
                pub storage_map: IMap<int, u64>,
            }

            init!{
                initialize() {
                    init opt = Option::Some(2);
                    init map = IMap::<int,u64>::empty().insert(1, 5);
                    init storage_map = IMap::<int,u64>::empty().insert(1, 6);
                }
            }

            #[invariant]
            pub fn maps_eq(&self) -> bool {
                equal(self.map.dom(), self.storage_map.dom())
            }

            #[invariant]
            pub fn maps_6(&self) -> bool {
                forall |k| imply(self.storage_map.dom().contains(k),
                    self.storage_map.index(k) == 6)
            }

            transition!{
                tr1() {
                    remove opt -= Some(let x);
                    require(x == 2);
                }
            }

            transition!{
                tr2(key: int) {
                    remove map -= [key => let x];
                    require(x == 5);

                    withdraw storage_map -= [key => let y];
                    assert(y == 6);
                }
            }

            readonly!{
                tr3(key: int) {
                    have map >= [key => let x];
                    require(x == 5);

                    guard storage_map >= [key => 6];
                }
            }

            property!{
                tr4(key: int) {
                    have map >= [key => let x];
                    require(x == 5);

                    guard storage_map >= [key => 6];
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self) { }

            #[inductive(tr2)]
            fn tr2_inductive(pre: Self, post: Self, key: int) { }
        }}

        verus! {
        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(2)
            &&& post.opt == Option::None
            &&& post.map == pre.map
            &&& post.storage_map == pre.storage_map
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt == Option::Some(2)
            &&& post.opt == Option::None
            &&& post.map == pre.map
            &&& post.storage_map == pre.storage_map
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State, key: int) -> bool {
            &&& pre.map.dom().contains(key)
            &&& pre.map.index(key) == 5

            &&& (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              ==> {
                &&& post.map == pre.map.remove(key)
                &&& post.storage_map == pre.storage_map.remove(key)
                &&& post.opt == pre.opt
              }
           )
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            &&& pre.map.dom().contains(key)
            &&& pre.map.index(key) == 5
            &&& (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              && {
                &&& post.map == pre.map.remove(key)
                &&& post.storage_map == pre.storage_map.remove(key)
                &&& post.opt == pre.opt
              }
           )
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State, key: int) -> bool {
            &&& pre.map.dom().contains(key)
            &&& pre.map.index(key) == 5

            &&& (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              ==> {
                &&& post.map == pre.map
                &&& post.storage_map == pre.storage_map
                &&& post.opt == pre.opt
              }
           )
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            &&& pre.map.dom().contains(key)
            &&& pre.map.index(key) == 5

            &&& (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              && {
                &&& post.map == pre.map
                &&& post.storage_map == pre.storage_map
                &&& post.opt == pre.opt
              }
           )
        }

        proof fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        proof fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        proof fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        proof fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        proof fn correct_tr2(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr2(pre, post, key));
            ensures(rel_tr2(pre, post, key));
        }

        proof fn rev_tr2(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr2(pre, post, key));
            ensures(Y::State::tr2(pre, post, key));
        }

        proof fn correct_tr2_strong(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr2_strong(pre, post, key));
            ensures(rel_tr2_strong(pre, post, key));
        }

        proof fn rev_tr2_strong(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr2_strong(pre, post, key));
            ensures(Y::State::tr2_strong(pre, post, key));
        }

        proof fn correct_tr3(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr3(pre, post, key));
            ensures(rel_tr3(pre, post, key));
        }

        proof fn rev_tr3(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr3(pre, post, key));
            ensures(Y::State::tr3(pre, post, key));
        }

        proof fn correct_tr3_strong(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr3_strong(pre, post, key));
            ensures(rel_tr3_strong(pre, post, key));
        }

        proof fn rev_tr3_strong(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr3_strong(pre, post, key));
            ensures(Y::State::tr3_strong(pre, post, key));
        }

        proof fn do_tokens() {
            let tracked mut m: IMap<int, u64> = IMap::tracked_empty();
            m.tracked_insert(1, 6u64);
            let tracked (Tracked(inst), Tracked(opt_token), Tracked(mut map_tokens)) = Y::Instance::initialize(m);

            match opt_token {
                Option::None => { assert(false); }
                Option::Some(opt_token) => {
                    inst.tr1(opt_token);

                    assert(map_tokens.dom().contains(1));
                    let tracked map_token = map_tokens.remove(1);

                    let tracked the_guard = inst.tr4(1, &map_token);
                    assert(*the_guard == 6);

                    let tracked t = inst.tr2(1, map_token);
                    assert(t == 6);
                }
            };
        }

        } // verus!

    } => Ok(())
}

test_verify_tsm! {
    #[test] bind_fail_add IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,
            }

            transition!{
                tr1() {
                    add opt += Some(let x);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "pattern-binding cannot be used in an 'add' statement")
}

test_verify_tsm! {
    #[test] bind_fail_deposit IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(storage_option)]
                pub opt: Option<int>,
            }

            transition!{
                tr1() {
                    deposit opt += Some(let x);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "pattern-binding cannot be used in a 'deposit' statement")
}

test_verify_tsm! {
    #[test] bind_fail_guard IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(storage_option)]
                pub opt: Option<int>,
            }

            transition!{
                tr1() {
                    guard opt >= Some(let x);
                }
            }
        }}
    } => Err(e) => assert_any_vir_error_msg(e, "pattern-binding cannot be used in a 'guard' statement")
}

test_verify_tsm! {
    #[test] assert_let_fail_1_bind IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(variable)]
                pub opt: Option<int>,
            }

            transition!{
                tr1() {
                    assert let Option::Some(x) = pre.opt;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "unable to prove safety condition that the pattern matches")
    // TODO(checked macro): report safety conditions with the trusted macro's messages and spans.
    ; verified => Err(e) => assert_fails_anywhere(e, 1)
}

test_verify_tsm! {
    #[test] assert_let_fail_0_bind IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(variable)]
                pub opt: Option<int>,
            }

            transition!{
                tr1() {
                    assert let Option::Some(_) = pre.opt;
                }
            }
        }}
    } => Err(e) => assert_any_vir_error_msg(e, "unable to prove safety condition that the pattern matches")
    // The checked macro reports the failing safety condition at the macro invocation.
    ; verified => Err(e) => assert_fails_anywhere(e, 1)
}

test_verify_tsm! {
    #[test] assert_require_let_codegen IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(variable)]
                pub opt1: Option<int>,

                #[sharding(variable)]
                pub opt2: Option<int>,

                #[sharding(variable)]
                pub opt3: Option<int>,

                #[sharding(variable)]
                pub opt4: Option<int>,
            }

            init!{
                initialize() {
                    init opt1 = Option::Some(0);
                    init opt2 = Option::Some(5);
                    init opt3 = Option::None;
                    init opt4 = Option::Some(5);
                }
            }

            transition!{
                tr1() {
                    require let (Option::Some(x), Option::Some(y)) = (pre.opt1, pre.opt2);
                    assert let (Option::None, Option::Some(z)) = (pre.opt3, pre.opt4);

                    assert(y == z);

                    update opt1 = Option::None;
                    update opt3 = Option::Some(x + y + z);
                }
            }

            #[invariant]
            pub fn the_inv(&self) -> bool {
                imply(self.opt1 is Some, (
                    self.opt2 is Some
                        && self.opt4 is Some
                        && equal(self.opt2, self.opt4)
                        && self.opt3 is None
                ))
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self) { }
        }}

        verus! {

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            match (pre.opt1, pre.opt2) {
                (Option::Some(x), Option::Some(y)) => {
                    match (pre.opt3, pre.opt4) {
                        (Option::None, Option::Some(z)) => {
                            y == z ==> {
                                &&& post.opt1 == Option::None
                                &&& post.opt2 == pre.opt2
                                &&& post.opt3 == Option::Some(x + y + z)
                                &&& post.opt4 == pre.opt4
                            }
                        }
                        _ => {
                            true
                        }
                    }
                }
                _ => {
                    false
                }
            }
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            match (pre.opt1, pre.opt2) {
                (Option::Some(x), Option::Some(y)) => {
                    match (pre.opt3, pre.opt4) {
                        (Option::None, Option::Some(z)) => {
                            y == z &&
                            equal(post.opt1, Option::None) &&
                            equal(post.opt2, pre.opt2) &&
                            equal(post.opt3, Option::Some(x + y + z)) &&
                            equal(post.opt4, pre.opt4)
                        }
                        _ => {
                            false
                        }
                    }
                }
                _ => {
                    false
                }
            }
        }

        proof fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        proof fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        proof fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        proof fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        proof fn test_transition(
            tracked inst: Y::Instance,
            tracked t1: Y::opt1,
            tracked t2: Y::opt2,
            tracked t3: Y::opt3,
            tracked t4: Y::opt4
        ) {
            requires([
                equal(inst.id(), t1.instance_id()),
                equal(inst.id(), t2.instance_id()),
                equal(inst.id(), t3.instance_id()),
                equal(inst.id(), t4.instance_id()),
                equal(t1.value(), Option::Some(0)),
                equal(t2.value(), Option::Some(5)),
            ]);

            let old_t1 = t1;
            let old_t3 = t3;

            let tracked mut t1 = t1;
            let tracked mut t3 = t3;

            inst.tr1(&mut t1, &t2, &mut t3, &t4);

            assert(equal(old_t3.value(), Option::None));
            assert(equal(t4.value(), Option::Some(5)));
            assert(equal(t1.value(), Option::None));
            assert(equal(t3.value(), Option::Some(10)));
        }

        proof fn test_start() {
            let tracked (Tracked(inst), Tracked(t1), Tracked(t2), Tracked(t3), Tracked(t4)) = Y::Instance::initialize();
            test_transition(inst, t1, t2, t3, t4);
        }

        } // verus!

    } => Ok(())
}

test_verify_tsm! {
    #[test] count_codegen IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(count)]
                pub c: nat,
            }

            init!{
                initialize() {
                    init c = 9;
                }
            }

            transition!{
                tr_add() {
                    add c += (2);
                }
            }

            transition!{
                tr_have() {
                    have c >= (2);
                }
            }

            transition!{
                tr_remove() {
                    remove c -= (2);
                }
            }
        }}

        verus!{

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            post.c == pre.c + 2
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            post.c == pre.c + 2
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.c >= 2 && post.c == pre.c
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.c >= 2 && post.c == pre.c
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            pre.c >= 2 && post.c == pre.c - 2
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            pre.c >= 2 && post.c == pre.c - 2
        }

        proof fn correct_tr(pre: Y::State, post: Y::State) {
            ensures([
                rel_tr1(pre, post) == Y::State::tr_add(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr_have(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),
                rel_tr3(pre, post) == Y::State::tr_remove(pre, post),
                rel_tr3_strong(pre, post) == Y::State::tr_remove_strong(pre, post),
            ]);
        }

        proof fn test_inst() {
            let tracked (Tracked(inst), Tracked(mut t1)) = Y::Instance::initialize();
            assert(t1.count() == 9);

            let tracked t2 = t1.split(2);
            let tracked t3 = t1;

            assert(t2.count() == 2);
            assert(t3.count() == 7);

            inst.tr_have(&t2);
            inst.tr_remove(t2);

            let tracked t4 = inst.tr_add();
            assert(t4.count() == 2);

            let tracked mut q = t4;
            q.join(t3);
            assert(q.count() == 9);
        }

        proof fn test_join_fail() {
            let tracked (Tracked(inst1), Tracked(t1)) = Y::Instance::initialize();
            let tracked (Tracked(inst2), Tracked(t2)) = Y::Instance::initialize();
            let tracked t = t1.join(t2); // FAILS
        }

        proof fn test_split_fail() {
            let tracked (Tracked(inst), Tracked(t1)) = Y::Instance::initialize();

            let tracked t2 = t1.split(10); // FAILS
        }

        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_tsm! {
    #[test] persistent_option_remove_fail IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_option)]
                pub c: Option<int>,
            }

            transition!{
                tr_remove() {
                    remove c -= Some(1);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "a persistent field's value can only grow, never remove or modify its data")
}

test_verify_tsm! {
    #[test] persistent_map_remove_fail IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_imap)]
                pub c: IMap<int, int>,
            }

            transition!{
                tr_remove() {
                    remove c -= [1 => 2];
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "a persistent field's value can only grow, never remove or modify its data")
}

test_verify_tsm! {
    #[test] persistent_bool_remove_fail IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_bool)]
                pub c: bool,
            }

            transition!{
                tr_remove() {
                    remove c -= true;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "a persistent field's value can only grow, never remove or modify its data")
}

test_verify_tsm! {
    #[test] use_plus_for_persistent_fail IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_bool)]
                pub c: bool,
            }

            transition!{
                tr_add() {
                    add c += true;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "for the persistent strategy `persistent_bool`, use `(union)=` instead of `+=`")
}

test_verify_tsm! {
    #[test] use_union_for_nonpersistent_fail IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(bool)]
                pub c: bool,
            }

            transition!{
                tr_add() {
                    add c (union)= true;
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "use `+=` instead of `(union)=`")
}

test_verify_tsm! {
    #[test] persistent_count_remove_fail IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_count)]
                pub c: nat,
            }

            transition!{
                tr_remove() {
                    remove c -= (1);
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "a persistent field's value can only grow, never remove or modify its data")
}

test_verify_tsm! {
    #[test] persistent_set_remove_fail IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_iset)]
                pub c: ISet<int>,
            }

            transition!{
                tr_remove() {
                    remove c -= set { 1 };
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "a persistent field's value can only grow, never remove or modify its data")
}

test_verify_tsm! {
    #[test] persistent_option_codegen IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_option)]
                pub c: Option<int>,

                #[sharding(persistent_option)]
                pub d: Option<int>,
            }

            init!{
                initialize() {
                    init c = Option::None;
                    init d = Option::Some(7);
                }
            }

            transition!{
                tr1() {
                    have d >= Some(7);
                    add c (union)= Some(3);
                }
            }

            transition!{
                tr2() {
                    add c (union)= ( Option::Some(3) );
                }
            }

            transition!{
                tr3() {
                    have c >= (
                        Option::Some(3)
                    );
                }
            }

            #[invariant]
            pub fn the_inv(&self) -> bool {
                (match self.c {
                    Option::Some(x) => x == 3,
                    _ => true,
                })
                &&
                (match self.d {
                    Option::Some(x) => x == 7,
                    _ => true,
                })
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self) { }

            #[inductive(tr2)]
            fn tr2_inductive(pre: Self, post: Self) { }

            #[inductive(tr3)]
            fn tr3_inductive(pre: Self, post: Self) { }
        }}

        verus! {
        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            &&& pre.d == Option::Some(7)
            &&& (
                (match pre.c {
                    Option::Some(x) => x == 3,
                    Option::None => true,
                })
                ==> {
                    &&& pre.d == post.d
                    &&& post.c == Option::Some(3)
                }
            )
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.d == Option::Some(7)
            &&& (
                (match pre.c {
                    Option::Some(x) => x == 3,
                    Option::None => true,
                })
                && {
                    &&& pre.d == post.d
                    &&& post.c == Option::Some(3)
                }
            )
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            (match pre.c {
                Option::Some(x) => x == 3,
                Option::None => true,
            })
            ==> {
                &&& pre.d == post.d
                &&& post.c == Option::Some(3)
            }
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            &&& (match pre.c {
                Option::Some(x) => x == 3,
                Option::None => true,
            })
            &&& {
                &&& pre.d == post.d
                &&& post.c == Option::Some(3)
            }
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            &&& pre.c == Option::Some(3)
            &&& post.c == pre.c
            &&& post.d == pre.d
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            rel_tr3(pre, post)
        }

        proof fn correct_tr(pre: Y::State, post: Y::State) {
            ensures([
                rel_tr1(pre, post) == Y::State::tr1(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr1_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr2(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr2_strong(pre, post),
                rel_tr3(pre, post) == Y::State::tr3(pre, post),
                rel_tr3_strong(pre, post) == Y::State::tr3_strong(pre, post),
            ]);
        }

        proof fn test_inst() {
            let tracked (Tracked(inst), Tracked(_c), Tracked(d_opt)) = Y::Instance::initialize();

            let tracked d = match d_opt {
                Option::Some(d) => d,
                Option::None => proof_from_false(),
            };

            let tracked cloned = d.clone();
            assert(equal(cloned.instance_id(), inst.id()));
            assert(d.value() == 7);

            let tracked c = inst.tr1(&d);
            assert(c.value() == 3);
            assert(equal(c.instance_id(), inst.id()));

            let tracked c2_opt = inst.tr2();
            let tracked c2 = match c2_opt {
                Option::Some(c2) => c2,
                Option::None => proof_from_false(),
            };
            assert(c2.value() == 3);
            assert(equal(c2.instance_id(), inst.id()));

            let tracked c_opt = Option::Some(c);
            inst.tr3(&c_opt);
        }

        } // verus!

    } => Ok(())
}

test_verify_tsm! {
    #[test] persistent_map_codegen_finite IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_map)]
                pub c: Map<int, int>,
            }

            init!{
                initialize() {
                    init c = Map::empty().insert(1, 2);
                }
            }

            transition!{
                tr1() {
                    have c >= [1 => 2];
                    add c (union)= [3 => 4];
                }
            }

            transition!{
                tr2() {
                    add c (union)= (
                        Map::empty().insert(5, 9).insert(12, 15)
                    );
                }
            }

            transition!{
                tr3() {
                    have c >= (
                        Map::empty().insert(5, 9).insert(12, 15)
                    );
                }
            }

            #[invariant]
            pub fn the_inv(&self) -> bool {
                imply(self.c.dom().contains(5), self.c.index(5) == 9)
                &&
                imply(self.c.dom().contains(12), self.c.index(12) == 15)
                &&
                imply(self.c.dom().contains(3), self.c.index(3) == 4)
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self) { }

            #[inductive(tr2)]
            fn tr2_inductive(pre: Self, post: Self) { }

            #[inductive(tr3)]
            fn tr3_inductive(pre: Self, post: Self) { }
        }}

        verus!{
        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            &&& pre.c.dom().contains(1)
            &&& pre.c.index(1) == 2
            &&& (
              (pre.c.dom().contains(3) ==> pre.c.index(3) == 4)
              ==> (
                post.c == pre.c.insert(3, 4)
              )
            )
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.c.dom().contains(1)
            &&& pre.c.index(1) == 2
            &&& (
              (pre.c.dom().contains(3) ==> pre.c.index(3) == 4)
              && (
                post.c == pre.c.insert(3, 4)
              )
            )
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            ((pre.c.dom().contains(5) ==> pre.c.index(5) == 9)
            && (pre.c.dom().contains(12) ==> pre.c.index(12) == 15))
            ==> post.c ==
                  pre.c.insert(5, 9).insert(12, 15)
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            ((pre.c.dom().contains(5) ==> pre.c.index(5) == 9)
            && (pre.c.dom().contains(12) ==> pre.c.index(12) == 15))
            && post.c ==
                  pre.c.insert(5, 9).insert(12, 15)
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            &&& (pre.c.dom().contains(5) && pre.c.index(5) == 9)
            &&& (pre.c.dom().contains(12) && pre.c.index(12) == 15)
            &&& pre.c == post.c
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            &&& (pre.c.dom().contains(5) && pre.c.index(5) == 9)
            &&& (pre.c.dom().contains(12) && pre.c.index(12) == 15)
            &&& pre.c == post.c
        }

        proof fn correct_tr(pre: Y::State, post: Y::State)
            ensures
                rel_tr1(pre, post) == Y::State::tr1(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr1_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr2(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr2_strong(pre, post),
                rel_tr3(pre, post) == Y::State::tr3(pre, post),
                rel_tr3_strong(pre, post) == Y::State::tr3_strong(pre, post),
        {
            assert_maps_equal!(
                pre.c.insert(5, 9).insert(12, 15),
                pre.c.union_prefer_right(
                    Map::empty().insert(5, 9).insert(12, 15)
                )
            );

            if rel_tr3(pre, post) {
                assert(
                  Map::empty().insert(5, 9).insert(12, 15).submap_of(pre.c)
                );
                assert(Y::State::tr3(pre, post));
            }
            if Y::State::tr3(pre, post) {
                assert(
                  Map::<int, int>::empty().insert(5, 9).insert(12, 15).dom().contains(5)
                );
                assert(
                  Map::<int, int>::empty().insert(5, 9).insert(12, 15).dom().contains(12)
                );
                assert(pre.c.dom().contains(5));
                assert(pre.c.dom().contains(12));
                assert(rel_tr3(pre, post));
            }
        }

        proof fn test_inst() {
            let tracked (Tracked(inst), Tracked(mut init_m)) = Y::Instance::initialize();
            assert(init_m.dom().contains(1));
            let tracked m_1 = init_m.remove(1);
            assert(m_1.value() == 2);

            let tracked cloned = m_1.clone();
            assert(equal(cloned.instance_id(), inst.id()));
            assert(cloned.key() == 1);
            assert(cloned.value() == 2);

            let tracked m_3 = inst.tr1(&m_1);
            assert(m_3.value() == 4);

            let tracked m_5_12 = inst.tr2();
            assert(m_5_12.map() =~= map![5 => 9, 12 => 15]);
            assert(m_5_12.instance_id() == inst.id());

            inst.tr3(&m_5_12);
        }

        } // verus!
    } => Ok(())
}

test_verify_tsm! {
    #[test] persistent_map_codegen_infinite IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_imap)]
                pub c: IMap<int, int>,
            }

            init!{
                initialize() {
                    init c = IMap::empty().insert(1, 2);
                }
            }

            transition!{
                tr1() {
                    have c >= [1 => 2];
                    add c (union)= [3 => 4];
                }
            }

            transition!{
                tr2() {
                    add c (union)= (
                        IMap::empty().insert(5, 9).insert(12, 15)
                    );
                }
            }

            transition!{
                tr3() {
                    have c >= (
                        IMap::empty().insert(5, 9).insert(12, 15)
                    );
                }
            }

            #[invariant]
            pub fn the_inv(&self) -> bool {
                imply(self.c.dom().contains(5), self.c.index(5) == 9)
                &&
                imply(self.c.dom().contains(12), self.c.index(12) == 15)
                &&
                imply(self.c.dom().contains(3), self.c.index(3) == 4)
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self) { }

            #[inductive(tr1)]
            fn tr1_inductive(pre: Self, post: Self) { }

            #[inductive(tr2)]
            fn tr2_inductive(pre: Self, post: Self) { }

            #[inductive(tr3)]
            fn tr3_inductive(pre: Self, post: Self) { }
        }}

        verus!{
        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            &&& pre.c.dom().contains(1)
            &&& pre.c.index(1) == 2
            &&& (
              (pre.c.dom().contains(3) ==> pre.c.index(3) == 4)
              ==> (
                post.c == pre.c.insert(3, 4)
              )
            )
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.c.dom().contains(1)
            &&& pre.c.index(1) == 2
            &&& (
              (pre.c.dom().contains(3) ==> pre.c.index(3) == 4)
              && (
                post.c == pre.c.insert(3, 4)
              )
            )
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            ((pre.c.dom().contains(5) ==> pre.c.index(5) == 9)
            && (pre.c.dom().contains(12) ==> pre.c.index(12) == 15))
            ==> post.c ==
                  pre.c.insert(5, 9).insert(12, 15)
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            ((pre.c.dom().contains(5) ==> pre.c.index(5) == 9)
            && (pre.c.dom().contains(12) ==> pre.c.index(12) == 15))
            && post.c ==
                  pre.c.insert(5, 9).insert(12, 15)
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            &&& (pre.c.dom().contains(5) && pre.c.index(5) == 9)
            &&& (pre.c.dom().contains(12) && pre.c.index(12) == 15)
            &&& pre.c == post.c
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            &&& (pre.c.dom().contains(5) && pre.c.index(5) == 9)
            &&& (pre.c.dom().contains(12) && pre.c.index(12) == 15)
            &&& pre.c == post.c
        }

        proof fn correct_tr(pre: Y::State, post: Y::State)
            ensures
                rel_tr1(pre, post) == Y::State::tr1(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr1_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr2(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr2_strong(pre, post),
                rel_tr3(pre, post) == Y::State::tr3(pre, post),
                rel_tr3_strong(pre, post) == Y::State::tr3_strong(pre, post),
        {
            assert_imaps_equal!(
                pre.c.insert(5, 9).insert(12, 15),
                pre.c.union_prefer_right(
                    IMap::empty().insert(5, 9).insert(12, 15)
                )
            );

            if rel_tr3(pre, post) {
                assert(
                  IMap::empty().insert(5, 9).insert(12, 15).submap_of(pre.c)
                );
                assert(Y::State::tr3(pre, post));
            }
            if Y::State::tr3(pre, post) {
                assert(
                  IMap::<int, int>::empty().insert(5, 9).insert(12, 15).dom().contains(5)
                );
                assert(
                  IMap::<int, int>::empty().insert(5, 9).insert(12, 15).dom().contains(12)
                );
                assert(pre.c.dom().contains(5));
                assert(pre.c.dom().contains(12));
                assert(rel_tr3(pre, post));
            }
        }

        proof fn test_inst() {
            let tracked (Tracked(inst), Tracked(mut init_m)) = Y::Instance::initialize();
            assert(init_m.dom().contains(1));
            let tracked m_1 = init_m.remove(1);
            assert(m_1.value() == 2);

            let tracked cloned = m_1.clone();
            assert(equal(cloned.instance_id(), inst.id()));
            assert(cloned.key() == 1);
            assert(cloned.value() == 2);

            let tracked m_3 = inst.tr1(&m_1);
            assert(m_3.value() == 4);

            let tracked m_5_12 = inst.tr2();
            assert(m_5_12.map() =~= imap![5 => 9, 12 => 15]);
            assert(m_5_12.instance_id() == inst.id());

            inst.tr3(&m_5_12);
        }

        } // verus!
    } => Ok(())
}

test_verify_tsm! {
    #[test] pattern_binding_withdraw_assert_fails IMPORTS.to_string() + verus_code_str! {
        pub enum Goo {
            Bar,
            Qux(u64),
            Tal(u64, u64),
        }

        tokenized_state_machine!{ Y {
            fields {
                #[sharding(storage_imap)]
                pub storage_m: IMap<int, Goo>,

                #[sharding(storage_option)]
                pub storage_opt: Option<Goo>,
            }

            transition!{
                tr1() {
                    withdraw storage_opt -= Some(let Goo::Bar) by { // FAILS
                        assume(pre.storage_opt is Some);
                    };
                }
            }

            transition!{
                tr2() {
                    withdraw storage_opt -= Some(let Goo::Qux(id1)) by { // FAILS
                        assume(pre.storage_opt is Some);
                    };
                }
            }

            transition!{
                tr3() {
                    withdraw storage_opt -= Some(let Goo::Tal(id1, id2)) by { // FAILS
                        assume(pre.storage_opt is Some);
                    };
                }
            }

            transition!{
                tr4() {
                    withdraw storage_m -= [1 => let Goo::Bar] by { // FAILS
                        assume(pre.storage_m.dom().contains(1));
                    };
                }
            }

            transition!{
                tr5() {
                    withdraw storage_m -= [1 => let Goo::Qux(id1)] by { // FAILS
                        assume(pre.storage_m.dom().contains(1));
                    };
                }
            }

            transition!{
                tr6() {
                    withdraw storage_m -= [1 => let Goo::Tal(id1, id2)] by { // FAILS
                        assume(pre.storage_m.dom().contains(1));
                    };
                }
            }
        }}
    } => Err(e) => assert_fails(e, 6)
    ; verified cheating "test source contains `by { assume(pre.storage_..) }` on its withdrawals"
}

test_verify_tsm! {
    #[test] special_refutable_pattern_binding_codegen_finite IMPORTS.to_string() + verus_code_str! {
        pub enum Goo {
            Bar,
            Qux(u64),
            Tal(u64, u64),
        }

        tokenized_state_machine!{ Y {
            fields {
                #[sharding(map)]
                pub m: Map<int, Goo>,

                #[sharding(storage_map)]
                pub storage_m: Map<int, Goo>,

                #[sharding(option)]
                pub opt: Option<Goo>,

                #[sharding(storage_option)]
                pub storage_opt: Option<Goo>,
            }

            init!{
                initialize(m: Map<int, Goo>, opt: Option<Goo>) {
                    init m = m;
                    init storage_m = m;
                    init opt = opt;
                    init storage_opt = opt;
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self, m: Map<int, Goo>, opt: Option<Goo>) { }

            transition!{
                tr1() {
                    remove opt -= Some(let Goo::Bar);
                    withdraw storage_opt -= Some(let Goo::Bar);
                }
            }

            transition!{
                tr2() {
                    remove opt -= Some(let Goo::Qux(i1));
                    withdraw storage_opt -= Some(let Goo::Qux(j1));
                    assert(i1 == j1);
                }
            }

            transition!{
                tr3() {
                    remove opt -= Some(let Goo::Tal(i1, i2));
                    withdraw storage_opt -= Some(let Goo::Tal(j1, j2));
                    assert(i1 == j1);
                    assert(i2 == j2);
                }
            }

            transition!{
                tr4(key: int) {
                    remove m -= [key => let Goo::Bar];
                    withdraw storage_m -= [key => let Goo::Bar];
                }
            }

            transition!{
                tr5(key: int) {
                    remove m -= [key => let Goo::Qux(i1)];
                    withdraw storage_m -= [key => let Goo::Qux(j1)];
                    assert(i1 == j1);
                }
            }

            transition!{
                tr6(key: int) {
                    remove m -= [key => let Goo::Tal(i1, i2)];
                    withdraw storage_m -= [key => let Goo::Tal(j1, j2)];
                    assert(i1 == j1);
                    assert(i2 == j2);
                }
            }

            transition!{
                tr7(key: int) {
                    have opt >= Some(let Goo::Bar);
                    have m >= [key => let Goo::Bar];
                }
            }

            transition!{
                tr8(key: int) {
                    have opt >= Some(let Goo::Qux(i1));
                    have m >= [key => let Goo::Qux(j1)];
                    require(i1 == j1);
                }
            }

            transition!{
                tr9(key: int) {
                    have opt >= Some(let Goo::Tal(i1, i2));
                    have m >= [key => let Goo::Tal(j1, j2)];
                    require(i1 == j1);
                    require(i2 == j2);
                }
            }

            #[invariant]
            pub fn the_inv(&self) -> bool {
                equal(self.m, self.storage_m)
                && equal(self.opt, self.storage_opt)
            }

                #[inductive(tr1)]
                fn tr1_inductive(pre: Self, post: Self) { }

                #[inductive(tr2)]
                fn tr2_inductive(pre: Self, post: Self) { }

                #[inductive(tr3)]
                fn tr3_inductive(pre: Self, post: Self) { }

                #[inductive(tr4)]
                fn tr4_inductive(pre: Self, post: Self, key: int) { }

                #[inductive(tr5)]
                fn tr5_inductive(pre: Self, post: Self, key: int) { }

                #[inductive(tr6)]
                fn tr6_inductive(pre: Self, post: Self, key: int) { }

                #[inductive(tr7)]
                fn tr7_inductive(pre: Self, post: Self, key: int) { }

                #[inductive(tr8)]
                fn tr8_inductive(pre: Self, post: Self, key: int) { }

                #[inductive(tr9)]
                fn tr9_inductive(pre: Self, post: Self, key: int) { }
        }}

        verus! {
        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            match pre.opt {
                Option::Some(Goo::Bar) => {
                    match pre.storage_opt {
                        Option::Some(Goo::Bar) => {
                            equal(post.opt, Option::None)
                            && equal(post.storage_opt, Option::None)
                            && equal(post.m, pre.m)
                            && equal(post.storage_m, pre.storage_m)
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            match pre.opt {
                Option::Some(Goo::Bar) => {
                    match pre.storage_opt {
                        Option::Some(Goo::Bar) => {
                            equal(post.opt, Option::None)
                            && equal(post.storage_opt, Option::None)
                            && equal(post.m, pre.m)
                            && equal(post.storage_m, pre.storage_m)
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            match pre.opt {
                Option::Some(Goo::Qux(i1)) => {
                    match pre.storage_opt {
                        Option::Some(Goo::Qux(j1)) => {
                            (i1 == j1) ==> {
                            &&& post.opt == Option::None
                            &&& post.storage_opt == Option::None
                            &&& post.m == pre.m
                            &&& post.storage_m == pre.storage_m
                            }
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            match pre.opt {
                Option::Some(Goo::Qux(i1)) => {
                    match pre.storage_opt {
                        Option::Some(Goo::Qux(j1)) => {
                            &&& i1 == j1
                            &&& post.opt == Option::None
                            &&& post.storage_opt == Option::None
                            &&& post.m == pre.m
                            &&& post.storage_m == pre.storage_m
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            match pre.opt {
                Option::Some(Goo::Tal(i1, i2)) => {
                    match pre.storage_opt {
                        Option::Some(Goo::Tal(j1, j2)) => {
                            (i1 == j1 && i2 == j2) ==> {
                            &&& post.opt == Option::None
                            &&& post.storage_opt == Option::None
                            &&& post.m == pre.m
                            &&& post.storage_m == pre.storage_m
                            }
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            match pre.opt {
                Option::Some(Goo::Tal(i1, i2)) => {
                    match pre.storage_opt {
                        Option::Some(Goo::Tal(j1, j2)) => {
                            &&& i1 == j1 && i2 == j2
                            &&& post.opt == Option::None
                            &&& post.storage_opt == Option::None
                            &&& post.m == pre.m
                            &&& post.storage_m == pre.storage_m
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.m.dom().contains(key)
            && match pre.m.index(key) {
                Goo::Bar => {
                    pre.storage_m.dom().contains(key)
                    ==> match pre.storage_m.index(key) {
                        Goo::Bar => {
                            &&& post.opt == pre.opt
                            &&& post.storage_opt == pre.storage_opt
                            &&& post.m == pre.m.remove(key)
                            &&& post.storage_m == pre.storage_m.remove(key)
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.m.dom().contains(key)
            && match pre.m.index(key) {
                Goo::Bar => {
                    pre.storage_m.dom().contains(key)
                    && match pre.storage_m.index(key) {
                        Goo::Bar => {
                            &&& post.opt == pre.opt
                            &&& post.storage_opt == pre.storage_opt
                            &&& post.m == pre.m.remove(key)
                            &&& post.storage_m == pre.storage_m.remove(key)
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr5(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.m.dom().contains(key)
            && match pre.m.index(key) {
                Goo::Qux(i1) => {
                    pre.storage_m.dom().contains(key)
                    ==> match pre.storage_m.index(key) {
                        Goo::Qux(j1) => {
                            (i1 == j1) ==> {
                            &&& post.opt == pre.opt
                            &&& post.storage_opt == pre.storage_opt
                            &&& post.m == pre.m.remove(key)
                            &&& post.storage_m == pre.storage_m.remove(key)
                            }
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr5_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.m.dom().contains(key)
            && match pre.m.index(key) {
                Goo::Qux(i1) => {
                    pre.storage_m.dom().contains(key)
                    && match pre.storage_m.index(key) {
                        Goo::Qux(j1) => {
                            &&& i1 == j1
                            &&& post.opt == pre.opt
                            &&& post.storage_opt == pre.storage_opt
                            &&& post.m == pre.m.remove(key)
                            &&& post.storage_m == pre.storage_m.remove(key)
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr6(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.m.dom().contains(key)
            && match pre.m.index(key) {
                Goo::Tal(i1, i2) => {
                    pre.storage_m.dom().contains(key)
                    ==> match pre.storage_m.index(key) {
                        Goo::Tal(j1, j2) => {
                            (i1 == j1 && i2 == j2) ==> {
                            &&& post.opt == pre.opt
                            &&& post.storage_opt == pre.storage_opt
                            &&& post.m == pre.m.remove(key)
                            &&& post.storage_m == pre.storage_m.remove(key)
                            }
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr6_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.m.dom().contains(key)
            && match pre.m.index(key) {
                Goo::Tal(i1, i2) => {
                    pre.storage_m.dom().contains(key)
                    && match pre.storage_m.index(key) {
                        Goo::Tal(j1, j2) => {
                            i1 == j1 && i2 == j2
                            && equal(post.opt, pre.opt)
                            && equal(post.storage_opt, pre.storage_opt)
                            && equal(post.m, pre.m.remove(key))
                            && equal(post.storage_m, pre.storage_m.remove(key))
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr7(pre: Y::State, post: Y::State, key: int) -> bool {
            match pre.opt {
                Option::Some(Goo::Bar) => {
                    pre.m.dom().contains(key)
                    && match pre.m.index(key) {
                        Goo::Bar => equal(post, pre),
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr7_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            rel_tr7(pre, post, key)
        }

        spec fn rel_tr8(pre: Y::State, post: Y::State, key: int) -> bool {
            match pre.opt {
                Option::Some(Goo::Qux(i1)) => {
                    pre.m.dom().contains(key)
                    && match pre.m.index(key) {
                        Goo::Qux(j1) => i1 == j1 && equal(post, pre),
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr8_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            rel_tr8(pre, post, key)
        }

        spec fn rel_tr9(pre: Y::State, post: Y::State, key: int) -> bool {
            match pre.opt {
                Option::Some(Goo::Tal(i1, i2)) => {
                    pre.m.dom().contains(key)
                    && match pre.m.index(key) {
                        Goo::Tal(j1, j2) => i1 == j1 && i2 == j2 && equal(post, pre),
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr9_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            rel_tr9(pre, post, key)
        }

        proof fn correct_tr(pre: Y::State, post: Y::State, key: int) {
          ensures([
              rel_tr1(pre, post) == Y::State::tr1(pre, post),
              rel_tr1_strong(pre, post) == Y::State::tr1_strong(pre, post),
              rel_tr2(pre, post) == Y::State::tr2(pre, post),
              rel_tr2_strong(pre, post) == Y::State::tr2_strong(pre, post),
              rel_tr3(pre, post) == Y::State::tr3(pre, post),
              rel_tr3_strong(pre, post) == Y::State::tr3_strong(pre, post),
              rel_tr4(pre, post, key) == Y::State::tr4(pre, post, key),
              rel_tr4_strong(pre, post, key) == Y::State::tr4_strong(pre, post, key),
              rel_tr5(pre, post, key) == Y::State::tr5(pre, post, key),
              rel_tr5_strong(pre, post, key) == Y::State::tr5_strong(pre, post, key),
              rel_tr6(pre, post, key) == Y::State::tr6(pre, post, key),
              rel_tr6_strong(pre, post, key) == Y::State::tr6_strong(pre, post, key),
              rel_tr7(pre, post, key) == Y::State::tr7(pre, post, key),
              rel_tr7_strong(pre, post, key) == Y::State::tr7_strong(pre, post, key),
              rel_tr8(pre, post, key) == Y::State::tr8(pre, post, key),
              rel_tr8_strong(pre, post, key) == Y::State::tr8_strong(pre, post, key),
              rel_tr9(pre, post, key) == Y::State::tr9(pre, post, key),
              rel_tr9_strong(pre, post, key) == Y::State::tr9_strong(pre, post, key),
          ]);
        }

        proof fn test_inst1() {
            let tracked mut p_m = Map::tracked_empty();
            p_m.tracked_insert(1, Goo::Bar);

            let tracked (Tracked(inst), Tracked(mut m_token), Tracked(opt_token)) = Y::Instance::initialize(
                map![1 => Goo::Bar],
                Option::Some(Goo::Bar),
                p_m,
                Option::Some(Goo::Bar),
            );

            assert(m_token.dom().contains(1));
            let tracked kv = m_token.remove(1);
            let tracked o = match opt_token {
                Option::None => proof_from_false(),
                Option::Some(t) => t,
            };

            inst.tr7(1, &kv, &o);

            let tracked wi = inst.tr1(o);
            assert(equal(wi, Goo::Bar));

            let tracked wi2 = inst.tr4(1, kv);
            assert(equal(wi2, Goo::Bar));
        }

        proof fn test_inst2() {
            let tracked mut p_m = Map::tracked_empty();
            p_m.tracked_insert(1, Goo::Qux(8u64));

            let tracked (Tracked(inst), Tracked(mut m_token), Tracked(opt_token)) = Y::Instance::initialize(
                map![1 => Goo::Qux(8u64)],
                Option::Some(Goo::Qux(8u64)),
                p_m,
                Option::Some(Goo::Qux(8u64)),
            );

            assert(m_token.dom().contains(1));
            let tracked kv = m_token.remove(1);
            let tracked o = match opt_token {
                Option::None => proof_from_false(),
                Option::Some(t) => t,
            };

            inst.tr8(1, &kv, &o);

            let tracked wi = inst.tr2(o);
            assert(equal(wi, Goo::Qux(8u64)));

            let tracked wi2 = inst.tr5(1, kv);
            assert(equal(wi2, Goo::Qux(8u64)));
        }

        proof fn test_inst3() {
            let tracked mut p_m = Map::tracked_empty();
            p_m.tracked_insert(1, Goo::Tal(8u64, 9u64));

            let tracked (Tracked(inst), Tracked(mut m_token), Tracked(opt_token)) = Y::Instance::initialize(
                map![1 => Goo::Tal(8u64, 9u64)],
                Option::Some(Goo::Tal(8u64, 9u64)),
                p_m,
                Option::Some(Goo::Tal(8u64, 9u64)),
            );

            assert(m_token.dom().contains(1));
            let tracked kv = m_token.remove(1);
            let tracked o = match opt_token {
                Option::None => proof_from_false(),
                Option::Some(t) => t,
            };

            inst.tr9(1, &kv, &o);

            let tracked wi = inst.tr3(o);
            assert(equal(wi, Goo::Tal(8u64, 9u64)));

            let tracked wi2 = inst.tr6(1, kv);
            assert(equal(wi2, Goo::Tal(8u64, 9u64)));
        }

        proof fn test_precondition_remove1(tracked inst: Y::Instance, tracked t: Y::opt)
        {
          requires(equal(t.instance_id(), inst.id()));
          let tracked k = inst.tr1(t); // FAILS
        }

        proof fn test_precondition_remove2(tracked inst: Y::Instance, tracked t: Y::opt)
        {
          requires(equal(t.instance_id(), inst.id()));
          let tracked k = inst.tr2(t); // FAILS
        }

        proof fn test_precondition_remove3(tracked inst: Y::Instance, tracked t: Y::opt)
        {
          requires(equal(t.instance_id(), inst.id()));
          let tracked k = inst.tr3(t); // FAILS
        }

        proof fn test_precondition_map_remove1(tracked inst: Y::Instance, tracked t: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && t.key() == 1);
          let tracked k = inst.tr4(1, t); // FAILS
        }

        proof fn test_precondition_map_remove2(tracked inst: Y::Instance, tracked t: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && t.key() == 1);
          let tracked k = inst.tr5(1, t); // FAILS
        }

        proof fn test_precondition_map_remove3(tracked inst: Y::Instance, tracked t: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && t.key() == 1);
          let tracked k = inst.tr6(1, t); // FAILS
        }

        proof fn test_precondition_have1(tracked inst: Y::Instance, tracked t: Y::opt, tracked u: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && equal(u.instance_id(), inst.id()) && u.key() == 1
              && equal(t.value(), Goo::Bar)
          );
          let tracked k = inst.tr7(1, &u, &t); // FAILS
        }

        proof fn test_precondition_have2(tracked inst: Y::Instance, tracked t: Y::opt, tracked u: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && equal(u.instance_id(), inst.id()) && u.key() == 1
              && equal(u.value(), Goo::Bar)
          );
          let tracked k = inst.tr7(1, &u, &t); // FAILS
        }

        proof fn test_precondition_have3(tracked inst: Y::Instance, tracked t: Y::opt, tracked u: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && equal(u.instance_id(), inst.id()) && u.key() == 1
              && equal(u.value(), t.value()));
          let tracked k = inst.tr8(1, &u, &t); // FAILS
        }

        proof fn test_precondition_have4(tracked inst: Y::Instance, tracked t: Y::opt, tracked u: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && equal(u.instance_id(), inst.id()) && u.key() == 1
              && equal(u.value(), t.value()));
          let k = inst.tr9(1, &u, &t); // FAILS
        }

        }
    } => Err(e) => assert_fails(e, 10)
}

test_verify_tsm! {
    #[test] special_refutable_pattern_binding_codegen_infinite IMPORTS.to_string() + verus_code_str! {
        pub enum Goo {
            Bar,
            Qux(u64),
            Tal(u64, u64),
        }

        tokenized_state_machine!{ Y {
            fields {
                #[sharding(imap)]
                pub m: IMap<int, Goo>,

                #[sharding(storage_imap)]
                pub storage_m: IMap<int, Goo>,

                #[sharding(option)]
                pub opt: Option<Goo>,

                #[sharding(storage_option)]
                pub storage_opt: Option<Goo>,
            }

            init!{
                initialize(m: IMap<int, Goo>, opt: Option<Goo>) {
                    // (the checked macro's storage tokens need a finite initial storage)
                    require m.dom().finite();
                    init m = m;
                    init storage_m = m;
                    init opt = opt;
                    init storage_opt = opt;
                }
            }

            #[inductive(initialize)]
            fn initialize_inductive(post: Self, m: IMap<int, Goo>, opt: Option<Goo>) { }

            transition!{
                tr1() {
                    remove opt -= Some(let Goo::Bar);
                    withdraw storage_opt -= Some(let Goo::Bar);
                }
            }

            transition!{
                tr2() {
                    remove opt -= Some(let Goo::Qux(i1));
                    withdraw storage_opt -= Some(let Goo::Qux(j1));
                    assert(i1 == j1);
                }
            }

            transition!{
                tr3() {
                    remove opt -= Some(let Goo::Tal(i1, i2));
                    withdraw storage_opt -= Some(let Goo::Tal(j1, j2));
                    assert(i1 == j1);
                    assert(i2 == j2);
                }
            }

            transition!{
                tr4(key: int) {
                    remove m -= [key => let Goo::Bar];
                    withdraw storage_m -= [key => let Goo::Bar];
                }
            }

            transition!{
                tr5(key: int) {
                    remove m -= [key => let Goo::Qux(i1)];
                    withdraw storage_m -= [key => let Goo::Qux(j1)];
                    assert(i1 == j1);
                }
            }

            transition!{
                tr6(key: int) {
                    remove m -= [key => let Goo::Tal(i1, i2)];
                    withdraw storage_m -= [key => let Goo::Tal(j1, j2)];
                    assert(i1 == j1);
                    assert(i2 == j2);
                }
            }

            transition!{
                tr7(key: int) {
                    have opt >= Some(let Goo::Bar);
                    have m >= [key => let Goo::Bar];
                }
            }

            transition!{
                tr8(key: int) {
                    have opt >= Some(let Goo::Qux(i1));
                    have m >= [key => let Goo::Qux(j1)];
                    require(i1 == j1);
                }
            }

            transition!{
                tr9(key: int) {
                    have opt >= Some(let Goo::Tal(i1, i2));
                    have m >= [key => let Goo::Tal(j1, j2)];
                    require(i1 == j1);
                    require(i2 == j2);
                }
            }

            #[invariant]
            pub fn the_inv(&self) -> bool {
                equal(self.m, self.storage_m)
                && equal(self.opt, self.storage_opt)
            }

                #[inductive(tr1)]
                fn tr1_inductive(pre: Self, post: Self) { }

                #[inductive(tr2)]
                fn tr2_inductive(pre: Self, post: Self) { }

                #[inductive(tr3)]
                fn tr3_inductive(pre: Self, post: Self) { }

                #[inductive(tr4)]
                fn tr4_inductive(pre: Self, post: Self, key: int) { }

                #[inductive(tr5)]
                fn tr5_inductive(pre: Self, post: Self, key: int) { }

                #[inductive(tr6)]
                fn tr6_inductive(pre: Self, post: Self, key: int) { }

                #[inductive(tr7)]
                fn tr7_inductive(pre: Self, post: Self, key: int) { }

                #[inductive(tr8)]
                fn tr8_inductive(pre: Self, post: Self, key: int) { }

                #[inductive(tr9)]
                fn tr9_inductive(pre: Self, post: Self, key: int) { }
        }}

        verus! {
        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            match pre.opt {
                Option::Some(Goo::Bar) => {
                    match pre.storage_opt {
                        Option::Some(Goo::Bar) => {
                            equal(post.opt, Option::None)
                            && equal(post.storage_opt, Option::None)
                            && equal(post.m, pre.m)
                            && equal(post.storage_m, pre.storage_m)
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            match pre.opt {
                Option::Some(Goo::Bar) => {
                    match pre.storage_opt {
                        Option::Some(Goo::Bar) => {
                            equal(post.opt, Option::None)
                            && equal(post.storage_opt, Option::None)
                            && equal(post.m, pre.m)
                            && equal(post.storage_m, pre.storage_m)
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            match pre.opt {
                Option::Some(Goo::Qux(i1)) => {
                    match pre.storage_opt {
                        Option::Some(Goo::Qux(j1)) => {
                            (i1 == j1) ==> {
                            &&& post.opt == Option::None
                            &&& post.storage_opt == Option::None
                            &&& post.m == pre.m
                            &&& post.storage_m == pre.storage_m
                            }
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            match pre.opt {
                Option::Some(Goo::Qux(i1)) => {
                    match pre.storage_opt {
                        Option::Some(Goo::Qux(j1)) => {
                            &&& i1 == j1
                            &&& post.opt == Option::None
                            &&& post.storage_opt == Option::None
                            &&& post.m == pre.m
                            &&& post.storage_m == pre.storage_m
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            match pre.opt {
                Option::Some(Goo::Tal(i1, i2)) => {
                    match pre.storage_opt {
                        Option::Some(Goo::Tal(j1, j2)) => {
                            (i1 == j1 && i2 == j2) ==> {
                            &&& post.opt == Option::None
                            &&& post.storage_opt == Option::None
                            &&& post.m == pre.m
                            &&& post.storage_m == pre.storage_m
                            }
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            match pre.opt {
                Option::Some(Goo::Tal(i1, i2)) => {
                    match pre.storage_opt {
                        Option::Some(Goo::Tal(j1, j2)) => {
                            &&& i1 == j1 && i2 == j2
                            &&& post.opt == Option::None
                            &&& post.storage_opt == Option::None
                            &&& post.m == pre.m
                            &&& post.storage_m == pre.storage_m
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.m.dom().contains(key)
            && match pre.m.index(key) {
                Goo::Bar => {
                    pre.storage_m.dom().contains(key)
                    ==> match pre.storage_m.index(key) {
                        Goo::Bar => {
                            &&& post.opt == pre.opt
                            &&& post.storage_opt == pre.storage_opt
                            &&& post.m == pre.m.remove(key)
                            &&& post.storage_m == pre.storage_m.remove(key)
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.m.dom().contains(key)
            && match pre.m.index(key) {
                Goo::Bar => {
                    pre.storage_m.dom().contains(key)
                    && match pre.storage_m.index(key) {
                        Goo::Bar => {
                            &&& post.opt == pre.opt
                            &&& post.storage_opt == pre.storage_opt
                            &&& post.m == pre.m.remove(key)
                            &&& post.storage_m == pre.storage_m.remove(key)
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr5(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.m.dom().contains(key)
            && match pre.m.index(key) {
                Goo::Qux(i1) => {
                    pre.storage_m.dom().contains(key)
                    ==> match pre.storage_m.index(key) {
                        Goo::Qux(j1) => {
                            (i1 == j1) ==> {
                            &&& post.opt == pre.opt
                            &&& post.storage_opt == pre.storage_opt
                            &&& post.m == pre.m.remove(key)
                            &&& post.storage_m == pre.storage_m.remove(key)
                            }
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr5_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.m.dom().contains(key)
            && match pre.m.index(key) {
                Goo::Qux(i1) => {
                    pre.storage_m.dom().contains(key)
                    && match pre.storage_m.index(key) {
                        Goo::Qux(j1) => {
                            &&& i1 == j1
                            &&& post.opt == pre.opt
                            &&& post.storage_opt == pre.storage_opt
                            &&& post.m == pre.m.remove(key)
                            &&& post.storage_m == pre.storage_m.remove(key)
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr6(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.m.dom().contains(key)
            && match pre.m.index(key) {
                Goo::Tal(i1, i2) => {
                    pre.storage_m.dom().contains(key)
                    ==> match pre.storage_m.index(key) {
                        Goo::Tal(j1, j2) => {
                            (i1 == j1 && i2 == j2) ==> {
                            &&& post.opt == pre.opt
                            &&& post.storage_opt == pre.storage_opt
                            &&& post.m == pre.m.remove(key)
                            &&& post.storage_m == pre.storage_m.remove(key)
                            }
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr6_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            pre.m.dom().contains(key)
            && match pre.m.index(key) {
                Goo::Tal(i1, i2) => {
                    pre.storage_m.dom().contains(key)
                    && match pre.storage_m.index(key) {
                        Goo::Tal(j1, j2) => {
                            i1 == j1 && i2 == j2
                            && equal(post.opt, pre.opt)
                            && equal(post.storage_opt, pre.storage_opt)
                            && equal(post.m, pre.m.remove(key))
                            && equal(post.storage_m, pre.storage_m.remove(key))
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr7(pre: Y::State, post: Y::State, key: int) -> bool {
            match pre.opt {
                Option::Some(Goo::Bar) => {
                    pre.m.dom().contains(key)
                    && match pre.m.index(key) {
                        Goo::Bar => equal(post, pre),
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr7_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            rel_tr7(pre, post, key)
        }

        spec fn rel_tr8(pre: Y::State, post: Y::State, key: int) -> bool {
            match pre.opt {
                Option::Some(Goo::Qux(i1)) => {
                    pre.m.dom().contains(key)
                    && match pre.m.index(key) {
                        Goo::Qux(j1) => i1 == j1 && equal(post, pre),
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr8_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            rel_tr8(pre, post, key)
        }

        spec fn rel_tr9(pre: Y::State, post: Y::State, key: int) -> bool {
            match pre.opt {
                Option::Some(Goo::Tal(i1, i2)) => {
                    pre.m.dom().contains(key)
                    && match pre.m.index(key) {
                        Goo::Tal(j1, j2) => i1 == j1 && i2 == j2 && equal(post, pre),
                        _ => false,
                    }
                }
                _ => false,
            }
        }

        spec fn rel_tr9_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            rel_tr9(pre, post, key)
        }

        proof fn correct_tr(pre: Y::State, post: Y::State, key: int) {
          ensures([
              rel_tr1(pre, post) == Y::State::tr1(pre, post),
              rel_tr1_strong(pre, post) == Y::State::tr1_strong(pre, post),
              rel_tr2(pre, post) == Y::State::tr2(pre, post),
              rel_tr2_strong(pre, post) == Y::State::tr2_strong(pre, post),
              rel_tr3(pre, post) == Y::State::tr3(pre, post),
              rel_tr3_strong(pre, post) == Y::State::tr3_strong(pre, post),
              rel_tr4(pre, post, key) == Y::State::tr4(pre, post, key),
              rel_tr4_strong(pre, post, key) == Y::State::tr4_strong(pre, post, key),
              rel_tr5(pre, post, key) == Y::State::tr5(pre, post, key),
              rel_tr5_strong(pre, post, key) == Y::State::tr5_strong(pre, post, key),
              rel_tr6(pre, post, key) == Y::State::tr6(pre, post, key),
              rel_tr6_strong(pre, post, key) == Y::State::tr6_strong(pre, post, key),
              rel_tr7(pre, post, key) == Y::State::tr7(pre, post, key),
              rel_tr7_strong(pre, post, key) == Y::State::tr7_strong(pre, post, key),
              rel_tr8(pre, post, key) == Y::State::tr8(pre, post, key),
              rel_tr8_strong(pre, post, key) == Y::State::tr8_strong(pre, post, key),
              rel_tr9(pre, post, key) == Y::State::tr9(pre, post, key),
              rel_tr9_strong(pre, post, key) == Y::State::tr9_strong(pre, post, key),
          ]);
        }

        proof fn test_inst1() {
            let tracked mut p_m = IMap::tracked_empty();
            p_m.tracked_insert(1, Goo::Bar);

            let tracked (Tracked(inst), Tracked(mut m_token), Tracked(opt_token)) = Y::Instance::initialize(
                imap![1 => Goo::Bar],
                Option::Some(Goo::Bar),
                p_m,
                Option::Some(Goo::Bar),
            );

            assert(m_token.dom().contains(1));
            let tracked kv = m_token.remove(1);
            let tracked o = match opt_token {
                Option::None => proof_from_false(),
                Option::Some(t) => t,
            };

            inst.tr7(1, &kv, &o);

            let tracked wi = inst.tr1(o);
            assert(equal(wi, Goo::Bar));

            let tracked wi2 = inst.tr4(1, kv);
            assert(equal(wi2, Goo::Bar));
        }

        proof fn test_inst2() {
            let tracked mut p_m = IMap::tracked_empty();
            p_m.tracked_insert(1, Goo::Qux(8u64));

            let tracked (Tracked(inst), Tracked(mut m_token), Tracked(opt_token)) = Y::Instance::initialize(
                imap![1 => Goo::Qux(8u64)],
                Option::Some(Goo::Qux(8u64)),
                p_m,
                Option::Some(Goo::Qux(8u64)),
            );

            assert(m_token.dom().contains(1));
            let tracked kv = m_token.remove(1);
            let tracked o = match opt_token {
                Option::None => proof_from_false(),
                Option::Some(t) => t,
            };

            inst.tr8(1, &kv, &o);

            let tracked wi = inst.tr2(o);
            assert(equal(wi, Goo::Qux(8u64)));

            let tracked wi2 = inst.tr5(1, kv);
            assert(equal(wi2, Goo::Qux(8u64)));
        }

        proof fn test_inst3() {
            let tracked mut p_m = IMap::tracked_empty();
            p_m.tracked_insert(1, Goo::Tal(8u64, 9u64));

            let tracked (Tracked(inst), Tracked(mut m_token), Tracked(opt_token)) = Y::Instance::initialize(
                imap![1 => Goo::Tal(8u64, 9u64)],
                Option::Some(Goo::Tal(8u64, 9u64)),
                p_m,
                Option::Some(Goo::Tal(8u64, 9u64)),
            );

            assert(m_token.dom().contains(1));
            let tracked kv = m_token.remove(1);
            let tracked o = match opt_token {
                Option::None => proof_from_false(),
                Option::Some(t) => t,
            };

            inst.tr9(1, &kv, &o);

            let tracked wi = inst.tr3(o);
            assert(equal(wi, Goo::Tal(8u64, 9u64)));

            let tracked wi2 = inst.tr6(1, kv);
            assert(equal(wi2, Goo::Tal(8u64, 9u64)));
        }

        proof fn test_precondition_remove1(tracked inst: Y::Instance, tracked t: Y::opt)
        {
          requires(equal(t.instance_id(), inst.id()));
          let tracked k = inst.tr1(t); // FAILS
        }

        proof fn test_precondition_remove2(tracked inst: Y::Instance, tracked t: Y::opt)
        {
          requires(equal(t.instance_id(), inst.id()));
          let tracked k = inst.tr2(t); // FAILS
        }

        proof fn test_precondition_remove3(tracked inst: Y::Instance, tracked t: Y::opt)
        {
          requires(equal(t.instance_id(), inst.id()));
          let tracked k = inst.tr3(t); // FAILS
        }

        proof fn test_precondition_map_remove1(tracked inst: Y::Instance, tracked t: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && t.key() == 1);
          let tracked k = inst.tr4(1, t); // FAILS
        }

        proof fn test_precondition_map_remove2(tracked inst: Y::Instance, tracked t: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && t.key() == 1);
          let tracked k = inst.tr5(1, t); // FAILS
        }

        proof fn test_precondition_map_remove3(tracked inst: Y::Instance, tracked t: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && t.key() == 1);
          let tracked k = inst.tr6(1, t); // FAILS
        }

        proof fn test_precondition_have1(tracked inst: Y::Instance, tracked t: Y::opt, tracked u: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && equal(u.instance_id(), inst.id()) && u.key() == 1
              && equal(t.value(), Goo::Bar)
          );
          let tracked k = inst.tr7(1, &u, &t); // FAILS
        }

        proof fn test_precondition_have2(tracked inst: Y::Instance, tracked t: Y::opt, tracked u: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && equal(u.instance_id(), inst.id()) && u.key() == 1
              && equal(u.value(), Goo::Bar)
          );
          let tracked k = inst.tr7(1, &u, &t); // FAILS
        }

        proof fn test_precondition_have3(tracked inst: Y::Instance, tracked t: Y::opt, tracked u: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && equal(u.instance_id(), inst.id()) && u.key() == 1
              && equal(u.value(), t.value()));
          let tracked k = inst.tr8(1, &u, &t); // FAILS
        }

        proof fn test_precondition_have4(tracked inst: Y::Instance, tracked t: Y::opt, tracked u: Y::m)
        {
          requires(equal(t.instance_id(), inst.id()) && equal(u.instance_id(), inst.id()) && u.key() == 1
              && equal(u.value(), t.value()));
          let k = inst.tr9(1, &u, &t); // FAILS
        }

        }
    } => Err(e) => assert_fails(e, 10)
}

test_verify_tsm! {
    #[test] labels_wrong_type_name IMPORTS.to_string() + verus_code_str! {
        state_machine!{ Y {
            fields {
                pub x: int,
            }

            pub struct AsdfWeirdName { }
        }}
    } => Err(e) => assert_vir_error_msg(e, "only supports the declaration of a `Label` and `InitLabel` types")
}

test_verify_tsm! {
    #[test] labels_init_missing IMPORTS.to_string() + verus_code_str! {
        state_machine!{ Y {
            fields {
                pub x: int,
            }

            pub struct Label { }
            pub struct InitLabel { }

            init!{
                tr() {
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "the first param to an 'init'")
}

test_verify_tsm! {
    #[test] labels_init_missing2 IMPORTS.to_string() + verus_code_str! {
        state_machine!{ Y {
            fields {
                pub x: int,
            }

            pub struct Label { }
            pub struct InitLabel { }

            init!{
                tr(x: int) {
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "the first param to an 'init'")
}

test_verify_tsm! {
    #[test] labels_tr_missing IMPORTS.to_string() + verus_code_str! {
        state_machine!{ Y {
            fields {
                pub x: int,
            }

            pub struct Label { }
            pub struct InitLabel { }

            transition!{
                tr(x: int) {
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "the first param to a 'transition'")
}

test_verify_tsm! {
    #[test] labels_readonly_missing IMPORTS.to_string() + verus_code_str! {
        state_machine!{ Y {
            fields {
                pub x: int,
            }

            pub struct Label { }
            pub struct InitLabel { }

            readonly!{
                tr(x: int) {
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "the first param to a 'readonly'")
}

test_verify_tsm! {
    #[test] bool_codegen IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(bool)]
                pub b: bool,
            }

            init!{
                init_false() {
                    init b = false;
                }
            }

            init!{
                init_true() {
                    init b = true;
                }
            }

            transition!{
                tr_add() {
                    add b += true by {
                        assert(pre.b == false); // FAILS
                    };
                }
            }

            transition!{
                tr_have() {
                    have b >= true;
                }
            }

            transition!{
                tr_remove() {
                    remove b -= true;
                }
            }

            transition!{
                tr_add_gen(x: bool) {
                    add b += (x) by {
                        assert(pre.b == false || x == false); // FAILS
                    };
                }
            }

            transition!{
                tr_have_gen(x: bool) {
                    have b >= (x);
                }
            }

            transition!{
                tr_remove_gen(x: bool) {
                    remove b -= (x);
                }
            }
        }}

        verus!{

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            pre.b == false ==> post.b == true
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b == false && post.b == true
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.b == true && post.b == true
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b == true && post.b == true
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            pre.b == true && post.b == false
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b == true && post.b == false
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State, x: bool) -> bool {
            (!pre.b || !x) ==> (post.b == (pre.b || x))
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
            (!pre.b || !x) && (post.b == (pre.b || x))
        }

        spec fn rel_tr5(pre: Y::State, post: Y::State, x: bool) -> bool {
            (x ==> pre.b) && (post.b == pre.b)
        }

        spec fn rel_tr5_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
            (x ==> pre.b) && (post.b == pre.b)
        }

        spec fn rel_tr6(pre: Y::State, post: Y::State, x: bool) -> bool {
            (x ==> pre.b) && (post.b == (pre.b && !x))
        }

        spec fn rel_tr6_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
            (x ==> pre.b) && (post.b == (pre.b && !x))
        }

        proof fn correct_tr(pre: Y::State, post: Y::State, x: bool) {
            ensures([
                rel_tr1(pre, post) == Y::State::tr_add(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr_have(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),
                rel_tr3(pre, post) == Y::State::tr_remove(pre, post),
                rel_tr3_strong(pre, post) == Y::State::tr_remove_strong(pre, post),

                rel_tr4(pre, post, x) == Y::State::tr_add_gen(pre, post, x),
                rel_tr4_strong(pre, post, x) == Y::State::tr_add_gen_strong(pre, post, x),
                rel_tr5(pre, post, x) == Y::State::tr_have_gen(pre, post, x),
                rel_tr5_strong(pre, post, x) == Y::State::tr_have_gen_strong(pre, post, x),
                rel_tr6(pre, post, x) == Y::State::tr_remove_gen(pre, post, x),
                rel_tr6_strong(pre, post, x) == Y::State::tr_remove_gen_strong(pre, post, x),
            ]);
        }

        proof fn test_inst1() {
            let tracked (Tracked(inst), Tracked(token_f)) = Y::Instance::init_false();
            assert(token_f is None);

            let tracked tok = inst.tr_add();
            assert(equal(tok.instance_id(), inst.id()));
            inst.tr_have(&tok);
            inst.tr_remove(tok);

            let tracked opt_tok = inst.tr_add_gen(true);
            assert(opt_tok is Some);
            assert(equal(opt_tok->0.instance_id(), inst.id()));
            inst.tr_have_gen(true, &opt_tok);
            inst.tr_remove_gen(true, opt_tok);

            let tracked opt_tok = inst.tr_add_gen(false);
            assert(opt_tok is None);
            inst.tr_have_gen(false, &opt_tok);
            inst.tr_remove_gen(false, opt_tok);
        }

        proof fn test_inst1_fail() {
            let tracked (Tracked(inst), Tracked(token_f)) = Y::Instance::init_false();
            assert(token_f is None);

            let tracked opt_tok = inst.tr_add_gen(false);
            assert(opt_tok is None);
            inst.tr_have_gen(true, &opt_tok);   // FAILS
        }

        proof fn test_inst2() {
            let tracked (Tracked(inst), Tracked(token_t)) = Y::Instance::init_true();
            assert(token_t is Some);
            assert(equal(token_t->0.instance_id(), inst.id()));
        }

        }
    } => Err(e) => assert_fails(e, 3)
}

test_verify_tsm! {
    #[test] persistent_bool_codegen IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_bool)]
                pub b: bool,
            }

            init!{
                init_false() {
                    init b = false;
                }
            }

            init!{
                init_true() {
                    init b = true;
                }
            }

            transition!{
                tr_add() {
                    add b (union)= true;
                }
            }

            transition!{
                tr_have() {
                    have b >= true;
                }
            }

            transition!{
                tr_add_gen(x: bool) {
                    add b (union)= (x);
                }
            }

            transition!{
                tr_have_gen(x: bool) {
                    have b >= (x);
                }
            }
        }}

        verus!{

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            post.b == true
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            post.b == true
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.b == true && post.b == true
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b == true && post.b == true
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State, x: bool) -> bool {
            (post.b == (pre.b || x))
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
            (post.b == (pre.b || x))
        }

        spec fn rel_tr5(pre: Y::State, post: Y::State, x: bool) -> bool {
            (x ==> pre.b) && (post.b == pre.b)
        }

        spec fn rel_tr5_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
            (x ==> pre.b) && (post.b == pre.b)
        }

        proof fn correct_tr(pre: Y::State, post: Y::State, x: bool) {
            ensures([
                rel_tr1(pre, post) == Y::State::tr_add(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr_have(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),

                rel_tr4(pre, post, x) == Y::State::tr_add_gen(pre, post, x),
                rel_tr4_strong(pre, post, x) == Y::State::tr_add_gen_strong(pre, post, x),
                rel_tr5(pre, post, x) == Y::State::tr_have_gen(pre, post, x),
                rel_tr5_strong(pre, post, x) == Y::State::tr_have_gen_strong(pre, post, x),
            ]);
        }

        proof fn test_inst1() {
            let tracked (Tracked(inst), Tracked(token_f)) = Y::Instance::init_false();
            assert(token_f is None);

            let tracked tok = inst.tr_add();
            assert(equal(tok.instance_id(), inst.id()));
            inst.tr_have(&tok);

            let tracked tok1 = tok.clone();
            assert(equal(tok, tok1));

            let tracked opt_tok = inst.tr_add_gen(true);
            assert(opt_tok is Some);
            assert(equal(opt_tok->0.instance_id(), inst.id()));
            inst.tr_have_gen(true, &opt_tok);

            let tracked opt_tok = inst.tr_add_gen(false);
            assert(opt_tok is None);
            inst.tr_have_gen(false, &opt_tok);
        }

        proof fn test_inst1_fail() {
            let tracked (Tracked(inst), Tracked(token_f)) = Y::Instance::init_false();
            assert(token_f is None);

            let tracked opt_tok = inst.tr_add_gen(false);
            assert(opt_tok is None);
            inst.tr_have_gen(true, &opt_tok);   // FAILS
        }

        proof fn test_inst2() {
            let tracked (Tracked(inst), Tracked(token_t)) = Y::Instance::init_true();
            assert(token_t is Some);
            assert(equal(token_t->0.instance_id(), inst.id()));
        }

        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_tsm! {
    #[test] persistent_count_codegen IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_count)]
                pub c: nat,
            }

            init!{
                initialize() {
                    init c = 9;
                }
            }

            transition!{
                tr_add() {
                    add c (union)= (2);
                }
            }

            transition!{
                tr_have() {
                    have c >= (2);
                }
            }
        }}

        verus!{

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            post.c == if pre.c <= 2 { 2 } else { pre.c }
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            post.c == if pre.c <= 2 { 2 } else { pre.c }
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.c >= 2 && post.c == pre.c
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.c >= 2 && post.c == pre.c
        }

        proof fn correct_tr(pre: Y::State, post: Y::State) {
            ensures([
                rel_tr1(pre, post) == Y::State::tr_add(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr_have(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),
            ]);
        }

        proof fn test_inst() {
            let tracked (Tracked(inst), Tracked(t1)) = Y::Instance::initialize();
            assert(t1.count() == 9);

            let tracked t2 = t1.weaken(2);

            inst.tr_have(&t2);

            let tracked t4 = inst.tr_add();
            assert(t4.count() == 2);

            let tracked t2_clone = t2.clone();
            assert(equal(t2, t2_clone));
        }

        proof fn test_weaken_fail() {
            let tracked (Tracked(inst), Tracked(t1)) = Y::Instance::initialize();
            let tracked t2 = t1.weaken(800); // FAILS
        }

        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_tsm! {
    #[test] set_codegen IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(set)]
                pub b: Set<int>,
            }

            init!{
                initialize() {
                    init b = Set::<int>::empty().insert(19);
                }
            }

            transition!{
                tr_add() {
                    add b += set { 5 }; // FAILS
                }
            }

            transition!{
                tr_have() {
                    have b >= set { 5 };
                }
            }

            transition!{
                tr_remove() {
                    remove b -= set { 5 };
                }
            }

            transition!{
                tr_add_gen() {
                    add b += (Set::<int>::empty().insert(6)); // FAILS
                }
            }

            transition!{
                tr_have_gen() {
                    have b >= (Set::<int>::empty().insert(6));
                }
            }

            transition!{
                tr_remove_gen() {
                    remove b -= (Set::<int>::empty().insert(6));
                }
            }
        }}

        verus!{

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            !pre.b.contains(5)
            ==> post.b == pre.b.insert(5)
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            !pre.b.contains(5)
            && post.b == pre.b.insert(5)
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && pre.b == post.b
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && pre.b == post.b
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && post.b == pre.b.remove(5)
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && post.b == pre.b.remove(5)
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            !pre.b.contains(6)
            ==> post.b == pre.b.union(Set::<int>::empty().insert(6))
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            !pre.b.contains(6)
            && post.b == pre.b.union(Set::<int>::empty().insert(6))
        }

        spec fn rel_tr5(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && pre.b == post.b
        }

        spec fn rel_tr5_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && pre.b == post.b
        }

        spec fn rel_tr6(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && post.b == pre.b.difference(Set::<int>::empty().insert(6))
        }

        spec fn rel_tr6_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && post.b == pre.b.difference(Set::<int>::empty().insert(6))
        }

        proof fn correct_tr(pre: Y::State, post: Y::State) {
            ensures([
                rel_tr1(pre, post) == Y::State::tr_add(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr_have(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),
                rel_tr3(pre, post) == Y::State::tr_remove(pre, post),
                rel_tr3_strong(pre, post) == Y::State::tr_remove_strong(pre, post),

                rel_tr4(pre, post) == Y::State::tr_add_gen(pre, post),
                rel_tr4_strong(pre, post) == Y::State::tr_add_gen_strong(pre, post),
                rel_tr5(pre, post) == Y::State::tr_have_gen(pre, post),
                rel_tr5_strong(pre, post) == Y::State::tr_have_gen_strong(pre, post),
                rel_tr6(pre, post) == Y::State::tr_remove_gen(pre, post),
                rel_tr6_strong(pre, post) == Y::State::tr_remove_gen_strong(pre, post),
            ]);
        }

        proof fn test_inst1() {
            let tracked (Tracked(inst), Tracked(token_f)) = Y::Instance::initialize();
            assert(token_f.set() =~= set![19]);
            assert(token_f.instance_id() == inst.id());

            let tracked token1 = inst.tr_add();
            assert(equal(token1.instance_id(), inst.id()));
            assert(token1.element() == 5);
            inst.tr_have(&token1);
            inst.tr_remove(token1);

            let tracked token_set = inst.tr_add_gen();
            assert(token_set.set() =~= set![6]);
            assert(token_set.instance_id() == inst.id());
            inst.tr_have_gen(&token_set);
            inst.tr_remove_gen(token_set);
        }

        }
    } => Err(e) => assert_fails(e, 2)
    // The checked macro proves both failing safety conditions in one generated function, so
    // Verus reports the first one only (and its span is the macro invocation).
    ; verified => Err(e) => assert_fails(e, 1)
}

test_verify_tsm! {
    #[test] iset_codegen IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(iset)]
                pub b: ISet<int>,
            }

            init!{
                initialize() {
                    init b = ISet::<int>::empty().insert(19);
                }
            }

            transition!{
                tr_add() {
                    add b += set { 5 }; // FAILS
                }
            }

            transition!{
                tr_have() {
                    have b >= set { 5 };
                }
            }

            transition!{
                tr_remove() {
                    remove b -= set { 5 };
                }
            }

            transition!{
                tr_add_gen() {
                    add b += (ISet::<int>::empty().insert(6)); // FAILS
                }
            }

            transition!{
                tr_have_gen() {
                    have b >= (ISet::<int>::empty().insert(6));
                }
            }

            transition!{
                tr_remove_gen() {
                    remove b -= (ISet::<int>::empty().insert(6));
                }
            }
        }}

        verus!{

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            !pre.b.contains(5)
            ==> post.b == pre.b.insert(5)
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            !pre.b.contains(5)
            && post.b == pre.b.insert(5)
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && pre.b == post.b
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && pre.b == post.b
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && post.b == pre.b.remove(5)
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && post.b == pre.b.remove(5)
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            !pre.b.contains(6)
            ==> post.b == pre.b.union(ISet::<int>::empty().insert(6))
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            !pre.b.contains(6)
            && post.b == pre.b.union(ISet::<int>::empty().insert(6))
        }

        spec fn rel_tr5(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && pre.b == post.b
        }

        spec fn rel_tr5_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && pre.b == post.b
        }

        spec fn rel_tr6(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && post.b == pre.b.difference(ISet::<int>::empty().insert(6))
        }

        spec fn rel_tr6_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && post.b == pre.b.difference(ISet::<int>::empty().insert(6))
        }

        proof fn correct_tr(pre: Y::State, post: Y::State) {
            ensures([
                rel_tr1(pre, post) == Y::State::tr_add(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr_have(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),
                rel_tr3(pre, post) == Y::State::tr_remove(pre, post),
                rel_tr3_strong(pre, post) == Y::State::tr_remove_strong(pre, post),

                rel_tr4(pre, post) == Y::State::tr_add_gen(pre, post),
                rel_tr4_strong(pre, post) == Y::State::tr_add_gen_strong(pre, post),
                rel_tr5(pre, post) == Y::State::tr_have_gen(pre, post),
                rel_tr5_strong(pre, post) == Y::State::tr_have_gen_strong(pre, post),
                rel_tr6(pre, post) == Y::State::tr_remove_gen(pre, post),
                rel_tr6_strong(pre, post) == Y::State::tr_remove_gen_strong(pre, post),
            ]);
        }

        proof fn test_inst1() {
            let tracked (Tracked(inst), Tracked(token_f)) = Y::Instance::initialize();
            assert(token_f.set() =~= iset![19]);
            assert(token_f.instance_id() == inst.id());

            let tracked token1 = inst.tr_add();
            assert(equal(token1.instance_id(), inst.id()));
            assert(token1.element() == 5);
            inst.tr_have(&token1);
            inst.tr_remove(token1);

            let tracked token_set = inst.tr_add_gen();
            assert(token_set.set() =~= iset![6]);
            assert(token_set.instance_id() == inst.id());
            inst.tr_have_gen(&token_set);
            inst.tr_remove_gen(token_set);
        }

        }
    } => Err(e) => assert_fails(e, 2)
    // The checked macro proves both failing safety conditions in one generated function, so
    // Verus reports the first one only (and its span is the macro invocation).
    ; verified => Err(e) => assert_fails_anywhere(e, 1)
}

test_verify_tsm! {
    #[test] persistent_set_codegen IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_set)]
                pub b: Set<int>,
            }

            init!{
                initialize() {
                    init b = Set::<int>::empty().insert(19);
                }
            }

            transition!{
                tr_add() {
                    add b (union)= set { 5 };
                }
            }

            transition!{
                tr_have() {
                    have b >= set { 5 };
                }
            }

            transition!{
                tr_add_gen() {
                    add b (union)= (Set::<int>::empty().insert(6));
                }
            }

            transition!{
                tr_have_gen() {
                    have b >= (Set::<int>::empty().insert(6));
                }
            }
        }}

        verus!{

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            post.b == pre.b.insert(5)
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            post.b == pre.b.insert(5)
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && pre.b == post.b
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && pre.b == post.b
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            post.b == pre.b.union(Set::<int>::empty().insert(6))
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            post.b == pre.b.union(Set::<int>::empty().insert(6))
        }

        spec fn rel_tr5(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && pre.b == post.b
        }

        spec fn rel_tr5_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && pre.b == post.b
        }

        proof fn correct_tr(pre: Y::State, post: Y::State) {
            ensures([
                rel_tr1(pre, post) == Y::State::tr_add(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr_have(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),

                rel_tr4(pre, post) == Y::State::tr_add_gen(pre, post),
                rel_tr4_strong(pre, post) == Y::State::tr_add_gen_strong(pre, post),
                rel_tr5(pre, post) == Y::State::tr_have_gen(pre, post),
                rel_tr5_strong(pre, post) == Y::State::tr_have_gen_strong(pre, post),
            ]);
        }

        proof fn test_inst1() {
            let tracked (Tracked(inst), Tracked(token_f)) = Y::Instance::initialize();
            assert(Set::<int>::empty().insert(19).contains(19));
            assert(token_f.set() =~= set![19]);
            assert(token_f.instance_id() == inst.id());

            let tracked token1 = inst.tr_add();
            assert(equal(token1.instance_id(), inst.id()));
            assert(token1.element() == 5);
            inst.tr_have(&token1);

            let token1_clone = token1.clone();
            assert(equal(token1_clone, token1));

            let tracked token_set = inst.tr_add_gen();
            assert(Set::<int>::empty().insert(6).contains(6));
            assert(token_set.set() =~= set![6]);
            assert(token_set.instance_id() == inst.id());
            inst.tr_have_gen(&token_set);
        }

        }
    } => Ok(())
}

test_verify_tsm! {
    #[test] persistent_iset_codegen IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_iset)]
                pub b: ISet<int>,
            }

            init!{
                initialize() {
                    init b = ISet::<int>::empty().insert(19);
                }
            }

            transition!{
                tr_add() {
                    add b (union)= set { 5 };
                }
            }

            transition!{
                tr_have() {
                    have b >= set { 5 };
                }
            }

            transition!{
                tr_add_gen() {
                    add b (union)= (ISet::<int>::empty().insert(6));
                }
            }

            transition!{
                tr_have_gen() {
                    have b >= (ISet::<int>::empty().insert(6));
                }
            }
        }}

        verus!{

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            post.b == pre.b.insert(5)
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            post.b == pre.b.insert(5)
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && pre.b == post.b
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && pre.b == post.b
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            post.b == pre.b.union(ISet::<int>::empty().insert(6))
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            post.b == pre.b.union(ISet::<int>::empty().insert(6))
        }

        spec fn rel_tr5(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && pre.b == post.b
        }

        spec fn rel_tr5_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && pre.b == post.b
        }

        proof fn correct_tr(pre: Y::State, post: Y::State) {
            ensures([
                rel_tr1(pre, post) == Y::State::tr_add(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr_have(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),

                rel_tr4(pre, post) == Y::State::tr_add_gen(pre, post),
                rel_tr4_strong(pre, post) == Y::State::tr_add_gen_strong(pre, post),
                rel_tr5(pre, post) == Y::State::tr_have_gen(pre, post),
                rel_tr5_strong(pre, post) == Y::State::tr_have_gen_strong(pre, post),
            ]);
        }

        proof fn test_inst1() {
            let tracked (Tracked(inst), Tracked(token_f)) = Y::Instance::initialize();
            assert(ISet::<int>::empty().insert(19).contains(19));
            assert(token_f.set() =~= iset![19]);
            assert(token_f.instance_id() == inst.id());

            let tracked token1 = inst.tr_add();
            assert(equal(token1.instance_id(), inst.id()));
            assert(token1.element() == 5);
            inst.tr_have(&token1);

            let token1_clone = token1.clone();
            assert(equal(token1_clone, token1));

            let tracked token_set = inst.tr_add_gen();
            assert(ISet::<int>::empty().insert(6).contains(6));
            assert(token_set.set() =~= iset![6]);
            assert(token_set.instance_id() == inst.id());
            inst.tr_have_gen(&token_set);
        }

        }
    } => Ok(())
}

test_verify_tsm! {
    #[test] tokenized_with_conditional IMPORTS.to_string() + verus_code_str! {

        tokenized_state_machine!{ Y {
            fields {
                #[sharding(variable)]
                pub x: int,

                #[sharding(variable)]
                pub y: int,
            }

            init!{
                initialize(x: int, y: int) {
                    init x = x;
                    init y = y;
                }
            }

            transition!{
                upd() {
                    if pre.x == 0 {
                        update y = 1;
                    } else {
                        update y = 2;
                    }
                }
            }

            transition!{
                req() {
                    if pre.x == 0 {
                        require(pre.y == 1);
                        update y = 20;
                    } else {
                        require(pre.y == 2);
                        update y = 25;
                    }
                }
            }
        }}

        verus!{
        proof fn test1() {
            let tracked (Tracked(inst), Tracked(x), Tracked(mut y)) = Y::Instance::initialize(0, 0);
            inst.upd(&x, &mut y);
            assert(y.value() == 1);
        }

        proof fn test2() {
            let tracked (Tracked(inst), Tracked(x), Tracked(mut y)) = Y::Instance::initialize(12, 0);
            inst.upd(&x, &mut y);
            assert(y.value() == 2);
        }

        proof fn test3() {
            let tracked (Tracked(inst), Tracked(x), Tracked(mut y)) = Y::Instance::initialize(0, 2);
            inst.req(&x, &mut y); // FAILS
        }

        proof fn test4() {
            let tracked (Tracked(inst), Tracked(x), Tracked(mut y)) = Y::Instance::initialize(1, 1);
            inst.req(&x, &mut y); // FAILS
        }
        }

    } => Err(e) => assert_fails(e, 2)
}

test_verify_tsm! {
    #[test] assert_in_if IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X {

            fields {
                pub m: IMap<int, int>,

                pub a: int,
                pub b: int,
            }

            transition!{
                tr(x: bool, y: bool, z: bool) {
                    if x {
                        assert y;   // FAILS
                    }

                    require x;
                }
            }
        }}

        proof fn test(s: X::State, s1: X::State, x: bool, y: bool, z: bool)
            ensures X::State::tr(s, s1, x, y, z) <==> (
                (x ==> y) ==> (x && s1 == s)
            )
        { }

        proof fn test2(s: X::State, s1: X::State, x: bool, y: bool, z: bool)
            ensures X::State::tr_strong(s, s1, x, y, z) <==> (
                (x ==> y) && x && s1 == s
            )
        { }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_tsm! {
    #[test] double_scoped_updates_if IMPORTS.to_string() + verus_code_str! {
      state_machine!{ X {

            fields {
                pub m: IMap<int, int>,

                pub a: int,
                pub b: int,
            }

            transition!{
                tr(x: bool, y: bool, z: bool, w: bool, v: bool) {
                    if x {
                        require w;
                        update m[0] = 10;
                    } else {
                        assert y by { assume(false); };
                        update a = 99;
                    }

                    assert z by { assume(false); };

                    if v {
                        update b = 11;
                    } else {
                        update m[1] = 11;
                    }
                }
            }
        }}

        spec fn tr_weak(pre: X::State, post: X::State, x: bool, y: bool, z: bool, w: bool, v: bool) -> bool {
            (x ==> w)
              && ((!x ==> y) ==> (
                  // TODO this should probably be under the `z ==>`
                  (x ==> post.a == pre.a) && (!x ==> post.a == 99)

                  && (z ==> (
                        (v ==> post.b == 11) && (!v ==> post.b == pre.b)
                        && (if x {
                            if v {
                                post.m =~= pre.m.insert(0, 10)
                            } else {
                                post.m =~= pre.m.insert(0, 10).insert(1, 11)
                            }
                        } else {
                            if v {
                                post.m =~= pre.m
                            } else {
                                post.m =~= pre.m.insert(1, 11)
                            }
                        })
                  ))
              ))
        }

        proof fn test(pre: X::State, post: X::State, x: bool, y: bool, z: bool, w: bool, v: bool)
            ensures X::State::tr(pre, post, x, y, z, w, v) <==> tr_weak(pre, post, x, y, z, w, v)
        { }

        spec fn tr_strong(pre: X::State, post: X::State, x: bool, y: bool, z: bool, w: bool, v: bool) -> bool {
            (x ==> w) && (!x ==> y)
                && z

                && (x ==> post.a == pre.a) && (!x ==> post.a == 99)
                && (v ==> post.b == 11) && (!v ==> post.b == pre.b)
                && (if x {
                    if v {
                        post.m =~= pre.m.insert(0, 10)
                    } else {
                        post.m =~= pre.m.insert(0, 10).insert(1, 11)
                    }
                } else {
                    if v {
                        post.m =~= pre.m
                    } else {
                        post.m =~= pre.m.insert(1, 11)
                    }
                })
        }

        proof fn test2(pre: X::State, post: X::State, x: bool, y: bool, z: bool, w: bool, v: bool)
            ensures X::State::tr_strong(pre, post, x, y, z, w, v) <==> tr_strong(pre, post, x, y, z, w, v)
        {
            if X::State::tr_strong(pre, post, x, y, z, w, v) {
                assert(tr_strong(pre, post, x, y, z, w, v));
            }

            if tr_strong(pre, post, x, y, z, w, v) {
                assert(X::State::tr_strong(pre, post, x, y, z, w, v));
            }
        }
    } => Ok(())
    ; verified cheating "test source contains `assert .. by { assume(false); }`"
}

test_verify_tsm! {
    #[test] double_scoped_updates_match IMPORTS.to_string() + verus_code_str! {

        state_machine!{ X {

            fields {
                pub m: IMap<int, int>,

                pub a: int,
                pub b: int,
            }

            transition!{
                tr(x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>) {
                    match x {
                        Option::Some(x1) => {
                            require w;
                            update m[0] = x1;
                        }
                        Option::None => {
                            assert y by { assume(false); };
                            update a = 99;
                        }
                    }

                    assert z by { assume(false); };

                    match v {
                        Option::Some(v1) => {
                            update b = v1;
                        }
                        Option::None => {
                            update m[1] = 11;
                        }
                    }
                }
            }
        }}

        spec fn tr_weak(pre: X::State, post: X::State, x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>) -> bool {
            (x is Some ==> w)
              && ((!(x is Some) ==> y) ==> (
                  // TODO this should probably be under the `z ==>`
                  (x is Some ==> post.a == pre.a) && (!(x is Some) ==> post.a == 99)

                  && (z ==> (
                        (v is Some ==> post.b == v->0) && (!(v is Some) ==> post.b == pre.b)
                        && (if x is Some {
                            if v is Some {
                                post.m =~= pre.m.insert(0, x->0)
                            } else {
                                post.m =~= pre.m.insert(0, x->0).insert(1, 11)
                            }
                        } else {
                            if v is Some {
                                post.m =~= pre.m
                            } else {
                                post.m =~= pre.m.insert(1, 11)
                            }
                        })
                  ))
              ))
        }

        proof fn test(pre: X::State, post: X::State, x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>)
            ensures X::State::tr(pre, post, x, y, z, w, v) <==> tr_weak(pre, post, x, y, z, w, v)
        { }

        spec fn tr_strong(pre: X::State, post: X::State, x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>) -> bool {
            (x is Some ==> w) && (!(x is Some) ==> y)
                && z

                && (x is Some ==> post.a == pre.a) && (!(x is Some) ==> post.a == 99)
                && (v is Some ==> post.b == v->0) && (!(v is Some) ==> post.b == pre.b)
                && (if x is Some {
                    if v is Some {
                        post.m =~= pre.m.insert(0, x->0)
                    } else {
                        post.m =~= pre.m.insert(0, x->0).insert(1, 11)
                    }
                } else {
                    if v is Some {
                        post.m =~= pre.m
                    } else {
                        post.m =~= pre.m.insert(1, 11)
                    }
                })
        }

        proof fn test2(pre: X::State, post: X::State, x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>)
            ensures X::State::tr_strong(pre, post, x, y, z, w, v) <==> tr_strong(pre, post, x, y, z, w, v)
        {
            if X::State::tr_strong(pre, post, x, y, z, w, v) {
                assert(tr_strong(pre, post, x, y, z, w, v));
            }

            if tr_strong(pre, post, x, y, z, w, v) {
                assert(X::State::tr_strong(pre, post, x, y, z, w, v));
            }
        }

        spec fn tr_enabled(pre: X::State, x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>) -> bool {
            x is Some ==> w
        }

        proof fn test3(pre: X::State, x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>)
            ensures X::State::tr_enabled(pre, x, y, z, w, v) <==> tr_enabled(pre, x, y, z, w, v)
        { }

        proof fn test_take_step(pre: X::State, x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>)
            requires x is Some ==> w,
        {
            let post = X::take_step::tr(pre, x, y, z, w, v);
            assert(X::State::tr(pre, post, x, y, z, w, v));
        }

        proof fn test_take_step2(pre: X::State, x: Option<int>, y: bool, z: bool, w: bool, v: Option<int>)
        {
            let post = X::take_step::tr(pre, x, y, z, w, v); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
    // The checked take_step states its precondition as two requires clauses.
    ; verified => Err(err) => assert_fails_anywhere(err, 2)
    ; verified cheating "test source contains `assert .. by { assume(false); }`"
}

test_verify_tsm! {
    #[test] if_let_assert_with_no_else IMPORTS.to_string() + verus_code_str! {
        pub struct Y {
            pub a: int,
            pub b: int,
        }

        state_machine!{ X {
            fields {
                pub m: IMap<int, int>,
            }

            transition!{
                tr(x: int, y: int, z: int, b: bool) {
                    if b {
                        let k: int = 9;
                        assert(k == x) by { assume(false); };
                        update m[y] = 12;
                    }

                    update m[z] = 13;
                }
            }
        }}

        spec fn tr_weak(pre: X::State, post: X::State, x: int, y: int, z: int, b: bool) -> bool {
            (b ==> (x == 9)) ==> (
                 (b ==> post.m =~= pre.m.insert(y, 12).insert(z, 13))
              && (!b ==> post.m =~= pre.m.insert(z, 13))
            )
        }

        proof fn test(pre: X::State, post: X::State, x: int, y: int, z: int, b: bool)
            ensures X::State::tr(pre, post, x, y, z, b) <==> tr_weak(pre, post, x, y, z, b)
        { }

        spec fn tr_strong(pre: X::State, post: X::State, x: int, y: int, z: int, b: bool) -> bool {
            (b ==> (x == 9))
              && (b ==> post.m =~= pre.m.insert(y, 12).insert(z, 13))
              && (!b ==> post.m =~= pre.m.insert(z, 13))
        }

        proof fn test2(pre: X::State, post: X::State, x: int, y: int, z: int, b: bool)
            ensures X::State::tr_strong(pre, post, x, y, z, b) <==> tr_strong(pre, post, x, y, z, b)
        {
        }

    } => Ok(())
    ; verified cheating "test source contains `assert(k == x) by { assume(false); }`"
}

test_verify_one_file! {
    #[test] step_is_variant IMPORTS.to_string() + verus_code_str! {
        use verus_state_machines_macros::state_machine;

        state_machine! { X {
            fields {
                pub number: int,
            }

            init!{
                initialize() {
                    init number = 0;
                }
            }

            transition!{
                add(n: int) {
                    update number = pre.number + 2*n;
                }
            }

            transition!{
                sub(n: int) {
                    update number = pre.number - 2*n;
                }
            }
        }}

        proof fn test(s: X::Step)
            requires s.is_add(),
        {
            match s {
                X::Step::add(_) => assert(true),
                X::Step::sub(_) => assert(false),
                _ => {},
            }
        }
    } => Ok(())
}

// Checked-macro version of step_is_variant: the original imports the trusted `state_machine`
// explicitly, which the prelude's macro switch cannot redirect.
test_verify_one_file_with_options! {
    #[test] step_is_variant_verified ["--no-cheating"] => IMPORTS.to_string() + verus_code_str! {
        use verus_state_machines_macros::verified_state_machine_model;

        verified_state_machine_model! { X {
            fields {
                pub number: int,
            }

            init!{
                initialize() {
                    init number = 0;
                }
            }

            transition!{
                add(n: int) {
                    update number = pre.number + 2*n;
                }
            }

            transition!{
                sub(n: int) {
                    update number = pre.number - 2*n;
                }
            }
        }}

        proof fn test(s: X::Step)
            requires s.is_add(),
        {
            match s {
                X::Step::add(_) => assert(true),
                X::Step::sub(_) => assert(false),
                _ => {},
            }
        }
    } => Ok(())
}

test_verify_tsm! {
    #[test] label_generics IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X<T, U> {
            fields {
                pub x: T,
                pub y: U,
            }

            pub type InitLabel<U> = Option<U>;

            pub type Label<T> = Option<T>;

            init!{
                g(l: InitLabel<U>, t: T, u: U) {
                    init x = t;
                    init y = u;
                }
            }


            transition!{
                f(l: Label<T>) {
                }
            }

        }}
    } => Ok(())
}

test_verify_tsm! {
    #[test] label_generics_fail1 IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X<T, U> {
            fields {
                pub x: T,
                pub y: U,
            }

            pub type InitLabel<U> = Option<U>;

            pub type Label<T> = Option<T>;

            init!{
                g(l: InitLabel<T>, t: T, u: U) {
                    init x = t;
                    init y = u;
                }
            }


            transition!{
                f(l: Label<T>) {
                }
            }

        }}
    } => Err(e) => assert_vir_error_msg(e, "the first param to an 'init' definition must be 'InitLabel'")
}

test_verify_tsm! {
    #[test] label_generics_fail2 IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X<T, U> {
            fields {
                pub x: T,
                pub y: U,
            }

            pub type InitLabel<U> = Option<U>;

            pub type Label<T> = Option<T>;

            init!{
                g(l: InitLabel<U>, t: T, u: U) {
                    init x = t;
                    init y = u;
                }
            }


            transition!{
                f(l: Label<U>) {
                }
            }

        }}

    } => Err(e) => assert_vir_error_msg(e, "the first param to a 'transition' must be 'Label'")
}

test_verify_tsm! {
    #[test] label_generics_fail3 IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X<T, U> {
            fields {
                pub x: T,
                pub y: U,
            }

            pub type Label<J> = Option<J>;

        }}

    } => Err(e) => assert_vir_error_msg(e, "invalid generic param")
}

test_verify_tsm! {
    #[test] label_generics_fail4 IMPORTS.to_string() + verus_code_str! {
        state_machine!{ X<T, U> {
            fields {
                pub x: T,
                pub y: U,
            }

            pub type InitLabel<J> = Option<J>;

        }}

    } => Err(e) => assert_vir_error_msg(e, "invalid generic param")
}

test_verify_tsm! {
    #[test] arrow_functions_regression_1002_1 IMPORTS.to_string() + verus_code_str! {
        state_machine!{ Example {
            fields {}

            pub enum Label
            {
                B { b: nat }
            }

            pub open spec fn test(t: Label) -> bool
                recommends t is B
            {
                t->b > 10
            }

            transition!{
                f(l: Label) {
                    require l->b > 10;
                }
            }
        }}
    } => Ok(())
}

test_verify_tsm! {
    #[test] arrow_functions_regression_1002_2 IMPORTS.to_string() + verus_code_str! {
        state_machine!{ Example {
            fields {
                pub x: nat,
            }

            pub enum InitLabel
            {
                B { b: nat }
            }

            init!{
                g(l: InitLabel) {
                    init x = l->b;
                }
            }
        }}
    } => Ok(())
}

test_verify_tsm! {
    #[test] inst_copy IMPORTS.to_string() + verus_code_str! {
        pub struct Y { }

        tokenized_state_machine!{ A {
            fields {
                #[sharding(variable)]
                pub x: IMap<int, Y>,
            }

            init!{
                initialize() {
                    init x = IMap::<int, Y>::empty();
                }
            }
        }}

        proof fn test(tracked t: A::Instance) -> (tracked r: (A::Instance, A::Instance)) {
            (t, t)
        }
    } => Ok(())
}

test_verify_tsm! {
    #[test] pers_token_copy IMPORTS.to_string() + verus_code_str! {
        pub struct Y { }

        tokenized_state_machine!{ A {
            fields {
                #[sharding(persistent_imap)]
                pub x: IMap<int, Y>,
            }

            init!{
                initialize() {
                    init x = IMap::<int, Y>::empty();
                }
            }
        }}

        proof fn test(tracked t: A::x) -> (tracked r: (A::x, A::x)) {
            (t, t)
        }
    } => Ok(())
}

test_verify_tsm! {
    #[test] other_token_not_copy IMPORTS.to_string() + verus_code_str! {
        pub struct Y { }

        tokenized_state_machine!{ A {
            fields {
                #[sharding(map)]
                pub x: Map<int, Y>,
            }

            init!{
                initialize() {
                    init x = Map::<int, Y>::empty();
                }
            }
        }}

        proof fn test(tracked t: A::x) -> (tracked r: (A::x, A::x)) {
            (t, t)
        }
    } => Err(e) => assert_rust_error_msg(e, "use of moved value")
}

test_verify_tsm! {
    #[test] assoc_type_in_field IMPORTS.to_string() + verus_code_str! {
        pub trait Tr {
            type AssocType;
        }

        tokenized_state_machine!{ X<T: Tr> {
            fields {
                #[sharding(imap)]
                pub m: IMap<int, T::AssocType>,
            }

            init!{
                initialize(m: IMap<int, T::AssocType>) {
                    init m = m;
                }
            }
        }}

        pub struct A {
        }
        pub struct B {
            i: int,
        }
        impl Tr for A {
            type AssocType = B;
        }

        proof fn test() {
            let tracked (Tracked(inst), Tracked(mut map_token)) = X::Instance::<A>::initialize(imap![3 => B { i: 9 }]);
            assert(map_token.instance_id() == inst.id());
            assert(map_token.map() =~= imap![3 => B { i: 9 }]);
            let tracked r = map_token.remove(3);
            assert(r.key() == 3);
            assert(r.value() == B { i: 9 });
            assert(r.instance_id() == inst.id());

            let j = X::m_map::<A>::empty(inst.id());
            assert(j.map() =~= imap![]);
        }
    } => Ok(())
}

test_verify_tsm! {
    #[test] pre_reserved_property_issue3083 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields { #[sharding(variable)] pub v: int, }
            init!{ initialize() { init v = 1; } }
            property!{ p() {
                let pre = State { v: 0 };  // shadows the real pre-state
            } }
        }}
    } => Err(err) => assert_vir_error_msg(err, "'pre' is a reserved identifier in state machine definitions")
}

test_verify_tsm! {
    #[test] pre_reserved_transition_issue3083 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields { #[sharding(variable)] pub v: int, }
            init!{ initialize() { init v = 1; } }
            transition!{ dec() {
                let pre = State { v: 2 };
            } }
            #[inductive(initialize)] fn init_inductive(post: Self) { }
            #[inductive(dec)] fn dec_inductive(pre: Self, post: Self) { }
        }}
    } => Err(err) => assert_vir_error_msg(err, "'pre' is a reserved identifier in state machine definitions")
}

test_verify_tsm! {
    #[test] post_reserved_transition_issue3083 IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ Y {
            fields { #[sharding(variable)] pub v: int, }
            init!{ initialize() { init v = 1; } }
            transition!{ dec() {
                let post = State { v: 2 };
            } }
            #[inductive(initialize)] fn init_inductive(post: Self) { }
            #[inductive(dec)] fn dec_inductive(pre: Self, post: Self) { }
        }}
    } => Err(err) => assert_vir_error_msg(err, "'post' is a reserved identifier in state machine definitions")
}

const SUB_UPDATE_TYPES: &str = verus_code_str! {
    pub struct Pt { pub x: int, pub y: int }
    pub struct Rec<A> { pub a: A, pub s: Seq<int> }
    pub struct Pair(pub int, pub bool);
    pub struct Outer { pub p: Pt }
    pub enum E { A { x: int }, B }
};

test_verify_tsm! {
    #[test] dot_field_sub_updates IMPORTS.to_string() + SUB_UPDATE_TYPES + verus_code_str! {
        state_machine!{ X {
            fields {
                pub p: Pt,
                pub r: Rec<int>,
                pub t: (int, (Pt, int)),
                pub q: Pair,
                pub m: Map<int, Pt>,
            }

            transition!{
                tr(v: int, w: int, k: int, b: bool) {
                    require(pre.r.s.len() == 2 && pre.m.dom().contains(k));
                    update p.x = v;
                    update p.y = w;
                    update p.x = v + 1;
                    update r.a = v;
                    update r.s[1] = w;
                    update t.1.0.y = v;
                    update t.0 = w;
                    update q.1 = b;
                    update m[k].y = v;
                }
            }

            transition!{
                branch(c: bool, v: int) {
                    if c { update p.x = v; } else { update p.y = v; }
                }
            }
        }}

        proof fn test(pre: X::State, post: X::State, v: int, w: int, k: int, b: bool)
            requires X::State::tr(pre, post, v, w, k, b)
            ensures
                post.p == (Pt { x: v + 1, y: w }),
                post.r.a == v && post.r.s[1] == w && post.r.s[0] == pre.r.s[0],
                post.t.0 == w && post.t.1.0.y == v && post.t.1.0.x == pre.t.1.0.x,
                post.t.1.1 == pre.t.1.1,
                post.q.1 == b && post.q.0 == pre.q.0,
                post.m[k] == (Pt { x: pre.m[k].x, y: v }),
        { }

        proof fn test_branch(pre: X::State, post: X::State, v: int)
            requires X::State::branch(pre, post, false, v)
            ensures post.p == (Pt { x: pre.p.x, y: v })
        { }

        proof fn test_fail(pre: X::State, post: X::State, v: int, w: int, k: int, b: bool)
            requires X::State::tr(pre, post, v, w, k, b)
            ensures post.p.x == v // FAILS
        { }
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] dot_field_sub_updates_tokenized IMPORTS.to_string() + SUB_UPDATE_TYPES + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub p: Pt,
                #[sharding(variable)] pub m: Map<int, Pt>,
                #[sharding(not_tokenized)] pub r: Rec<int>,
            }

            #[invariant]
            pub fn inv(&self) -> bool { self.m.dom().contains(1) }

            init!{
                initialize() {
                    init p = Pt { x: 0, y: 0 };
                    init m = Map::empty().insert(1, Pt { x: 0, y: 0 });
                    init r = Rec { a: 0, s: Seq::empty() };
                }
            }

            transition!{
                tr(v: int, w: int) {
                    update p.x = v;
                    update p.y = w;
                    update m[1].y = v;
                    update r.a = w;
                }
            }

            transition!{
                branch(c: bool, v: int) {
                    if c { update p.x = v; } else { update p.y = v; }
                }
            }

            #[inductive(initialize)] fn initialize_inductive(post: Self) { }
            #[inductive(tr)] fn tr_inductive(pre: Self, post: Self, v: int, w: int) {
                assert(post.m.dom() =~= pre.m.dom());
            }
            #[inductive(branch)] fn branch_inductive(pre: Self, post: Self, c: bool, v: int) { }
        }}

        proof fn client() {
            let tracked (Tracked(inst), Tracked(mut p), Tracked(mut m)) = X::Instance::initialize();
            inst.tr(1, 2, &mut p, &mut m);
            assert(p.value() == Pt { x: 1, y: 2 });
            assert(m.value()[1] == Pt { x: 0, y: 1 });
            inst.branch(true, 5, &mut p);
            assert(p.value() == Pt { x: 5, y: 2 });
            assert(p.value().y == 3); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_tsm! {
    #[test] dot_field_sub_update_unknown_type IMPORTS.to_string() + SUB_UPDATE_TYPES + verus_code_str! {
        state_machine!{ X {
            fields { pub o: Outer, }
            transition!{ tr(v: int) { update o.p.x = v; } }
        }}
    } => Err(e) => assert_vir_error_msg(e, "cannot update a field of `o.p`: its type is not known to the state machine macro")
}

test_verify_tsm! {
    #[test] dot_field_sub_update_tuple_index IMPORTS.to_string() + SUB_UPDATE_TYPES + verus_code_str! {
        state_machine!{ X {
            fields { pub t: (int, int), }
            transition!{ tr(v: int) { update t.2 = v; } }
        }}
    } => Err(e) => assert_vir_error_msg(e, "`t` has no element 2")
}

test_verify_tsm! {
    #[test] dot_field_sub_update_enum IMPORTS.to_string() + SUB_UPDATE_TYPES + verus_code_str! {
        state_machine!{ X {
            fields { pub e: E, }
            transition!{ tr(v: int) { update e.x = v; } }
        }}
    } => Err(e) => assert_rust_error_msg(e, "expected struct, variant or union type, found enum `E`")
}

test_verify_tsm! {
    #[test] dot_field_sub_updates_tokenized_paths IMPORTS.to_string() + SUB_UPDATE_TYPES + verus_code_str! {
        tokenized_state_machine!{ X {
            fields { #[sharding(variable)] pub p: Pt, }
            transition!{
                tr(c: bool, v: int) {
                    update p.x = v;
                    if c { update p.y = v; }
                }
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "tokenized transitions support one field or index update of a field per path")
}

// Regression (checked macro): a general `remove` or `have` of a `map`, `imap`, `set`, `iset` or
// `multiset` field after a `remove` of the same field failed the generated readiness proof
// (`__tsm_ready_<tr>`, "assertion failed" at the macro). The later operand is observed in the
// fragment the removal leaves, and the transition's enabling condition needs it disjoint from the
// removed operand (for a multiset: their sum in the state); the inclusion of each input token in
// `op(owned, h)` does not say that. Singleton later operands, and general ones after no removal,
// were not affected.
test_verify_tsm! {
    #[test] general_operand_after_remove_same_field IMPORTS.to_string() + verus_code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)] pub m: Map<int, int>,
                #[sharding(imap)] pub im: IMap<int, int>,
                #[sharding(set)] pub s: Set<int>,
                #[sharding(iset)] pub is: ISet<int>,
                #[sharding(multiset)] pub ms: Multiset<int>,
            }

            init!{ initialize() {
                init m = Map::empty(); init im = IMap::empty(); init s = Set::empty();
                init is = ISet::empty(); init ms = Multiset::empty();
            } }

            // The reported case: constant operands.
            transition!{ map_constants() {
                remove m -= ( Map::<int, int>::empty().insert(0, 1) );
                have m >= ( Map::<int, int>::empty().insert(2, 3) );
            } }

            transition!{ map_remove_have(a: Map<int, int>, b: Map<int, int>) {
                remove m -= (a);
                have m >= (b);
            } }
            transition!{ map_remove_remove(a: Map<int, int>, b: Map<int, int>) {
                remove m -= (a);
                remove m -= (b);
            } }
            transition!{ map_remove_remove_have_add(a: Map<int, int>, b: Map<int, int>, c: Map<int, int>) {
                remove m -= (a);
                remove m -= (b);
                have m >= (c);
                add m += (a);
            } }
            transition!{ map_singleton_remove_have(k: int, v: int, b: Map<int, int>) {
                remove m -= [k => v];
                have m >= (b);
            } }

            transition!{ imap_remove_have(a: IMap<int, int>, b: IMap<int, int>) {
                remove im -= (a);
                have im >= (b);
            } }
            transition!{ imap_remove_remove_have(a: IMap<int, int>, b: IMap<int, int>, c: IMap<int, int>) {
                remove im -= (a);
                remove im -= (b);
                have im >= (c);
            } }

            transition!{ set_remove_have(a: Set<int>, b: Set<int>) {
                remove s -= (a);
                have s >= (b);
            } }
            transition!{ set_remove_remove_have(a: Set<int>, b: Set<int>, c: Set<int>) {
                remove s -= (a);
                remove s -= (b);
                have s >= (c);
            } }
            transition!{ set_singleton_remove_have(e: int, b: Set<int>) {
                remove s -= set { e };
                have s >= (b);
            } }

            transition!{ iset_remove_have(a: ISet<int>, b: ISet<int>) {
                remove is -= (a);
                have is >= (b);
            } }
            transition!{ iset_remove_remove(a: ISet<int>, b: ISet<int>) {
                remove is -= (a);
                remove is -= (b);
            } }

            // The checked macro's generic interface requires a borrowed multiset
            // operand without repeated elements.
            transition!{ multiset_remove_have(a: Multiset<int>, b: Multiset<int>) {
                require(forall|x: int| b.count(x) <= 1);
                remove ms -= (a);
                have ms >= (b);
            } }
            transition!{ multiset_remove_remove_have(a: Multiset<int>, b: Multiset<int>, c: Multiset<int>) {
                require(forall|x: int| c.count(x) <= 1);
                remove ms -= (a);
                remove ms -= (b);
                have ms >= (c);
            } }
            transition!{ multiset_singleton_remove_have(e: int, b: Multiset<int>) {
                require(forall|x: int| b.count(x) <= 1);
                remove ms -= {e};
                have ms >= (b);
            } }
        }}
    } => Ok(())
}

// Checked-macro version of general_operand_after_remove_same_field for the raw interface's
// `#[verified_local_ready]` operations (the trusted macro has neither); local-ready also needs a
// storage field. Their readiness proof (`local_ready::<tr>::ready`) failed for a map or set `have` or
// general `remove`, and for any `remove`/`have` after a `remove` of the same field: the later
// operand is observed in the fragment the removal leaves, and only the first singleton `remove`
// of a field had a hint lifting its operand to the completion's state.
test_verify_one_file_with_options! {
    #[test] general_operand_after_remove_same_field_local_ready_verified ["--no-cheating"] => IMPORTS.to_string() + verus_code_str! {
        verified_tokenized_state_machine!{
            #[verified_raw_tokens]
            #[verified_local_ready(map_constants, map_have, map_remove, map_remove_have,
                map_remove_remove, map_remove_remove_have_add, map_singleton_remove_have,
                map_singleton_remove_remove, map_let_remove_have, map_have_bound_remove,
                imap_remove_have, imap_remove_remove_have, set_remove_have, set_remove_remove_have,
                set_singleton_remove_have, iset_remove_have, iset_remove_remove, multiset_remove_have,
                multiset_remove_remove_have, multiset_singleton_remove_have,
                multiset_singleton_remove_remove, persistent_haves, two_fields)]
            X {
            fields {
                #[sharding(map)] pub m: Map<int, int>,
                #[sharding(imap)] pub im: IMap<int, int>,
                #[sharding(set)] pub s: Set<int>,
                #[sharding(iset)] pub is: ISet<int>,
                #[sharding(multiset)] pub ms: Multiset<int>,
                #[sharding(persistent_map)] pub pm: Map<int, int>,
                #[sharding(persistent_set)] pub ps: Set<int>,
                #[sharding(storage_option)] pub st: Option<int>,
            }

            init!{ initialize() {
                init m = Map::empty(); init im = IMap::empty(); init s = Set::empty();
                init is = ISet::empty(); init ms = Multiset::empty(); init pm = Map::empty();
                init ps = Set::empty(); init st = None;
            } }

            transition!{ map_constants() {
                remove m -= ( Map::<int, int>::empty().insert(0, 1) );
                have m >= ( Map::<int, int>::empty().insert(2, 3) );
            } }
            transition!{ map_have(a: Map<int, int>) {
                have m >= (a);
            } }
            transition!{ map_remove(a: Map<int, int>) {
                remove m -= (a);
            } }
            transition!{ map_remove_have(a: Map<int, int>, b: Map<int, int>) {
                remove m -= (a);
                have m >= (b);
            } }
            transition!{ map_remove_remove(a: Map<int, int>, b: Map<int, int>) {
                remove m -= (a);
                remove m -= (b);
            } }
            transition!{ map_remove_remove_have_add(a: Map<int, int>, b: Map<int, int>, c: Map<int, int>) {
                remove m -= (a);
                remove m -= (b);
                have m >= (c);
                add m += (a);
            } }
            transition!{ map_singleton_remove_have(k: int, v: int, b: Map<int, int>) {
                remove m -= [k => v];
                have m >= (b);
            } }
            transition!{ map_singleton_remove_remove(k: int, v: int, l: int, w: int) {
                remove m -= [k => v];
                remove m -= [l => w];
            } }
            transition!{ map_let_remove_have(a: Map<int, int>, b: Map<int, int>) {
                let x = a;
                remove m -= (x);
                require(b.len() > 0);
                have m >= (b);
            } }
            transition!{ map_have_bound_remove(k: int, b: Map<int, int>) {
                have m >= [k => let v];
                remove m -= (b);
                have m >= [k => v];
            } }

            transition!{ imap_remove_have(a: IMap<int, int>, b: IMap<int, int>) {
                remove im -= (a);
                have im >= (b);
            } }
            transition!{ imap_remove_remove_have(a: IMap<int, int>, b: IMap<int, int>, c: IMap<int, int>) {
                remove im -= (a);
                remove im -= (b);
                have im >= (c);
            } }

            transition!{ set_remove_have(a: Set<int>, b: Set<int>) {
                remove s -= (a);
                have s >= (b);
            } }
            transition!{ set_remove_remove_have(a: Set<int>, b: Set<int>, c: Set<int>) {
                remove s -= (a);
                remove s -= (b);
                have s >= (c);
            } }
            transition!{ set_singleton_remove_have(e: int, b: Set<int>) {
                remove s -= set { e };
                have s >= (b);
            } }

            transition!{ iset_remove_have(a: ISet<int>, b: ISet<int>) {
                remove is -= (a);
                have is >= (b);
            } }
            transition!{ iset_remove_remove(a: ISet<int>, b: ISet<int>) {
                remove is -= (a);
                remove is -= (b);
            } }

            transition!{ multiset_remove_have(a: Multiset<int>, b: Multiset<int>) {
                remove ms -= (a);
                have ms >= (b);
            } }
            transition!{ multiset_remove_remove_have(a: Multiset<int>, b: Multiset<int>, c: Multiset<int>) {
                remove ms -= (a);
                remove ms -= (b);
                have ms >= (c);
            } }
            transition!{ multiset_singleton_remove_have(e: int, f: int) {
                remove ms -= {e};
                have ms >= {f};
            } }
            transition!{ multiset_singleton_remove_remove(e: int, f: int) {
                remove ms -= {e};
                remove ms -= {f};
            } }

            transition!{ persistent_haves(a: Map<int, int>, k: int, v: int, b: Set<int>, e: int) {
                have pm >= (a);
                have pm >= [k => v];
                have ps >= (b);
                have ps >= set { e };
            } }

            transition!{ two_fields(a: Map<int, int>, b: Set<int>, c: Map<int, int>, d: Set<int>) {
                remove m -= (a);
                remove s -= (b);
                have m >= (c);
                have s >= (d);
            } }
        }}
    } => Ok(())
}

// Branch version of general_operand_after_remove_same_field_local_ready_verified (checked macro
// only, as there): `remove`s and `have`s under `if`/`match`, before and after the join. The
// readiness proof replayed only the statements before the first `if`/`match`; and a map
// observation after a join that changes the owned fragment had no usable trigger.
test_verify_one_file_with_options! {
    #[test] branch_operands_local_ready_verified ["--no-cheating"] => IMPORTS.to_string() + verus_code_str! {
        verified_tokenized_state_machine!{
            #[verified_raw_tokens]
            #[verified_local_ready(remove_if_have, if_remove_have, if_else_remove_have,
                remove_if_else_have, nested, nested_join, if_let, if_tuple, if_require_assert,
                if_remove_add, match_remove_have, match_guard, if_singleton,
                imap_if_else_remove_have, set_if_else_remove_have, set_nested,
                multiset_if_else_remove_have, persistent_match, persistent_if_add, two_fields)]
            X {
            fields {
                #[sharding(map)] pub m: Map<int, int>,
                #[sharding(imap)] pub im: IMap<int, int>,
                #[sharding(set)] pub s: Set<int>,
                #[sharding(multiset)] pub ms: Multiset<int>,
                #[sharding(persistent_map)] pub pm: Map<int, int>,
                #[sharding(storage_option)] pub st: Option<int>,
            }

            init!{ initialize() {
                init m = Map::empty(); init im = IMap::empty(); init s = Set::empty();
                init ms = Multiset::empty(); init pm = Map::empty(); init st = None;
            } }

            transition!{ remove_if_have(a: Map<int, int>, b: Map<int, int>, c: bool) {
                remove m -= (a);
                if c { have m >= (b); }
            } }
            transition!{ if_remove_have(a: Map<int, int>, b: Map<int, int>, c: bool) {
                if c { remove m -= (a); have m >= (b); }
            } }
            transition!{ if_else_remove_have(a: Map<int, int>, b: Map<int, int>, d: Map<int, int>, c: bool) {
                if c { remove m -= (a); } else { remove m -= (b); }
                have m >= (d);
            } }
            transition!{ remove_if_else_have(a: Map<int, int>, b: Map<int, int>, d: Map<int, int>, c: bool) {
                remove m -= (a);
                if c { remove m -= (b); } else { have m >= (b); }
                have m >= (d);
            } }
            transition!{ nested(a: Map<int, int>, b: Map<int, int>, d: Map<int, int>, c: bool, e: bool) {
                if c {
                    if e { remove m -= (a); } else { have m >= (a); }
                    have m >= (b);
                } else {
                    remove m -= (b);
                }
                have m >= (d);
            } }
            transition!{ nested_join(a: Map<int, int>, b: Map<int, int>, d: Map<int, int>, c: bool, e: bool) {
                remove m -= (a);
                if c {
                    if e { remove m -= (b); }
                    have m >= (d);
                }
                have m >= (d);
            } }
            transition!{ if_let(a: Map<int, int>, b: Map<int, int>, c: bool) {
                if c {
                    let x = a;
                    remove m -= (x);
                    have m >= (b);
                }
            } }
            transition!{ if_tuple(a: Map<int, int>, b: Map<int, int>, d: Map<int, int>, c: bool) {
                if c {
                    let (x, y) = (a, b);
                    remove m -= (x);
                    remove m -= (y);
                    have m >= (d);
                }
            } }
            transition!{ if_require_assert(a: Map<int, int>, b: Map<int, int>, c: bool) {
                if c {
                    require(b.len() > 0);
                    remove m -= (a);
                    assert(c);
                    have m >= (b);
                }
            } }
            transition!{ if_remove_add(a: Map<int, int>, b: Map<int, int>, c: bool) {
                if c { remove m -= (a); } else { remove m -= (a); have m >= (b); }
                add m += (a);
            } }
            transition!{ match_remove_have(a: Map<int, int>, b: Map<int, int>, o: Option<int>) {
                match o {
                    Some(v) => { remove m -= (a); have m >= (b); }
                    None => { have m >= (b); }
                }
            } }
            transition!{ match_guard(a: Map<int, int>, b: Map<int, int>, d: Map<int, int>, o: Option<int>) {
                remove m -= (a);
                match o {
                    Some(v) if v > 0 => { have m >= (b); }
                    _ => { remove m -= (b); }
                }
                have m >= (d);
            } }
            transition!{ if_singleton(k: int, v: int, l: int, w: int, b: Map<int, int>, c: bool) {
                if c { remove m -= [k => v]; have m >= (b); } else { remove m -= [k => v]; remove m -= [l => w]; }
            } }

            transition!{ imap_if_else_remove_have(a: IMap<int, int>, b: IMap<int, int>, d: IMap<int, int>, c: bool) {
                if c { remove im -= (a); } else { remove im -= (b); }
                have im >= (d);
            } }
            transition!{ set_if_else_remove_have(a: Set<int>, b: Set<int>, d: Set<int>, c: bool) {
                if c { remove s -= (a); } else { remove s -= (b); }
                have s >= (d);
            } }
            transition!{ set_nested(a: Set<int>, b: Set<int>, d: Set<int>, c: bool, e: bool) {
                if c {
                    if e { remove s -= (a); } else { have s >= (a); }
                    have s >= (b);
                } else {
                    remove s -= (b);
                }
                have s >= (d);
            } }
            transition!{ multiset_if_else_remove_have(a: Multiset<int>, b: Multiset<int>, d: Multiset<int>, c: bool) {
                require(forall|x: int| d.count(x) <= 1);
                if c { remove ms -= (a); } else { remove ms -= (b); }
                have ms >= (d);
            } }
            transition!{ persistent_match(a: Map<int, int>, b: Map<int, int>, o: Option<int>) {
                match o {
                    Some(v) => { have pm >= (a); add pm (union)= (a); }
                    None => { have pm >= (b); }
                }
            } }
            transition!{ persistent_if_add(a: Map<int, int>, b: Map<int, int>, d: Map<int, int>, c: bool) {
                have pm >= (a);
                if c { have pm >= (b); } else { have pm >= (d); }
                add pm (union)= (a);
            } }
            transition!{ two_fields(a: Map<int, int>, b: Set<int>, d: Map<int, int>, e: Set<int>, c: bool) {
                if c { remove m -= (a); remove s -= (b); } else { remove s -= (b); }
                have m >= (d);
                have s >= (e);
            } }
        }}
    } => Ok(())
}

// Storage operations under a branch (and after a `let`) in a `#[verified_local_ready]`
// transition (checked macro only): the readiness proof's deposit equality quantified over the
// inline `local_ready::<tr>::deposited`/`<tr>_deposited`, whose `let`/`match` bodies Verus cannot
// choose a trigger in ("Could not automatically infer triggers").
test_verify_one_file_with_options! {
    #[test] branch_storage_local_ready_verified ["--no-cheating"] => IMPORTS.to_string() + verus_code_str! {
        pub struct Tok { pub v: int }
        pub enum Cmd { Put(int), Take, Nop }

        verified_tokenized_state_machine!{
            #[verified_raw_tokens]
            #[verified_local_ready(branchy, keyed)]
            X {
            fields {
                #[sharding(variable)] pub auth: Map<int, Tok>,
                #[sharding(storage_map)] pub stored: Map<int, Tok>,
                #[sharding(variable)] pub n: int,
                #[sharding(constant)] pub k: int,
                #[sharding(map)] pub m: Map<int, int>,
            }
            #[invariant] pub fn same(&self) -> bool { self.auth == self.stored }
            init!{ initialize(k: int) {
                init auth = Map::empty(); init stored = Map::empty(); init n = 0; init k = k;
                init m = Map::empty();
            } }
            transition!{ branchy(cmd: Cmd, t: Tok, a: Map<int, int>, b: Map<int, int>) {
                let key = pre.k + 1;
                match cmd {
                    Cmd::Put(v) => {
                        require(!pre.auth.contains_key(key));
                        remove m -= (a);
                        deposit stored += [key => t];
                        update auth = pre.auth.insert(key, t);
                        update n = v;
                    }
                    Cmd::Take => {
                        require(pre.auth.contains_key(key) && pre.auth[key] == t);
                        withdraw stored -= [key => t];
                        update auth = pre.auth.remove(key);
                    }
                    Cmd::Nop => {}
                }
                have m >= (b);
            } }
            transition!{ keyed(t: Tok) {
                let key = pre.k + 1;
                require(!pre.auth.contains_key(key));
                deposit stored += [key => t];
                update auth = pre.auth.insert(key, t);
            } }
            #[inductive(initialize)] fn initialize_inductive(post: Self, k: int) {}
            #[inductive(branchy)] fn branchy_inductive(pre: Self, post: Self, cmd: Cmd, t: Tok, a: Map<int, int>, b: Map<int, int>) {}
            #[inductive(keyed)] fn keyed_inductive(pre: Self, post: Self, t: Tok) {}
        }}
    } => Ok(())
}

// Checked-macro test of `#[verified_local_ready]` for values bound by patterns (the trusted
// macro has no local-ready operations): `remove`/`have` of a map entry `[k => let v]` (map, imap,
// persistent map), of `Some(let x)` (option, persistent option), refutable patterns, bound
// values in requirements, updates, conditions, later keys and deposits, keys bound by a `let`
// or a pattern, a path after a refutable pattern, and a `let`-bound withdrawal. The local requirement used to read such a value from `__observed(..)`, which is
// arbitrary, so no client could establish it; the local state now takes it from the supplied
// fragments. The clients establish each local requirement from their tokens, some with the
// observed entry in the shared fragment.
test_verify_one_file_with_options! {
    #[test] implicit_bindings_local_ready_verified ["--no-cheating"] => IMPORTS.to_string() + verus_code_str! {
        use vstd::resource::tsm::Machine;
        pub enum Tag { A(int), B }
        verified_tokenized_state_machine!{
            #[verified_raw_tokens]
            #[verified_local_ready(map_remove_bound, map_have_bound, imap_remove_readd,
                pmap_have_bound, option_remove_readd, poption_have_bound, refutable_option,
                refutable_map, bound_condition, bound_key, let_key, refutable_then_have, bound_set,
                literal_after_remove, put, take)]
            X {
            fields {
                #[sharding(map)] pub m: Map<int, int>,
                #[sharding(imap)] pub im: IMap<int, int>,
                #[sharding(persistent_map)] pub pm: Map<int, int>,
                #[sharding(option)] pub o: Option<int>,
                #[sharding(persistent_option)] pub po: Option<int>,
                #[sharding(option)] pub ro: Option<Tag>,
                #[sharding(map)] pub rm: Map<int, Tag>,
                #[sharding(set)] pub s: Set<int>,
                #[sharding(variable)] pub cnt: int,
                #[sharding(option)] pub held: Option<int>,
                #[sharding(variable)] pub full: bool,
                #[sharding(storage_option)] pub st: Option<int>,
            }
            #[invariant] pub fn stored(&self) -> bool {
                self.st == self.held && self.full == (self.held is Some)
            }
            init!{ initialize() {
                init m = Map::empty().insert(1, 5).insert(12, 13); init im = IMap::empty().insert(2, 6);
                init pm = Map::empty().insert(3, 7); init o = Some(8); init po = Some(9);
                init ro = Some(Tag::A(10)); init rm = Map::empty().insert(4, Tag::A(11));
                init s = Set::empty().insert(8);
                init cnt = 0; init held = None; init full = false; init st = None;
            } }
            init!{ initialize_held(v: int) {
                init m = Map::empty(); init im = IMap::empty(); init pm = Map::empty(); init o = None;
                init po = None; init ro = None; init rm = Map::empty(); init s = Set::empty(); init cnt = 0;
                init held = Some(v); init full = true; init st = Some(v);
            } }
            transition!{ map_remove_bound(k: int) {
                remove m -= [k => let v]; require(v > 0); update cnt = v;
            } }
            transition!{ map_have_bound(k: int) { have m >= [k => let v]; require(v > 0); } }
            transition!{ imap_remove_readd(k: int) {
                remove im -= [k => let v]; require(v > 0); add im += [k => v + 1];
            } }
            transition!{ pmap_have_bound(k: int) { have pm >= [k => let v]; require(v > 0); } }
            transition!{ option_remove_readd() {
                remove o -= Some(let x); require(x > 0); add o += Some(x + 1);
            } }
            transition!{ poption_have_bound() { have po >= Some(let x); require(x > 0); } }
            transition!{ refutable_option() {
                remove ro -= Some(let Tag::A(x)); require(x > 0); add ro += Some(Tag::B);
            } }
            transition!{ refutable_map(k: int) { have rm >= [k => let Tag::A(x)]; require(x > 0); } }
            transition!{ bound_condition(k: int, j: int) {
                remove m -= [k => let v];
                if v > 0 { remove m -= [j => let w]; require(w > v); } else { update cnt = 0; }
            } }
            transition!{ bound_key() { remove o -= Some(let x); have m >= [x + 4 => let v]; require(v == 13); } }
            // Keys bound by a `let` or a pattern (no ground fragment term until the
            // completion's entry is read), a path after a refutable pattern, a literal value.
            transition!{ let_key(cur: int) {
                let j = pre.cnt + 1; remove m -= [j => cur]; add m += [j => 0];
            } }
            transition!{ refutable_then_have() {
                remove rm -= [4 => let Tag::A(x)]; add rm += [4 => Tag::B]; have pm >= [3 => 7];
            } }
            transition!{ bound_set() { have o >= Some(let x); remove s -= set { x }; } }
            transition!{ literal_after_remove(a: Map<int, int>) { remove m -= (a); have m >= [12 => 13]; } }
            transition!{ put() {
                remove o -= Some(let x); require(!pre.full);
                add held += Some(x); deposit st += Some(x); update full = true;
            } }
            transition!{ take() { remove held -= Some(let x); withdraw st -= Some(let y); update full = false; } }
            #[inductive(initialize)] fn initialize_inductive(post: Self) { }
            #[inductive(initialize_held)] fn initialize_held_inductive(post: Self, v: int) { }
            #[inductive(map_remove_bound)] fn map_remove_bound_inductive(pre: Self, post: Self, k: int) { }
            #[inductive(map_have_bound)] fn map_have_bound_inductive(pre: Self, post: Self, k: int) { }
            #[inductive(imap_remove_readd)] fn imap_remove_readd_inductive(pre: Self, post: Self, k: int) { }
            #[inductive(pmap_have_bound)] fn pmap_have_bound_inductive(pre: Self, post: Self, k: int) { }
            #[inductive(option_remove_readd)] fn option_remove_readd_inductive(pre: Self, post: Self) { }
            #[inductive(poption_have_bound)] fn poption_have_bound_inductive(pre: Self, post: Self) { }
            #[inductive(refutable_option)] fn refutable_option_inductive(pre: Self, post: Self) { }
            #[inductive(refutable_map)] fn refutable_map_inductive(pre: Self, post: Self, k: int) { }
            #[inductive(bound_condition)] fn bound_condition_inductive(pre: Self, post: Self, k: int, j: int) { }
            #[inductive(bound_key)] fn bound_key_inductive(pre: Self, post: Self) { }
            #[inductive(let_key)] fn let_key_inductive(pre: Self, post: Self, cur: int) { }
            #[inductive(refutable_then_have)] fn refutable_then_have_inductive(pre: Self, post: Self) { }
            #[inductive(bound_set)] fn bound_set_inductive(pre: Self, post: Self) { }
            #[inductive(literal_after_remove)] fn literal_after_remove_inductive(pre: Self, post: Self, a: Map<int, int>) { }
            #[inductive(put)] fn put_inductive(pre: Self, post: Self) { }
            #[inductive(take)] fn take_inductive(pre: Self, post: Self) { }
        }}

        proof fn start() -> (tracked t: X::Token)
            ensures t.fragment() == X::Protocol::embed(X::State {
                m: Map::empty().insert(1, 5).insert(12, 13), im: IMap::empty().insert(2, 6),
                pm: Map::empty().insert(3, 7), o: Some(8), po: Some(9), ro: Some(Tag::A(10)),
                rm: Map::empty().insert(4, Tag::A(11)), s: Set::empty().insert(8), cnt: 0, held: None,
                full: false, st: None })
        {
            let tracked t = X::Protocol::initialize(IMap::tracked_empty());
            let s = choose|s: X::State| X::State::initialize(s) && s.invariant() && t.fragment() == X::Protocol::embed(s);
            assert(s.m =~= Map::empty().insert(1, 5).insert(12, 13));
            assert(s.s =~= Set::empty().insert(8));
            t
        }

        proof fn owned_clients() {
            let tracked t = X::local_ready::map_remove_bound::run(start(), 1);
            let tracked t = X::local_ready::map_have_bound::run(start(), 1);
            let tracked t = X::local_ready::imap_remove_readd::run(start(), 2);
            let tracked t = X::local_ready::pmap_have_bound::run(start(), 3);
            let tracked t = X::local_ready::option_remove_readd::run(start());
            let tracked t = X::local_ready::poption_have_bound::run(start());
            let tracked t = X::local_ready::refutable_option::run(start());
            let tracked t = X::local_ready::refutable_map::run(start(), 4);
            let tracked t = X::local_ready::bound_condition::run(start(), 1, 12);
            let tracked t = X::local_ready::bound_key::run(start());
            let tracked t = X::local_ready::let_key::run(start(), 5);
            let tracked t = X::local_ready::refutable_then_have::run(start());
            let tracked t = X::local_ready::bound_set::run(start());
            let tracked t = X::local_ready::literal_after_remove::run(start(), Map::empty().insert(1, 5));
        }

        // The observed entry is in the shared fragment.
        proof fn shared_clients() {
            let tracked (m, rest) = X::Protocol::take_m(start());
            let tracked rest = X::local_ready::map_have_bound::run_with_shared(rest, &m, 1);
            let tracked (po, rest) = X::Protocol::take_po(start());
            let tracked rest = X::local_ready::poption_have_bound::run_with_shared(rest, &po);
        }

        // The deposit is the removed option's value.
        proof fn deposit_client(tracked v: int) requires v == 8 {
            let tracked mut d = IMap::tracked_empty();
            d.tracked_insert(X::__StorageKey::st, X::__StorageValue::st(v));
            assert(d =~= IMap::empty().insert(X::__StorageKey::st, X::__StorageValue::st(8)));
            let tracked t = X::local_ready::put::run(start(), d);
        }

        // The withdrawn value is bound by a pattern; the invariant links it to `held`.
        proof fn withdraw_client(tracked v: int) {
            let tracked mut b = IMap::tracked_empty();
            b.tracked_insert(X::__StorageKey::st, X::__StorageValue::st(v));
            let tracked t = X::Protocol::initialize_held(b, v);
            let s = choose|s: X::State| X::State::initialize_held(s, v) && s.invariant() && t.fragment() == X::Protocol::embed(s);
            let tracked (t, w) = X::local_ready::take::run(t);
        }
    } => Ok(())
}

// The local-ready API of a transition `t` is the associated items of the generated type
// `local_ready::t` (`run`, `run_with_shared`, `observed`, `precondition`, `ready`, ...). Its
// names used to be suffixes of `t` on `Protocol` and `State` (`Protocol::t_local`, ...), and the
// macro rejected machines where they collided: here transitions `a`, `a_local` and `a_observed`
// (whose raw operations were `a`'s local-ready ones) and State functions named like the former
// `a_declared_requires` and `b_local_deposited` (with `b`'s pattern-bound value: a named local state).
test_verify_one_file_with_options! {
    #[test] local_ready_namespace_former_conflicts_verified ["--no-cheating"] => IMPORTS.to_string() + verus_code_str! {
        use vstd::resource::tsm::Machine;
        pub struct Tok { pub v: int }
        verified_tokenized_state_machine! {
            #[verified_raw_tokens]
            #[verified_local_ready(a, a_local, a_observed, b)]
            N {
                fields {
                    #[sharding(variable)] pub auth: Map<nat, Tok>,
                    #[sharding(storage_map)] pub stored: Map<nat, Tok>,
                    #[sharding(option)] pub o: Option<nat>,
                    #[sharding(variable)] pub n: nat,
                }
                #[invariant] pub fn same(&self) -> bool { self.auth == self.stored }
                // Former names of the local-ready State predicates of `a` and `b`.
                pub open spec fn a_declared_requires(&self) -> bool { self.n == 0 }
                pub open spec fn b_local_deposited(&self) -> nat { self.n }
                init! { initialize() { init auth = Map::empty(); init stored = Map::empty(); init o = Some(1); init n = 0; } }
                transition! { a(t: Tok) {
                    require(!pre.auth.contains_key(1nat));
                    deposit stored += [1nat => t];
                    update auth = pre.auth.insert(1nat, t);
                } }
                transition! { a_local(t: Tok) {
                    require(!pre.auth.contains_key(2nat));
                    deposit stored += [2nat => t];
                    update auth = pre.auth.insert(2nat, t);
                } }
                transition! { a_observed(t: Tok) {
                    require(pre.auth.contains_key(1nat) && pre.auth[1nat] == t);
                    withdraw stored -= [1nat => t];
                    update auth = pre.auth.remove(1nat);
                } }
                transition! { b() {
                    remove o -= Some(let x);
                    update n = x;
                } }
                #[inductive(initialize)] fn initialize_inductive(post: Self) {}
                #[inductive(a)] fn a_inductive(pre: Self, post: Self, t: Tok) {}
                #[inductive(a_local)] fn a_local_inductive(pre: Self, post: Self, t: Tok) {}
                #[inductive(a_observed)] fn a_observed_inductive(pre: Self, post: Self, t: Tok) {}
                #[inductive(b)] fn b_inductive(pre: Self, post: Self) {}
            }
        }

        proof fn client(tracked x: Tok, tracked y: Tok) {
            assert(IMap::<nat, Tok>::empty() =~= Map::<nat, Tok>::empty().to_imap());
            assert(N::__tag_stored(IMap::empty()) =~= IMap::empty());
            let tracked token = N::Protocol::initialize(IMap::tracked_empty());
            let tracked mut d = IMap::tracked_empty();
            d.tracked_insert(N::__StorageKey::stored(1nat), N::__StorageValue::stored(x));
            assert(d =~= IMap::empty().insert(N::__StorageKey::stored(1nat), N::__StorageValue::stored(x)));
            let tracked token = N::local_ready::a::run(token, d, x);
            let tracked mut d = IMap::tracked_empty();
            d.tracked_insert(N::__StorageKey::stored(2nat), N::__StorageValue::stored(y));
            assert(d =~= IMap::empty().insert(N::__StorageKey::stored(2nat), N::__StorageValue::stored(y)));
            let tracked obs = N::local_ready::a_local::observed(token, d, y);
            assert(obs.before.auth.contains_key(1nat));
            let tracked (token, mut w) = N::local_ready::a_observed::run(obs.token, x);
            let tracked x2 = N::__unwrap_stored(w.tracked_remove(N::__StorageKey::stored(1nat)));
            assert(x2 == x);
            let tracked token = N::local_ready::b::run(token);
        }

        proof fn ready_lemma(owned: N::Fragment, h: N::Fragment, deposit: IMap<N::__StorageKey, N::__StorageValue>, t: Tok)
            requires N::local_ready::a_local::precondition(owned, h, deposit, t)
            ensures N::Protocol::a_local_requires(owned, h, deposit, t)
        {
            N::local_ready::a_local::ready(owned, h, deposit, t);
        }
    } => Ok(())
}

// The local-ready namespace of a machine with type parameters: `M::local_ready::t::<T>::run(..)`.
test_verify_one_file_with_options! {
    #[test] local_ready_namespace_generic_verified ["--no-cheating"] => IMPORTS.to_string() + verus_code_str! {
        use vstd::resource::tsm::Machine;
        verified_tokenized_state_machine! {
            #[verified_raw_tokens]
            #[verified_local_ready(put, put_local)]
            G<T> {
                fields {
                    #[sharding(variable)] pub auth: Map<nat, T>,
                    #[sharding(storage_map)] pub stored: Map<nat, T>,
                }
                #[invariant] pub fn same(&self) -> bool { self.auth == self.stored }
                pub open spec fn put_declared_requires(&self) -> bool { true }
                init! { initialize() { init auth = Map::empty(); init stored = Map::empty(); } }
                transition! { put(t: T) {
                    require(!pre.auth.contains_key(1nat));
                    deposit stored += [1nat => t];
                    update auth = pre.auth.insert(1nat, t);
                } }
                transition! { put_local(t: T) {
                    require(!pre.auth.contains_key(2nat));
                    deposit stored += [2nat => t];
                    update auth = pre.auth.insert(2nat, t);
                } }
                #[inductive(initialize)] fn initialize_inductive(post: Self) {}
                #[inductive(put)] fn put_inductive(pre: Self, post: Self, t: T) {}
                #[inductive(put_local)] fn put_local_inductive(pre: Self, post: Self, t: T) {}
            }
        }

        proof fn client<T>(tracked x: T, tracked y: T) {
            assert(IMap::<nat, T>::empty() =~= Map::<nat, T>::empty().to_imap());
            assert(G::__tag_stored::<T>(IMap::empty()) =~= IMap::empty());
            let tracked token = G::Protocol::<T>::initialize(IMap::tracked_empty());
            let tracked mut d = IMap::tracked_empty();
            d.tracked_insert(G::__StorageKey::stored(1nat), G::__StorageValue::<T>::stored(x));
            assert(d =~= IMap::empty().insert(G::__StorageKey::stored(1nat), G::__StorageValue::<T>::stored(x)));
            let tracked token = G::local_ready::put::<T>::run(token, d, x);
            let tracked mut d = IMap::tracked_empty();
            d.tracked_insert(G::__StorageKey::stored(2nat), G::__StorageValue::<T>::stored(y));
            assert(d =~= IMap::empty().insert(G::__StorageKey::stored(2nat), G::__StorageValue::<T>::stored(y)));
            let tracked obs = G::local_ready::put_local::<T>::observed(token, d, y);
            assert(obs.after.auth.contains_key(2nat));
        }
    } => Ok(())
}
