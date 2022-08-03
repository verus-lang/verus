#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const IMPORTS: &str = code_str! {
    #[allow(unused_imports)] use crate::pervasive::{atomic::*};
    #[allow(unused_imports)] use crate::pervasive::{modes::*};
    #[allow(unused_imports)] use crate::pervasive::result::*;
    #[allow(unused_imports)] use crate::pervasive::option::*;
    #[allow(unused_imports)] use crate::pervasive::map::*;
    #[allow(unused_imports)] use crate::pervasive::set::*;
    #[allow(unused_imports)] use crate::pervasive::multiset::*;
    #[allow(unused_imports)] use builtin::*;
    #[allow(unused_imports)] use builtin_macros::*;
    #[allow(unused_imports)] use state_machines_macros::*;

    #[spec]
    #[is_variant]
    pub enum Foo {
        Bar(int),
        Qax(int),
        Duck(int),
    }
};

test_verify_one_file! {
    #[test] test_birds_eye_init_error IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields { #[sharding(variable)] pub t: int }

            init!{
                initialize() {
                    birds_eye let x = 5; // error
                    init t = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "`birds_eye` has no effect in an init!")
}

test_verify_one_file! {
    #[test] test_birds_eye_nontokenized_error IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields { pub t: int }

            transition!{
                tr() {
                    birds_eye let x = 5; // error
                    update t = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "`birds_eye` only makes sense for tokenized state machines")
}

test_verify_one_file! {
    #[test] test_birds_eye_guard IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "a guard value must be a deterministic function")
}

test_verify_one_file! {
    #[test] test_withdraw_bind_guard IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "a guard value must be a deterministic function")
}

test_verify_one_file! {
    #[test] test_birds_eye_req IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'require' statements should not be in the scope of a `birds_eye` let-binding")
}

test_verify_one_file! {
    #[test] require_let_birds_eye_fail IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'require' statements should not be in the scope of a `birds_eye` let-binding")
}

test_verify_one_file! {
    #[test] test_withdraw_bind_req IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'require' statements should not be in the scope of a `withdraw` let-binding")
}

test_verify_one_file! {
    #[test] test_birds_eye_req2 IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'require' statements should not be preceeded by an assert which is in the scope of")
}

test_verify_one_file! {
    #[test] test_withdraw_bind_req2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub so: Option<int>
            }

            property!{
                tr() {
                    if 0 == 0 {
                        withdraw so -= Some(let x);
                        assert(x == 5);
                    }
                    require(x == 5); // error: require depends on withdraw binding
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "'require' statements should not be preceeded by an assert which is in the scope of")
}

test_verify_one_file! {
    #[test] test_birds_eye_special IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'remove' statements should not be in the scope of a `birds_eye` let-binding")
}

test_verify_one_file! {
    #[test] test_withdraw_binding_remove IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'remove' statements should not be in the scope of a `withdraw` let-binding")
}

test_verify_one_file! {
    #[test] test_birds_eye_special2 IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'remove' statements should not be preceeded by an assert which is in the scope of")
}

test_verify_one_file! {
    #[test] test_update_constant IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'update' statement not allowed for field with sharding strategy 'constant'")
}

test_verify_one_file! {
    #[test] test_add_constant IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'add' statement not allowed for field with sharding strategy 'constant'")
}

test_verify_one_file! {
    #[test] test_have_constant IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'have' statement not allowed for field with sharding strategy 'constant'")
}

test_verify_one_file! {
    #[test] test_use_option_directly IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)] pub t: Option<int>,
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.t.get_Some_0();
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "cannot be directly referenced here")
}

test_verify_one_file! {
    #[test] test_use_map_directly IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "cannot be directly referenced here")
}

test_verify_one_file! {
    #[test] test_use_multiset_directly IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "cannot be directly referenced here")
}

test_verify_one_file! {
    #[test] test_use_storage_option_directly IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)] pub t: Option<int>,
                #[sharding(variable)] pub v: int,
            }

            transition!{
                tr() {
                    update v = pre.t.get_Some_0();
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "cannot be directly referenced here")
}

test_verify_one_file! {
    #[test] test_use_nottokenized_directly IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "cannot be directly referenced here")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "cannot be used opaquely")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field_withdraw_kv_value IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)] pub v: Map<int, int>,
            }

            transition!{
                tr() {
                    withdraw v -= [5 => { let s = pre; s.v } ];
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "cannot be used opaquely")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field_remove_kv_key IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "cannot be used opaquely")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field_withdraw_kv_key IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)] pub v: Map<int, int>,
            }

            init!{
                initialize() {
                    init v = Map::empty();
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

        proof fn foo(tracked m: Map<int, int>) {
            requires(equal(m, Map::empty()));

            let tracked inst = X::Instance::initialize(tracked m);
            let tracked t = (tracked inst).tr();
            assert(t === 5);
        }

        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_use_pre_no_field2 IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "`pre` cannot be used opaquely")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field3 IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "any field access must be a state field")
}

test_verify_one_file! {
    #[test] test_use_pre_no_field4 IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "expected a named field")
}

test_verify_one_file! {
    #[test] field_name_reserved_ident1 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub instance: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] field_name_reserved_ident2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub token_a: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] sm_name_reserved_ident1 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ instance {
            fields {
                #[sharding(variable)] pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] sm_name_reserved_ident2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ token_a {
            fields {
                #[sharding(variable)] pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] let_name_reserved_ident1 IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] let_name_reserved_ident2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr() {
                    let token_a = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] arg_reserved_ident1 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(instance: int) {
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] arg_reserved_ident2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            transition!{
                tr(token_a: int) {
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] binding_reserved_ident1 IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "reserved identifier")
}

test_verify_one_file! {
    #[test] duplicate_inductive_lemma IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "duplicate 'inductive' lemma")
}

test_verify_one_file! {
    #[test] missing_inductive_lemma IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "missing inductiveness proofs for")
}

test_verify_one_file! {
    #[test] missing_inductive_lemma_init IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "missing inductiveness proofs for")
}

test_verify_one_file! {
    #[test] inductive_lemma_readonly IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'inductive' lemma does not make sense for a 'readonly' transition")
}

test_verify_one_file! {
    #[test] inductive_lemma_property IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'inductive' lemma does not make sense for a 'property' definition")
}

test_verify_one_file! {
    #[test] lemma_wrong_args IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "params for 'inductive' lemma should be")
}

test_verify_one_file! {
    #[test] lemma_bad_transition_name IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "could not find transition")
}

test_verify_one_file! {
    #[test] lemma_bad_generic_params IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "should have no generic parameters")
}

test_verify_one_file! {
    #[test] lemma_bad_return_type IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "should have no return type")
}

test_verify_one_file! {
    #[test] lemma_bad_header IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "the precondition and postcondition are implicit")
}

test_verify_one_file! {
    #[test] lemma_doesnt_verify IMPORTS.to_string() + code_str! {
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

            #[inductive(tr)]
            pub fn lemma_tr1(pre: Self, post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] lemma_doesnt_verify_init IMPORTS.to_string() + code_str! {
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

            #[inductive(tr)]
            pub fn lemma_tr1(post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] sm_generic_param_not_type IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X<'a> {
            fields {
                #[sharding(variable)] pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "Only generic type parameters are supported")
}

test_verify_one_file! {
    #[test] multiple_fields IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }

            fields {
                #[sharding(variable)] pub x: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "Expected only one declaration of `fields` block")
}

test_verify_one_file! {
    #[test] no_fields IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
        }}
    } => Err(e) => assert_error_msg(e, "'fields' declaration was not found")
}

test_verify_one_file! {
    #[test] conflicting_attrs IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "conflicting attributes")
}

test_verify_one_file! {
    #[test] explicit_mode_inv IMPORTS.to_string() + code_str! {
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
            #[spec]
            pub fn the_inv(self) -> bool {
                true
            }
        }}
    } => Err(e) => assert_error_msg(e, "should not be explicitly labelled")
}

test_verify_one_file! {
    #[test] wrong_mode_inv IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "an invariant function should be `spec`")
}

test_verify_one_file! {
    #[test] wrong_mode_inductive IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "an inductiveness lemma should be `proof`")
}

test_verify_one_file! {
    #[test] explicit_mode_field IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)] #[spec] pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "should not be explicitly labelled")
}

test_verify_one_file! {
    #[test] explicit_mode_proof IMPORTS.to_string() + code_str! {
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
            #[proof]
            pub fn lemma_tr1(post: Self, x: int) {
            }
        }}
    } => Err(e) => assert_error_msg(e, "should not be explicitly labelled")
}

test_verify_one_file! {
    #[test] inv_wrong_params IMPORTS.to_string() + code_str! {
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
            #[proof]
            pub fn lemma_tr1(post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_error_msg(e, "an invariant function must take 1 argument (self)")
}

test_verify_one_file! {
    #[test] inv_wrong_ret IMPORTS.to_string() + code_str! {
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
            #[proof]
            pub fn lemma_tr1(post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_error_msg(e, "an invariant function must return a bool")
}

test_verify_one_file! {
    #[test] inv_wrong_generics IMPORTS.to_string() + code_str! {
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
            #[proof]
            pub fn lemma_tr1(post: Self, x: int) {
            } // FAILS
        }}
    } => Err(e) => assert_error_msg(e, "an invariant function must take 0 type arguments")
}

test_verify_one_file! {
    #[test] normal_sm_sharding IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                #[sharding(variable)] pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "sharding strategy only makes sense for tokenized state machines")
}

test_verify_one_file! {
    #[test] tokenized_sm_no_sharding IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "tokenized state machine requires a sharding strategy")
}

test_verify_one_file! {
    #[test] unrecognized_sharding_strategy_name IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(foo)] pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "unrecognized sharding strategy")
}

test_verify_one_file! {
    #[test] duplicate_sharding_attr IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)]
                #[sharding(variable)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "duplicate sharding attribute")
}

test_verify_one_file! {
    #[test] wrong_form_option IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Option<_>")
}

test_verify_one_file! {
    #[test] wrong_form_option2 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Multiset<int>,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Option<_>")
}

test_verify_one_file! {
    #[test] wrong_form_option3 IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(option)]
                pub t: Map<int, int>,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Option<_>")
}

test_verify_one_file! {
    #[test] wrong_form_storage_option IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Option<_>")
}

test_verify_one_file! {
    #[test] wrong_form_map IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(map)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Map<_, _>")
}

test_verify_one_file! {
    #[test] wrong_form_storage_map IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Map<_, _>")
}

test_verify_one_file! {
    #[test] wrong_form_multiset IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(multiset)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Multiset<_>")
}

test_verify_one_file! {
    #[test] wrong_form_set IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(set)]
                pub t: Multiset<int>,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be of the form Set<_>")
}

test_verify_one_file! {
    #[test] wrong_form_count IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(count)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be nat")
}

test_verify_one_file! {
    #[test] wrong_form_bool IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(bool)]
                pub t: int,
            }
        }}
    } => Err(e) => assert_error_msg(e, "must be bool")
}

test_verify_one_file! {
    #[test] special_op_conditional IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statements are not supported inside conditionals")
}

test_verify_one_file! {
    #[test] special_op_binding_conditional IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statements are not supported inside conditionals")
}

test_verify_one_file! {
    #[test] special_op_match IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statements are not supported inside conditionals")
}

test_verify_one_file! {
    #[test] remove_after_have IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "remove -> have -> add")
}

test_verify_one_file! {
    #[test] remove_after_have_with_binding IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "remove -> have -> add")
}

test_verify_one_file! {
    #[test] have_after_add IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "remove -> have -> add")
}

test_verify_one_file! {
    #[test] remove_after_add IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "remove -> have -> add")
}

test_verify_one_file! {
    #[test] init_wf_init_missing IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: int,
            }

            init!{
                init() {
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "procedure does not initialize")
}

test_verify_one_file! {
    #[test] init_wf_init_dupe IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "might be initialized multiple times")
}

test_verify_one_file! {
    #[test] init_wf_init_dupe_conditional IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "might be initialized multiple times")
}

test_verify_one_file! {
    #[test] init_wf_init_if IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "the else-branch does not initialize")
}

test_verify_one_file! {
    #[test] init_wf_init_dupe_match IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "might be initialized multiple times")
}

test_verify_one_file! {
    #[test] init_wf_init_else IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "the if-branch does not initialize")
}

test_verify_one_file! {
    #[test] init_wf_init_match IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "all branches of a match-statement must initialize")
}

test_verify_one_file! {
    #[test] init_wf_init_match2 IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "all branches of a match-statement must initialize")
}

test_verify_one_file! {
    #[test] init_wf_update IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'update' statement not allowed in initialization")
}

test_verify_one_file! {
    #[test] init_wf_update2 IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'update' statement not allowed in initialization")
}

test_verify_one_file! {
    #[test] init_wf_special IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "use 'init' instead")
}

test_verify_one_file! {
    #[test] init_wf_special_with_binding IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "use 'init' instead")
}

test_verify_one_file! {
    #[test] init_wf_assert IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'assert' statement not allowed in initialization")
}

test_verify_one_file! {
    #[test] normal_wf_update_dupe IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "might be updated multiple times")
}

test_verify_one_file! {
    #[test] normal_wf_update_dupe_conditional IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "might be updated multiple times")
}

test_verify_one_file! {
    #[test] normal_wf_update_dupe_conditional2 IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "might be updated multiple times")
}

test_verify_one_file! {
    #[test] normal_wf_update_dupe_match IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "might be updated multiple times")
}

test_verify_one_file! {
    #[test] normal_wf_update_init IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'init' statement not allowed")
}

test_verify_one_file! {
    #[test] normal_wf_update_guard IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "'guard' statement only allowed in 'readonly' transition or 'property' definition")
}

test_verify_one_file! {
    #[test] readonly_wf_update IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_one_file! {
    #[test] property_wf_update IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statement not allowed in property definition")
}

test_verify_one_file! {
    #[test] readonly_wf_init IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statement not allowed outside 'init' routine")
}

test_verify_one_file! {
    #[test] property_wf_init IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statement not allowed outside 'init' routine")
}

test_verify_one_file! {
    #[test] readonly_wf_add IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_one_file! {
    #[test] property_wf_add IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statement not allowed in 'property' definition")
}

test_verify_one_file! {
    #[test] readonly_wf_remove_with_binding IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_one_file! {
    #[test] readonly_wf_remove IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_one_file! {
    #[test] readonly_wf_deposit IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_one_file! {
    #[test] readonly_wf_withdraw IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statement not allowed in readonly transition")
}

test_verify_one_file! {
    #[test] field_not_found IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "field 'whats_this' not found")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_remove IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_remove_with_binding IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_remove IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_remove IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_add IMPORTS.to_string() + code_str! {
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
                assert(pre.t.is_None());
                assert(post.t.is_Some());
                assert(post.t.get_Some_0() == 5);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_general_add IMPORTS.to_string() + code_str! {
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
                assert(pre.t.is_None());
                assert(post.t.is_Some());
                assert(post.t.get_Some_0() == 5);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_add IMPORTS.to_string() + code_str! {
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

test_verify_one_file! {
    #[test] inherent_safety_condition_map_general_add IMPORTS.to_string() + code_str! {
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

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_add IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_general_add IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_have IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_have IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_have IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "adding a proof body is meaningless")
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_withdraw IMPORTS.to_string() + code_str! {
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
                assert(pre.t.is_Some());
                assert(pre.t.get_Some_0() == 5);
                assert(post.t.is_None());
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_withdraw IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: Map<int, int>
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

test_verify_one_file! {
    #[test] inherent_safety_condition_map_withdraw_with_binding IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: Map<int, int>
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

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_withdraw IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "storage_multiset strategy not implemented")
    //} => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>
            }

            property!{
                tr() {
                    guard t >= Some(5) by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.is_Some() && t.get_Some_0() == 5);
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: Map<int, int>
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

test_verify_one_file! {
    #[test] inherent_safety_condition_option_general_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_option)]
                pub t: Option<int>
            }

            property!{
                tr() {
                    guard t >= (Option::Some(5)) by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.is_Some() && t.get_Some_0() == 5);
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_general_guard IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: Map<int, int>
            }

            property!{
                tr() {
                    guard t >= (Map::<int,int>::empty().insert(5, 7)) by { }; // FAILS

                    birds_eye let t = pre.t;
                    assert(t.dom().contains(5) && t.index(5) == 7) by {
                        assert(Map::<int,int>::empty().insert(5, 7).dom().contains(5));
                        assert(Map::<int,int>::empty().insert(5, 7).index(5) == 7);
                    };
                }
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_guard IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "storage_multiset strategy not implemented")
    //} => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_general_guard IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "unrecognized sharding strategy: 'storage_multiset'")
    //} => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_option_deposit IMPORTS.to_string() + code_str! {
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
                assert(pre.t.is_None());
                assert(post.t.is_Some());
                assert(post.t.get_Some_0() == 5);
            }
        }}
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] inherent_safety_condition_map_deposit IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(storage_map)]
                pub t: Map<int, int>
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

test_verify_one_file! {
    #[test] inherent_safety_condition_multiset_deposit IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "storage_multiset strategy not implemented")
}

test_verify_one_file! {
    #[test] assert_safety_condition_fail IMPORTS.to_string() + code_str! {
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

test_verify_one_file! {
    #[test] assert_safety_condition_readonly_fail IMPORTS.to_string() + code_str! {
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

test_verify_one_file! {
    #[test] assert_safety_condition_property_fail IMPORTS.to_string() + code_str! {
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

test_verify_one_file! {
    #[test] wrong_op_var_add_option IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "statement not allowed for field with sharding strategy")
}

test_verify_one_file! {
    #[test] wrong_op_multiset_add_option IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'multiset'")
}

test_verify_one_file! {
    #[test] wrong_op_multiset_add_set IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'multiset'")
}

test_verify_one_file! {
    #[test] wrong_op_set_add_multiset IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'set'")
}

test_verify_one_file! {
    #[test] wrong_op_multiset_add_option_with_binding IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'multiset'")
}

test_verify_one_file! {
    #[test] wrong_op_map_add_option IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'map'")
}

test_verify_one_file! {
    #[test] wrong_op_option_add_map IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'option'")
}

test_verify_one_file! {
    #[test] wrong_op_option_add_multiset IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'option'")
}

test_verify_one_file! {
    #[test] wrong_op_map_add_multiset IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'map'")
}

test_verify_one_file! {
    #[test] wrong_op_multiset_add_map IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'multiset'")
}

test_verify_one_file! {
    #[test] wrong_op_map_guard_option IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'map'")
}

test_verify_one_file! {
    #[test] wrong_op_count_add_option IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(count)]
                pub t: nat,
            }

            transition!{
                tr() {
                    add t += Some(spec_literal_nat("5"));
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "element but the given field has sharding strategy 'count'")
}

test_verify_one_file! {
    #[test] wrong_op_option_deposit_option IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "is only for storage types")
}

test_verify_one_file! {
    #[test] wrong_op_storage_option_add_option IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "use deposit/withdraw/guard statements for storage strategies")
}

test_verify_one_file! {
    #[test] no_let_repeated_idents IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: Map<int, int>
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
    } => Err(e) => assert_error_msg(e, "bound variables with the same name")
}

test_verify_one_file! {
    #[test] no_let_repeated_idents2 IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: Map<int, int>
            }

            transition!{
                tr() {
                    let x = 5;
                    let x = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "bound variables with the same name")
}

test_verify_one_file! {
    #[test] no_let_repeated_idents3 IMPORTS.to_string() + code_str! {
        state_machine!{ X {
            fields {
                pub t: Map<int, int>
            }

            transition!{
                tr(x: int) {
                    let x = 5;
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "bound variables with the same name")
}

test_verify_one_file! {
    #[test] no_let_repeated_idents4 IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "bound variables with the same name")
}

test_verify_one_file! {
    #[test] type_recursion_fail IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                #[sharding(variable)]
                pub t: X::Instance,
            }
        }}
    } => Err(e) => assert_error_msg(e, "recursive type")
}

test_verify_one_file! {
    #[test] type_recursion_fail_negative IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ X {
            fields {
                // this should fail because Map has a maybe_negative first param

                #[sharding(variable)]
                pub t: Map<X::Instance, int>
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "non-positive polarity")
}

test_verify_one_file! {
    #[test] lemma_recursion_fail IMPORTS.to_string() + code_str! {
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
                #[proof] let tracked (inst, token) = X::Instance::initialize();
                tracked inst.ro(&token);
                // this should derive a contradiction if not for the recursion checking
            }
        }}
    } => Err(e) => assert_vir_error_msg(e, "recursive function must call decreases")
}

test_verify_one_file! {
    #[test] lemma_recursion_assert_fail IMPORTS.to_string() + code_str! {
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

        #[proof]
        fn foo_lemma() {
            #[proof] let (inst, token) = X::Instance::initialize();
            inst.ro(&token);
        }
    } => Err(e) => assert_vir_error_msg(e, "recursive function must call decreases")
}

test_verify_one_file! {
    #[test] relation_codegen IMPORTS.to_string() + code_str! {
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

test_verify_one_file! {
    #[test] relation_codegen_match IMPORTS.to_string() + code_str! {
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
                        Foo::Duck(d) => { assert(foo.is_Duck()); }
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

test_verify_one_file! {
    #[test] relation_codegen_special IMPORTS.to_string() + code_str! {
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
            &&& pre.opt === Option::Some(5)
            &&& pre.map.contains_pair(0, 1)
            &&& pre.map.remove(0).contains_pair(2, 3)
            &&& !pre.map.remove(0).dom().contains(4)
              ==> pre.mset.count(10) >= 1
              && pre.mset.remove(10).count(11) >= 1
              && (pre.storage_opt === Option::Some(13)
                ==> (pre.storage_map.contains_pair(15, 16)
                  ==> (!pre.storage_map.remove(15).dom().contains(17)
                    ==> post.storage_map === pre.storage_map.remove(15).insert(17, 18)
                     && post.opt === Option::Some(8)
                     && post.map === pre.map.remove(0).insert(4, 5)
                     && post.mset === pre.mset.remove(10).insert(12)
                     && post.storage_opt === Option::Some(14)
                  )))
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::Some(5)
            &&& post.opt === Option::Some(8)

            &&& pre.map.contains_pair(0, 1)
            &&& pre.map.remove(0).contains_pair(2, 3)
            &&& !pre.map.remove(0).dom().contains(4)
            &&& post.map === pre.map.remove(0).insert(4, 5)

            &&& pre.mset.count(10) >= 1
            &&& pre.mset.remove(10).count(11) >= 1
            &&& post.mset === pre.mset.remove(10).insert(12)

            &&& pre.storage_opt === Option::Some(13)
            &&& post.storage_opt === Option::Some(14)

            &&& pre.storage_map.contains_pair(15, 16)
            &&& !pre.storage_map.remove(15).dom().contains(17)
            &&& post.storage_map === pre.storage_map.remove(15).insert(17, 18)
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::Some(7)
            &&& !pre.map.dom().contains(4) ==> {
                &&& post.map === pre.map.insert(4, 5)
                &&& post.opt === pre.opt
                &&& post.storage_opt === pre.storage_opt
                &&& post.storage_map === pre.storage_map
                &&& post.mset === pre.mset
            }
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::Some(7)
            &&& !pre.map.dom().contains(4)
            &&& post.map === pre.map.insert(4, 5)
            &&& post.opt === pre.opt
            &&& post.storage_opt === pre.storage_opt
            &&& post.storage_map === pre.storage_map
            &&& post.mset === pre.mset
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::Some(7)
            &&& pre.storage_opt === Option::Some(12)
              ==> post.storage_opt === Option::None
                && post.map === pre.map
                && post.storage_map === pre.storage_map
                && post.mset === pre.mset
                && post.opt === Option::None
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::Some(7)
            &&& post.opt === Option::None
            &&& pre.storage_opt === Option::Some(12)
            &&& post.storage_opt === Option::None
            &&& post.map === pre.map
            &&& post.storage_map === pre.storage_map
            &&& post.mset === pre.mset
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            pre.opt === Option::None ==> (
              (pre.storage_opt === Option::None ==> {
                &&& post.storage_opt === Option::Some(12)
                &&& post.map === pre.map
                &&& post.storage_map === pre.storage_map
                &&& post.mset === pre.mset
                &&& post.opt === Option::Some(7)
              })
            )
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::None
            &&& post.opt === Option::Some(7)
            &&& pre.storage_opt === Option::None
            &&& post.storage_opt === Option::Some(12)
            &&& post.map === pre.map
            &&& post.storage_map === pre.storage_map
            &&& post.mset === pre.mset
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
}

test_verify_one_file! {
    #[test] relation_codegen_special_general IMPORTS.to_string() + code_str! {
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
            &&& pre.opt === Option::Some(5)

            &&& map![0 => 1].le(pre.map)
            &&& map![2 => 3].le(pre.map.remove_keys(map![0 => 1int].dom()))
            &&& pre.map.remove_keys(map![0 => 1int].dom()).dom().disjoint(map![4 => 5int].dom())

            ==> {

            &&& Multiset::singleton(10).le(pre.mset)
            &&& Multiset::singleton(11).le(pre.mset.sub(Multiset::singleton(10)))

            &&& (pre.storage_opt === Option::Some(13)

            ==>

            (map![15 => 16].le(pre.storage_map)

            ==>

            (pre.storage_map.remove_keys(map![15 => 16int].dom()).dom().disjoint(map![17 => 18int].dom())

            ==> {

            &&& post.opt === Option::Some(8)
            &&& post.map === pre.map.remove_keys(map![0 => 1int].dom()).union_prefer_right(map![4 => 5])
            &&& post.mset ===
                pre.mset.sub(Multiset::singleton(10)).add(Multiset::singleton(12))
            &&& post.storage_opt === Option::Some(14)
            &&& post.storage_map ===
                pre.storage_map.remove_keys(map![15 => 16int].dom()).union_prefer_right(map![17 => 18])
            })))}
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::Some(5)
            &&& post.opt === Option::Some(8)

            &&& map![0 => 1].le(pre.map)
            &&& map![2 => 3].le(pre.map.remove_keys(map![0 => 1int].dom()))
            &&& pre.map.remove_keys(map![0 => 1int].dom()).dom().disjoint(map![4 => 5int].dom())
            &&& post.map === pre.map.remove_keys(map![0 => 1int].dom()).union_prefer_right(map![4 => 5])

            &&& Multiset::singleton(10).le(pre.mset)
            &&& Multiset::singleton(11).le(pre.mset.sub(Multiset::singleton(10)))
            &&& post.mset ===
                pre.mset.sub(Multiset::singleton(10)).add(Multiset::singleton(12))

            &&& pre.storage_opt === Option::Some(13)
            &&& post.storage_opt === Option::Some(14)

            &&& map![15 => 16].le(pre.storage_map)
            &&& pre.storage_map.remove_keys(map![15 => 16int].dom()).dom().disjoint(map![17 => 18int].dom())
            &&& post.storage_map ===
                pre.storage_map.remove_keys(map![15 => 16int].dom()).union_prefer_right(map![17 => 18])
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::Some(7)
            &&& !pre.map.dom().contains(4) ==> {
                &&& post.map === pre.map.union_prefer_right(map![4 => 5])
                &&& post.opt === pre.opt
                &&& post.storage_opt === pre.storage_opt
                &&& post.storage_map === pre.storage_map
                &&& post.mset === pre.mset
            }
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::Some(7)
            &&& !pre.map.dom().contains(4)
            &&& post.map === pre.map.union_prefer_right(map![4 => 5])
            &&& post.opt === pre.opt
            &&& post.storage_opt === pre.storage_opt
            &&& post.storage_map === pre.storage_map
            &&& post.mset === pre.mset
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::Some(7)
            &&& pre.storage_opt === Option::Some(12) ==> {
                &&& post.storage_opt === Option::None
                &&& post.map === pre.map
                &&& post.storage_map === pre.storage_map
                &&& post.mset === pre.mset
                &&& post.opt === Option::None
            }
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::Some(7)
            &&& post.opt === Option::None
            &&& pre.storage_opt === Option::Some(12)
            &&& post.storage_opt === Option::None
            &&& post.map === pre.map
            &&& post.storage_map === pre.storage_map
            &&& post.mset === pre.mset
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            pre.opt === Option::None ==> (
              (pre.storage_opt === Option::None ==> {
                &&& post.storage_opt === Option::Some(12)
                &&& post.map === pre.map
                &&& post.storage_map === pre.storage_map
                &&& post.mset === pre.mset
                &&& post.opt === Option::Some(7)
              })
            )
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::None
            &&& post.opt === Option::Some(7)
            &&& pre.storage_opt === Option::None
            &&& post.storage_opt === Option::Some(12)
            &&& post.map === pre.map
            &&& post.storage_map === pre.storage_map
            &&& post.mset === pre.mset
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
}

test_verify_one_file! {
    #[test] relation_codegen_opt_general IMPORTS.to_string() + code_str! {
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

test_verify_one_file! {
    #[test] nondet_tokenizing IMPORTS.to_string() + code_str! {
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

        #[proof]
        fn go() {
            #[proof] let (instance, mut v1, v2) = Z::Instance::initialize();
            assert(equal(v1.instance, instance));
            assert(equal(v2.instance, instance));
            assert(equal(v1.value, spec_literal_int("0")));
            assert(equal(v2.value, spec_literal_int("1")));
            assert(equal(instance.c(), spec_literal_int("3")));

            #[proof] instance.tr1(&mut v1);
            assert(equal(v1.instance, instance));
            assert(equal(v1.value, spec_literal_int("2")));

            #[spec] let old_v1_value = v1.value;
            #[proof] let (birds_eye_v2, birds_eye_nt) = instance.tr2(&mut v1);
            assert(equal(v1.instance, instance));
            assert(equal(v1.value,
                birds_eye_nt.value() + instance.c() + old_v1_value - birds_eye_v2.value()));

            #[spec] let old_v1_value = v1.value;
            #[proof] let birds_eye_nt = instance.tr3(&mut v1, &v2);
            assert(equal(v1.instance, instance));
            assert(equal(v1.value, birds_eye_nt.value() + instance.c() + old_v1_value + spec_literal_int("3") * v2.value));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] pre_in_init IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "no previous state to refer to")
}

test_verify_one_file! {
    #[test] self_in_transition IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "`self` is meaningless")
}

test_verify_one_file! {
    #[test] post_in_transition IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "cannot refer directly to `post`")
}

test_verify_one_file! {
    #[test] test_let_pattern IMPORTS.to_string() + code_str! {
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

test_verify_one_file! {
    #[test] super_error IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "`super::` path not allowed here")
}

test_verify_one_file! {
    #[test] if_let_fail IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "do not support if-let conditionals")
}

test_verify_one_file! {
    #[test] if_let_fail_with_else IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "do not support if-let conditionals")
}

test_verify_one_file! {
    #[test] if_let_fail_with_chain IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "do not support if-let conditionals")
}

test_verify_one_file! {
    #[test] use_self_type IMPORTS.to_string() + code_str! {
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

        pub fn foo() {
            #[proof] let (inst, mut x_tok, mut r_tok) = Y::Instance::ini(
                Y::State { x: spec_literal_int("5"), recursing: Option::None }
            );
            inst.tr(spec_literal_int("19"), &mut x_tok);
            assert(x_tok.value == spec_literal_int("20"));

            inst.tr2(Option::<Box<Y::State>>::None, &mut r_tok);
            assert(equal(Option::<Box<Y::State>>::None, r_tok.value));

            inst.tr3(&mut r_tok);
            assert(equal(Option::<Box<Y::State>>::None, r_tok.value));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] bind_codegen IMPORTS.to_string() + code_str! {

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
                forall(|k| imply(self.storage_map.dom().contains(k),
                    self.storage_map.index(k) == 6))
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
            &&& pre.opt === Option::Some(2)
            &&& post.opt === Option::None
            &&& post.map === pre.map
            &&& post.storage_map === pre.storage_map
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.opt === Option::Some(2)
            &&& post.opt === Option::None
            &&& post.map === pre.map
            &&& post.storage_map === pre.storage_map
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State, key: int) -> bool {
            &&& pre.map.dom().contains(key)
            &&& pre.map.index(key) == 5

            &&& (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              ==> {
                &&& post.map === pre.map.remove(key)
                &&& post.storage_map === pre.storage_map.remove(key)
                &&& post.opt === pre.opt
              }
           )
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            &&& pre.map.dom().contains(key)
            &&& pre.map.index(key) == 5
            &&& (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              && {
                &&& post.map === pre.map.remove(key)
                &&& post.storage_map === pre.storage_map.remove(key)
                &&& post.opt === pre.opt
              }
           )
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State, key: int) -> bool {
            &&& pre.map.dom().contains(key)
            &&& pre.map.index(key) == 5

            &&& (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              ==> {
                &&& post.map === pre.map
                &&& post.storage_map === pre.storage_map
                &&& post.opt === pre.opt
              }
           )
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            &&& pre.map.dom().contains(key)
            &&& pre.map.index(key) == 5

            &&& (
              (pre.storage_map.dom().contains(key) && pre.storage_map.index(key) == 6)
              && {
                &&& post.map === pre.map
                &&& post.storage_map === pre.storage_map
                &&& post.opt === pre.opt
              }
           )
        }
        } // verus!

        #[proof]
        fn correct_tr1(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1(pre, post));
            ensures(rel_tr1(pre, post));
        }

        #[proof]
        fn rev_tr1(pre: Y::State, post: Y::State) {
            requires(rel_tr1(pre, post));
            ensures(Y::State::tr1(pre, post));
        }

        #[proof]
        fn correct_tr1_strong(pre: Y::State, post: Y::State) {
            requires(Y::State::tr1_strong(pre, post));
            ensures(rel_tr1_strong(pre, post));
        }

        #[proof]
        fn rev_tr1_strong(pre: Y::State, post: Y::State) {
            requires(rel_tr1_strong(pre, post));
            ensures(Y::State::tr1_strong(pre, post));
        }

        #[proof]
        fn correct_tr2(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr2(pre, post, key));
            ensures(rel_tr2(pre, post, key));
        }

        #[proof]
        fn rev_tr2(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr2(pre, post, key));
            ensures(Y::State::tr2(pre, post, key));
        }

        #[proof]
        fn correct_tr2_strong(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr2_strong(pre, post, key));
            ensures(rel_tr2_strong(pre, post, key));
        }

        #[proof]
        fn rev_tr2_strong(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr2_strong(pre, post, key));
            ensures(Y::State::tr2_strong(pre, post, key));
        }

        #[proof]
        fn correct_tr3(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr3(pre, post, key));
            ensures(rel_tr3(pre, post, key));
        }

        #[proof]
        fn rev_tr3(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr3(pre, post, key));
            ensures(Y::State::tr3(pre, post, key));
        }

        #[proof]
        fn correct_tr3_strong(pre: Y::State, post: Y::State, key: int) {
            requires(Y::State::tr3_strong(pre, post, key));
            ensures(rel_tr3_strong(pre, post, key));
        }

        #[proof]
        fn rev_tr3_strong(pre: Y::State, post: Y::State, key: int) {
            requires(rel_tr3_strong(pre, post, key));
            ensures(Y::State::tr3_strong(pre, post, key));
        }

        fn do_tokens() {
            #[proof] let mut m: Map<int, u64> = Map::tracked_empty();
            m.tracked_insert(spec_literal_int("1"), 6);
            #[proof] let (inst, opt_token, mut map_tokens) = Y::Instance::initialize(m);

            match opt_token {
                Option::None => { assert(false); }
                Option::Some(opt_token) => {
                    inst.tr1(opt_token);

                    assert(map_tokens.dom().contains(spec_literal_int("1")));
                    #[proof] let map_token = map_tokens.tracked_remove(spec_literal_int("1"));

                    #[proof] let the_guard = inst.tr4(spec_literal_int("1"), &map_token);
                    assert(*the_guard == 6);

                    #[proof] let t = inst.tr2(spec_literal_int("1"), map_token);
                    assert(t == 6);
                }
            };
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] bind_fail_add IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "pattern-binding cannot be used in an 'add' statement")
}

test_verify_one_file! {
    #[test] bind_fail_deposit IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "pattern-binding cannot be used in a 'deposit' statement")
}

test_verify_one_file! {
    #[test] bind_fail_guard IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "pattern-binding cannot be used in a 'guard' statement")
}

test_verify_one_file! {
    #[test] assert_let_fail_1_bind IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "unable to prove safety condition that the pattern matches")
}

test_verify_one_file! {
    #[test] assert_let_fail_0_bind IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "unable to prove safety condition that the pattern matches")
}

test_verify_one_file! {
    #[test] assert_require_let_codegen IMPORTS.to_string() + code_str! {
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
                imply(self.opt1.is_Some(), (
                    self.opt2.is_Some()
                        && self.opt4.is_Some()
                        && equal(self.opt2, self.opt4)
                        && self.opt3.is_None()
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
                                &&& post.opt1 === Option::None
                                &&& post.opt2 === pre.opt2
                                &&& post.opt3 === Option::Some(x + y + z)
                                &&& post.opt4 === pre.opt4
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
            #[proof] inst: Y::Instance,
            #[proof] t1: Y::opt1,
            #[proof] t2: Y::opt2,
            #[proof] t3: Y::opt3,
            #[proof] t4: Y::opt4
        ) {
            requires([
                equal(inst, t1.instance),
                equal(inst, t2.instance),
                equal(inst, t3.instance),
                equal(inst, t4.instance),
                equal(t1.value, Option::Some(0)),
                equal(t2.value, Option::Some(5)),
            ]);

            #[spec] let old_t1 = t1;
            #[spec] let old_t3 = t3;

            #[proof] let mut t1 = tracked t1;
            #[proof] let mut t3 = tracked t3;

            tracked inst.tr1(&mut t1, &t2, &mut t3, &t4);

            assert(equal(old_t3.value, Option::None));
            assert(equal(t4.value, Option::Some(5)));
            assert(equal(t1.value, Option::None));
            assert(equal(t3.value, Option::Some(10)));
        }

        proof fn test_start() {
            #[proof] let (inst, t1, t2, t3, t4) = Y::Instance::initialize();
            test_transition(tracked inst, tracked t1, tracked t2, tracked t3, tracked t4);
        }

        } // verus!

    } => Ok(())
}

test_verify_one_file! {
    #[test] count_codegen IMPORTS.to_string() + code_str! {
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
                    add c += (spec_literal_nat("2"));
                }
            }

            transition!{
                tr_have() {
                    have c >= (spec_literal_nat("2"));
                }
            }

            transition!{
                tr_remove() {
                    remove c -= (spec_literal_nat("2"));
                }
            }
        }}

        #[spec]
        fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            post.c == pre.c + spec_literal_nat("2")
        }

        #[spec]
        fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            post.c == pre.c + spec_literal_nat("2")
        }

        #[spec]
        fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.c >= spec_literal_nat("2") && post.c == pre.c
        }

        #[spec]
        fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.c >= spec_literal_nat("2") && post.c == pre.c
        }

        #[spec]
        fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            pre.c >= spec_literal_nat("2") && post.c == pre.c - spec_literal_nat("2")
        }

        #[spec]
        fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            pre.c >= spec_literal_nat("2") && post.c == pre.c - spec_literal_nat("2")
        }

        #[proof]
        fn correct_tr(pre: Y::State, post: Y::State) {
            ensures([
                rel_tr1(pre, post) == Y::State::tr_add(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr_have(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),
                rel_tr3(pre, post) == Y::State::tr_remove(pre, post),
                rel_tr3_strong(pre, post) == Y::State::tr_remove_strong(pre, post),
            ]);
        }

        fn test_inst() {
            #[proof] let (inst, t1) = Y::Instance::initialize();
            assert(t1.value == spec_literal_nat("9"));

            #[proof] let (t2, t3) = t1.split(spec_literal_nat("2"));

            assert(t2.value == spec_literal_nat("2"));
            assert(t3.value == spec_literal_nat("7"));

            inst.tr_have(&t2);
            inst.tr_remove(t2);

            #[proof] let t4 = inst.tr_add();
            assert(t4.value == spec_literal_nat("2"));

            #[proof] let q = t4.join(t3);
            assert(q.value == spec_literal_nat("9"));
        }

        fn test_join_fail() {
            #[proof] let (inst1, t1) = Y::Instance::initialize();
            #[proof] let (inst2, t2) = Y::Instance::initialize();
            #[proof] let t = t1.join(t2); // FAILS
        }

        fn test_split_fail() {
            #[proof] let (inst, t1) = Y::Instance::initialize();

            #[proof] let (t2, t3) = t1.split(spec_literal_nat("10")); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] persistent_option_remove_fail IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "a persistent field's value can only grow, never remove or modify its data")
}

test_verify_one_file! {
    #[test] persistent_map_remove_fail IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_map)]
                pub c: Map<int, int>,
            }

            transition!{
                tr_remove() {
                    remove c -= [1 => 2];
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "a persistent field's value can only grow, never remove or modify its data")
}

test_verify_one_file! {
    #[test] persistent_bool_remove_fail IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "a persistent field's value can only grow, never remove or modify its data")
}

test_verify_one_file! {
    #[test] persistent_count_remove_fail IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "a persistent field's value can only grow, never remove or modify its data")
}

test_verify_one_file! {
    #[test] persistent_set_remove_fail IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_set)]
                pub c: Set<int>,
            }

            transition!{
                tr_remove() {
                    remove c -= set { 1 };
                }
            }
        }}
    } => Err(e) => assert_error_msg(e, "a persistent field's value can only grow, never remove or modify its data")
}

test_verify_one_file! {
    #[test] persistent_option_codegen IMPORTS.to_string() + code_str! {
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
                    add c += Some(3);
                }
            }

            transition!{
                tr2() {
                    add c += ( Option::Some(3) );
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
            &&& pre.d === Option::Some(7)
            &&& (
                (match pre.c {
                    Option::Some(x) => x == 3,
                    Option::None => true,
                })
                ==> {
                    &&& pre.d === post.d
                    &&& post.c === Option::Some(3)
                }
            )
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.d === Option::Some(7)
            &&& (
                (match pre.c {
                    Option::Some(x) => x == 3,
                    Option::None => true,
                })
                && {
                    &&& pre.d === post.d
                    &&& post.c === Option::Some(3)
                }
            )
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            (match pre.c {
                Option::Some(x) => x == 3,
                Option::None => true,
            })
            ==> {
                &&& pre.d === post.d
                &&& post.c === Option::Some(3)
            }
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            &&& (match pre.c {
                Option::Some(x) => x == 3,
                Option::None => true,
            })
            &&& {
                &&& pre.d === post.d
                &&& post.c === Option::Some(3)
            }
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            &&& pre.c === Option::Some(3)
            &&& post.c === pre.c
            &&& post.d === pre.d
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            rel_tr3(pre, post)
        }

        } // verus!

        #[proof]
        fn correct_tr(pre: Y::State, post: Y::State) {
            ensures([
                rel_tr1(pre, post) == Y::State::tr1(pre, post),
                rel_tr1_strong(pre, post) == Y::State::tr1_strong(pre, post),
                rel_tr2(pre, post) == Y::State::tr2(pre, post),
                rel_tr2_strong(pre, post) == Y::State::tr2_strong(pre, post),
                rel_tr3(pre, post) == Y::State::tr3(pre, post),
                rel_tr3_strong(pre, post) == Y::State::tr3_strong(pre, post),
            ]);
        }

        fn test_inst() {
            #[proof] let (inst, _c, d_opt) = Y::Instance::initialize();

            #[proof] let d = match d_opt {
                Option::Some(d) => d,
                Option::None => proof_from_false(),
            };

            #[proof] let cloned = d.clone();
            assert(equal(cloned.instance, inst));
            assert(d.value == spec_literal_int("7"));

            #[proof] let c = inst.tr1(&d);
            assert(c.value == spec_literal_int("3"));
            assert(equal(c.instance, inst));

            #[proof] let c2_opt = inst.tr2();
            #[proof] let c2 = match c2_opt {
                Option::Some(c2) => c2,
                Option::None => proof_from_false(),
            };
            assert(c2.value == spec_literal_int("3"));
            assert(equal(c2.instance, inst));

            #[proof] let c_opt = Option::Some(c);
            inst.tr3(&c_opt);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] persistent_map_codegen IMPORTS.to_string() + code_str! {
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
                    add c += [3 => 4];
                }
            }

            transition!{
                tr2() {
                    add c += (
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
                post.c === pre.c.insert(3, 4)
              )
            )
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            &&& pre.c.dom().contains(1)
            &&& pre.c.index(1) == 2
            &&& (
              (pre.c.dom().contains(3) ==> pre.c.index(3) == 4)
              && (
                post.c === pre.c.insert(3, 4)
              )
            )
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            ((pre.c.dom().contains(5) ==> pre.c.index(5) == 9)
            && (pre.c.dom().contains(12) ==> pre.c.index(12) == 15))
            ==> post.c ===
                  pre.c.insert(5, 9).insert(12, 15)
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            ((pre.c.dom().contains(5) ==> pre.c.index(5) == 9)
            && (pre.c.dom().contains(12) ==> pre.c.index(12) == 15))
            && post.c ===
                  pre.c.insert(5, 9).insert(12, 15)
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            &&& ((pre.c.dom().contains(5) && pre.c.index(5) == 9)
            &&& (pre.c.dom().contains(12) && pre.c.index(12) == 15))
            &&& pre.c === post.c
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            &&& ((pre.c.dom().contains(5) && pre.c.index(5) == 9)
            &&& (pre.c.dom().contains(12) && pre.c.index(12) == 15))
            &&& pre.c === post.c
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
            assert_maps_equal_verus!(
                pre.c.insert(5, 9).insert(12, 15),
                pre.c.union_prefer_right(
                    Map::empty().insert(5, 9).insert(12, 15)
                )
            );

            if rel_tr3(pre, post) {
                assert(
                  Map::empty().insert(5, 9).insert(12, 15).le(pre.c)
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
        } // verus!

        fn test_inst() {
            #[proof] let (inst, mut init_m) = Y::Instance::initialize();
            assert(init_m.dom().contains(spec_literal_int("1")));
            #[proof] let m_1 = init_m.tracked_remove(spec_literal_int("1"));
            assert(m_1.value == spec_literal_int("2"));

            #[proof] let cloned = m_1.clone();
            assert(equal(cloned.instance, inst));
            assert(cloned.key == spec_literal_int("1"));
            assert(cloned.value == spec_literal_int("2"));

            #[proof] let m_3 = inst.tr1(&m_1);
            assert(m_3.value == spec_literal_int("4"));

            #[proof] let m_5_12 = inst.tr2();
            assert(m_5_12.dom().contains(spec_literal_int("5")));
            assert(m_5_12.index(spec_literal_int("5")).value == spec_literal_int("9"));
            assert(m_5_12.dom().contains(spec_literal_int("12")));
            assert(m_5_12.index(spec_literal_int("12")).value == spec_literal_int("15"));

            inst.tr3(&m_5_12);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] pattern_binding_withdraw_assert_fails IMPORTS.to_string() + code_str! {
        pub enum Goo {
            Bar,
            Qux(u64),
            Tal(u64, u64),
        }

        tokenized_state_machine!{ Y {
            fields {
                #[sharding(storage_map)]
                pub storage_m: Map<int, Goo>,

                #[sharding(storage_option)]
                pub storage_opt: Option<Goo>,
            }

            transition!{
                tr1() {
                    withdraw storage_opt -= Some(let Goo::Bar) by { // FAILS
                        assume(pre.storage_opt.is_Some());
                    };
                }
            }

            transition!{
                tr2() {
                    withdraw storage_opt -= Some(let Goo::Qux(id1)) by { // FAILS
                        assume(pre.storage_opt.is_Some());
                    };
                }
            }

            transition!{
                tr3() {
                    withdraw storage_opt -= Some(let Goo::Tal(id1, id2)) by { // FAILS
                        assume(pre.storage_opt.is_Some());
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
}

test_verify_one_file! {
    #[test] special_refutable_pattern_binding_codegen IMPORTS.to_string() + code_str! {
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
        #[spec]
        fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
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

        #[spec]
        fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
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
                            &&& post.opt === Option::None
                            &&& post.storage_opt === Option::None
                            &&& post.m === pre.m
                            &&& post.storage_m === pre.storage_m
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
                            &&& post.opt === Option::None
                            &&& post.storage_opt === Option::None
                            &&& post.m === pre.m
                            &&& post.storage_m === pre.storage_m
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
                            &&& post.opt === Option::None
                            &&& post.storage_opt === Option::None
                            &&& post.m === pre.m
                            &&& post.storage_m === pre.storage_m
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
                            &&& post.opt === Option::None
                            &&& post.storage_opt === Option::None
                            &&& post.m === pre.m
                            &&& post.storage_m === pre.storage_m
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
                            &&& post.opt === pre.opt
                            &&& post.storage_opt === pre.storage_opt
                            &&& post.m === pre.m.remove(key)
                            &&& post.storage_m === pre.storage_m.remove(key)
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
                            &&& post.opt === pre.opt
                            &&& post.storage_opt === pre.storage_opt
                            &&& post.m === pre.m.remove(key)
                            &&& post.storage_m === pre.storage_m.remove(key)
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
                            &&& post.opt === pre.opt
                            &&& post.storage_opt === pre.storage_opt
                            &&& post.m === pre.m.remove(key)
                            &&& post.storage_m === pre.storage_m.remove(key)
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
                            &&& post.opt === pre.opt
                            &&& post.storage_opt === pre.storage_opt
                            &&& post.m === pre.m.remove(key)
                            &&& post.storage_m === pre.storage_m.remove(key)
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
                            &&& post.opt === pre.opt
                            &&& post.storage_opt === pre.storage_opt
                            &&& post.m === pre.m.remove(key)
                            &&& post.storage_m === pre.storage_m.remove(key)
                            }
                        }
                        _ => true,
                    }
                }
                _ => false,
            }
        }

        #[spec]
        fn rel_tr6_strong(pre: Y::State, post: Y::State, key: int) -> bool {
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

        #[spec]
        fn rel_tr7(pre: Y::State, post: Y::State, key: int) -> bool {
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

        #[spec]
        fn rel_tr7_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            rel_tr7(pre, post, key)
        }

        #[spec]
        fn rel_tr8(pre: Y::State, post: Y::State, key: int) -> bool {
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

        #[spec]
        fn rel_tr8_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            rel_tr8(pre, post, key)
        }

        #[spec]
        fn rel_tr9(pre: Y::State, post: Y::State, key: int) -> bool {
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

        #[spec]
        fn rel_tr9_strong(pre: Y::State, post: Y::State, key: int) -> bool {
            rel_tr9(pre, post, key)
        }

        #[proof]
        fn correct_tr(pre: Y::State, post: Y::State, key: int) {
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

        } // verus!

        fn test_inst1() {
            #[proof] let mut p_m = Map::tracked_empty();
            p_m.tracked_insert(spec_literal_int("1"), Goo::Bar);

            #[proof] let (inst, mut m_token, opt_token) = Y::Instance::initialize(
                map![spec_literal_int("1") => Goo::Bar],
                Option::Some(Goo::Bar),
                p_m,
                Option::Some(Goo::Bar),
            );

            assert(m_token.dom().contains(spec_literal_int("1")));
            #[proof] let kv = m_token.tracked_remove(spec_literal_int("1"));
            #[proof] let o = match opt_token {
                Option::None => proof_from_false(),
                Option::Some(t) => t,
            };

            inst.tr7(spec_literal_int("1"), &kv, &o);

            #[proof] let wi = inst.tr1(o);
            assert(equal(wi, Goo::Bar));

            #[proof] let wi2 = inst.tr4(spec_literal_int("1"), kv);
            assert(equal(wi2, Goo::Bar));
        }

        fn test_inst2() {
            #[proof] let mut p_m = Map::tracked_empty();
            p_m.tracked_insert(spec_literal_int("1"), Goo::Qux(8));

            #[proof] let (inst, mut m_token, opt_token) = Y::Instance::initialize(
                map![spec_literal_int("1") => Goo::Qux(8)],
                Option::Some(Goo::Qux(8)),
                p_m,
                Option::Some(Goo::Qux(8)),
            );

            assert(m_token.dom().contains(spec_literal_int("1")));
            #[proof] let kv = m_token.tracked_remove(spec_literal_int("1"));
            #[proof] let o = match opt_token {
                Option::None => proof_from_false(),
                Option::Some(t) => t,
            };

            inst.tr8(spec_literal_int("1"), &kv, &o);

            #[proof] let wi = inst.tr2(o);
            assert(equal(wi, Goo::Qux(8)));

            #[proof] let wi2 = inst.tr5(spec_literal_int("1"), kv);
            assert(equal(wi2, Goo::Qux(8)));
        }

        fn test_inst3() {
            #[proof] let mut p_m = Map::tracked_empty();
            p_m.tracked_insert(spec_literal_int("1"), Goo::Tal(8, 9));

            #[proof] let (inst, mut m_token, opt_token) = Y::Instance::initialize(
                map![spec_literal_int("1") => Goo::Tal(8, 9)],
                Option::Some(Goo::Tal(8, 9)),
                p_m,
                Option::Some(Goo::Tal(8, 9)),
            );

            assert(m_token.dom().contains(spec_literal_int("1")));
            #[proof] let kv = m_token.tracked_remove(spec_literal_int("1"));
            #[proof] let o = match opt_token {
                Option::None => proof_from_false(),
                Option::Some(t) => t,
            };

            inst.tr9(spec_literal_int("1"), &kv, &o);

            #[proof] let wi = inst.tr3(o);
            assert(equal(wi, Goo::Tal(8, 9)));

            #[proof] let wi2 = inst.tr6(spec_literal_int("1"), kv);
            assert(equal(wi2, Goo::Tal(8, 9)));
        }

        fn test_precondition_remove1(inst: Y::Instance, t: Y::opt)
        {
          requires(equal(t.instance, inst));
          #[proof] let k = inst.tr1(t); // FAILS
        }

        fn test_precondition_remove2(inst: Y::Instance, t: Y::opt)
        {
          requires(equal(t.instance, inst));
          #[proof] let k = inst.tr2(t); // FAILS
        }

        fn test_precondition_remove3(inst: Y::Instance, t: Y::opt)
        {
          requires(equal(t.instance, inst));
          #[proof] let k = inst.tr3(t); // FAILS
        }

        fn test_precondition_map_remove1(inst: Y::Instance, t: Y::m)
        {
          requires(equal(t.instance, inst) && t.key == spec_literal_int("1"));
          #[proof] let k = inst.tr4(spec_literal_int("1"), t); // FAILS
        }

        fn test_precondition_map_remove2(inst: Y::Instance, t: Y::m)
        {
          requires(equal(t.instance, inst) && t.key == spec_literal_int("1"));
          #[proof] let k = inst.tr5(spec_literal_int("1"), t); // FAILS
        }

        fn test_precondition_map_remove3(inst: Y::Instance, t: Y::m)
        {
          requires(equal(t.instance, inst) && t.key == spec_literal_int("1"));
          #[proof] let k = inst.tr6(spec_literal_int("1"), t); // FAILS
        }

        fn test_precondition_have1(inst: Y::Instance, t: Y::opt, u: Y::m)
        {
          requires(equal(t.instance, inst) && equal(u.instance, inst) && u.key == spec_literal_int("1")
              && equal(t.value, Goo::Bar)
          );
          #[proof] let k = inst.tr7(spec_literal_int("1"), &u, &t); // FAILS
        }

        fn test_precondition_have2(inst: Y::Instance, t: Y::opt, u: Y::m)
        {
          requires(equal(t.instance, inst) && equal(u.instance, inst) && u.key == spec_literal_int("1")
              && equal(u.value, Goo::Bar)
          );
          #[proof] let k = inst.tr7(spec_literal_int("1"), &u, &t); // FAILS
        }

        fn test_precondition_have3(inst: Y::Instance, t: Y::opt, u: Y::m)
        {
          requires(equal(t.instance, inst) && equal(u.instance, inst) && u.key == spec_literal_int("1")
              && equal(u.value, t.value));
          #[proof] let k = inst.tr8(spec_literal_int("1"), &u, &t); // FAILS
        }

        verus!{

        proof fn test_precondition_have4(tracked inst: Y::Instance, tracked t: Y::opt, tracked u: Y::m)
        {
          requires(equal(t.instance, inst) && equal(u.instance, inst) && u.key == spec_literal_int("1")
              && equal(u.value, t.value));
          let k = tracked inst.tr9(1, tracked &u, tracked &t); // FAILS
        }

        }
    } => Err(e) => assert_fails(e, 10)
}

test_verify_one_file! {
    #[test] labels_wrong_type_name IMPORTS.to_string() + code_str! {
        state_machine!{ Y {
            fields {
                pub x: int,
            }

            pub struct AsdfWeirdName { }
        }}
    } => Err(e) => assert_error_msg(e, "only supports the declaration of a `Label` and `InitLabel` types")
}

test_verify_one_file! {
    #[test] labels_init_missing IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "the first param to an 'init'")
}

test_verify_one_file! {
    #[test] labels_init_missing2 IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "the first param to an 'init'")
}

test_verify_one_file! {
    #[test] labels_tr_missing IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "the first param to a 'transition'")
}

test_verify_one_file! {
    #[test] labels_readonly_missing IMPORTS.to_string() + code_str! {
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
    } => Err(e) => assert_error_msg(e, "the first param to a 'readonly'")
}

test_verify_one_file! {
    #[test] bool_codegen IMPORTS.to_string() + code_str! {
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
                        assert(pre.b === false); // FAILS
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
                        assert(pre.b === false || x === false); // FAILS
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
            pre.b === false ==> post.b === true
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b === false && post.b === true
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.b === true && post.b === true
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b === true && post.b === true
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            pre.b === true && post.b === false
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b === true && post.b === false
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State, x: bool) -> bool {
            (!pre.b || !x) ==> (post.b === (pre.b || x))
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
            (!pre.b || !x) && (post.b === (pre.b || x))
        }

        spec fn rel_tr5(pre: Y::State, post: Y::State, x: bool) -> bool {
            (x ==> pre.b) && (post.b === pre.b)
        }

        spec fn rel_tr5_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
            (x ==> pre.b) && (post.b === pre.b)
        }

        spec fn rel_tr6(pre: Y::State, post: Y::State, x: bool) -> bool {
            (x ==> pre.b) && (post.b === (pre.b && !x))
        }

        spec fn rel_tr6_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
            (x ==> pre.b) && (post.b === (pre.b && !x))
        }

        }

        #[proof]
        fn correct_tr(pre: Y::State, post: Y::State, x: bool) {
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

        fn test_inst1() {
            #[proof] let (inst, token_f) = Y::Instance::init_false();
            assert(token_f.is_None());

            #[proof] let tok = inst.tr_add();
            assert(equal(tok.instance, inst));
            inst.tr_have(&tok);
            inst.tr_remove(tok);

            #[proof] let opt_tok = inst.tr_add_gen(true);
            assert(opt_tok.is_Some());
            assert(equal(opt_tok.get_Some_0().instance, inst));
            inst.tr_have_gen(true, &opt_tok);
            inst.tr_remove_gen(true, opt_tok);

            #[proof] let opt_tok = inst.tr_add_gen(false);
            assert(opt_tok.is_None());
            inst.tr_have_gen(false, &opt_tok);
            inst.tr_remove_gen(false, opt_tok);
        }

        fn test_inst1_fail() {
            #[proof] let (inst, token_f) = Y::Instance::init_false();
            assert(token_f.is_None());

            #[proof] let opt_tok = inst.tr_add_gen(false);
            assert(opt_tok.is_None());
            inst.tr_have_gen(true, &opt_tok);   // FAILS
        }

        fn test_inst2() {
            #[proof] let (inst, token_t) = Y::Instance::init_true();
            assert(token_t.is_Some());
            assert(equal(token_t.get_Some_0().instance, inst));
        }
    } => Err(e) => assert_fails(e, 3)
}

test_verify_one_file! {
    #[test] persistent_bool_codegen IMPORTS.to_string() + code_str! {
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
                    add b += true;
                }
            }

            transition!{
                tr_have() {
                    have b >= true;
                }
            }

            transition!{
                tr_add_gen(x: bool) {
                    add b += (x);
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
            post.b === true
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            post.b === true
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.b === true && post.b === true
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b === true && post.b === true
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State, x: bool) -> bool {
            (post.b === (pre.b || x))
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
            (post.b === (pre.b || x))
        }

        spec fn rel_tr5(pre: Y::State, post: Y::State, x: bool) -> bool {
            (x ==> pre.b) && (post.b === pre.b)
        }

        spec fn rel_tr5_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
            (x ==> pre.b) && (post.b === pre.b)
        }

        }

        #[proof]
        fn correct_tr(pre: Y::State, post: Y::State, x: bool) {
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

        fn test_inst1() {
            #[proof] let (inst, token_f) = Y::Instance::init_false();
            assert(token_f.is_None());

            #[proof] let tok = inst.tr_add();
            assert(equal(tok.instance, inst));
            inst.tr_have(&tok);

            #[proof] let tok1 = tok.clone();
            assert(equal(tok, tok1));

            #[proof] let opt_tok = inst.tr_add_gen(true);
            assert(opt_tok.is_Some());
            assert(equal(opt_tok.get_Some_0().instance, inst));
            inst.tr_have_gen(true, &opt_tok);

            #[proof] let opt_tok = inst.tr_add_gen(false);
            assert(opt_tok.is_None());
            inst.tr_have_gen(false, &opt_tok);
        }

        fn test_inst1_fail() {
            #[proof] let (inst, token_f) = Y::Instance::init_false();
            assert(token_f.is_None());

            #[proof] let opt_tok = inst.tr_add_gen(false);
            assert(opt_tok.is_None());
            inst.tr_have_gen(true, &opt_tok);   // FAILS
        }

        fn test_inst2() {
            #[proof] let (inst, token_t) = Y::Instance::init_true();
            assert(token_t.is_Some());
            assert(equal(token_t.get_Some_0().instance, inst));
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file! {
    #[test] persistent_count_codegen IMPORTS.to_string() + code_str! {
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
                    add c += (2);
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

        }

        fn test_inst() {
            #[proof] let (inst, t1) = Y::Instance::initialize();
            assert(t1.value == spec_literal_nat("9"));

            #[proof] let t2 = t1.weaken(spec_literal_nat("2"));

            inst.tr_have(&t2);

            #[proof] let t4 = inst.tr_add();
            assert(t4.value == spec_literal_nat("2"));

            #[proof] let t2_clone = t2.clone();
            assert(equal(t2, t2_clone));
        }

        fn test_weaken_fail() {
            #[proof] let (inst, t1) = Y::Instance::initialize();
            #[proof] let t2 = t1.weaken(spec_literal_nat("800")); // FAILS
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file! {
    #[test] set_codegen IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(set)]
                pub b: Set<int>,
            }

            init!{
                initialize() {
                    init b = Set::empty().insert(19);
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
                    add b += (Set::empty().insert(6)); // FAILS
                }
            }

            transition!{
                tr_have_gen() {
                    have b >= (Set::empty().insert(6));
                }
            }

            transition!{
                tr_remove_gen() {
                    remove b -= (Set::empty().insert(6));
                }
            }
        }}

        verus!{

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            !pre.b.contains(5)
            ==> post.b === pre.b.insert(5)
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            !pre.b.contains(5)
            && post.b === pre.b.insert(5)
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && pre.b === post.b
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && pre.b === post.b
        }

        spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && post.b === pre.b.remove(5)
        }

        spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && post.b === pre.b.remove(5)
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            !pre.b.contains(6)
            ==> post.b === pre.b.union(Set::empty().insert(6))
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            !pre.b.contains(6)
            && post.b === pre.b.union(Set::empty().insert(6))
        }

        spec fn rel_tr5(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && pre.b === post.b
        }

        spec fn rel_tr5_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && pre.b === post.b
        }

        spec fn rel_tr6(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && post.b === pre.b.difference(Set::empty().insert(6))
        }

        spec fn rel_tr6_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && post.b === pre.b.difference(Set::empty().insert(6))
        }

        }

        #[proof]
        fn correct_tr(pre: Y::State, post: Y::State) {
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

        #[proof]
        fn test_inst1() {
            #[proof] let (inst, token_f) = Y::Instance::initialize();
            assert(Set::empty().insert(spec_literal_int("19")).contains(spec_literal_int("19")));
            assert(token_f.contains(Y![
                inst => b => spec_literal_int("19")
            ]));

            #[proof] let token1 = inst.tr_add();
            assert(equal(token1.instance, inst));
            assert(token1.value == spec_literal_int("5"));
            inst.tr_have(&token1);
            inst.tr_remove(token1);

            #[proof] let token_set = inst.tr_add_gen();
            assert(Set::empty().insert(spec_literal_int("6")).contains(spec_literal_int("6")));
            assert(token_set.contains(Y![
                inst => b => spec_literal_int("6")
            ]));
            inst.tr_have_gen(&token_set);
            inst.tr_remove_gen(token_set);
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] persistent_set_codegen IMPORTS.to_string() + code_str! {
        tokenized_state_machine!{ Y {
            fields {
                #[sharding(persistent_set)]
                pub b: Set<int>,
            }

            init!{
                initialize() {
                    init b = Set::empty().insert(19);
                }
            }

            transition!{
                tr_add() {
                    add b += set { 5 };
                }
            }

            transition!{
                tr_have() {
                    have b >= set { 5 };
                }
            }

            transition!{
                tr_add_gen() {
                    add b += (Set::empty().insert(6));
                }
            }

            transition!{
                tr_have_gen() {
                    have b >= (Set::empty().insert(6));
                }
            }
        }}

        verus!{

        spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
            post.b === pre.b.insert(5)
        }

        spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
            post.b === pre.b.insert(5)
        }

        spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && pre.b === post.b
        }

        spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(5)
            && pre.b === post.b
        }

        spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
            post.b === pre.b.union(Set::empty().insert(6))
        }

        spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
            post.b === pre.b.union(Set::empty().insert(6))
        }

        spec fn rel_tr5(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && pre.b === post.b
        }

        spec fn rel_tr5_strong(pre: Y::State, post: Y::State) -> bool {
            pre.b.contains(6)
            && pre.b === post.b
        }

        }

        #[proof]
        fn correct_tr(pre: Y::State, post: Y::State) {
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

        #[proof]
        fn test_inst1() {
            #[proof] let (inst, token_f) = Y::Instance::initialize();
            assert(Set::empty().insert(spec_literal_int("19")).contains(spec_literal_int("19")));
            assert(token_f.contains(Y![
                inst => b => spec_literal_int("19")
            ]));

            #[proof] let token1 = inst.tr_add();
            assert(equal(token1.instance, inst));
            assert(token1.value == spec_literal_int("5"));
            inst.tr_have(&token1);

            let token1_clone = token1.clone();
            assert(equal(token1_clone, token1));

            #[proof] let token_set = inst.tr_add_gen();
            assert(Set::empty().insert(spec_literal_int("6")).contains(spec_literal_int("6")));
            assert(token_set.contains(Y![
                inst => b => spec_literal_int("6")
            ]));
            inst.tr_have_gen(&token_set);
        }
    } => Ok(())
}
