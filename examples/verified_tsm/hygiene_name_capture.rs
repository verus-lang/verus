// rust_verify/tests/example.rs expect-warnings
//! Regression tests for hygiene (name capture): the checked macros generate
//! helpers, binders and type parameters named `__tsm_*`; a user identifier with
//! such a name (type parameter, transition parameter, closure binder, raw
//! identifier) must neither be captured by nor clash with the generated code.
//! One representative per generator:
//! the model (`take_step`, aggregate relations), the generic interface
//! (initializers, parameters, closures, option operands) and nondeterministic
//! (`birds_eye`) tokenizing. Intentionally non-camel-case names cause warnings.

// ----------------------------------------------------------------------------
pub mod model_take_step {
    use verus_state_machines_macros::verified_state_machine_model;
    use vstd::prelude::*;
    verus! {

    verified_state_machine_model!{ G<__tsm_checked_take_step_initialize> {
        fields {pub value: __tsm_checked_take_step_initialize, pub n: int}
        init!{ initialize(value: __tsm_checked_take_step_initialize) {init value = value; init n = 0;} }
        transition!{ set(value: __tsm_checked_take_step_initialize, r#__tsm_checked_take_step_set: int) {
            require r#__tsm_checked_take_step_set >= 0;
            let n: int = r#__tsm_checked_take_step_set;
            update value = value; update n = n;
        } }
        readonly!{ observe() {assert pre.n >= 0;} }
        #[invariant] pub fn nonnegative(&self)->bool {self.n>=0}
        #[inductive(initialize)] fn initialize_inductive(post: Self, value: __tsm_checked_take_step_initialize) {}
        #[inductive(set)] fn set_inductive(pre: Self, post: Self, value: __tsm_checked_take_step_initialize, r#__tsm_checked_take_step_set: int) {}
    }}

    pub fn run() {
        proof {
            let a = G::take_step::initialize::<int>(5int);
            let b = G::take_step::set(a, 7int, 3int);
            assert(b.value == 7 && b.n == 3 && b.invariant());
            let c = G::take_step::observe(b);
            assert(c == b && c.invariant());
        }
    }

    } // verus!
}

// ----------------------------------------------------------------------------
pub mod model_aggregate {
    use verus_state_machines_macros::verified_state_machine_model;
    use vstd::prelude::*;

    verus! {

    verified_state_machine_model!{ X {
        fields {
            pub number: int,
        }
        init!{
            initialize() {
                init number = 0;
            }
        }
        transition!{
            add(r#__tsm_aggregate_pre: int) {
                update number = pre.number + 2*r#__tsm_aggregate_pre;
            }
        }
        transition!{
            sub(n: int) {
                update number = pre.number - 2*n;
            }
        }
    }}

    proof fn test(s: X::Step)
        requires
            s.is_add(),
    {
        match s {
            X::Step::add(_) => assert(true),
            X::Step::sub(_) => assert(false),
            _ => {},
        }
    }

    proof fn classify() {
        let pre = X::State { number: 0int };
        let post = X::State { number: 4int };
        X::show::initialize(pre);
        X::show::add(pre, post, 2int);
        assert(X::State::init(pre));
        assert(X::State::next(pre, post));
        reveal(X::State::next_strong);
        reveal(X::State::next_strong_by);
        assert(X::State::next_strong_by(pre, post, X::Step::add(2int)));
        assert(X::State::next_strong(pre, post));
    }

    pub fn run() {
    }

    } // verus!
}

// ----------------------------------------------------------------------------
pub mod init_names {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    use vstd::thread::*;
    verus! {

    verified_tokenized_state_machine!(

        Generic<T> {
            fields { #[sharding(variable)] pub item:T, }
            init!{initialize(item:T){init item=item;}}
            transition!{replace(__tsm_field_owned_0:T){update item=__tsm_field_owned_0;}}
            property!{observed(__tsm_field_state_0:T){require(pre.item==__tsm_field_state_0);assert(pre.item==__tsm_field_state_0);}}
            #[inductive(initialize)] fn initialize_inductive(post:Self,item:T){}
            #[inductive(replace)] fn replace_inductive(pre:Self,post:Self,__tsm_field_owned_0:T){}
        }
    );

    proof fn update_generic<T>(
        tracked instance: &Generic::Instance<T>,
        tracked token: &mut Generic::item<T>,
        owned: T,
    )
        requires
            token.instance_id() == instance.id(),
        ensures
            final(token).instance_id() == instance.id(),
            final(token).value() == owned,
    {
        instance.replace(owned, token);
    }

    pub fn run() {
        let tracked (Tracked(instance), Tracked(item)) = Generic::Instance::<u64>::initialize(7);
        let ghost location = instance.id();
        let tracked instance = instance.clone();
        let handle = spawn(
            move || -> (result: Tracked<Generic::item<u64>>)
                ensures
                    result@.instance_id() == location,
                    result@.value() == 9,
                {
                    let tracked mut item = item;
                    proof {
                        update_generic(&instance, &mut item, 9);
                        instance.observed(9, &item);
                    }
                    Tracked(item)
                },
        );
        match handle.join() {
            Ok(token) => {
                proof {
                    assert(token@.value() == 9);
                }
            },
            Err(_) => {},
        }
    }

    } // verus!
}

// ----------------------------------------------------------------------------
pub mod nested_closure {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    verus! {

    verified_tokenized_state_machine! {
         Constant {
            fields {
                #[sharding(constant)] pub limit: int,
                #[sharding(variable)] pub value: int,
            }
            #[invariant] pub fn inv(&self) -> bool { self.value <= self.limit }
            init! { initialize(limit: int) {
                require limit >= 0;
                init limit = limit;
                init value = 0;
            } }
            transition! { set(value: int) {
                require value <= pre.limit;
                update value = if ISet::new(|__tsm_field_argument_value_0:int| ISet::new(|__tsm_field_argument_value_1:int| __tsm_field_argument_value_1 == pre.value).contains(__tsm_field_argument_value_0)).contains(value) { value } else { value };
            } }
            #[inductive(initialize)] fn initialize_inductive(post:Self, limit:int) {}
            #[inductive(set)] fn set_inductive(pre:Self, post:Self, value:int) {}
        }
    }

    pub fn run() {
        proof {
            let tracked (Tracked(instance), Tracked(mut value)) = Constant::Instance::initialize(10);
            let tracked constant = instance.clone();
            instance.set(9, &mut value);
            assert(constant.limit() == 10);
            assert(value.value() == 9);
            constant.set(4, &mut value);
            assert(value.value() == 4);
        }
    }

    } // verus!
}

// ----------------------------------------------------------------------------
pub mod optional_names {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    verus! {

    verified_tokenized_state_machine!{X{
    fields{#[sharding(option)]pub c:Option<int>,}
    init!{new(){init c=Some(7);}}
    transition!{observe(source:int){have c >=Some(source);}}
    transition!{consume(__tsm_optional_typed:int){remove c -=Some(__tsm_optional_typed);}}
    transition!{neutral(value:Option<int>){remove c -=(value);}}
    }
    }

    pub fn run() {
        proof {
            let tracked (Tracked(inst), Tracked(c)) = X::Instance::new();
            let tracked c = c.tracked_unwrap();
            inst.observe(7, &c);
            inst.consume(7, c);
            inst.neutral(None, None);
        }
    }

    } // verus!
}

// ----------------------------------------------------------------------------
pub mod nondet_tokenizing {
    use verus_state_machines_macros::verified_tokenized_state_machine;
    use vstd::prelude::*;
    verified_tokenized_state_machine! {  Z<r#__tsm_nt_before> {
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

    verus! {

    proof fn go() {
        let tracked (Tracked(instance), Tracked(mut v1), Tracked(v2)) = Z::Instance::<()>::initialize();
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
        assert(equal(v1.value(), birds_eye_nt + instance.c() + old_v1_value - birds_eye_v2));

        let old_v1_value = v1.value();
        let birds_eye_nt = instance.tr3(&mut v1, &v2);
        assert(equal(v1.instance_id(), instance.id()));
        assert(equal(v1.value(), birds_eye_nt + instance.c() + old_v1_value + 3 * v2.value()));
    }

    } // verus!
}

fn main() {
    model_take_step::run();
    model_aggregate::run();
    init_names::run();
    nested_closure::run();
    optional_names::run();
}
