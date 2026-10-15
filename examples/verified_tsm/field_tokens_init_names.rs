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

fn main() {
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
