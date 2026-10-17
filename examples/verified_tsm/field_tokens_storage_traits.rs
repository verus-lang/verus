use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::pcell_maybe_uninit as cell;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm_context::Descriptor;
use vstd::resource::tsm_helpers::*;
use vstd::std_specs::option::OptionAdditionalFns;
verus! {

broadcast use {vstd::imap::group_imap_lemmas, vstd::iset::group_iset_lemmas};

type Perm<S> = cell::PointsTo<S>;

verified_tokenized_state_machine! {

    Store<#[verifier::reject_recursive_types] S> {
        fields {
            #[sharding(constant)] pub permission:Perm<S>,
            #[sharding(variable)] pub occupied:bool,
            #[sharding(variable)] pub spare:bool,
            #[sharding(storage_option)] pub storage:Option<Perm<S>>,
        }
        #[invariant] pub fn inv(&self)->bool {
            self.permission.is_init() && (if self.occupied {self.storage==Some(self.permission)}else{self.storage.is_none()})
        }
        init!{initialize(permission:Perm<S>){require(permission.is_init());init permission=permission;init occupied=false;init spare=false;init storage=None;}}
        transition!{deposit(x:Perm<S>){require(!pre.occupied);require(x==pre.permission);update occupied=true;update spare=pre.spare;deposit storage += Some(x);}}
        transition!{withdraw(){require(pre.occupied);update occupied=false;update spare=pre.spare;withdraw storage -= Some(let x);assert(x==pre.permission);}}
        #[inductive(initialize)] fn initialize_inductive(post:Self,permission:Perm<S>){}
        #[inductive(deposit)] fn deposit_inductive(pre:Self,post:Self,x:Perm<S>){}
        #[inductive(withdraw)] fn withdraw_inductive(pre:Self,post:Self){}
    }
}

fn assert_send<T: Send>() {
}

fn assert_sync<T: Sync>() {
}

fn main() {
    assert_send::<Store::occupied<u64>>();
    assert_sync::<Store::occupied<u64>>();
    assert_send::<Store::spare<u64>>();
    assert_sync::<Store::spare<u64>>();
    let (pcell, Tracked(permission)) = cell::PCell::new(7u64);
    let tracked (Tracked(instance), Tracked(mut field), Tracked(mut spare)) = Store::Instance::<
        u64,
    >::initialize(permission, None);
    let tracked instance = instance.clone();
    proof {
        instance.deposit(permission, &mut field, &mut spare, permission);
    }
    let tracked mut returned;
    proof {
        returned = instance.withdraw(&mut field, &mut spare);
        assert(returned == instance.permission());
    }
    let value = pcell.take(Tracked(&mut returned));
    assert(value == 7);
}

} // verus!
