//! Borrowing a reader permits creating a new reader while retaining the old one.
//! Removal still requires an owned reader, alongside the exclusive total token.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_finite_multiset::finite_multiset_frag;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    SharedPool<T> {
        fields {
            #[sharding(variable)] pub total:nat,
            #[sharding(multiset)] pub readers:Multiset<T>,
        }
        #[invariant] pub fn total_matches_readers(&self)->bool { self.total == self.readers.len() }
        init! { initialize(value:T) { init total=1; init readers=Multiset::singleton(value); } }
        transition! { clone_reader(value:T) {
            have readers >= {value};
            add readers += {value};
            update total = pre.total + 1;
        } }
        transition! { consume_reader(value:T) {
            require pre.total >= 2;
            remove readers -= {value};
            update total = (pre.total - 1) as nat;
        } }
        #[inductive(initialize)] fn initialize_inductive(post:Self,value:T) {}
        #[inductive(clone_reader)] fn clone_inductive(pre:Self,post:Self,value:T) {}
        #[inductive(consume_reader)] fn consume_inductive(pre:Self,post:Self,value:T) {}
    }
}

pub proof fn shared_reader_demo<T>(value: T) {
    use vstd::resource::exclusive::ExclusiveRA;
    let tracked all = SharedPool::Protocol::<T>::initialize(value);
    let counter = SharedPool::Fragment::<T> {
        total: Some(ExclusiveRA::Exclusive(1nat)),
        readers: finite_multiset_frag(Multiset::empty()),
        ..SharedPool::Fragment::unit()
    };
    let reader = SharedPool::Fragment::<T> {
        total: None,
        readers: finite_multiset_frag(Multiset::singleton(value)),
        ..SharedPool::Fragment::unit()
    };
    reader.readers.op_unit();
    vstd::resource::tsm_finite_multiset::FiniteMultisetRA::commutative(
        counter.readers,
        reader.readers,
    );
    let tracked (counter, reader) = all.split(counter, reader);
    let tracked cloned = SharedPool::Protocol::<T>::clone_reader_with_shared(
        counter,
        &reader,
        value,
    );
    assert(cloned.fragment().readers.at(value).count == 1);
    assert(reader.fragment().readers.at(value).count == 1);
    let tracked consumed = SharedPool::Protocol::<T>::consume_reader(cloned, value);
    assert(consumed.fragment().total->Some_0->Exclusive_0 == 1);
    assert(consumed.fragment().readers.at(value).count == 0);
    assert(reader.fragment().readers.at(value).count == 1);
}

} // verus!
fn main() {}
