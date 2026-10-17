//! Boolean ownership and individual readers remain independent under control flow.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::CountRA;
use vstd::resource::tsm_finite_multiset::finite_multiset_frag;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    Mixed {
        fields {
            #[sharding(bool)] pub writer:bool,
            #[sharding(multiset)] pub readers:Multiset<nat>,
            #[sharding(count)] pub completed:nat,
        }
        #[invariant] pub fn valid(&self)->bool { true }
        init! { initialize() {
            init writer=true;
            init readers=Multiset::singleton(7nat);
            init completed=0;
        } }
        transition! { finish(value:nat, record:bool) {
            remove readers -= {value};
            if record {
                add completed += (1);
            }
        } }
        transition! { release_writer() { remove writer -= true; } }
        #[inductive(initialize)] fn initialize_inductive(post:Self) {}
        #[inductive(finish)] fn finish_inductive(pre:Self,post:Self,value:nat,record:bool) {}
        #[inductive(release_writer)] fn release_inductive(pre:Self,post:Self) {}
    }
}

pub proof fn independent_owners() {
    let tracked all = Mixed::Protocol::initialize();
    let writer = Mixed::Fragment { writer: CountRA { count: 1 }, ..Mixed::Fragment::unit() };
    let reader = Mixed::Fragment {
        readers: finite_multiset_frag(Multiset::singleton(7nat)),
        ..Mixed::Fragment::unit()
    };
    reader.readers.op_unit();
    vstd::resource::tsm_finite_multiset::FiniteMultisetRA::commutative(
        writer.readers,
        reader.readers,
    );
    let tracked (writer, reader) = all.split(writer, reader);
    let tracked reader = Mixed::Protocol::finish(reader, 7nat, false);
    assert(reader.fragment().readers.at(7nat).count == 0);
    assert(writer.fragment().writer.count == 1);
    let tracked writer = Mixed::Protocol::release_writer(writer);
    assert(writer.fragment().writer.count == 0);
}

} // verus!
fn main() {}
