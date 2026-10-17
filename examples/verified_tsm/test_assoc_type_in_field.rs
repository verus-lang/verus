use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

pub trait Tr {
    type AssocType;
}

verified_tokenized_state_machine!{  X<T: Tr> {
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

pub struct A {}

pub struct B {
    i: int,
}

impl Tr for A {
    type AssocType = B;
}

proof fn test() {
    let tracked (Tracked(inst), Tracked(mut map_token)) = X::Instance::<A>::initialize(
        imap![3 => B { i: 9 }],
    );
    assert(map_token.instance_id() == inst.id());
    assert(map_token.map() =~= imap![3 => B { i: 9 }]);
    let tracked r = map_token.remove(3);
    assert(r.key() == 3);
    assert(r.value() == B { i: 9 });
    assert(r.instance_id() == inst.id());

    let j = X::m_map::<A>::empty(inst.id());
    assert(j.map() =~= imap![]);
}

fn main() {
}

} // verus!
