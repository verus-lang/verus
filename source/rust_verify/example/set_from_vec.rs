use vstd::prelude::*;

verus! {

struct VecSet {
    vt: Vec<u64>,
}

impl VecSet {
    pub closed spec fn view(&self) -> Set<u64> {
        self.vt@.to_set()
    }

    pub fn new() -> (s: Self)
        ensures
            s@ =~= Set::<u64>::empty(),
    {
        VecSet { vt: Vec::new() }
    }

    pub fn insert(&mut self, v: u64)
        ensures
            self@ =~= old(self)@.insert(v),
    {
        self.vt.push(v);
        proof {
            vstd::seq_lib::lemma_seq_properties::<u64>();
        }
        assert(self.vt@ =~= old(self).vt@ + seq![v]);
    }

    pub fn contains(&self, v: u64) -> (contained: bool)
        ensures
            contained == self@.contains(v),
    {
        for i in iter: 0..self.vt.len()
            invariant
                forall|j: nat| j < i ==> self.vt[j as int] != v,
        {
            if self.vt[i] == v {
                return true;
            }
        }
        false
    }
}

fn main() {
    let mut vs: VecSet = VecSet::new();
    assert(vs@ =~= set![]);
    vs.insert(3);
    vs.insert(5);
    let contains2 = vs.contains(2);
    assert(!contains2);
    assert(vs@ =~= set![3, 5]);
}

} // verus!
