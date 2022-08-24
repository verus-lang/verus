#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use pervasive::multiset::*;
use pervasive::option::*;
use pervasive::ptr::*;
use pervasive::cell::*;
use pervasive::seq::*;
use pervasive::map::*;
use pervasive::vec::*;
use pervasive::modes::*;
use pervasive::invariant::*;

use state_machines_macros::tokenized_state_machine;

tokenized_state_machine!{InternSystem<T> {
    fields {
        #[sharding(variable)]
        pub auth: Seq<T>,

        #[sharding(persistent_map)]
        pub frag: Map<nat, T>,
    }

    init!{
        empty() {
            init auth = Seq::empty();
            init frag = Map::empty();
        }
    }

    transition!{
        insert(val: T) {
            require(forall |i: int| 0 <= i && i < pre.auth.len() ==> pre.auth.index(i) !== val);
            update auth = pre.auth.push(val);
        }
    }

    transition!{
        get_frag(idx: nat) {
            require(0 <= idx && idx < pre.auth.len());
            let val = pre.auth.index(idx);
            add frag (union)= [idx => val];
        }
    }

    property!{
        get_value(i: nat) {
            have frag >= [i => let val];
            assert(i < pre.auth.len() && pre.auth.index(i) === val);
        }
    }

    property!{
        compute_equality(idx1: nat, val1: T, idx2: nat, val2: T) {
            have frag >= [idx1 => val1];
            have frag >= [idx2 => val2];
            assert((idx1 == idx2) == equal(val1, val2));
        }
    }

    #[invariant]
    pub fn agreement(&self) -> bool {
        forall |k| #[trigger] self.frag.dom().contains(k) ==>
            0 <= k && k < self.auth.len()
                && self.auth.index(k) === self.frag.index(k)
    }

    #[invariant]
    pub fn distinct(&self) -> bool {
        forall |i: int, j: int|
            0 <= i && i < self.auth.len() &&
            0 <= j && j < self.auth.len() &&
            i != j
            ==>
            self.auth.index(i) !== self.auth.index(j)
    }

    #[inductive(empty)]
    fn empty_inductive(post: Self) { }
   
    #[inductive(insert)]
    fn insert_inductive(pre: Self, post: Self, val: T) {
        /*assert_forall_by(|k| {
            requires(post.frag.dom().contains(k));
            ensures(0 <= k && k < post.auth.len()
                && equal(post.auth.index(k), post.frag.index(k)));

            assert(pre.frag.dom().contains(k));
            assert(k < pre.auth.len());
            assert(k < post.auth.len());
            assert(equal(post.auth.index(k), post.frag.index(k)));
        })*/
        /*assert_forall_by(|i: int, j: int| {
            requires(
                0 <= i && i < post.auth.len() &&
                0 <= j && j < post.auth.len() &&
                i != j
            );
            ensures(!equal(post.auth.index(i), post.auth.index(j)));

            if i == post.auth.len() as int - 1 {
                if j == post.auth.len() as int - 1 {
                    assert(!equal(post.auth.index(i), post.auth.index(j)));
                } else {
                    assert(!equal(post.auth.index(i), post.auth.index(j)));
                }
            } else {
                if j == post.auth.len() as int - 1 {
                    assert(equal(post.auth.index(pre.auth.len()), val));
                    assert(equal(post.auth.index(j), val));
                    assert(equal(post.auth.index(i), pre.auth.index(i)));
                    assert(!equal(pre.auth.index(i), val));
                    assert(!equal(post.auth.index(i), post.auth.index(j)));
                } else {
                    assert(!equal(post.auth.index(i), post.auth.index(j)));
                }
            }
        })*/
    }
   
    #[inductive(get_frag)]
    fn get_frag_inductive(pre: Self, post: Self, idx: nat) { }
}}

// We want the following properties:
//
// There is an `Interner` object. You need access to this object in order to:
//
//  - intern a new string and get an ID for it
//  - look up the original string for a given ID
//
// However, WITHOUT access to the object, you should be able to:
//
// - use `.view()` to get the original string (in spec-code)
//   so that you could reason about the string as if you just had the original
// - evaluate string equality by comparing the IDs

struct Interner<T> {
    #[proof] inst: InternSystem::Instance<T>,
    #[proof] auth: InternSystem::auth<T>,
    store: Vec<T>
}

struct Interned<T> {
    #[proof] inst: InternSystem::Instance<T>,
    #[proof] frag: InternSystem::frag<T>,
    id: usize,
}

verus!{

#[verifier(external_body)]
fn compute_eq<T>(a: &T, b: &T) -> (res: bool)
  ensures res == equal(a, b)
{
  unimplemented!();
}

}

impl<T> Interner<T> {
    verus!{
    spec fn wf(&self, inst: InternSystem::Instance<T>) -> bool {
        &&& self.inst === inst
        &&& self.auth@.instance === inst
        &&& self.auth@.value === self.store@
    }
    }

    fn new() -> (Self, Trk<InternSystem::Instance<T>>) {
        ensures(|x: (Self, Trk<InternSystem::Instance<T>>)| {
            #[spec] let s = x.0;
            #[spec] let inst = x.1.0;
            s.wf(inst)
        });

        #[proof] let (Trk(inst), Trk(auth), Trk(_f)) = InternSystem::Instance::empty();
        let store = Vec::new();

        (Interner { inst: inst.clone(), auth, store }, Trk(inst))
    }

    fn insert(&mut self, #[spec] inst: InternSystem::Instance<T>, val: T) -> Interned<T> {
        requires(old(self).wf(inst));
        ensures(|st: Interned<T>| self.wf(inst) && st.wf(inst) && equal(st.view(), val));

        let idx: usize = 0;
        while idx < self.store.len() {
            invariant([
                0 <= idx && idx <= self.store.view().len(),
                self.wf(inst),
            ]);

            let eq = compute_eq(&val, self.store.index(idx));
            if eq {
                #[proof] let frag = self.inst.get_frag(idx, &self.auth);
                return Interned {
                    inst: self.inst.clone(),
                    frag,
                    id: idx,
                };
            }
        }

        let idx: usize = self.store.len();
        self.store.push(val);

        self.inst.insert(val, &mut self.auth);

        #[proof] let frag = self.inst.get_frag(idx, &self.auth);
        Interned {
            inst: self.inst.clone(),
            frag,
            id: idx,
        }
    }

    fn get<'a>(&'a self, interned: &Interned<T>,
        #[spec] inst: InternSystem::Instance<T>) -> &'a T
    {
        requires(self.wf(inst) && interned.wf(inst));
        ensures(|st| equal(st, interned.view()));

        self.inst.get_value(interned.id as nat, &self.auth, &interned.frag);

        self.store.index(interned.id)
    }
}

impl<T> Interned<T> {
    verus!{
    spec fn wf(&self, inst: InternSystem::Instance<T>) -> bool {
        &&& self.frag@.instance === inst
        &&& inst === self.inst
        &&& self.id as int == self.frag@.key
    }

    spec fn view(&self) -> T {
        self.frag@.value
    }
    }

    fn clone(&self, #[spec] inst: InternSystem::Instance<T>) -> Self {
        requires(self.wf(inst));
        ensures(|s: Self| s.wf(inst) && equal(s.view(), self.view()));

        Interned {
            inst: self.inst.clone(),
            frag: self.frag.clone(),
            id: self.id,
        }
    }

    fn cmp_eq(&self, other: &Self, #[spec] inst: InternSystem::Instance<T>) -> bool {
        requires(self.wf(inst) && other.wf(inst));
        ensures(|b: bool| b == equal(self.view(), other.view()));

        self.inst.compute_equality(
            self.frag.view().key,
            self.frag.view().value,
            other.frag.view().key,
            other.frag.view().value,
            &self.frag, &other.frag);

        self.id == other.id
    }
}



fn main() {
    let (mut interner, Trk(inst)) = Interner::<u64>::new();

    let s1 = interner.insert(inst, 1);
    let s2 = interner.insert(inst, 2);
    let s3 = interner.insert(inst, 3);

    let s1_other = interner.insert(inst, 1);

    let b1 = s1.cmp_eq(&s1_other, inst);
    assert(b1);

    let b2 = s1.cmp_eq(&s2, inst);
    assert(!b2);

    let t1 = s1.clone(inst);
    let get1 = *interner.get(&t1, inst);
    assert(get1 == 1);

    let t2 = s2.clone(inst);
    let get2 = *interner.get(&t2, inst);
    assert(get1 == 1);

}


