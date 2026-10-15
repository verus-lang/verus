#![allow(non_snake_case)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::simple_pptr::*;
verus! {

pub enum Stage {
    Fresh,
    Acquire,
    Release,
}

verified_tokenized_state_machine!( #[verified_local_ready(deposit_perm_a,deposit_perm_b,acquire,release,withdraw_a,withdraw_b)] DemoToks<before,frame,key> {
    fields {
        // Remember the pointer addresses we're manipulating
        #[sharding(constant)]
        pub ptr_a: PPtr<usize>,

        #[sharding(constant)]
        pub ptr_b: PPtr<usize>,

        // Storage for the permissions that control access to the pointer locations
        #[sharding(storage_option)]
        pub perm_a: Option<PointsTo<usize>>,

        #[sharding(storage_option)]
        pub perm_b: Option<PointsTo<usize>>,

        // Permission to deposit a pointer permission
        #[sharding(bool)]
        pub can_deposit_a: bool,

        #[sharding(bool)]
        pub can_deposit_b: bool,

        // Allows a thread to retrieve the pointer permission at the end
        #[sharding(bool)]
        pub own_a: bool,

        #[sharding(bool)]
        pub own_b: bool,

        // The permission for `a` is inside the state machine
        #[sharding(variable)]
        pub deposited_a: bool,

        #[sharding(variable)]
        pub deposited_b: bool,

        // Overall state of the state machine
        #[sharding(variable)]
        pub stage: Stage,

        // We've swapped the values
        #[sharding(persistent_bool)]
        pub swapped: bool,

        // Could be used to allow cancelation of the barrier
        #[sharding(persistent_bool)]
        pub cancel: bool,
    }

    init! {
        new(a: PPtr<usize>, b: PPtr<usize>) {
            init ptr_a = a;
            init ptr_b = b;
            init perm_a = None;
            init perm_b = None;
            init can_deposit_a = true;
            init can_deposit_b = true;
            init own_a = true;
            init own_b = true;
            init deposited_a = false;
            init deposited_b = false;
            init stage = Stage::Fresh;
            init swapped = false;
            init cancel = false;
        }
    }
    #[inductive(new)]
    fn new_inductive(post: Self, a: PPtr<usize>, b: PPtr<usize>) {
    }

    transition! {
        deposit_perm_a(pt_a: PointsTo<usize>) {
            require (pt_a.pptr() == pre.ptr_a && pt_a.is_init() && pt_a.value() == 43);
            require (!pre.deposited_a);
            remove can_deposit_a -= true;
            deposit perm_a += Some(pt_a);
            update deposited_a = true;
        }
    }
    #[inductive(deposit_perm_a)]
    fn deposit_perm_a_inductive(pre:Self, post: Self, pt_a: PointsTo<usize>) {
    }

    transition! {
        deposit_perm_b(pt_b: PointsTo<usize>) {
            require (pt_b.pptr() == pre.ptr_b && pt_b.is_init() && pt_b.value() == 1);
            require (!pre.deposited_b);
            remove can_deposit_b -= true;
            deposit perm_b += Some(pt_b);
            update deposited_b = true;
        }
    }
    #[inductive(deposit_perm_b)]
    fn deposit_perm_b_inductive(pre:Self, post: Self, pt_b: PointsTo<usize>) {
    }

    transition! {
        acquire() {
            require (pre.deposited_a && pre.deposited_b);
            require (pre.stage is Fresh);
            withdraw perm_a -= Some(let t_a);
            withdraw perm_b -= Some(let t_b);
            update deposited_a = false;
            update deposited_b = false;
            update stage = Stage::Acquire;
            assert(t_a.pptr() == pre.ptr_a && t_a.is_init() && t_a.value() == 43);
            assert(t_b.pptr() == pre.ptr_b && t_b.is_init() && t_b.value() == 1);
        }
    }
    #[inductive(acquire)]
    fn acquire_inductive(pre:Self, post: Self) {
    }

    transition! {
        release(pt_a: PointsTo<usize>, pt_b: PointsTo<usize>) {
            require (pre.stage is Acquire);
            require (pt_a.pptr() == pre.ptr_a && pt_a.is_init() && pt_a.value() == 1);
            require (pt_b.pptr() == pre.ptr_b && pt_b.is_init() && pt_b.value() == 43);

            deposit perm_a += Some(pt_a);
            deposit perm_b += Some(pt_b);

            add swapped (union)= true;
            update stage = Stage::Release;
        }
    }
    #[inductive(release)]
    fn release_inductive(pre:Self, post: Self, pt_a: PointsTo<usize>, pt_b: PointsTo<usize>) {
    }

    transition! {
        withdraw_a() {
            remove own_a -= true;
            have swapped >= (true);
            withdraw perm_a -= Some(let p);
            assert(p.pptr() == pre.ptr_a && p.is_init() && p.value() == 1);
        }
    }
    #[inductive(withdraw_a)]
    fn withdraw_a_inductive(pre:Self, post: Self) {
    }

    transition! {
        withdraw_b() {
            remove own_b -= true;
            have swapped >= (true);
            withdraw perm_b -= Some(let p);
            assert(p.pptr() == pre.ptr_b && p.is_init() && p.value() == 43);
        }
    }
    #[inductive(withdraw_b)]
    fn withdraw_b_inductive(pre:Self, post: Self) {
    }

    #[invariant]
    pub fn deposit_rules(&self) -> bool {
        &&& !self.deposited_a && self.can_deposit_a ==> self.perm_a is None
        &&& !self.deposited_b && self.can_deposit_b ==> self.perm_b is None
        &&& self.deposited_a ==> self.perm_a is Some
        &&& self.deposited_b ==> self.perm_b is Some
    }

    #[invariant]
    pub fn can_deposit(&self) -> bool {
        &&& self.can_deposit_a ==> self.stage is Fresh
        &&& self.can_deposit_b ==> self.stage is Fresh
        &&& self.deposited_a ==> !self.can_deposit_a
        &&& self.deposited_b ==> !self.can_deposit_b
    }

    #[invariant]
    pub fn storage(&self) -> bool {
        &&& self.perm_a matches Some(p) ==> p.pptr() == self.ptr_a && p.is_init() && (self.stage is Fresh ==> p.value() == 43) && (self.stage is Release ==> p.value() == 1)
        &&& self.perm_b matches Some(p) ==> p.pptr() == self.ptr_b && p.is_init() && (self.stage is Fresh ==> p.value() == 1) && (self.stage is Release ==> p.value() == 43)
    }

    #[invariant]
    pub fn stages(&self) -> bool {
        use Stage::*;
        match self.stage {
            Fresh => self.own_a && self.own_b && !self.swapped,
            Acquire => self.own_a && self.own_b && !self.deposited_a && !self.deposited_b && !self.swapped && self.perm_a is None && self.perm_b is None,
            Release => self.swapped && !self.deposited_a && !self.deposited_b ,
        }
    }

    #[invariant]
    pub fn swapped(&self) -> bool {
        &&& self.swapped ==> self.stage is Release
    }

    #[invariant]
    pub fn ownership(&self) -> bool {
        &&& self.own_a && self.swapped ==> self.perm_a is Some
        &&& self.own_b && self.swapped ==> self.perm_b is Some
    }

    #[invariant]
    pub fn never_cancel(&self) -> bool {
        !self.cancel
    }


    property! {
        cannot_cancel() {
            have cancel >= (true);
            assert(false);
        }
    }
});

fn main() {
    let (a, Tracked(mut a_points_to)) = PPtr::<usize>::new(43);
    let (b, Tracked(mut b_points_to)) = PPtr::<usize>::new(1);
    let tracked (
        Tracked(instance),
        Tracked(can_deposit_a),
        Tracked(can_deposit_b),
        Tracked(own_a),
        Tracked(own_b),
        Tracked(mut deposited_a),
        Tracked(mut deposited_b),
        Tracked(mut stage),
        Tracked(_swapped),
        Tracked(_cancel),
    ) = DemoToks::Instance::<usize, usize, usize>::new(a, b, None, None);
    proof {
        instance.deposit_perm_a(
            a_points_to,
            a_points_to,
            can_deposit_a.tracked_unwrap(),
            &mut deposited_a,
        );
        instance.deposit_perm_b(
            b_points_to,
            b_points_to,
            can_deposit_b.tracked_unwrap(),
            &mut deposited_b,
        );
        let tracked (Tracked(perm_a), Tracked(perm_b)) = instance.acquire(
            &mut deposited_a,
            &mut deposited_b,
            &mut stage,
        );
        a_points_to = perm_a;
        b_points_to = perm_b;
    }
    let tmp = a.read(Tracked(&a_points_to));
    a.write(Tracked(&mut a_points_to), b.read(Tracked(&b_points_to)));
    b.write(Tracked(&mut b_points_to), tmp);
    let tracked mut swapped;
    let tracked swapped_b;
    proof {
        swapped = instance.release(a_points_to, b_points_to, a_points_to, b_points_to, &mut stage);
        swapped_b = swapped.clone();
        a_points_to = instance.withdraw_a(own_a.tracked_unwrap(), &swapped);
        b_points_to = instance.withdraw_b(own_b.tracked_unwrap(), &swapped_b);
        assert(a_points_to.pptr() == a && a_points_to.value() == 1);
        assert(b_points_to.pptr() == b && b_points_to.value() == 43);
        assert(stage.value() is Release);
    }
    let observed_a = a.read(Tracked(&a_points_to));
    let observed_b = b.read(Tracked(&b_points_to));
    assert(observed_a == 1);
    assert(observed_b == 43);
    let a_value = a.into_inner(Tracked(a_points_to));
    let b_value = b.into_inner(Tracked(b_points_to));
    assert(a_value == 1);
    assert(b_value == 43);
}

} // verus!
