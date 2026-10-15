//! Ordered ownership tracks local rights across lexical scopes and branches.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::CountRA;

verus! {

verified_tokenized_state_machine!(
    #[verified_raw_tokens]
Ordered {
    fields {
        #[sharding(variable)] pub phase: nat,
        #[sharding(count)] pub count: nat,
    }
    #[invariant]
    pub fn count_matches_phase(self) -> bool { self.count == self.phase }
    init! { initialize() { init phase = 10; init count = 10; } }
    transition! {
        remove_then_have() {
            let amount: nat = 1;
            remove count -= (amount);
            have count >= (2);
            update phase = (pre.phase - amount) as nat;
        }
    }
    transition! {
        branch_then_have(remove_one: bool) {
            if remove_one {
                remove count -= (1);
                update phase = (pre.phase - 1) as nat;
            }
            have count >= (2);
        }
    }
    transition! {
        match_then_have(branch: Option<nat>) {
            match branch {
                Some(amount) => {
                    remove count -= (amount);
                    update phase = (pre.phase - amount) as nat;
                }
                None => {}
            }
            have count >= (2);
        }
    }
    #[inductive(initialize)] fn initialize_inductive(post: Self) {}
    #[inductive(remove_then_have)] fn remove_then_have_inductive(pre: Self, post: Self) {}
    #[inductive(branch_then_have)] fn branch_then_have_inductive(pre: Self, post: Self, remove_one: bool) {}
    #[inductive(match_then_have)] fn match_then_have_inductive(pre: Self, post: Self, branch: Option<nat>) {}
});

pub proof fn allocate_local(local_count: nat) -> (tracked out: Ordered::Token)
    requires
        local_count <= 10,
    ensures
        out.fragment() == (Ordered::Fragment {
            phase: Some(ExclusiveRA::Exclusive(10nat)),
            count: CountRA { count: local_count },
        }),
{
    let tracked token = Ordered::Protocol::initialize();
    let owner = Ordered::Fragment {
        phase: Some(ExclusiveRA::Exclusive(10nat)),
        count: CountRA { count: local_count },
    };
    let frame = Ordered::Fragment {
        count: CountRA { count: (10 - local_count) as nat },
        ..Ordered::Fragment::unit()
    };
    let tracked (owner, frame) = token.split(owner, frame);
    owner
}

proof fn ordered_scopes_and_branches() {
    let tracked token = Ordered::Protocol::remove_then_have(allocate_local(3nat));
    assert(token.fragment().count.count == 2);
    let tracked token = Ordered::Protocol::branch_then_have(allocate_local(3nat), true);
    assert(token.fragment().count.count == 2);
    let tracked token = Ordered::Protocol::branch_then_have(allocate_local(2nat), false);
    assert(token.fragment().count.count == 2);
    let tracked token = Ordered::Protocol::match_then_have(allocate_local(4nat), Some(2nat));
    assert(token.fragment().count.count == 2);
    let tracked token = Ordered::Protocol::match_then_have(allocate_local(2nat), None);
    assert(token.fragment().count.count == 2);
}

fn main() {
    proof {
        ordered_scopes_and_branches();
        pattern_binding_observes_owned_value();
        have_after_remove_includes_unchanged_borrow();
    }
}

} // verus!
verus! {

verified_tokenized_state_machine!(
    #[verified_raw_tokens]
ScopedPattern {
    fields { #[sharding(option)] pub item: Option<nat>, }
    init! { initialize() { init item = Some(4nat); } }
    transition! {
        replace_and_have(unused: nat) {
            remove item -= Some(let value);
            add item += Some(value + 1);
            have item >= Some(value + 1);
        }
    }
    #[inductive(initialize)] fn initialize_inductive(post: Self) {}
    #[inductive(replace_and_have)] fn replace_and_have_inductive(pre: Self, post: Self, unused: nat) {}
});

proof fn pattern_binding_observes_owned_value() {
    let tracked token = ScopedPattern::Protocol::initialize();
    // The bound value is four; the unrelated argument is ninety-nine.
    let tracked token = ScopedPattern::Protocol::replace_and_have(token, 99nat);
    assert(token.fragment().item == Some(ExclusiveRA::Exclusive(5nat)));
}

pub proof fn allocate_shared(local_count: nat, shared_count: nat) -> (tracked out: (
    Ordered::Token,
    Ordered::Token,
))
    requires
        local_count + shared_count <= 10,
    ensures
        out.0.loc() == out.1.loc(),
        out.0.fragment() == (Ordered::Fragment {
            phase: Some(ExclusiveRA::Exclusive(10nat)),
            count: CountRA { count: local_count },
        }),
        out.1.fragment() == (Ordered::Fragment {
            count: CountRA { count: shared_count },
            ..Ordered::Fragment::unit()
        }),
{
    let tracked token = Ordered::Protocol::initialize();
    let owner = Ordered::Fragment {
        phase: Some(ExclusiveRA::Exclusive(10nat)),
        count: CountRA { count: local_count },
    };
    let rest = Ordered::Fragment {
        count: CountRA { count: (10 - local_count) as nat },
        ..Ordered::Fragment::unit()
    };
    let tracked (owner, rest) = token.split(owner, rest);
    let shared = Ordered::Fragment {
        count: CountRA { count: shared_count },
        ..Ordered::Fragment::unit()
    };
    let remainder = Ordered::Fragment {
        count: CountRA { count: (10 - local_count - shared_count) as nat },
        ..Ordered::Fragment::unit()
    };
    let tracked (shared, remainder) = rest.split(shared, remainder);
    (owner, shared)
}

proof fn have_after_remove_includes_unchanged_borrow() {
    let tracked (owner, shared) = allocate_shared(2nat, 1nat);
    let tracked owner = Ordered::Protocol::remove_then_have_with_shared(owner, &shared);
    assert(owner.fragment().count.count == 1);
    assert(shared.fragment().count.count == 1);
}

} // verus!
