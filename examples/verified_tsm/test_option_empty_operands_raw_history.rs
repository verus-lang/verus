//! Complete empty optional-operand relation case and physical resource histories.
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
verified_state_machine_model! { Y {
    fields {
        #[sharding(option)]
        pub opt: Option<int>,

        #[sharding(storage_option)]
        pub storage_opt: Option<int>,
    }

    property!{
        ro() {
            guard storage_opt >= (Option::<int>::None);
        }
    }

    transition!{
        tr1() {
            have opt >= (Option::<int>::None);
        }
    }

    transition!{
        tr2() {
            add opt += (Option::<int>::None);
            deposit storage_opt += (Option::<int>::None);
        }
    }

    transition!{
        tr3() {
            remove opt -= (Option::<int>::None);
            withdraw storage_opt -= (Option::<int>::None);
        }
    }
}}
verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
}

spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
    equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
}

spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
    equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
}

proof fn correct_tr1(pre: Y::State, post: Y::State) {
    requires(Y::State::tr1(pre, post));
    ensures(rel_tr1(pre, post));
}

proof fn rev_tr1(pre: Y::State, post: Y::State) {
    requires(rel_tr1(pre, post));
    ensures(Y::State::tr1(pre, post));
}

proof fn correct_tr1_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr1_strong(pre, post));
    ensures(rel_tr1_strong(pre, post));
}

proof fn rev_tr1_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr1_strong(pre, post));
    ensures(Y::State::tr1_strong(pre, post));
}

proof fn correct_tr2(pre: Y::State, post: Y::State) {
    requires(Y::State::tr2(pre, post));
    ensures(rel_tr2(pre, post));
}

proof fn rev_tr2(pre: Y::State, post: Y::State) {
    requires(rel_tr2(pre, post));
    ensures(Y::State::tr2(pre, post));
}

proof fn correct_tr2_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr2_strong(pre, post));
    ensures(rel_tr2_strong(pre, post));
}

proof fn rev_tr2_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr2_strong(pre, post));
    ensures(Y::State::tr2_strong(pre, post));
}

proof fn correct_tr3(pre: Y::State, post: Y::State) {
    requires(Y::State::tr3(pre, post));
    ensures(rel_tr3(pre, post));
}

proof fn rev_tr3(pre: Y::State, post: Y::State) {
    requires(rel_tr3(pre, post));
    ensures(Y::State::tr3(pre, post));
}

proof fn correct_tr3_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr3_strong(pre, post));
    ensures(rel_tr3_strong(pre, post));
}

proof fn rev_tr3_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr3_strong(pre, post));
    ensures(Y::State::tr3_strong(pre, post));
}

} // verus!
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 SafeY {
    fields {
        #[sharding(option)]
        pub opt: Option<int>,

        #[sharding(storage_option)]
        pub storage_opt: Option<int>,

        // Every original transition is a storage no-op. This checked
        // authority retains the value supplied by the initializer.
        #[sharding(constant)]
        pub physical_authority: Option<int>,
    }
    #[invariant] pub fn retained_physical(self)->bool {
        self.storage_opt==self.physical_authority
    }

    init! { initialize(logical:Option<int>,physical:Option<int>) {
        init opt=logical;
        init storage_opt=physical;
        init physical_authority=physical;
    } }
    property!{
        ro() {
            guard storage_opt >= (Option::<int>::None);
        }
    }

    transition!{
        tr1() {
            have opt >= (Option::<int>::None);
        }
    }

    transition!{
        tr2() {
            add opt += (Option::<int>::None);
            deposit storage_opt += (Option::<int>::None);
        }
    }

    transition!{
        tr3() {
            remove opt -= (Option::<int>::None);
            withdraw storage_opt -= (Option::<int>::None);
        }
    }
    property! {retained_permission(value:int) {
        require pre.physical_authority==Some(value);
        guard storage_opt >= Some(value);
    }}
    #[inductive(initialize)] fn initialize_inductive(post:Self,logical:Option<int>,physical:Option<int>){}
    #[inductive(tr1)] fn tr1_inductive(pre:Self,post:Self){}
    #[inductive(tr2)] fn tr2_inductive(pre:Self,post:Self){}
    #[inductive(tr3)] fn tr3_inductive(pre:Self,post:Self){}
}}

verus! {

broadcast use {vstd::imap::group_imap_lemmas, vstd::iset::group_iset_lemmas};

pub open spec fn original_projection(state: SafeY::State) -> Y::State {
    Y::State { opt: state.opt, storage_opt: state.storage_opt }
}

pub proof fn whole_original_refinement(pre: SafeY::State, post: SafeY::State)
    requires
        pre.invariant(),
        post.invariant(),
    ensures
        SafeY::State::tr1_strong(pre, post) ==> Y::State::tr1_strong(
            original_projection(pre),
            original_projection(post),
        ),
        SafeY::State::tr2_strong(pre, post) ==> Y::State::tr2_strong(
            original_projection(pre),
            original_projection(post),
        ),
        SafeY::State::tr3_strong(pre, post) ==> Y::State::tr3_strong(
            original_projection(pre),
            original_projection(post),
        ),
{
}

/// None needs no local resource and transfers no physical permission, even
/// when both logical and physical fields are populated.
pub proof fn no_op_ready(owned: SafeY::Fragment)
    ensures
        SafeY::Protocol::tr1_requires(owned, SafeY::Fragment::unit(), IMap::empty()),
        SafeY::Protocol::tr2_requires(owned, SafeY::Fragment::unit(), IMap::empty()),
        SafeY::Protocol::tr3_requires(owned, SafeY::Fragment::unit(), IMap::empty()),
{
    SafeY::Fragment::op_unit(owned);
    assert forall|frame: SafeY::Fragment, pre: SafeY::State|
        pre.invariant() && SafeY::Fragment::op(
            SafeY::Fragment::op(owned, SafeY::Fragment::unit()),
            frame,
        ) == SafeY::Protocol::embed(pre) implies SafeY::State::tr1_enabled(pre)
        && SafeY::State::tr1_owners_enabled(pre, owned, SafeY::Fragment::unit()) && IMap::empty()
        == SafeY::State::tr1_deposited(pre) && SafeY::State::tr2_enabled(pre)
        && SafeY::State::tr2_owners_enabled(pre, owned, SafeY::Fragment::unit()) && IMap::empty()
        == SafeY::State::tr2_deposited(pre) && SafeY::State::tr3_enabled(pre)
        && SafeY::State::tr3_owners_enabled(pre, owned, SafeY::Fragment::unit()) && IMap::empty()
        == SafeY::State::tr3_deposited(pre) by {};
}

pub proof fn retained_permission_ready(owned: SafeY::Fragment, value: int)
    requires
        owned.physical_authority == Some(vstd::resource::agree::AgreementRA::Agree(Some(value))),
    ensures
        SafeY::Protocol::retained_permission_requires(owned, value),
{
    assert forall|frame: SafeY::Fragment, pre: SafeY::State|
        pre.invariant() && SafeY::Fragment::op(owned, frame) == SafeY::Protocol::embed(
            pre,
        ) implies SafeY::State::retained_permission_enabled(pre, value)
        && SafeY::State::retained_permission_owners_enabled(
        pre,
        owned,
        SafeY::Fragment::unit(),
        value,
    ) by {
        assert(pre.physical_authority == Some(value));
        assert(pre.storage_opt == Some(value));
    }
}

pub proof fn empty_resource_history() {
    let tracked token = SafeY::Protocol::initialize(IMap::tracked_empty(), None, None);
    let tracked guard = SafeY::Protocol::ro(&token);
    assert(*guard =~= IMap::empty());
    no_op_ready(token.fragment());
    let before = token.fragment();
    let tracked token = SafeY::Protocol::tr1(token);
    let (pre, post, frame) = SafeY::Protocol::tr1_witness(
        before,
        SafeY::Fragment::unit(),
        token.fragment(),
        IMap::empty(),
        IMap::empty(),
    );
    whole_original_refinement(pre, post);
    assert(Y::State::tr1_strong(original_projection(pre), original_projection(post)));
    no_op_ready(token.fragment());
    let before = token.fragment();
    let tracked token = SafeY::Protocol::tr2(token, IMap::tracked_empty());
    let (pre, post, frame) = SafeY::Protocol::tr2_witness(
        before,
        SafeY::Fragment::unit(),
        token.fragment(),
        IMap::empty(),
        IMap::empty(),
    );
    whole_original_refinement(pre, post);
    assert(Y::State::tr2_strong(original_projection(pre), original_projection(post)));
    no_op_ready(token.fragment());
    let before = token.fragment();
    let tracked (token, withdrawn) = SafeY::Protocol::tr3(token);
    let (pre, post, frame) = SafeY::Protocol::tr3_witness(
        before,
        SafeY::Fragment::unit(),
        token.fragment(),
        IMap::empty(),
        withdrawn,
    );
    whole_original_refinement(pre, post);
    assert(Y::State::tr3_strong(original_projection(pre), original_projection(post)));
    assert(withdrawn =~= IMap::empty());
    token.validate();
}

pub proof fn present_resource_history() {
    let tracked mut base = IMap::tracked_empty();
    let tracked actual_permission = 9int;
    base.tracked_insert(0int, actual_permission);
    let tracked token = SafeY::Protocol::initialize(base, Some(7int), Some(9int));
    let tracked guard = SafeY::Protocol::ro(&token);
    assert(*guard =~= IMap::empty());
    no_op_ready(token.fragment());
    let before = token.fragment();
    let tracked token = SafeY::Protocol::tr1(token);
    let (pre, post, frame) = SafeY::Protocol::tr1_witness(
        before,
        SafeY::Fragment::unit(),
        token.fragment(),
        IMap::empty(),
        IMap::empty(),
    );
    whole_original_refinement(pre, post);
    assert(Y::State::tr1_strong(original_projection(pre), original_projection(post)));
    no_op_ready(token.fragment());
    let before = token.fragment();
    let tracked token = SafeY::Protocol::tr2(token, IMap::tracked_empty());
    let (pre, post, frame) = SafeY::Protocol::tr2_witness(
        before,
        SafeY::Fragment::unit(),
        token.fragment(),
        IMap::empty(),
        IMap::empty(),
    );
    whole_original_refinement(pre, post);
    assert(Y::State::tr2_strong(original_projection(pre), original_projection(post)));
    no_op_ready(token.fragment());
    let before = token.fragment();
    let tracked (token, withdrawn) = SafeY::Protocol::tr3(token);
    let (pre, post, frame) = SafeY::Protocol::tr3_witness(
        before,
        SafeY::Fragment::unit(),
        token.fragment(),
        IMap::empty(),
        withdrawn,
    );
    whole_original_refinement(pre, post);
    assert(Y::State::tr3_strong(original_projection(pre), original_projection(post)));
    assert(withdrawn =~= IMap::empty());
    assert(token.fragment().opt == Some(vstd::resource::exclusive::ExclusiveRA::Exclusive(7int)));
    assert(token.fragment().physical_authority == Some(
        vstd::resource::agree::AgreementRA::Agree(Some(9int)),
    ));
    retained_permission_ready(token.fragment(), 9int);
    let tracked retained = SafeY::Protocol::retained_permission(&token, 9int);
    let tracked actual_borrow = retained.tracked_borrow(0int);
    assert(*actual_borrow == 9int);
    token.validate();
}

pub fn demonstration() {
    proof {
        empty_resource_history();
        present_resource_history();
    }
}

} // verus!
fn main() {
    demonstration();
}
