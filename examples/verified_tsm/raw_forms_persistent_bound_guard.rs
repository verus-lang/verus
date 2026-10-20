//! A storage guard of a value bound by `have o >= Some(let x)` on a
//! `persistent_option` field (as for an exclusive `option` field): the raw
//! backend reads the bound value from the borrowed agreement fragment, so the
//! guarded map is a function of the fragment, and links it to every
//! completion's state with `persistent_option_owned_frame`.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

// The raw interface.
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    RawPublished {
        fields {
            #[sharding(persistent_option)]
            pub published: Option<u64>,

            #[sharding(storage_option)]
            pub cell: Option<u64>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.cell == self.published
        }

        init!{
            initialize(v: u64) {
                init published = Some(v);
                init cell = Some(v);
            }
        }

        property!{
            peek() {
                have published >= Some(let x);
                guard cell >= Some(x);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, v: u64) { }
    }
}

// The generic interface (the default) over the same raw operation, with an
// exclusive `option` field and a `persistent_option` field.
verified_tokenized_state_machine! {
    Published {
        fields {
            #[sharding(persistent_option)]
            pub published: Option<u64>,

            #[sharding(option)]
            pub draft: Option<u64>,

            #[sharding(storage_option)]
            pub cell: Option<u64>,

            #[sharding(storage_option)]
            pub draft_cell: Option<u64>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.cell == self.published && self.draft_cell == self.draft
        }

        init!{
            initialize(v: u64, w: u64) {
                init published = Some(v);
                init draft = Some(w);
                init cell = Some(v);
                init draft_cell = Some(w);
            }
        }

        property!{
            peek() {
                have published >= Some(let x);
                guard cell >= Some(x);
            }
        }

        property!{
            peek_both() {
                have published >= Some(let x);
                have draft >= Some(let y);
                guard cell >= Some(x);
                guard draft_cell >= Some(y);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, v: u64, w: u64) { }
    }
}

verus! {

proof fn raw_client() {
    // The storage is one `IMap<__StorageKey, __StorageValue>`; `__pack_cell`
    // tags the `Option` of the `storage_option` field.
    let tracked base = RawPublished::__pack_cell(Some(5u64));
    let tracked token = RawPublished::Protocol::initialize(base, 5);
    let tracked g = RawPublished::Protocol::peek(&token);
    assert(*g =~= RawPublished::__tag_cell(Some(5u64)));
}

proof fn client() {
    let tracked (Tracked(inst), Tracked(published), Tracked(draft)) =
        Published::Instance::initialize(5, 7, Some(5), Some(7));
    let tracked published = published.tracked_unwrap();
    let tracked draft = draft.tracked_unwrap();
    assert(published.value() == 5);
    let tracked g = inst.peek(&published);
    assert(*g == 5);
    // Persistent tokens are `Copy`: guard from a copy.
    let tracked p2 = published;
    let tracked (Tracked(a), Tracked(b)) = inst.peek_both(&p2, &draft);
    assert(*a == 5 && *b == 7);
}

}

fn main() {}
