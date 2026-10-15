//! Complete owned-fragment histories retained apart from the original clients.
use vstd::prelude::*;
#[path = "counting_to_2.rs"]
mod counting_to_2;
#[path = "counting_to_n.rs"]
mod counting_to_n;
verus! {

fn main() {
    proof {
        {
            let tracked all = counting_to_2::X::Protocol::initialize();
            let tracked (owner_b, owner_a) = counting_to_2::X::Protocol::take_inc_b(all);
            let tracked owner_a = counting_to_2::X::Protocol::tr_inc_a(owner_a);
            let tracked combined = owner_a.join(owner_b);
            let tracked combined = counting_to_2::X::Protocol::tr_inc_b(combined);
            let tracked final_token = counting_to_2::X::Protocol::finalize(combined);
            assert(final_token.fragment().value_counter() == 2);

        }
        {
            let tracked all = counting_to_n::X::Protocol::initialize(2);
            let tracked (b, a) = counting_to_n::X::Protocol::split_unstamped_tickets(all, 1);
            let tracked a = counting_to_n::X::Protocol::tr_inc(a);
            assert(a.fragment().value_stamped_tickets() == 1);
            assert(b.fragment().value_unstamped_tickets() == 1);
            let tracked combined = a.join(b);
            let tracked combined = counting_to_n::X::Protocol::tr_inc(combined);
            let tracked final_token = counting_to_n::X::Protocol::finalize(combined);
            assert(final_token.fragment().value_counter() == 2);
            assert(final_token.fragment().value_unstamped_tickets() == 0);
            assert(final_token.fragment().value_stamped_tickets() == 2);

        }
    }
}

} // verus!
