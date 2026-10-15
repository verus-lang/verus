//! Checked general optional operands; None is the neutral operand.
use vstd::prelude::*;
use vstd::resource::agree::AgreementRA;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_collections::*;

verus! {

proof fn arbitrary_neutral_operands<V>(
    owned: OptionFragment<V>,
    frame: OptionFragment<V>,
    whole: Option<V>,
)
    requires
        OptionFragment::op(owned, frame) == option_frag(whole),
{
    option_have_general_frame(owned, frame, whole, None);
    option_add_general_frame(owned, frame, whole, None);
    option_remove_general_frame(owned, frame, whole, None);
}

proof fn exclusive_present_operands() {
    option_have_general_frame(option_frag(Some(7int)), None, Some(7int), Some(7int));
    option_remove_general_frame(option_frag(Some(7int)), None, Some(7int), Some(7int));
    option_add_general_frame(None, None, None, Some(9int));
}

proof fn persistent_operand_agreement() {
    persistent_option_have_general_frame(
        None,
        persistent_option_frag(Some(7int)),
        Some(7int),
        None,
    );
    persistent_option_union_general_frame(
        None,
        persistent_option_frag(Some(7int)),
        Some(7int),
        None,
    );
    persistent_option_union_general_frame(
        None,
        persistent_option_frag(Some(7int)),
        Some(7int),
        Some(7int),
    );
    persistent_option_union_general_frame(
        persistent_option_frag(Some(7int)),
        persistent_option_frag(Some(7int)),
        Some(7int),
        Some(7int),
    );
    persistent_option_have_general_frame(
        persistent_option_frag(Some(7int)),
        persistent_option_frag(Some(7int)),
        Some(7int),
        Some(7int),
    );
}

fn main() {
    proof {
        exclusive_present_operands();
        persistent_operand_agreement();
    }
}

} // verus!
