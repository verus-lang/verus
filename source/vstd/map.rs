pub use super::gmap::{
    Map, IMap,
    axiom_map_finite_from_type,
    axiom_map_index_decreases_finite,
    axiom_map_index_decreases_infinite,
    lemma_infinite_new_ensures,
    lemma_map_empty,
    lemma_map_insert_domain,
    lemma_map_insert_same,
    lemma_map_insert_different,
    lemma_map_remove_domain,
    lemma_map_remove_different,
    lemma_map_ext_equal,
    lemma_map_ext_equal_deep,
    lemma_congruence_extensionality,
    group_map_axioms,
    map,
    imap,
    assert_maps_equal,
};

#[doc(hidden)]
pub use super::gmap::{
    axiom_map_finite_from_trait,
    lemma_new_from_set_ensures,
    check_argument_is_map,
    map_internal,
    imap_internal,
    assert_maps_equal_internal,
};
