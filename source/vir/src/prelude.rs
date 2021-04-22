use crate::def::{FUEL_BOOL, FUEL_BOOL_DEFAULT, FUEL_DEFAULTS, FUEL_ID};
use air::print_parse::{macro_push_node, str_to_node};
use air::{node, nodes_vec};
use sise::Node;

pub(crate) fn prelude_nodes() -> Vec<Node> {
    #[allow(non_snake_case)]
    let FuelId = str_to_node(FUEL_ID);
    let fuel_bool = str_to_node(FUEL_BOOL);
    let fuel_bool_default = str_to_node(FUEL_BOOL_DEFAULT);
    let fuel_defaults = str_to_node(FUEL_DEFAULTS);

    nodes_vec!(
        (declare-sort [FuelId])
        (declare-fun [fuel_bool] ([FuelId]) Bool)
        (declare-fun [fuel_bool_default] ([FuelId]) Bool)
        (declare-const [fuel_defaults] Bool)
        (axiom (=> [fuel_defaults]
            (forall ((id [FuelId])) (!
                (= ([fuel_bool] id) ([fuel_bool_default] id))
                ":pattern" (([fuel_bool] id))
            ))
        ))
    )
}
