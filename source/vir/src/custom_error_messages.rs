struct CustomErr {
    msg: String,

    // Index of the precondition (or None if it's for all of them)
    is_for_precondition: Option<u64>,

    skip_highlight_precondition: bool,
}

pub struct CustomErrors {
    errs: Vec<CustomErr>,
}

impl CustomErrors {
    pub error_for_callsite() {
        
    }
}
