use crate::ast::Mode;
use air::ast::Span;
use air::errors::ErrorLabel;

/// Handles the construction of error messages for precondition failures on a function call.
/// Deals both with custom error messages and the common default behavior absent any such
/// custom message.

#[derive(Debug, Default, Clone)]
pub struct FnCallErrors {
    /// Corresponds to
    /// #[verifier(custom_req_err("msg"))]
    custom_msg: Option<String>,

    precondition_errs: Vec<PreconditionErr>,
}

/// Corresponds to
/// #[verifier(custom_req_err("msg", idx))]

#[derive(Debug, Default, Clone)]
struct PreconditionErr {
    idx: usize,
    msg: String,
}

impl FnCallErrors {
    pub fn from_attrs(main_msg: Option<String>, precondition_msgs: Vec<(String, usize)>) -> Self {
        FnCallErrors {
            custom_msg: main_msg,
            precondition_errs: precondition_msgs
                .into_iter()
                .map(|(s, i)| PreconditionErr { idx: i, msg: s })
                .collect(),
        }
    }

    pub fn msg_for_callsite(&self, mode: Mode) -> String {
        match &self.custom_msg {
            Some(msg) => msg.clone(),
            None => {
                if mode == Mode::Spec {
                    "recommendation not met".to_string()
                } else {
                    "precondition not satisfied".to_string()
                }
            }
        }
    }

    pub fn labels_for_req_defn(&self, mode: Mode, i: usize, req_span: &Span) -> Vec<ErrorLabel> {
        match self.custom_error_for_precondition(i) {
            None => {
                if self.custom_msg.is_some() {
                    vec![]
                } else {
                    let msg = if mode == Mode::Spec {
                        "recommendation not met"
                    } else {
                        "failed precondition"
                    };
                    vec![ErrorLabel { span: req_span.clone(), msg: msg.to_string() }]
                }
            }
            Some(custom) => {
                vec![ErrorLabel { span: req_span.clone(), msg: custom.msg.clone() }]
            }
        }
    }

    fn custom_error_for_precondition(&self, i: usize) -> Option<&PreconditionErr> {
        for err in self.precondition_errs.iter() {
            if err.idx == i {
                return Some(err);
            }
        }
        None
    }
}
