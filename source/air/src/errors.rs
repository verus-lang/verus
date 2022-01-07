use crate::ast::{Error, ErrorLabel, ErrorLabels, ErrorX, Span};
use std::sync::Arc;

pub fn error_str(span: &Span, msg: &str) -> Error {
    return error_string(span, msg.to_string());
}

pub fn error_string(span: &Span, msg: String) -> Error {
    return Arc::new(ErrorX { msg: msg, spans: vec![span.clone()], labels: Vec::new() });
}

pub fn error_string_with_label(span: &Span, msg: String, span2: &Span, msg2: String) -> Error {
    return Arc::new(ErrorX {
        msg: msg,
        spans: vec![span.clone()],
        labels: vec![ErrorLabel { span: span2.clone(), msg: msg2 }],
    });
}

pub fn error_from_spans(spans: Vec<Span>) -> Error {
    return Arc::new(ErrorX { msg: "".to_string(), spans: spans, labels: Vec::new() });
}

pub fn error_from_labels(labels: ErrorLabels) -> Error {
    if labels.len() == 0 {
        return Arc::new(ErrorX { msg: "".to_string(), spans: Vec::new(), labels: Vec::new() });
    } else {
        // Choose the first label to make the "primary" span.
        let ErrorLabel { msg, span } = labels[0].clone();
        return Arc::new(ErrorX { msg: msg, spans: vec![span], labels: labels[1..].to_vec() });
    }
}

pub fn all_msgs_from_error(error: &Error) -> Vec<String> {
    let mut v = vec![error.msg.clone()];
    for l in &error.labels {
        v.push(l.msg.clone());
    }
    return v;
}

impl ErrorX {
    pub fn append_labels(&self, labels: &Vec<ErrorLabel>) -> Error {
        let mut l = self.labels.clone();
        for label in labels {
            l.push(label.clone());
        }
        Arc::new(ErrorX { msg: self.msg.clone(), spans: self.spans.clone(), labels: l })
    }
}
