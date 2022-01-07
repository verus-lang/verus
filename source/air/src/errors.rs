use crate::ast::{Error, ErrorLabel, ErrorLabels, ErrorX, Span};
use std::sync::Arc;

// To build an error, use one of the constructors below:

/// Basic error, with a message and a single span to be highlighted.
pub fn error_str(span: &Span, msg: &str) -> Error {
    return error_string(span, msg.to_string());
}

/// Basic error, with a message and a single span to be highlighted.
pub fn error_string(span: &Span, msg: String) -> Error {
    return Arc::new(ErrorX { msg: msg, spans: vec![span.clone()], labels: Vec::new() });
}

/// Error with a message, a span to be highlighted, and a label for that span
pub fn error_with_label(msg: String, span: &Span, label: String) -> Error {
    return Arc::new(ErrorX {
        msg: msg,
        spans: vec![span.clone()],
        labels: vec![ErrorLabel { span: span.clone(), msg: label }],
    });
}

// Add additional stuff with the "builders" below.

impl ErrorX {
    /// Add a new primary span
    pub fn primary_span(&self, span: &Span) -> Error {
        let mut e = self.clone();
        e.spans.push(span.clone());
        Arc::new(e)
    }

    /// Add a new primary span with a label
    pub fn primary_label(&self, span: &Span, label: String) -> Error {
        let mut e = self.clone();
        e.spans.push(span.clone());
        e.labels.push(ErrorLabel { span: span.clone(), msg: label });
        Arc::new(e)
    }

    /// Add a secondary_span to be highlighted, with no label
    pub fn secondary_span(&self, span: &Span) -> Error {
        let mut e = self.clone();
        e.labels.push(ErrorLabel { span: span.clone(), msg: "".to_string() });
        Arc::new(e)
    }

    /// Add a secondary_span to be highlighted, with a label
    pub fn secondary_label(&self, span: &Span, label: String) -> Error {
        let mut e = self.clone();
        e.labels.push(ErrorLabel { span: span.clone(), msg: label });
        Arc::new(e)
    }

    /// Append secondary labels
    pub fn append_labels(&self, labels: &Vec<ErrorLabel>) -> Error {
        let mut l = self.labels.clone();
        for label in labels {
            l.push(label.clone());
        }
        Arc::new(ErrorX { msg: self.msg.clone(), spans: self.spans.clone(), labels: l })
    }
}

/// (Lossy) conversions between the complicated Error format and the simpler format used by air

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
