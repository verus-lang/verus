use crate::ast::Span;
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct ErrorLabel {
    pub span: Span,
    pub msg: String,
}
pub type ErrorLabels = Arc<Vec<ErrorLabel>>;

/// If you just want to build an Error message, see the builders below.
///
/// Our Error type is designed to resemble Rust's MultiSpan,
/// with an additional 'msg' String to serve as an error message.
/// An Error should always have at least one 'span' which represents
/// the primary point where the error is. It is possible to have more
/// than one span, and it is possible to have additional label information.
///
/// Here's an example error:
///
/// error: precondition not satisfied                 // msg (String)
///   --> filename.rs:18:5
///    |
/// 14 |     requires(b);
///    |              - failed precondition           // label (Span, String)
/// ...
/// 18 |     has_expectations(false);
///    |     ^^^^^^^^^^^^^^^^^^^^^^^                  // primary span (Span)
///
/// Note that if you want to get an error that is rendered with ^^^^ AND has a label
/// it needs to BOTH be in the primary spans list AND in the labels.

#[derive(Clone)] // for Debug, see ast_util
pub struct ErrorX {
    pub msg: String,
    pub spans: Vec<Span>,        // "primary" spans
    pub labels: Vec<ErrorLabel>, // additional spans, with string annotations
}
pub type Error = Arc<ErrorX>;

// To build an error, use one of the constructors below:

/// Basic error, with a message and a single span to be highlighted with ^^^^^^
pub fn error<S: Into<String>>(msg: S, span: &Span) -> Error {
    return Arc::new(ErrorX { msg: msg.into(), spans: vec![span.clone()], labels: Vec::new() });
}

/// Error with a message, a span to be highlighted with ^^^^^^, and a label for that span
pub fn error_with_label<S: Into<String>, T: Into<String>>(msg: S, span: &Span, label: T) -> Error {
    return Arc::new(ErrorX {
        msg: msg.into(),
        spans: vec![span.clone()],
        labels: vec![ErrorLabel { span: span.clone(), msg: label.into() }],
    });
}

// Add additional stuff with the "builders" below.

impl ErrorX {
    /// Add a new primary span (rendered with ^^^^^^)
    pub fn primary_span(&self, span: &Span) -> Error {
        let mut e = self.clone();
        e.spans.push(span.clone());
        Arc::new(e)
    }

    /// Add a new primary span with a label (rendered with ^^^^^^)
    pub fn primary_label<S: Into<String>>(&self, span: &Span, label: S) -> Error {
        let mut e = self.clone();
        e.spans.push(span.clone());
        e.labels.push(ErrorLabel { span: span.clone(), msg: label.into() });
        Arc::new(e)
    }

    /// Add a secondary_span to be highlighted, with no label (rendered with ------)
    pub fn secondary_span(&self, span: &Span) -> Error {
        let mut e = self.clone();
        e.labels.push(ErrorLabel { span: span.clone(), msg: "".to_string() });
        Arc::new(e)
    }

    /// Add a secondary_span to be highlighted, with a label (rendered with ------)
    pub fn secondary_label<S: Into<String>>(&self, span: &Span, label: S) -> Error {
        let mut e = self.clone();
        e.labels.push(ErrorLabel { span: span.clone(), msg: label.into() });
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
