use crate::ast::Span;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct MessageLabel {
    pub span: Span,
    pub note: String,
}
pub type MessageLabels = Arc<Vec<MessageLabel>>;

#[derive(Debug, Serialize, Deserialize, Clone, Copy, PartialEq, Eq)]
pub enum MessageLevel {
    Error,
    Warning,
    Note,
}

/// If you just want to build a simple message, see the builders below.
///
/// Our Message type is designed to resemble Rust's MultiSpan,
/// with an additional 'note' String to provide a top-level description.
/// A Message should typically have at least one 'span' which represents
/// the primary point described. It is possible to have more
/// than one span, and it is possible to have additional label information.
///
/// Here's an example message:
///
/// error: precondition not satisfied                 // note (String)
///   --> filename.rs:18:5
///    |
/// 14 |     requires(b);
///    |              - failed precondition           // label (Span, String)
/// ...
/// 18 |     has_expectations(false);
///    |     ^^^^^^^^^^^^^^^^^^^^^^^                  // primary span (Span)
///
/// Note that if you want to get a message that is rendered with ^^^^ AND has a label
/// it needs to BOTH be in the primary spans list AND in the labels.

#[derive(Clone, Serialize, Deserialize)] // for Debug, see ast_util
pub struct MessageX {
    pub level: MessageLevel,
    pub note: String,
    pub spans: Vec<Span>,          // "primary" spans
    pub labels: Vec<MessageLabel>, // additional spans, with string annotations
    pub help: Option<String>,
}
pub type Message = Arc<MessageX>;

pub trait Diagnostics {
    /// Display the corresponding message
    fn report(&self, msg: &Message) {
        self.report_as(msg, msg.level)
    }

    /// Immediately display the message, regardless of which module is currently printing
    fn report_now(&self, msg: &Message) {
        self.report_as_now(msg, msg.level);
    }

    /// Override the msg's reporting level
    fn report_as(&self, msg: &Message, msg_as: MessageLevel);

    /// Override the msg's reporting level and immediately display the message
    fn report_as_now(&self, msg: &Message, msg_as: MessageLevel) {
        self.report_as(msg, msg_as);
    }
}

/// Very simple implementation of Diagnostics for use in AIR
pub struct Reporter {}
impl Diagnostics for Reporter {
    fn report_as(&self, msg: &Message, level: MessageLevel) {
        use MessageLevel::*;
        match level {
            Note => println!("Note: {}", msg.note),
            Warning => println!("Warning: {}", msg.note),
            Error => eprintln!("Error: {}", msg.note),
        }
    }
}

// Basic Message constructors

/// Basic message, with a note and a single span to be highlighted with ^^^^^^
pub fn message<S: Into<String>>(level: MessageLevel, note: S, span: &Span) -> Message {
    Arc::new(MessageX {
        level,
        note: note.into(),
        spans: vec![span.clone()],
        labels: Vec::new(),
        help: None,
    })
}

/// Bare message without any span
pub fn message_bare<S: Into<String>>(level: MessageLevel, note: S) -> Message {
    Arc::new(MessageX { level, note: note.into(), spans: vec![], labels: Vec::new(), help: None })
}

/// Message with a span to be highlighted with ^^^^^^, and a label for that span
pub fn message_with_label<S: Into<String>, T: Into<String>>(
    level: MessageLevel,
    note: S,
    span: &Span,
    label: T,
) -> Message {
    Arc::new(MessageX {
        level,
        note: note.into(),
        spans: vec![span.clone()],
        labels: vec![MessageLabel { span: span.clone(), note: label.into() }],
        help: None,
    })
}

// Convenience functions

/// Bare note without any spans
pub fn note_bare<S: Into<String>>(note: S) -> Message {
    message_bare(MessageLevel::Note, note)
}

/// Basic note, with a message and a single span to be highlighted with ^^^^^^
pub fn note<S: Into<String>>(note: S, span: &Span) -> Message {
    message(MessageLevel::Note, note, span)
}

/// Bare warning without any spans
pub fn warning_bare<S: Into<String>>(note: S) -> Message {
    message_bare(MessageLevel::Warning, note)
}

/// Basic warning, with a message and a single span to be highlighted with ^^^^^^
pub fn warning<S: Into<String>>(note: S, span: &Span) -> Message {
    message(MessageLevel::Warning, note, span)
}

/// Bare error without any spans; use the builders below to add spans and labels
pub fn error_bare<S: Into<String>>(note: S) -> Message {
    message_bare(MessageLevel::Error, note)
}

/// Basic error, with a message and a single span to be highlighted with ^^^^^^
pub fn error<S: Into<String>>(note: S, span: &Span) -> Message {
    message(MessageLevel::Error, note, span)
}

/// Prepend the error with "Verus Internal Error"
/// Helpful for distinguishing user errors from Verus bugs.
pub fn internal_error<S: Into<String>>(note: S, span: &Span) -> Message {
    let msg = format!("Verus Internal Error: {:}", note.into());
    message(MessageLevel::Error, msg, span)
}

/// Error message with a span to be highlighted with ^^^^^^, and a label for that span
pub fn error_with_label<S: Into<String>, T: Into<String>>(
    note: S,
    span: &Span,
    label: T,
) -> Message {
    message_with_label(MessageLevel::Error, note, span, label)
}

// Add additional stuff with the "builders" below.

impl MessageX {
    /// Add a new primary span (rendered with ^^^^^^)
    pub fn primary_span(&self, span: &Span) -> Message {
        let mut e = self.clone();
        e.spans.push(span.clone());
        Arc::new(e)
    }

    /// Add a new primary span with a label (rendered with ^^^^^^)
    pub fn primary_label<S: Into<String>>(&self, span: &Span, label: S) -> Message {
        let mut e = self.clone();
        e.spans.push(span.clone());
        e.labels.push(MessageLabel { span: span.clone(), note: label.into() });
        Arc::new(e)
    }

    /// Add a secondary_span to be highlighted, with no label (rendered with ------)
    pub fn secondary_span(&self, span: &Span) -> Message {
        let mut e = self.clone();
        e.labels.push(MessageLabel { span: span.clone(), note: "".to_string() });
        Arc::new(e)
    }

    /// Add a secondary_span to be highlighted, with a label (rendered with ------)
    pub fn secondary_label<S: Into<String>>(&self, span: &Span, label: S) -> Message {
        let mut e = self.clone();
        e.labels.push(MessageLabel { span: span.clone(), note: label.into() });
        Arc::new(e)
    }

    /// Append secondary labels
    pub fn append_labels(&self, labels: &Vec<MessageLabel>) -> Message {
        let mut l = self.labels.clone();
        for label in labels {
            l.push(label.clone());
        }
        Arc::new(MessageX {
            level: self.level,
            note: self.note.clone(),
            spans: self.spans.clone(),
            labels: l,
            help: None,
        })
    }

    pub fn help(&self, help: impl Into<String>) -> Message {
        let MessageX { level, note, spans, labels, help: _ } = &self;
        Arc::new(MessageX {
            level: *level,
            note: note.clone(),
            spans: spans.clone(),
            labels: labels.clone(),
            help: Some(help.into()),
        })
    }
}

/// (Lossy) conversions between the complicated Message format and the simpler format used by air

pub fn error_from_spans(spans: Vec<Span>) -> Message {
    Arc::new(MessageX {
        level: MessageLevel::Error,
        note: "".to_string(),
        spans: spans,
        labels: Vec::new(),
        help: None,
    })
}

pub fn error_from_labels(labels: MessageLabels) -> Message {
    if labels.len() == 0 {
        Arc::new(MessageX {
            level: MessageLevel::Error,
            note: "".to_string(),
            spans: Vec::new(),
            labels: Vec::new(),
            help: None,
        })
    } else {
        // Choose the first label to make the "primary" span.
        let MessageLabel { note, span } = labels[0].clone();
        Arc::new(MessageX {
            level: MessageLevel::Error,
            note: note,
            spans: vec![span],
            labels: labels[1..].to_vec(),
            help: None,
        })
    }
}

pub fn all_msgs_from_error(error: &Message) -> Vec<String> {
    let mut v = vec![error.note.clone()];
    for l in &error.labels {
        v.push(l.note.clone());
    }
    v
}
