pub use air::messages::MessageLevel;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

fn empty_raw_span() -> RawSpan {
    Arc::new(())
}

pub type RawSpan = Arc<dyn std::any::Any + std::marker::Sync + std::marker::Send>;
pub type AstId = u64;
#[derive(Debug, Clone, Serialize, Deserialize)] // for Debug, see ast_util
pub struct Span {
    #[serde(skip)]
    #[serde(default = "crate::messages::empty_raw_span")]
    pub raw_span: RawSpan,
    pub id: AstId, // arbitrary integer identifier that may be set and used in any way (e.g. as unique id, or just left as 0)
    pub data: Vec<u64>, // arbitrary integers (e.g. for serialization/deserialization)
    pub as_string: String, // if we can't print (description, raw_span), print as_string instead
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct MessageLabel {
    pub span: Span,
    pub note: String,
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

#[derive(Debug, Clone, Serialize, Deserialize)] // for Debug, see ast_util
pub struct MessageX {
    pub level: MessageLevel,
    pub note: String,
    pub spans: Vec<Span>,          // "primary" spans
    pub labels: Vec<MessageLabel>, // additional spans, with string annotations
    pub help: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)] // for Debug, see ast_util
pub struct Message(Arc<MessageX>);

impl core::ops::Deref for Message {
    type Target = MessageX;

    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl air::messages::Message for Message {
    type MessageLabel = MessageLabel;

    fn empty() -> Self {
        Message(Arc::new(MessageX {
            level: MessageLevel::Error,
            note: "".to_owned(),
            spans: Vec::new(),
            labels: Vec::new(),
            help: None,
        }))
    }

    fn all_msgs(&self) -> Vec<String> {
        Some(self.note.clone())
            .into_iter()
            .chain(self.labels.iter().map(|l| l.note.clone()))
            .collect()
    }

    fn bare(level: MessageLevel, note: &str) -> Self {
        Message(Arc::new(MessageX {
            level,
            note: note.to_owned(),
            spans: Vec::new(),
            labels: Vec::new(),
            help: None,
        }))
    }

    fn unexpected_z3_version(expected: &str, found: &str) -> Self {
        Message(Arc::new(MessageX {
            level: MessageLevel::Error,
            note: format!("expected z3 version {expected}, found {found}"),
            labels: Vec::new(),
            spans: Vec::new(),
            help: None,
        }))
    }

    fn get_note(&self) -> &str {
        &self.note
    }

    fn get_label_note(message_label: &Self::MessageLabel) -> &str {
        &message_label.note
    }

    fn append_labels(&self, labels: &Vec<Self::MessageLabel>) -> Self {
        let mut s = (*self.0).clone();
        s.labels.extend(labels.iter().cloned());
        Message(Arc::new(s))
    }

    fn label_from_air_span(air_span: &str, note: &str) -> Self::MessageLabel {
        MessageLabel {
            span: Span {
                raw_span: Arc::new(()),
                id: 0,
                data: Vec::new(),
                as_string: air_span.to_owned(),
            },
            note: note.to_owned(),
        }
    }

    fn from_labels(labels: &Vec<Self::MessageLabel>) -> Self {
        if labels.len() == 0 {
            Self::empty()
        } else {
            let MessageLabel { span, note } = labels[0].clone();
            Message(Arc::new(MessageX {
                level: MessageLevel::Error,
                note,
                spans: vec![span],
                labels: labels[1..].to_vec(),
                help: None,
            }))
        }
    }
}

// /// Construct an Error and wrap it in Err.
// /// For more complex Error objects, use the builder functions in air::errors
//
// pub fn error<A, S: Into<String>>(span: &Span, msg: S) -> Result<A, VirErr> {
//     Err(Err(message(msg, span)))
// }
//
// pub fn internal_error<A, S: Into<String>>(span: &Span, msg: S) -> Result<A, VirErr> {
//     Err(crate::messages::internal_error(msg, span))
// }
//
// pub fn error_with_help<A, S: Into<String>, H: Into<String>>(
//     span: &Span,
//     msg: S,
//     help: H,
// ) -> Result<A, VirErr> {
//     Err(error(span, msg).help(help))
// }

// Basic Message constructors

/// Basic message, with a note and a single span to be highlighted with ^^^^^^
pub fn message<S: Into<String>>(level: MessageLevel, note: S, span: &Span) -> Message {
    Message(Arc::new(MessageX {
        level,
        note: note.into(),
        spans: vec![span.clone()],
        labels: Vec::new(),
        help: None,
    }))
}

/// Bare message without any span
pub fn message_bare<S: Into<String>>(level: MessageLevel, note: S) -> Message {
    Message(Arc::new(MessageX {
        level,
        note: note.into(),
        spans: vec![],
        labels: Vec::new(),
        help: None,
    }))
}

/// Message with a span to be highlighted with ^^^^^^, and a label for that span
pub fn message_with_label<S: Into<String>, T: Into<String>>(
    level: MessageLevel,
    note: S,
    span: &Span,
    label: T,
) -> Message {
    Message(Arc::new(MessageX {
        level,
        note: note.into(),
        spans: vec![span.clone()],
        labels: vec![MessageLabel { span: span.clone(), note: label.into() }],
        help: None,
    }))
}

// Convenience functions

/// Bare note without any spans
pub fn note_bare<S: Into<String>>(note: S) -> Message {
    message_bare(MessageLevel::Note, note)
}

/// Basic note, with a message and a single span to be highlighted with ^^^^^^
pub fn note<S: Into<String>>(span: &Span, note: S) -> Message {
    message(MessageLevel::Note, note, span)
}

/// Bare warning without any spans
pub fn warning_bare<S: Into<String>>(note: S) -> Message {
    message_bare(MessageLevel::Warning, note)
}

/// Basic warning, with a message and a single span to be highlighted with ^^^^^^
pub fn warning<S: Into<String>>(span: &Span, note: S) -> Message {
    message(MessageLevel::Warning, note, span)
}

/// Bare error without any spans; use the builders below to add spans and labels
pub fn error_bare<S: Into<String>>(note: S) -> Message {
    message_bare(MessageLevel::Error, note)
}

/// Basic error, with a message and a single span to be highlighted with ^^^^^^
pub fn error<S: Into<String>>(span: &Span, note: S) -> Message {
    message(MessageLevel::Error, note, span)
}

/// Prepend the error with "Verus Internal Error"
/// Helpful for distinguishing user errors from Verus bugs.
pub fn internal_error<S: Into<String>>(span: &Span, note: S) -> Message {
    let msg = format!("Verus Internal Error: {:}", note.into());
    message(MessageLevel::Error, msg, span)
}

/// Error message with a span to be highlighted with ^^^^^^, and a label for that span
pub fn error_with_label<S: Into<String>, T: Into<String>>(
    span: &Span,
    note: S,
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
        Message(Arc::new(e))
    }

    /// Add a new primary span with a label (rendered with ^^^^^^)
    pub fn primary_label<S: Into<String>>(&self, span: &Span, label: S) -> Message {
        let mut e = self.clone();
        e.spans.push(span.clone());
        e.labels.push(MessageLabel { span: span.clone(), note: label.into() });
        Message(Arc::new(e))
    }

    /// Add a secondary_span to be highlighted, with no label (rendered with ------)
    pub fn secondary_span(&self, span: &Span) -> Message {
        let mut e = self.clone();
        e.labels.push(MessageLabel { span: span.clone(), note: "".to_string() });
        Message(Arc::new(e))
    }

    /// Add a secondary_span to be highlighted, with a label (rendered with ------)
    pub fn secondary_label<S: Into<String>>(&self, span: &Span, label: S) -> Message {
        let mut e = self.clone();
        e.labels.push(MessageLabel { span: span.clone(), note: label.into() });
        Message(Arc::new(e))
    }

    pub fn help(&self, help: impl Into<String>) -> Message {
        let MessageX { level, note, spans, labels, help: _ } = &self;
        Message(Arc::new(MessageX {
            level: *level,
            note: note.clone(),
            spans: spans.clone(),
            labels: labels.clone(),
            help: Some(help.into()),
        }))
    }
}
