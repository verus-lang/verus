pub use air::messages::MessageLevel;
use air::messages::{ArcDynMessage, ArcDynMessageLabel};
use serde::{Deserialize, Serialize};
use std::{any::Any, sync::Arc};

fn empty_raw_span() -> RawSpan {
    Arc::new(())
}

pub type RawSpan =
    Arc<dyn std::any::Any + std::marker::Sync + std::marker::Send + std::panic::RefUnwindSafe>;
pub type AstId = u64;
#[derive(Clone, Serialize, Deserialize)] // for Debug, see ast_util
pub struct Span {
    #[serde(skip)]
    #[serde(default = "crate::messages::empty_raw_span")]
    pub raw_span: RawSpan,
    pub id: AstId, // arbitrary integer identifier that may be set and used in any way (e.g. as unique id, or just left as 0)
    pub data: Vec<u64>, // arbitrary integers (e.g. for serialization/deserialization)
    pub as_string: String, // if we can't print (description, raw_span), print as_string instead
}

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Span")
            .field("raw_span", &"ANY")
            .field("id", &self.id)
            .field("data", &self.data)
            .field("as_string", &self.as_string)
            .finish()
    }
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

pub type Message = Arc<MessageX>;

pub trait ToAny {
    fn to_any(self) -> Arc<dyn Any + Send + Sync>;
}

impl ToAny for Message {
    fn to_any(self) -> Arc<dyn Any + Send + Sync> {
        self
    }
}

impl ToAny for MessageLabel {
    fn to_any(self) -> Arc<dyn Any + Send + Sync> {
        Arc::new(self)
    }
}

pub struct VirMessageInterface {}

impl air::messages::MessageInterface for VirMessageInterface {
    fn empty(&self) -> ArcDynMessage {
        Arc::new(MessageX {
            level: MessageLevel::Error,
            note: "".to_owned(),
            spans: Vec::new(),
            labels: Vec::new(),
            help: None,
        })
    }

    fn all_msgs(&self, message: &ArcDynMessage) -> Vec<String> {
        let message: &MessageX =
            message.downcast_ref().expect("unexpected value in Any -> Message conversion");
        Some(message.note.clone())
            .into_iter()
            .chain(message.labels.iter().map(|l| l.note.clone()))
            .collect()
    }

    fn bare(&self, level: MessageLevel, note: &str) -> ArcDynMessage {
        Arc::new(MessageX {
            level,
            note: note.to_owned(),
            spans: Vec::new(),
            labels: Vec::new(),
            help: None,
        })
    }

    fn unexpected_z3_version(&self, expected: &str, found: &str) -> ArcDynMessage {
        Arc::new(MessageX {
            level: MessageLevel::Error,
            note: format!("expected z3 version {expected}, found {found}"),
            labels: Vec::new(),
            spans: Vec::new(),
            help: None,
        })
    }

    fn get_note<'b>(&self, message: &'b ArcDynMessage) -> &'b str {
        let message: &MessageX =
            message.downcast_ref().expect("unexpected value in Any -> Message conversion");
        &message.note
    }

    fn get_message_label_note<'b>(&self, message_label: &'b ArcDynMessageLabel) -> &'b str {
        let message_label: &MessageLabel =
            message_label.downcast_ref().expect("unexpected value in Any -> Message conversion");
        &message_label.note
    }

    fn append_labels(
        &self,
        message: &ArcDynMessage,
        labels: &Vec<ArcDynMessageLabel>,
    ) -> ArcDynMessage {
        let message: &MessageX =
            message.downcast_ref().expect("unexpected value in Any -> Message conversion");
        let mut s = message.clone();
        s.labels.extend(
            labels
                .iter()
                .map(|l| l.downcast_ref().expect("unexpected value in Any -> Message conversion"))
                .cloned(),
        );
        Arc::new(s)
    }

    fn message_label_from_air_span(&self, air_span: &str, note: &str) -> ArcDynMessageLabel {
        Arc::new(MessageLabel {
            span: Span {
                raw_span: Arc::new(()),
                id: 0,
                data: Vec::new(),
                as_string: air_span.to_owned(),
            },
            note: note.to_owned(),
        })
    }

    fn from_labels(&self, labels: &Vec<ArcDynMessageLabel>) -> ArcDynMessage {
        if labels.len() == 0 {
            self.empty()
        } else {
            let MessageLabel { span, note } =
                labels[0].downcast_ref::<MessageLabel>().unwrap().clone();
            Arc::new(MessageX {
                level: MessageLevel::Error,
                note,
                spans: vec![span],
                labels: labels[1..]
                    .iter()
                    .map(|l| {
                        l.downcast_ref().expect("unexpected value in Any -> Message conversion")
                    })
                    .cloned()
                    .collect(),
                help: None,
            })
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
