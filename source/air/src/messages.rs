use serde::{Deserialize, Serialize};

pub trait Message: std::fmt::Debug + Clone {
    type MessageLabel: std::fmt::Debug + Clone + Serialize + for<'de> Deserialize<'de>;

    fn empty() -> Self;
    fn label_from_air_span(air_span: &str, note: &str) -> Self::MessageLabel;
    fn all_msgs(&self) -> Vec<String>;
    fn bare(level: MessageLevel, notes: &str) -> Self;
    fn unexpected_z3_version(expected: &str, found: &str) -> Self;
    fn get_note(&self) -> &str;
    fn get_label_note(message_label: &Self::MessageLabel) -> &str;
    fn from_labels(labels: &Vec<Self::MessageLabel>) -> Self;
    fn append_labels(&self, labels: &Vec<Self::MessageLabel>) -> Self;
}

#[derive(Debug, Serialize, Deserialize, Clone, Copy, PartialEq, Eq)]
pub enum MessageLevel {
    Error,
    Warning,
    Note,
}

pub trait Diagnostics<Message> {
    /// Display the corresponding message
    fn report(&self, msg: &Message);

    /// Immediately display the message, regardless of which module is currently printing
    fn report_now(&self, msg: &Message);

    /// Override the msg's reporting level
    fn report_as(&self, msg: &Message, msg_as: MessageLevel);

    /// Override the msg's reporting level and immediately display the message
    fn report_as_now(&self, msg: &Message, msg_as: MessageLevel);
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AirSpan {
    pub as_string: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AirMessageLabel {
    pub span: AirSpan,
    pub note: String,
}

/// Very simple implementation of Diagnostics for use in AIR
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AirMessage {
    pub level: MessageLevel,
    pub note: String,
    pub span: Option<AirSpan>,
    pub labels: Vec<AirMessageLabel>,
}

impl Message for AirMessage {
    type MessageLabel = AirMessageLabel;

    fn empty() -> Self {
        Self { level: MessageLevel::Error, labels: Vec::new(), note: "".to_owned(), span: None }
    }

    fn all_msgs(&self) -> Vec<String> {
        Some(self.note.clone())
            .into_iter()
            .chain(self.labels.iter().map(|l| l.note.clone()))
            .collect()
    }

    fn bare(level: MessageLevel, msg: &str) -> Self {
        Self { level, note: msg.to_owned(), labels: Vec::new(), span: None }
    }

    fn unexpected_z3_version(expected: &str, found: &str) -> Self {
        Self {
            level: MessageLevel::Error,
            note: format!("expected z3 version {expected}, found {found}"),
            labels: Vec::new(),
            span: None,
        }
    }

    fn get_label_note(message_label: &AirMessageLabel) -> &str {
        &message_label.note
    }

    fn append_labels(&self, labels: &Vec<AirMessageLabel>) -> Self {
        let mut m = self.clone();
        for l in labels {
            m.labels.push(l.clone());
        }
        m
    }

    fn get_note(&self) -> &str {
        &self.note
    }

    fn label_from_air_span(air_span: &str, note: &str) -> Self::MessageLabel {
        AirMessageLabel { span: AirSpan { as_string: air_span.to_owned() }, note: note.to_owned() }
    }

    fn from_labels(labels: &Vec<Self::MessageLabel>) -> Self {
        if labels.len() == 0 {
            Self::empty()
        } else {
            let AirMessageLabel { span, note } = labels[0].clone();
            AirMessage {
                span: Some(span),
                level: MessageLevel::Error,
                note: note.clone(),
                labels: labels[1..].to_vec(),
            }
        }
    }
}

pub struct Reporter {}

impl Diagnostics<AirMessage> for Reporter {
    fn report_as(&self, msg: &AirMessage, level: MessageLevel) {
        use MessageLevel::*;
        match level {
            Note => println!("Note: {}", msg.note),
            Warning => println!("Warning: {}", msg.note),
            Error => eprintln!("Error: {}", msg.note),
        }
    }

    fn report(&self, msg: &AirMessage) {
        self.report_as(msg, msg.level)
    }

    fn report_now(&self, msg: &AirMessage) {
        self.report_as(msg, msg.level)
    }

    fn report_as_now(&self, msg: &AirMessage, msg_as: MessageLevel) {
        self.report_as(msg, msg_as)
    }
}
