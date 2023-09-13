use std::{any::Any, sync::Arc};

use serde::{Deserialize, Serialize};

pub trait MessageInterface {
    fn empty(&self) -> Arc<dyn Any + Send + Sync>;
    fn message_label_from_air_span(&self, air_span: &str, note: &str)
    -> Arc<dyn Any + Send + Sync>;
    fn all_msgs(&self, message: &Arc<dyn Any + Send + Sync>) -> Vec<String>;
    fn bare(&self, level: MessageLevel, notes: &str) -> Arc<dyn Any + Send + Sync>;
    fn unexpected_z3_version(&self, expected: &str, found: &str) -> Arc<dyn Any + Send + Sync>;
    fn get_note<'b>(&self, message: &'b Arc<dyn Any + Send + Sync>) -> &'b str;
    fn from_labels(&self, labels: &Vec<Arc<dyn Any + Send + Sync>>) -> Arc<dyn Any + Send + Sync>;
    fn append_labels(
        &self,
        message: &Arc<dyn Any + Send + Sync>,
        labels: &Vec<Arc<dyn Any + Send + Sync>>,
    ) -> Arc<dyn Any + Send + Sync>;
    fn get_message_label_note<'b>(&self, message_label: &'b Arc<dyn Any + Send + Sync>) -> &'b str;
}

#[derive(Debug, Serialize, Deserialize, Clone, Copy, PartialEq, Eq)]
pub enum MessageLevel {
    Error,
    Warning,
    Note,
}

pub trait Diagnostics {
    /// Display the corresponding message
    fn report(&self, msg: &Arc<dyn Any + Send + Sync>);

    /// Immediately display the message, regardless of which module is currently printing
    fn report_now(&self, msg: &Arc<dyn Any + Send + Sync>);

    /// Override the msg's reporting level
    fn report_as(&self, msg: &Arc<dyn Any + Send + Sync>, msg_as: MessageLevel);

    /// Override the msg's reporting level and immediately display the message
    fn report_as_now(&self, msg: &Arc<dyn Any + Send + Sync>, msg_as: MessageLevel);
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

pub struct AirMessageInterface {}

impl MessageInterface for AirMessageInterface {
    fn empty(&self) -> Arc<dyn Any + Send + Sync> {
        Arc::new(Box::new(AirMessage {
            level: MessageLevel::Error,
            labels: Vec::new(),
            note: "".to_owned(),
            span: None,
        }))
    }

    fn all_msgs(&self, message: &Arc<dyn Any + Send + Sync>) -> Vec<String> {
        let message = message.downcast_ref::<AirMessage>().unwrap();
        Some(message.note.clone())
            .into_iter()
            .chain(message.labels.iter().map(|l| l.note.clone()))
            .collect()
    }

    fn bare(&self, level: MessageLevel, msg: &str) -> Arc<dyn Any + Send + Sync> {
        Arc::new(Box::new(AirMessage {
            level,
            note: msg.to_owned(),
            labels: Vec::new(),
            span: None,
        }))
    }

    fn unexpected_z3_version(&self, expected: &str, found: &str) -> Arc<dyn Any + Send + Sync> {
        Arc::new(Box::new(AirMessage {
            level: MessageLevel::Error,
            note: format!("expected z3 version {expected}, found {found}"),
            labels: Vec::new(),
            span: None,
        }))
    }

    fn get_message_label_note<'b>(&self, message_label: &'b Arc<dyn Any + Send + Sync>) -> &'b str {
        let message_label = message_label.downcast_ref::<AirMessageLabel>().unwrap();
        &message_label.note
    }

    fn append_labels(
        &self,
        message: &Arc<dyn Any + Send + Sync>,
        labels: &Vec<Arc<dyn Any + Send + Sync>>,
    ) -> Arc<dyn Any + Send + Sync> {
        let message = message.downcast_ref::<AirMessage>().unwrap();
        let mut m = message.clone();
        for l in labels {
            let l = l.downcast_ref::<AirMessageLabel>().unwrap().clone();
            m.labels.push(l.clone());
        }
        Arc::new(Box::new(m))
    }

    fn get_note<'b>(&self, message: &'b Arc<dyn Any + Send + Sync>) -> &'b str {
        let message = message.downcast_ref::<AirMessage>().unwrap();
        &message.note
    }

    fn message_label_from_air_span(
        &self,
        air_span: &str,
        note: &str,
    ) -> Arc<dyn Any + Send + Sync> {
        Arc::new(Box::new(AirMessageLabel {
            span: AirSpan { as_string: air_span.to_owned() },
            note: note.to_owned(),
        }))
    }

    fn from_labels(&self, labels: &Vec<Arc<dyn Any + Send + Sync>>) -> Arc<dyn Any + Send + Sync> {
        if labels.len() == 0 {
            Arc::new(Box::new(AirMessage {
                level: MessageLevel::Error,
                labels: Vec::new(),
                note: "".to_owned(),
                span: None,
            }))
        } else {
            let AirMessageLabel { span, note } =
                labels[0].downcast_ref::<AirMessageLabel>().unwrap().clone();
            Arc::new(Box::new(AirMessage {
                span: Some(span),
                level: MessageLevel::Error,
                note: note.clone(),
                labels: labels[1..]
                    .iter()
                    .map(|l| l.downcast_ref::<AirMessageLabel>().unwrap().clone())
                    .collect(),
            }))
        }
    }
}

pub struct Reporter {}

impl Diagnostics for Reporter {
    fn report_as(&self, msg: &Arc<dyn Any + Send + Sync>, level: MessageLevel) {
        let msg = msg.downcast_ref::<AirMessage>().unwrap();
        use MessageLevel::*;
        match level {
            Note => println!("Note: {}", msg.note),
            Warning => println!("Warning: {}", msg.note),
            Error => eprintln!("Error: {}", msg.note),
        }
    }

    fn report(&self, msg: &Arc<dyn Any + Send + Sync>) {
        let air_msg = msg.downcast_ref::<AirMessage>().unwrap();
        self.report_as(msg, air_msg.level)
    }

    fn report_now(&self, msg: &Arc<dyn Any + Send + Sync>) {
        let air_msg = msg.downcast_ref::<AirMessage>().unwrap();
        self.report_as(msg, air_msg.level)
    }

    fn report_as_now(&self, msg: &Arc<dyn Any + Send + Sync>, msg_as: MessageLevel) {
        self.report_as(msg, msg_as)
    }
}
