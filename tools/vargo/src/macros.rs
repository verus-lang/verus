macro_rules! info {
    ($($arg:tt)*) => {{
        use yansi::Paint;
        eprintln!(
            "{}{}",
            format!("vargo info: ").blue().bold(),
            format!($($arg)*).blue()
        )
    }};
}

macro_rules! warning {
    ($($arg:tt)*) => {{
        use yansi::Paint;
        eprintln!(
            "{}{}",
            format!("vargo warn: ").yellow().bold(),
            format!($($arg)*).yellow()
        )
    }};
}

pub(crate) use info;
pub(crate) use warning;
