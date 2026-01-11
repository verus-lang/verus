macro_rules! info {
    ($($arg:tt)*) => {{
        use yansi::Paint;
        use crate::VARGO_NEST;
        let vargo_nest = *VARGO_NEST.read().unwrap();
        eprintln!(
            "{}{}",
            format!("vargo info [{vargo_nest}]: ").blue().bold(),
            format!($($arg)*).blue()
        )
    }};
}

macro_rules! warning {
    ($($arg:tt)*) => {{
        use yansi::Paint;
        use crate::VARGO_NEST;
        let vargo_nest = *VARGO_NEST.read().unwrap();
        eprintln!(
            "{}{}",
            format!("vargo warn [{vargo_nest}]: ").yellow().bold(),
            format!($($arg)*).yellow()
        )
    }};
}

pub(crate) use info;
pub(crate) use warning;
