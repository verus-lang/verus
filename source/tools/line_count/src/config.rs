pub struct Config {
    pub print_all: bool,
    pub json: bool,
    pub no_external_by_default: bool,
    pub delimiters_are_layout: bool,
    pub proofs_arent_trusted: bool,
}

pub enum RunMode<'a> {
    DepsPath(&'a std::path::Path),
    OneFile(&'a std::path::Path),
}
