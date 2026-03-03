use crate::algorithm::Printer;
use verus_syn::Lifetime;

impl Printer {
    pub fn lifetime(&mut self, lifetime: &Lifetime) {
        self.word("'");
        self.ident(&lifetime.ident);
    }
}
