use air::ast::Span;
use std::rc::Rc;

#[derive(Debug)]
pub struct Spanned<X> {
    pub span: Span,
    pub x: X,
}

impl<X> Spanned<X> {
    pub fn new(span: Span, x: X) -> Rc<Spanned<X>> {
        Rc::new(Spanned { span: span, x: x })
    }
}
