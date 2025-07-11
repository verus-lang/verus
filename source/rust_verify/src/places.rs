use vir::ast::*;

pub fn expr_to_place_for_mut_ref(e: &Expr) -> Result<Place, VirErr> {
    match &e.x {
        ExprX::Var(ident) => Ok(SpannedTyped::new(&e.span, &e.typ, PlaceX::Local(ident.clone()))),
        ExprX::DerefMut(arg) => {
            match &arg.x {
                ExprX::BorrowMut(place) => {
                    // `* &mut _` cancels out.
                    // It's also pretty common, so it's worth checking for to avoid cluttering
                    // the VIR. (Note that the other direction, `&mut * _` does NOT cancel out;
                    // this is a reborrow.)
                    Ok(place.clone())
                }
                _ => {
                    let p = expr_to_place_for_mut_ref(arg)?;
                    Ok(SpannedTyped::new(&e.span, &e.typ, PlaceX::DerefMut(p)))
                }
            }
        }
        ExprX::UnaryOpr(UnaryOpr::Field(opr), arg) => {
            let p = expr_to_place_for_mut_ref(arg)?;
            Ok(SpannedTyped::new(&e.span, &e.typ, PlaceX::Field(opr.clone(), p)))
        }
        _ => {
            dbg!(&e.x);
            Err(vir::messages::error(
                &e.span,
                "Not supported: this kind of expression in a place expression",
            ))
        }
    }
}
