use syn::Error;

pub fn combine_errors_or_ok(errors: Vec<Error>) -> syn::parse::Result<()> {
    let mut res = Ok(());
    for e in errors {
        match res {
            Ok(()) => {
                res = Err(e);
            }
            Err(e0) => {
                let mut e0 = e0;
                e0.combine(e);
                res = Err(e0);
            }
        }
    }
    res
}
