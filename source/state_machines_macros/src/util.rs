use syn::Error;

// If there is at least one error, combine them all into one
// Else, return Ok(())

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

pub fn combine_results(errors: Vec<syn::parse::Result<()>>) -> syn::parse::Result<()> {
    combine_errors_or_ok(
        errors
            .iter()
            .filter_map(|res| match res {
                Ok(_) => None,
                Err(e) => Some(e.clone()),
            })
            .collect(),
    )
}
