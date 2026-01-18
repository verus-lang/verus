use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use proc_macro::TokenStream;
use proc_macro2::{Group, Span, TokenStream as TokenStream2, TokenTree};
use quote::{quote, quote_spanned};
use verus_syn::parse::{Parse, ParseStream};
use verus_syn::spanned::Spanned;
use verus_syn::token::Comma;
use verus_syn::{
    Arm, AttrStyle, Attribute, BinOp, Block, Error, Expr, ExprBinary, ExprClosure, ExprMatches,
    ExprPath, Fields, FnArgKind, FnMode, GenericArgument, Ident, Index, Item, ItemEnum, ItemFn,
    ItemStruct, Lit, MatchesOpExpr, MatchesOpToken, Member, Meta, Pat, PatType, Path,
    PathArguments, PathSegment, ReturnType, Stmt, Type, UnOp, Visibility, parse_macro_input,
};

/// Checks if the given path is of the form
/// `idents[0]::idents[1]::...::idents[n]`,
/// ignoring any path arguments.
fn is_path_eq(path: &Path, idents: &[&str]) -> bool {
    if path.segments.len() != idents.len() {
        return false;
    }
    for (seg, id) in path.segments.iter().zip(idents) {
        if seg.ident != id {
            return false;
        }
    }
    true
}

/// Gets the n-th (angle-bracket) argument as a type.
fn get_seg_type_arg(seg: &PathSegment, n: usize) -> Result<&Type, Error> {
    match &seg.arguments {
        PathArguments::AngleBracketed(args) if n < args.args.len() => {
            if let GenericArgument::Type(typ) = &args.args[n] {
                Ok(typ)
            } else {
                Err(Error::new_spanned(&args.args[n], "expected type argument"))
            }
        }
        _ => Err(Error::new_spanned(seg, "expected type argument")),
    }
}

/// A simple pattern is either a variable (`a`) or a typed variable (`a: T`).
fn get_simple_pat(pat: &Pat) -> Result<(&Ident, Option<Box<Type>>), Error> {
    if let Pat::Ident(pat_ident) = pat {
        return Ok((&pat_ident.ident, None));
    }
    if let Pat::Type(PatType { pat, ty, .. }) = pat {
        if let Pat::Ident(pat_ident) = pat.as_ref() {
            return Ok((&pat_ident.ident, Some(ty.clone())));
        }
    }

    Err(Error::new_spanned(pat, "expect a simple pattern (variable or typed variable)"))
}

/// Appends a `prefix` to the n-th segment of the path.
fn prefix_nth_segment(path: &Path, prefix: &str, n: usize) -> Result<Path, Error> {
    if n >= path.segments.len() {
        return Err(Error::new_spanned(path, "path too short"));
    }

    let seg = &path.segments[n];
    let mut new_path = path.clone();

    new_path.segments[n] = PathSegment {
        ident: Ident::new(&format!("{}{}", prefix, seg.ident), seg.ident.span()),
        arguments: seg.arguments.clone(),
    };

    Ok(new_path)
}

/// Custom parser for a list of items.
struct Items(Vec<Item>);

impl Parse for Items {
    fn parse(input: ParseStream) -> verus_syn::parse::Result<Items> {
        let mut items = Vec::new();
        while !input.is_empty() {
            items.push(input.parse()?);
        }
        Ok(Items(items))
    }
}

/// Custom parser for a comma-separated list of expressions.
struct Exprs(Vec<Expr>);

impl Parse for Exprs {
    fn parse(input: ParseStream) -> verus_syn::parse::Result<Exprs> {
        let mut exprs = Vec::new();
        while !input.is_empty() {
            exprs.push(input.parse()?);
            if input.peek(Comma) {
                input.parse::<Comma>()?;
            }
        }
        Ok(Exprs(exprs))
    }
}

#[derive(Clone, Copy, Debug)]
enum TypeKind {
    Owned,
    Ref,
}

/// Converts a spec type to exec type via `<T as ExecSpecType>::Exec`.
fn compile_type(typ: &Type, ctx: TypeKind) -> Result<TokenStream2, Error> {
    let span = typ.span();
    match typ {
        // Treat Seq<T> as a special case since
        // we don't implement ExecSpecType for it (to avoid
        // conflicting with SpecString)
        Type::Path(type_path) => {
            #[allow(clippy::cmp_owned)] // There is no other way to compare an Ident
            if type_path.path.segments.len() == 1 {
                if type_path.path.segments[0].ident.to_string() == "Seq" {
                    let type_arg = get_seg_type_arg(&type_path.path.segments[0], 0)?;
                    let param = compile_type(type_arg, TypeKind::Owned)?;
                    return match ctx {
                        TypeKind::Owned => Ok(quote_spanned! { span => Vec<#param> }),
                        TypeKind::Ref => Ok(quote_spanned! { span => &[#param] }),
                    };
                } else if type_path.path.segments[0].ident.to_string() == "Option" {
                    // TODO: implement ExecSpecType for Option<T> so that
                    // we don't need this special case
                    let type_arg = get_seg_type_arg(&type_path.path.segments[0], 0)?;
                    let param = compile_type(type_arg, TypeKind::Owned)?;
                    return match ctx {
                        TypeKind::Owned => Ok(quote_spanned! { span => Option<#param> }),
                        TypeKind::Ref => Ok(quote_spanned! { span => &Option<#param> }),
                    };
                }
            }
        }

        // Treat tuples as special case since we
        // can't enumerate all possible impls for them
        Type::Tuple(type_tuple) => {
            let types = type_tuple
                .elems
                .iter()
                .map(|ty| compile_type(ty, TypeKind::Owned))
                .collect::<Result<Vec<_>, Error>>()?;
            return match ctx {
                TypeKind::Owned => Ok(quote_spanned! { span => (#(#types,)*) }),
                TypeKind::Ref => Ok(quote_spanned! { span => &(#(#types,)*) }),
            };
        }

        _ => {}
    }

    // Otherwise we assume that the type has
    // ExecSpecType implemented
    Ok(match ctx {
        TypeKind::Owned => {
            quote_spanned! { span => <#typ as vstd::contrib::exec_spec::ExecSpecType>::ExecOwnedType }
        }
        TypeKind::Ref => {
            quote_spanned! { span => <#typ as vstd::contrib::exec_spec::ExecSpecType>::ExecRefType<'_> }
        }
    })
}

/// Compiles a struct item.
fn compile_struct(item_struct: &ItemStruct) -> Result<TokenStream2, Error> {
    if !item_struct.generics.params.is_empty() {
        return Err(Error::new_spanned(&item_struct.generics, "generics not supported"));
    }

    let spec_name = &item_struct.ident;
    let exec_name: Ident = Ident::new(&format!("Exec{}", item_struct.ident), item_struct.span());

    // Generate the fields
    let exec_fields = match &item_struct.fields {
        Fields::Named(fields_named) => {
            let span = fields_named.span();
            let fields = fields_named
                .named
                .iter()
                .map(|field| {
                    let vis = &field.vis;
                    let field_name = field.ident.as_ref().unwrap();
                    let field_type = compile_type(&field.ty, TypeKind::Owned)?;
                    let span = field.span();
                    Ok(quote_spanned! { span => #vis #field_name: #field_type })
                })
                .collect::<Result<Vec<_>, Error>>()?;

            quote_spanned! { span => { #(#fields,)* } }
        }
        Fields::Unnamed(fields_unnamed) => {
            let span = fields_unnamed.span();
            let fields = fields_unnamed
                .unnamed
                .iter()
                .map(|field| {
                    let vis = &field.vis;
                    let field_type = compile_type(&field.ty, TypeKind::Owned)?;
                    let span = field.span();
                    Ok(quote_spanned! { span => #vis #field_type })
                })
                .collect::<Result<Vec<_>, Error>>()?;

            quote_spanned! { span => ( #(#fields,)* ) ; }
        }
        Fields::Unit => {
            let span = item_struct.span();
            quote_spanned! { span => ; }
        }
    };

    // Generate the body of fn view
    let view_body = match &item_struct.fields {
        Fields::Named(fields_named) => {
            let span = fields_named.span();
            let field_views = fields_named.named.iter().map(|field| {
                let field_name = &field.ident;
                let span = field.span();
                quote_spanned! { span => #field_name: self.#field_name.deep_view() }
            });

            quote_spanned! { span => #spec_name { #(#field_views,)* } }
        }
        Fields::Unnamed(fields_unnamed) => {
            let span = fields_unnamed.span();
            let field_views = fields_unnamed.unnamed.iter().enumerate().map(|(i, field)| {
                let i = Index::from(i);
                let span = field.span();
                quote_spanned! { span => self.#i.deep_view() }
            });

            quote_spanned! { span => #spec_name(#(#field_views,)*) }
        }
        Fields::Unit => {
            let span = item_struct.span();
            quote_spanned! { span => #spec_name }
        }
    };

    // Generate body of the DeepViewClone impl
    let clone_body = match &item_struct.fields {
        Fields::Named(fields_named) => {
            let span = fields_named.span();
            let field_views = fields_named.named.iter().map(|field| {
                let field_name = &field.ident;
                let span = field.span();
                quote_spanned! { span => #field_name: self.#field_name.deep_clone() }
            });

            quote_spanned! { span => #exec_name { #(#field_views,)* } }
        }
        Fields::Unnamed(fields_unnamed) => {
            let span = fields_unnamed.span();
            let field_views = fields_unnamed.unnamed.iter().enumerate().map(|(i, field)| {
                let i = Index::from(i);
                let span = field.span();
                quote_spanned! { span => self.#i.deep_clone() }
            });

            quote_spanned! { span => #exec_name(#(#field_views,)*) }
        }
        Fields::Unit => {
            let span = item_struct.span();
            quote_spanned! { span => #exec_name }
        }
    };

    let vis = &item_struct.vis;

    // Only open the view if the struct and all fields are public
    let span = item_struct.vis.span();
    let open_or_close = if let Visibility::Public(..) = item_struct.vis {
        if item_struct
            .fields
            .iter()
            .all(|field| if let Visibility::Public(..) = field.vis { true } else { false })
        {
            quote_spanned! { span => open }
        } else {
            quote_spanned! { span => closed }
        }
    } else {
        quote_spanned! { span => closed }
    };

    let span = item_struct.span();
    Ok(quote_spanned! { span =>
        #[verifier::ext_equal]
        #item_struct

        #vis struct #exec_name #exec_fields

        impl vstd::contrib::exec_spec::ExecSpecType for #spec_name {
            type ExecOwnedType = #exec_name;
            type ExecRefType<'a> = &'a #exec_name;
        }

        impl<'a> vstd::contrib::exec_spec::ToRef<&'a #exec_name> for &'a #exec_name {
            fn get_ref(self) -> &'a #exec_name {
                self
            }
        }

        impl<'a> vstd::contrib::exec_spec::ToOwned<#exec_name> for &'a #exec_name {
            fn get_owned(self) -> #exec_name {
                self.deep_clone()
            }
        }

        impl DeepView for #exec_name {
            type V = #spec_name;

            #open_or_close
            spec fn deep_view(&self) -> #spec_name {
                #view_body
            }
        }

        impl vstd::contrib::exec_spec::DeepViewClone for #exec_name {
            fn deep_clone(&self) -> Self {
                #clone_body
            }
        }
    })
}

/// Compiles an enum item.
fn compile_enum(item_enum: &ItemEnum) -> Result<TokenStream2, Error> {
    if !item_enum.generics.params.is_empty() {
        return Err(Error::new_spanned(&item_enum.generics, "generics not supported"));
    }

    let spec_name = &item_enum.ident;
    let exec_name: Ident = Ident::new(&format!("Exec{}", item_enum.ident), item_enum.span());

    // Compile the type of each variant
    let exec_variants = item_enum
        .variants
        .iter()
        .map(|variant| {
            let name = &variant.ident;

            Ok(match &variant.fields {
                Fields::Named(fields_named) => {
                    let span = fields_named.span();
                    let fields = fields_named
                        .named
                        .iter()
                        .map(|field| {
                            let field_name = field.ident.as_ref().unwrap();
                            let typ = compile_type(&field.ty, TypeKind::Owned)?;
                            let span = field.span();
                            Ok(quote_spanned! { span => #field_name: #typ })
                        })
                        .collect::<Result<Vec<_>, Error>>()?;

                    quote_spanned! { span =>
                        #name {
                            #(#fields,)*
                        }
                    }
                }
                Fields::Unnamed(fields_unnamed) => {
                    let fields = fields_unnamed
                        .unnamed
                        .iter()
                        .map(|field| compile_type(&field.ty, TypeKind::Owned))
                        .collect::<Result<Vec<_>, Error>>()?;
                    let span = fields_unnamed.span();
                    quote_spanned! { span =>
                        #name(#(#fields,)*)
                    }
                }
                Fields::Unit => {
                    let span = variant.span();
                    quote_spanned! { span => #name }
                }
            })
        })
        .collect::<Result<Vec<_>, Error>>()?;

    // Match arms in the DeepView implementation
    let deep_view_variant_arms = item_enum.variants.iter()
        .map(|variant| {
            let variant_name = &variant.ident;

            // Generate match arms for each variant
            match &variant.fields {
                Fields::Named(fields_named) => {
                    let span = fields_named.span();
                    let field_names = fields_named.named.iter().map(|field| &field.ident);
                    let field_views = fields_named.named.iter().map(|field| {
                        let field_name = &field.ident;
                        let span = field.span();
                        quote_spanned! { span => #field_name: #field_name.deep_view() }
                    });

                    quote_spanned! { span => #exec_name::#variant_name { #(#field_names,)* } => #spec_name::#variant_name { #(#field_views,)* } }
                }
                Fields::Unnamed(fields_unnamed) => {
                    let span = fields_unnamed.span();
                    let field_names = fields_unnamed.unnamed.iter()
                        .enumerate()
                        .map(|(i, field)| Ident::new(&format!("f{}", i), field.span()))
                        .collect::<Vec<_>>();

                    let field_views = fields_unnamed.unnamed.iter().enumerate().map(|(i, field)| {
                        let field_name = &field_names[i];
                        let span = field.span();
                        quote_spanned! { span => #field_name.deep_view() }
                    });

                    quote_spanned! { span => #exec_name::#variant_name(#(#field_names,)*) => #spec_name::#variant_name(#(#field_views,)*) }
                }
                Fields::Unit => {
                    let span = variant.span();
                    quote_spanned! { span =>
                        #exec_name::#variant_name => #spec_name::#variant_name
                    }
                }
            }
        });

    // Match arms in the DeepViewClone implementation
    let clone_variant_arms = item_enum.variants.iter()
        .map(|variant| {
            let variant_name = &variant.ident;

            // Generate match arms for each variant
            match &variant.fields {
                Fields::Named(fields_named) => {
                    let span = fields_named.span();
                    let field_names = fields_named.named.iter().map(|field| &field.ident);
                    let field_views = fields_named.named.iter().map(|field| {
                        let field_name = &field.ident;
                        let span = field.span();
                        quote_spanned! { span => #field_name: #field_name.deep_clone() }
                    });

                    quote_spanned! { span => #exec_name::#variant_name { #(#field_names,)* } => #exec_name::#variant_name { #(#field_views,)* } }
                }
                Fields::Unnamed(fields_unnamed) => {
                    let span = fields_unnamed.span();
                    let field_names = fields_unnamed.unnamed.iter()
                        .enumerate()
                        .map(|(i, field)| Ident::new(&format!("f{}", i), field.span()))
                        .collect::<Vec<_>>();

                    let field_views = fields_unnamed.unnamed.iter().enumerate().map(|(i, field)| {
                        let field_name = &field_names[i];
                        let span = field.span();
                        quote_spanned! { span => #field_name.deep_clone() }
                    });

                    quote_spanned! { span => #exec_name::#variant_name(#(#field_names,)*) => #exec_name::#variant_name(#(#field_views,)*) }
                }
                Fields::Unit => {
                    let span = variant.span();
                    quote_spanned! { span =>
                        #exec_name::#variant_name => #exec_name::#variant_name
                    }
                }
            }
        });

    let vis = &item_enum.vis;

    let span = item_enum.vis.span();
    let open_or_close = if let Visibility::Public(..) = item_enum.vis {
        quote_spanned! { span => open }
    } else {
        quote_spanned! { span => closed }
    };

    let span = item_enum.span();
    Ok(quote_spanned! { span =>
        #[verifier::ext_equal]
        #item_enum

        #vis enum #exec_name {
            #(#exec_variants,)*
        }

        impl vstd::contrib::exec_spec::ExecSpecType for #spec_name {
            type ExecOwnedType = #exec_name;
            type ExecRefType<'a> = &'a #exec_name;
        }

        impl<'a> vstd::contrib::exec_spec::ToRef<&'a #exec_name> for &'a #exec_name {
            fn get_ref(self) -> &'a #exec_name {
                self
            }
        }

        impl<'a> vstd::contrib::exec_spec::ToOwned<#exec_name> for &'a #exec_name {
            fn get_owned(self) -> #exec_name {
                self.deep_clone()
            }
        }

        impl DeepView for #exec_name {
            type V = #spec_name;

            #open_or_close
            spec fn deep_view(&self) -> #spec_name {
                match self {
                    #(#deep_view_variant_arms,)*
                }
            }
        }

        impl vstd::contrib::exec_spec::DeepViewClone for #exec_name {
            fn deep_clone(&self) -> Self {
                match self {
                    #(#clone_variant_arms,)*
                }
            }
        }
    })
}

/// Compiles a spec fn to the exec fn signature.
fn compile_sig(ctx: &mut LocalCtx, item_fn: &ItemFn) -> Result<TokenStream2, Error> {
    let spec_params = item_fn
        .sig
        .inputs
        .iter()
        .map(|param| {
            if let FnArgKind::Typed(pat_type) = &param.kind {
                let name = &pat_type.pat;
                let (name, _) = get_simple_pat(name)?;
                Ok((name, pat_type.ty.as_ref()))
            } else {
                Err(Error::new_spanned(param, "unsupported parameter type"))
            }
        })
        .collect::<Result<Vec<_>, Error>>()?;

    // Compile parameters
    let params = spec_params
        .iter()
        .map(|(name, typ)| {
            ctx.add((*name).clone(), VarMode::Ref);
            let typ = compile_type(typ, TypeKind::Ref)?;
            let span = name.span();
            Ok(quote_spanned! { span => #name: #typ })
        })
        .collect::<Result<Vec<_>, Error>>()?;

    // Compile return type
    let span = item_fn.sig.output.span();
    let ret_type = match &item_fn.sig.output {
        ReturnType::Default => quote_spanned! { span => () },
        ReturnType::Type(_, _, _, ty) => {
            let typ = compile_type(ty, TypeKind::Owned)?;
            quote_spanned! { span => #typ }
        }
    };

    let vis = &item_fn.vis;
    let spec_name = &item_fn.sig.ident;
    let exec_name = Ident::new(&format!("exec_{spec_name}"), spec_name.span());

    // Generate a specification stating that
    //   requires <recommends clause of spec_f>
    //   ensures result.deep_view() =~~= spec_f(x1.deep_view(), ..., xn.deep_view())
    //   decreases <decreases clause of spec_f>

    // Substitute each spec var with <exec_var>.deep_view()
    let bindings = spec_params
        .iter()
        .map(|(name, typ)| {
            let span = name.span();
            quote_spanned! { span =>
                let #name: #typ = #name.deep_view();
            }
        })
        .collect::<Vec<_>>();

    let span = item_fn.sig.spec.span();
    let mut requires = if let Some(recommends) = &item_fn.sig.spec.recommends {
        let requires = recommends.exprs.exprs.iter().map(|expr| {
            let span = expr.span();
            quote_spanned! { span =>
                ({ #(#bindings)* #expr })
            }
        });

        quote_spanned! { span =>
            #(#requires,)*
        }
    } else {
        quote_spanned! { span => true }
    };

    let decreases = if let Some(decreases) = &item_fn.sig.spec.decreases {
        let decrease_exprs = decreases.decreases.exprs.exprs.iter().map(|expr| {
            let span = expr.span();
            quote_spanned! { span =>
                ({ #(#bindings)* #expr })
            }
        });

        // When clauses are put into the requires clause
        // since it is only supported in spec mode
        if let Some((_, when_expr)) = &decreases.when {
            let span = when_expr.span();
            requires = quote_spanned! { span =>
                ({ #(#bindings)* #when_expr }), #requires
            };
        }

        if decreases.via.is_some() {
            return Err(Error::new_spanned(decreases, "via clause is not supported"));
        }

        quote_spanned! { span =>
            decreases #(#decrease_exprs),*
        }
    } else {
        quote_spanned! { span => }
    };

    let args_deep_view = spec_params.iter().map(|(name, _)| {
        let span = name.span();
        quote_spanned! { span => #name.deep_view() }
    });

    let ext_eq = BinOp::ExtDeepEq(Default::default());

    let span = item_fn.sig.span();
    let sig = quote_spanned! { span =>
        #vis fn #exec_name(
            #(#params,)*
        ) -> (res: #ret_type)
            requires #requires
            ensures res.deep_view() #ext_eq #spec_name(#(#args_deep_view),*)
            #decreases
    };

    // Set token's span to the original signature's span
    // e.g. this will forward all "failed post-condition"
    // errors to the signature
    Ok(respan(sig, item_fn.sig.span()))
}

/// Each variable is marked with a mode indicating
/// whether it is the owned or the borrowed version
/// of the spec type.
#[derive(Clone, Copy, Debug, PartialEq)]
enum VarMode {
    Owned,
    Ref,
}

/// Records the locals and their modes.
#[derive(Clone, Debug)]
struct LocalCtx {
    /// Name of the current spec function
    cur_fn: Ident,
    /// Mapping local variables to their modes
    vars: HashMap<Ident, VarMode>,
    /// A global counter for generating fresh trigger
    /// function names (unique per function).
    trigger_fns: Rc<RefCell<HashMap<Ident, Type>>>,
}

impl LocalCtx {
    fn new(cur_fn: &Ident) -> Self {
        LocalCtx {
            cur_fn: cur_fn.clone(),
            vars: HashMap::new(),
            trigger_fns: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn add(&mut self, ident: Ident, mode: VarMode) {
        self.vars.insert(ident, mode);
    }

    /// Generates a fresh trigger function name
    fn gen_fresh_trigger_fn(&self, typ: &Type) -> Ident {
        let idx = self.trigger_fns.borrow().len();
        let name = Ident::new(&format!("trigger_{}_{}", self.cur_fn, idx), Span::call_site());
        self.trigger_fns.borrow_mut().insert(name.clone(), typ.clone());
        name
    }
}

/// Maps a spec mode path to the corresponding exec mode path
/// Assuming that it is already checked that path is not a
/// local variable.
fn compile_pat_path(path: &Path) -> Result<Path, Error> {
    if path.segments.len() <= 2 {
        // Special case: do not change Some, None, Ok, Err
        if is_path_eq(path, &["Some"])
            || is_path_eq(path, &["None"])
            || is_path_eq(path, &["Ok"])
            || is_path_eq(path, &["Err"])
        {
            return Ok(path.clone());
        }

        // Assuming this is either a enum variant (length 2)
        // or struct name (length 1)
        prefix_nth_segment(path, "Exec", 0)
    } else {
        Err(Error::new_spanned(path, "unexpected path"))
    }
}

#[derive(Clone, Debug, PartialEq)]
enum ExprPathKind {
    Local(VarMode),
    FnName,
    StructOrEnum,
    Constant,
    Unknown,
}

/// Infers the kind of path based on context and the form of the path.
/// TODO: a bit ad-hoc
fn infer_expr_path_kind(ctx: &LocalCtx, path: &Path) -> ExprPathKind {
    if is_path_eq(path, &["Some"])
        || is_path_eq(path, &["None"])
        || is_path_eq(path, &["Ok"])
        || is_path_eq(path, &["Err"])
    {
        return ExprPathKind::StructOrEnum;
    }

    // e.g. usize::MAX, usize::MIN, ...
    if path.segments.len() == 2 {
        // Check if the last segment is all capital letters
        let all_capitals = path
            .segments
            .last()
            .as_ref()
            .unwrap()
            .ident
            .to_string()
            .chars()
            .all(|c| c.is_uppercase());

        let first_seg = path.segments[0].ident.to_string();

        if all_capitals {
            match first_seg.as_str() {
                "usize" | "u8" | "u16" | "u32" | "u64" | "u128" | "isize" | "i8" | "i16"
                | "i32" | "i64" | "i128" | "char" | "f32" | "f64" => return ExprPathKind::Constant,
                _ => {}
            }
        }
    }

    if path.segments.len() == 1 {
        let seg = &path.segments[0];
        if let Some(mode) = ctx.vars.get(&seg.ident) {
            return ExprPathKind::Local(*mode);
        }
    }

    // TODO: currently we can't reliably distinguish
    // between enum/struct names from function calls
    // so we simply use a heuristic that if the path
    // contains any capital letters, we assume that
    // it is a struct/enum name; otherwise we assume that
    // it is a function name

    let has_capital =
        path.segments.iter().any(|seg| seg.ident.to_string().chars().any(|c| c.is_uppercase()));

    if has_capital {
        if path.segments.len() <= 2 { ExprPathKind::StructOrEnum } else { ExprPathKind::Unknown }
    } else {
        if path.segments.len() != 0 { ExprPathKind::FnName } else { ExprPathKind::Unknown }
    }
}

/// Similar to `compile_pat_path`, but for paths occurring in expressions.
/// TODO: find ways to make this more reliable
fn compile_expr_path(
    ctx: &LocalCtx,
    path: &Path,
    known_kind: Option<ExprPathKind>,
) -> Result<(Path, ExprPathKind), Error> {
    // Special case: do not change Some, None, Ok, Err
    if is_path_eq(path, &["Some"])
        || is_path_eq(path, &["None"])
        || is_path_eq(path, &["Ok"])
        || is_path_eq(path, &["Err"])
    {
        return Ok((path.clone(), ExprPathKind::StructOrEnum));
    }

    // Get or infer the path kind
    let kind = if let Some(kind) = known_kind { kind } else { infer_expr_path_kind(ctx, path) };

    let new_path = match kind {
        // Do not change local variables or function parameters
        ExprPathKind::Local(..) => path.clone(),
        ExprPathKind::FnName => prefix_nth_segment(path, "exec_", path.segments.len() - 1)?,
        ExprPathKind::StructOrEnum => prefix_nth_segment(path, "Exec", 0)?,
        ExprPathKind::Constant => path.clone(),
        ExprPathKind::Unknown => return Err(Error::new_spanned(path, "unknown path kind")),
    };

    Ok((new_path, kind))
}

/// Compiles a spec mode pattern to an exec mode pattern,
/// potentially shadowing some local variables.
///
/// For paths occurring in the patterns,
/// we assume that they are only used in two ways:
///   - SpecEnumName::Variant => ExecSpecEnumName::ExecVariant
///   - SpecStructName => ExecSpecStructName
///
/// i.e. for paths of length 2, we prefix the first segment with `Exec`
/// and for paths of length 1, we prefix the last segment with `Exec`.
fn compile_pattern(
    ctx: &mut LocalCtx,
    pat: &Pat,
    new_locals: &mut HashSet<Ident>,
) -> Result<TokenStream2, Error> {
    match pat {
        Pat::Ident(pat_ident) => {
            // TODO: why do we need this case?
            #[allow(clippy::cmp_owned)] // There is no other way to compare an Ident
            if pat_ident.ident.to_string() == "None" {
                return Ok(quote! { #pat });
            }

            // Bound variables are added as params since
            // we will explicitly convert them to borrowed types
            // as opposed to owned types
            ctx.add(pat_ident.ident.clone(), VarMode::Ref);
            new_locals.insert(pat_ident.ident.clone());
            Ok(quote! { #pat })
        }

        Pat::Path(pat_path) => {
            let new_path = compile_pat_path(&pat_path.path)?;
            Ok(quote! { #new_path })
        }

        Pat::Wild(..) => Ok(quote! { #pat }),
        Pat::Rest(..) => Ok(quote! { #pat }),

        Pat::TupleStruct(pat_tuple_struct) => {
            let new_path = compile_pat_path(&pat_tuple_struct.path)?;
            let pats = pat_tuple_struct
                .elems
                .iter()
                .map(|pat| compile_pattern(ctx, pat, new_locals))
                .collect::<Result<Vec<_>, Error>>()?;

            Ok(quote! {
                #new_path(#(#pats,)*)
            })
        }

        Pat::Struct(pat_struct) => {
            let new_path = compile_pat_path(&pat_struct.path)?;
            let pats = pat_struct
                .fields
                .iter()
                .map(|field| {
                    let Member::Named(name) = &field.member else {
                        return Err(Error::new_spanned(field, "unsupported unamed field pattern"));
                    };
                    let pat = compile_pattern(ctx, &field.pat, new_locals)?;
                    Ok(quote! {
                        #name: #pat
                    })
                })
                .collect::<Result<Vec<_>, Error>>()?;

            let wildcard = if pat_struct.rest.is_some() {
                quote! { .. }
            } else {
                quote! {}
            };

            Ok(quote! {
                #new_path { #(#pats,)* #wildcard }
            })
        }

        Pat::Tuple(pat_tuple) => {
            let pats = pat_tuple
                .elems
                .iter()
                .map(|pat| compile_pattern(ctx, pat, new_locals))
                .collect::<Result<Vec<_>, Error>>()?;

            Ok(quote! {
                (#(#pats,)*)
            })
        }

        // TODO: maybe?
        // Pat::Struct(pat_struct) => todo!(),
        // Pat::Or(pat_or) => todo!(),
        // Pat::Macro(pat_macro) => todo!(),
        // Pat::Lit(pat_lit) => todo!(),
        _ => Err(Error::new_spanned(pat, "unsupported pattern")),
    }
}

/// Compiles a match arm.
fn compile_match_arm(ctx: &LocalCtx, arm: &Arm) -> Result<TokenStream2, Error> {
    let mut ctx = ctx.clone();
    let mut new_locals = HashSet::new();

    let pat = compile_pattern(&mut ctx, &arm.pat, &mut new_locals)?;

    // New locals needs to be converted into the canonical borrowed types (e.g. from &String => &str)
    let local_converts = new_locals.iter().map(|ident| {
        quote! {
            let #ident = #ident.get_ref();
        }
    });

    let body = compile_expr(&ctx, &arm.body, VarMode::Owned)?;

    Ok(quote! {
        #pat => {
            #(#local_converts)*
            #body
        }
    })
}

struct GuardedQuantifier {
    quant_var: Ident,
    quant_type: Box<Type>,
    lower: Box<Expr>,
    upper: Box<Expr>,
    guard_op: BinOp,
    body: Box<Expr>,
}

/// Matches the closure to the form
///   `|x| <lower> <= x < <upper> ==> <body>`
/// or
///   `|x| <lower> <= x < <upper> && <body>`
fn get_guarded_range_quant(closure: &ExprClosure) -> Result<GuardedQuantifier, Error> {
    if closure.inputs.len() != 1 {
        return Err(Error::new_spanned(closure, "only support single quantified variable"));
    }

    let (quant_var, Some(quant_type)) = get_simple_pat(&closure.inputs[0].pat)? else {
        return Err(Error::new_spanned(closure, "only supports a typed variable as quantifier"));
    };

    // |x| <guard> ==>/&& <body>
    let Expr::Binary(ExprBinary { left: guard, op: guard_op, right: body, .. }) =
        closure.body.as_ref()
    else {
        return Err(Error::new_spanned(closure, "unsupported quantified expression"));
    };

    // <guard> == <lower> <= x < <upper>
    let Expr::Binary(ExprBinary { left: lower_guard, op: BinOp::Lt(..), right: upper, .. }) =
        guard.as_ref()
    else {
        return Err(Error::new_spanned(guard, "unsupported quantifier guard upper bound"));
    };

    let Expr::Binary(ExprBinary { left: lower, op: BinOp::Le(..), right: guard_var, .. }) =
        lower_guard.as_ref()
    else {
        return Err(Error::new_spanned(lower_guard, "unsupported quantifier guard lower bound"));
    };

    // Parses the guard variable as a one-component path
    let guard_var = if let Expr::Path(ExprPath { path, .. }) = guard_var.as_ref() {
        let segments: Vec<_> = path.segments.iter().collect();
        if segments.len() == 1 {
            &segments[0].ident
        } else {
            return Err(Error::new_spanned(guard_var, "expect a simple variable"));
        }
    } else {
        return Err(Error::new_spanned(guard_var, "expect a simple variable"));
    };

    if guard_var != quant_var {
        return Err(Error::new_spanned(
            guard_var,
            "quantified variable does not match the guard variable",
        ));
    }

    Ok(GuardedQuantifier {
        quant_var: quant_var.clone(),
        quant_type,
        lower: lower.clone(),
        upper: upper.clone(),
        guard_op: guard_op.clone(),
        body: body.clone(),
    })
}

/// Compiles some forms of forall/exists quantifiers to loops.
fn compile_guarded_quant(ctx: &LocalCtx, op: &UnOp, expr: &Expr) -> Result<TokenStream2, Error> {
    // Quantified variables and the body of the quantified expression
    // is expected to be described as a closure.
    let Expr::Closure(closure) = expr else {
        return Err(Error::new_spanned(expr, "ill-formed quantified expression"));
    };

    // TODO: support other forms of quantifiers
    let quant = get_guarded_range_quant(closure)?;

    let quant_var = &quant.quant_var;
    let quant_type = &quant.quant_type;
    let body = &quant.body;
    let compiled_lower = compile_expr(ctx, &quant.lower, VarMode::Owned)?;
    let compiled_upper = compile_expr(ctx, &quant.upper, VarMode::Owned)?;

    let mut body_ctx = ctx.clone();
    body_ctx.add(quant_var.clone(), VarMode::Owned);
    let compiled_body = compile_expr(&body_ctx, &quant.body, VarMode::Ref)?;
    let mut quant_attrs = closure.inner_attrs.clone();

    if quant_attrs.len() == 0 {
        quant_attrs.push(Attribute {
            pound_token: Default::default(),
            style: AttrStyle::Inner(Default::default()),
            bracket_token: Default::default(),
            meta: Meta::Path(Path::from(Ident::new("auto", Span::call_site()))),
        });
    }

    // Since #body and #expr will be used as spec code in exec mode
    // we have to convert all variables in the context to their spec versions via deep_view
    let local_view: Vec<TokenStream2> = ctx
        .vars
        .keys()
        .map(|name| {
            quote! { let #name = #name.deep_view(); }
        })
        .collect();

    // Some common pieces
    let expr_span = expr.span();
    let inv_bound = quote_spanned! { expr_span => _lower <= #quant_var <= _upper };
    let decreases = quote_spanned! { expr_span => _upper - #quant_var };
    let final_assert = quote_spanned! { expr_span => _res == { #(#local_view)* #op #expr } };

    // Generate a fresh trigger function
    let trigger_fn_name = ctx.gen_fresh_trigger_fn(&quant.quant_type);

    match (op, &quant.guard_op) {
        (UnOp::Forall(..), BinOp::Imply(..)) => {
            // Generate some pieces separately so that we can attach spans to them
            let inv = quote_spanned! { expr_span => _res == {
                let _upper = #quant_var;
                #(#local_view)*
                forall |#quant_var: #quant_type|
                    #![trigger #trigger_fn_name(#quant_var)]
                    #(#quant_attrs)* !(_lower <= #quant_var < _upper) || (#body)
            }};
            let assert_trigger = quote_spanned! { expr_span => { #(#local_view)* !(#body) } };

            Ok(quote! {
                {
                    let _lower = #compiled_lower;
                    let _upper = #compiled_upper;
                    let mut _res = true;
                    let mut #quant_var = _lower;

                    if _lower < _upper {
                        while #quant_var < _upper
                            invariant #inv_bound, #inv,
                            decreases #decreases,
                        {
                            if !(#compiled_body) {
                                proof { let _ = #trigger_fn_name(#quant_var); }
                                assert(#assert_trigger);
                                _res = false;
                                break;
                            }
                            #quant_var += 1;
                        }
                    }
                    proof { let _ = #trigger_fn_name(_lower); }
                    assert(#final_assert);
                    _res
                }
            })
        }

        (UnOp::Exists(..), BinOp::And(..)) => {
            let inv = quote_spanned! { expr_span => _res == {
                let _upper = #quant_var;
                #(#local_view)*
                exists |#quant_var: #quant_type|
                    #![trigger #trigger_fn_name(#quant_var)]
                    #(#quant_attrs)*
                    (_lower <= #quant_var < _upper) && (#body)
            }};
            let assert_trigger = quote_spanned! { expr_span => { #(#local_view)* (#body) } };

            Ok(quote! {
                {
                    let _lower = #compiled_lower;
                    let _upper = #compiled_upper;
                    let mut _res = false;
                    let mut #quant_var = _lower;

                    if _lower < _upper {
                        while #quant_var < _upper
                            invariant #inv_bound, #inv,
                            decreases #decreases,
                        {
                            if (#compiled_body) {
                                proof { let _ = #trigger_fn_name(#quant_var); }
                                assert(#assert_trigger);
                                _res = true;
                                break;
                            }
                            #quant_var += 1;
                        }
                    }
                    proof { let _ = #trigger_fn_name(_lower); }
                    assert(#final_assert);
                    _res
                }
            })
        }

        _ => Err(Error::new_spanned(expr, "unsupported quantified expression")),
    }
}

/// Compiles an expression
///
/// Suppose the original expression has (spec) type `T`
/// the exec expression returned from this function should
/// have the type
/// - `T::ExecRefType<'_>` if mode is `VarMode::Ref`
/// - `T::ExecOwnedType` if mode is `VarMode::Owned`
fn compile_expr(ctx: &LocalCtx, expr: &Expr, mode: VarMode) -> Result<TokenStream2, Error> {
    let expr_ts = match expr {
        Expr::Lit(lit) => match &lit.lit {
            Lit::Str(..) => match mode {
                VarMode::Ref => quote! { #lit },
                VarMode::Owned => quote! { #lit.to_string() },
            },

            // Same owned/borrowed types for these cases
            Lit::Byte(..) | Lit::Char(..) | Lit::Int(..) | Lit::Float(..) | Lit::Bool(..) => {
                quote! { #lit }
            }

            _ => return Err(Error::new_spanned(lit, "unsupported literal")),
        },

        // Blocks have the owned type, so we need to
        // convert back a reference again
        Expr::Block(expr_block) => {
            let block_expr = compile_block(ctx, &expr_block.block)?;

            match mode {
                VarMode::Ref => quote! { #block_expr.get_ref() },
                VarMode::Owned => quote! { #block_expr }, // block already have the owned mode
            }
        }

        // Macro invocations get passed through
        // except for the case of `seq![...]` => `&[...]`
        Expr::Macro(expr_macro) => {
            if is_path_eq(&expr_macro.mac.path, &["seq"]) {
                let spec_args = &expr_macro.mac.tokens;

                // Parse the seq! macro call arguments
                let args = verus_syn::parse2::<Exprs>(spec_args.clone())?;

                // Compile each argument
                let args = args
                    .0
                    .iter()
                    .map(|arg| compile_expr(ctx, arg, VarMode::Owned))
                    .collect::<Result<Vec<_>, Error>>()?;

                // We need to convert each argument to the owned type
                let owned = quote! { {
                    let v = vec![ #(#args),* ];
                    // Sometimes required for proving functional correctness
                    assert(v.deep_view() == seq![ #spec_args ]);
                    v
                } };

                match mode {
                    VarMode::Ref => quote! { #owned.get_ref() },
                    VarMode::Owned => owned,
                }
            } else {
                // TODO: typing?
                quote! { #expr_macro }
            }
        }

        Expr::Paren(expr_paren) => {
            let inner = compile_expr(ctx, &expr_paren.expr, mode)?;
            quote! { #inner } // we'll insert the parenthesis in the end
        }

        Expr::Field(expr_field) => {
            // The base of a field is always get as a reference
            // since we want to avoid partially moving the base
            let expr = compile_expr(ctx, &expr_field.base, VarMode::Ref)?;
            let field = &expr_field.member;
            // By default, x.y have the owned type of field y
            // so we need to take the reference and convert it
            // into the ref type
            match mode {
                VarMode::Ref => quote! { (&#expr.#field).get_ref() },

                // Basically clone the field
                VarMode::Owned => quote! { (&#expr.#field).get_ref().get_owned() },
            }
        }

        // If the variable is a local variable
        // we need to convert it into ref type;
        // otherwise if it is a parameter,
        // we can directly use it
        Expr::Path(expr_path) => {
            let (new_path, kind) = compile_expr_path(ctx, &expr_path.path, None)?;

            match kind {
                ExprPathKind::Local(local_mode) => match (local_mode, mode) {
                    // Borrowed type should be structural, so we can just copy
                    (VarMode::Ref, VarMode::Ref) => quote! { #new_path },
                    (VarMode::Ref, VarMode::Owned) => quote! { (#new_path).get_owned() },
                    (VarMode::Owned, VarMode::Ref) => quote! { (#new_path).get_ref() },

                    // We still need to clone in this case, since
                    // we don't want to move the variable
                    (VarMode::Owned, VarMode::Owned) => quote! { #new_path.get_ref().get_owned() },
                },

                ExprPathKind::StructOrEnum => match mode {
                    VarMode::Ref => quote! { #new_path.get_ref() },
                    VarMode::Owned => quote! { #new_path },
                },

                // We assume that constants (e.g. usize::MAX)
                // have the borrowed type
                ExprPathKind::Constant => match mode {
                    VarMode::Ref => quote! { #new_path },
                    VarMode::Owned => quote! { #new_path.get_owned() },
                },

                _ => return Err(Error::new_spanned(expr_path, "unsupported path expression")),
            }
        }

        // Currently we only support binary operators
        // on arithmetic and boolean types
        //
        // Since these types have ExecSpecType::ExecRefType<'_>
        // being the same as ExecSpecType::ExecOwnedType (see vstd::exec_spec),
        // we can just apply the operator directly
        //
        // We also support equality (TODO)
        Expr::Binary(expr_binary) => match &expr_binary.op {
            // `bool` has the same owned and borrowed types, so no need to convert here
            BinOp::Eq(..) => {
                let left = compile_expr(ctx, &expr_binary.left, VarMode::Ref)?;
                let right = compile_expr(ctx, &expr_binary.right, VarMode::Ref)?;
                quote! { vstd::contrib::exec_spec::ExecSpecEq::exec_eq(#left, #right) }
            }

            BinOp::Ne(..) => {
                let left = compile_expr(ctx, &expr_binary.left, VarMode::Ref)?;
                let right = compile_expr(ctx, &expr_binary.right, VarMode::Ref)?;
                quote! { !vstd::contrib::exec_spec::ExecSpecEq::exec_eq(#left, #right) }
            }

            // TODO
            // BinOp::BigEq(..) => todo!(),
            // BinOp::BigNe(..) => todo!(),
            // BinOp::ExtEq(..) => todo!(),
            // BinOp::ExtNe(..) => todo!(),
            // BinOp::ExtDeepEq(..) => todo!(),
            // BinOp::ExtDeepNe(..) => todo!(),

            // Assuming these return integer/boolean types
            // which have the same owned and borrowed types
            // so no need to convert with get_ref/get_owned
            BinOp::Add(..)
            | BinOp::Sub(..)
            | BinOp::Mul(..)
            | BinOp::Div(..)
            | BinOp::Rem(..)
            | BinOp::And(..)
            | BinOp::Or(..)
            | BinOp::BitXor(..)
            | BinOp::BitAnd(..)
            | BinOp::BitOr(..)
            | BinOp::Shl(..)
            | BinOp::Shr(..)
            | BinOp::Lt(..)
            | BinOp::Le(..)
            | BinOp::Ge(..)
            | BinOp::Gt(..) => {
                let op = &expr_binary.op;
                let left = compile_expr(ctx, &expr_binary.left, VarMode::Ref)?;
                let right = compile_expr(ctx, &expr_binary.right, VarMode::Ref)?;

                quote! { #left #op #right }
            }

            // `a ==> b` to `!a || b`
            BinOp::Imply(..) => {
                let left = compile_expr(ctx, &expr_binary.left, VarMode::Ref)?;
                let right = compile_expr(ctx, &expr_binary.right, VarMode::Ref)?;
                quote! { !(#left) || (#right) }
            }

            // `a <== b` to `!b || a`
            BinOp::Exply(..) => {
                let left = compile_expr(ctx, &expr_binary.left, VarMode::Ref)?;
                let right = compile_expr(ctx, &expr_binary.right, VarMode::Ref)?;
                quote! { !(#right) || (#left) }
            }

            // `a <==> b` to `a == b`
            BinOp::Equiv(..) => {
                let left = compile_expr(ctx, &expr_binary.left, VarMode::Ref)?;
                let right = compile_expr(ctx, &expr_binary.right, VarMode::Ref)?;
                quote! { vstd::contrib::exec_spec::ExecSpecEq::exec_eq(#left, #right) }
            }

            // No plan to support
            // BinOp::AddAssign(plus_eq) => todo!(),
            // BinOp::SubAssign(minus_eq) => todo!(),
            // BinOp::MulAssign(star_eq) => todo!(),
            // BinOp::DivAssign(slash_eq) => todo!(),
            // BinOp::RemAssign(percent_eq) => todo!(),
            // BinOp::BitXorAssign(caret_eq) => todo!(),
            // BinOp::BitAndAssign(and_eq) => todo!(),
            // BinOp::BitOrAssign(or_eq) => todo!(),
            // BinOp::ShlAssign(shl_eq) => todo!(),
            // BinOp::ShrAssign(shr_eq) => todo!(),
            _ => return Err(Error::new_spanned(expr_binary, "unsupported binary operator")),
        },

        // `as T` for a primitive T will be preserved
        // `as int`/`as nat` will be removed
        // TODO: more strict checking here
        Expr::Cast(expr_cast) => match expr_cast.ty.as_ref() {
            Type::Path(type_path)
                if is_path_eq(&type_path.path, &["int"])
                    || is_path_eq(&type_path.path, &["nat"]) =>
            {
                compile_expr(ctx, &expr_cast.expr, mode)?
            }

            _ => {
                let typ = compile_type(&expr_cast.ty, TypeKind::Ref)?;
                let expr = compile_expr(ctx, &expr_cast.expr, mode)?;

                quote! {
                    (#expr as #typ)
                }
            }
        },

        Expr::If(expr_if) => {
            let cond = compile_expr(ctx, &expr_if.cond, VarMode::Ref)?;
            let then_branch = compile_block(ctx, &expr_if.then_branch)?;

            // let e = &expr_if.else_branch.as_ref().unwrap().1;
            // println!("???: {}", quote! { #e });

            let else_branch = compile_expr(
                ctx,
                &expr_if
                    .else_branch
                    .as_ref()
                    .ok_or(Error::new_spanned(
                        expr_if,
                        "else branch is required for if expression",
                    ))?
                    .1,
                VarMode::Owned, // to align with the owned type of then_branch
            )?;

            let owned = quote! {
                if #cond
                    #then_branch
                else {
                    #else_branch
                }
            };

            match mode {
                VarMode::Ref => quote! { #owned.get_ref() },
                VarMode::Owned => owned,
            }
        }

        // View expressions are ignored (e.g. "abc"@ => "abc")
        // TODO: more strict rules here
        Expr::View(view) => {
            let expr = compile_expr(ctx, &view.expr, mode)?;
            quote! { #expr }
        }

        // NOTE: this only supports indexing into Seq<T>
        // but NOT SpecString, whose exec version (String)
        // does not have a direct indexing operator
        Expr::Index(expr_index) => {
            let base = compile_expr(ctx, &expr_index.expr, VarMode::Ref)?;
            let index = compile_expr(ctx, &expr_index.index, VarMode::Ref)?;

            match mode {
                VarMode::Ref => quote! { #base.exec_index(#index).get_ref() },

                // Clone to avoid partial moves
                VarMode::Owned => quote! { #base.exec_index(#index).get_ref().get_owned() },
            }
        }

        // Only support unary arithmetic operators
        Expr::Unary(expr_unary) => match &expr_unary.op {
            UnOp::Neg(..) | UnOp::Not(..) => {
                let op = &expr_unary.op;
                let expr = compile_expr(ctx, &expr_unary.expr, VarMode::Ref)?;
                quote! { #op #expr }
            }
            UnOp::Forall(..) | UnOp::Exists(..) => {
                let compiled = compile_guarded_quant(ctx, &expr_unary.op, &expr_unary.expr)?;
                match mode {
                    VarMode::Ref => quote! { #compiled.get_ref() },
                    VarMode::Owned => compiled,
                }
            }
            _ => return Err(Error::new_spanned(expr_unary, "unsupported unary operator")),
        },

        Expr::BigAnd(big_and) => {
            let exprs = big_and
                .exprs
                .iter()
                .map(|e| compile_expr(ctx, &e.expr, VarMode::Ref))
                .collect::<Result<Vec<_>, Error>>()?;
            quote! { #((#exprs))&&* }
        }

        Expr::BigOr(big_or) => {
            let exprs = big_or
                .exprs
                .iter()
                .map(|e| compile_expr(ctx, &e.expr, VarMode::Ref))
                .collect::<Result<Vec<_>, Error>>()?;
            quote! { #((#exprs))||* }
        }

        // The current assumption is that the called
        // function has a corresponding exec version
        // with an "exec_" prefix
        // i.e. spec: foo, exec: exec_foo
        //
        // TODO: this assumption might be a bit brittle
        Expr::Call(expr_call) => {
            // Assume that the function is a path
            let Expr::Path(fn_path) = expr_call.func.as_ref() else {
                return Err(Error::new_spanned(expr_call, "unsupported callee"));
            };

            let (exec_fn_path, kind) = compile_expr_path(ctx, &fn_path.path, None)?;

            let owned = match kind {
                // Struct/enums requires owned arguments
                ExprPathKind::StructOrEnum => {
                    let args = expr_call
                        .args
                        .iter()
                        .map(|arg| compile_expr(ctx, arg, VarMode::Owned))
                        .collect::<Result<Vec<_>, Error>>()?;
                    quote! { #exec_fn_path(#(#args),*) }
                }

                ExprPathKind::FnName => {
                    let args = expr_call
                        .args
                        .iter()
                        .map(|arg| compile_expr(ctx, arg, VarMode::Ref))
                        .collect::<Result<Vec<_>, Error>>()?;
                    quote! { #exec_fn_path(#(#args),*) }
                }

                _ => return Err(Error::new_spanned(expr_call, "unsupported callee path")),
            };

            match mode {
                VarMode::Ref => quote! { #owned.get_ref() },
                VarMode::Owned => owned,
            }
        }

        // We only permit a limited set of method calls
        Expr::MethodCall(expr_method_call) => match expr_method_call.method.to_string().as_str() {
            "len" => {
                let receiver = compile_expr(ctx, &expr_method_call.receiver, VarMode::Ref)?;
                quote! { #receiver.exec_len() }
            }

            _ => return Err(Error::new_spanned(expr_method_call, "unsupported method call")),
        },

        Expr::Match(expr_match) => {
            let expr = compile_expr(ctx, &expr_match.expr, VarMode::Ref)?;
            let arms = expr_match
                .arms
                .iter()
                .map(|arm| compile_match_arm(ctx, arm))
                .collect::<Result<Vec<_>, Error>>()?;

            let owned = quote! {
                match #expr {
                    #(#arms,)*
                }
            };

            match mode {
                VarMode::Ref => quote! { #owned.get_ref() },
                VarMode::Owned => owned,
            }
        }

        Expr::Tuple(expr_tuple) => {
            let exprs = expr_tuple
                .elems
                .iter()
                .map(|e| compile_expr(ctx, e, VarMode::Owned))
                .collect::<Result<Vec<_>, Error>>()?;

            match mode {
                VarMode::Ref => quote! { (#(#exprs),*).get_ref() },
                VarMode::Owned => quote! { (#(#exprs),*) },
            }
        }

        Expr::Struct(expr_struct) => {
            let (new_path, kind) =
                compile_expr_path(ctx, &expr_struct.path, Some(ExprPathKind::StructOrEnum))?;

            if kind != ExprPathKind::StructOrEnum {
                return Err(Error::new_spanned(expr_struct, "expected a struct or enum path"));
            }

            // Compile the fields
            let fields = expr_struct
                .fields
                .iter()
                .map(|field| {
                    let Member::Named(name) = &field.member else {
                        return Err(Error::new_spanned(
                            field,
                            "unsupported unamed field in struct expression",
                        ));
                    };
                    let value = compile_expr(ctx, &field.expr, VarMode::Owned)?;
                    Ok(quote! { #name: #value })
                })
                .collect::<Result<Vec<_>, Error>>()?;

            let owned = quote! {
                #new_path {
                    #(#fields,)*
                }
            };

            match mode {
                VarMode::Ref => quote! { #owned.get_ref() },
                VarMode::Owned => owned,
            }
        }

        // 1. `lhs matches pat ==> rhs` to `match lhs { pat => rhs, _ => true }`
        // 2. `lhs matches pat && rhs` to `match lhs { pat => rhs, _ => false }`
        // 3. `lhs matches pat` to `match lhs { pat => true, _ => false }`
        Expr::Matches(ExprMatches { lhs, pat, op_expr, .. }) => {
            let mut ctx = ctx.clone();
            let mut new_locals = HashSet::new();
            let pat = compile_pattern(&mut ctx, pat, &mut new_locals)?;

            let lhs = compile_expr(&ctx, lhs, VarMode::Ref)?;

            let true_rhs = if let Some(MatchesOpExpr { rhs, .. }) = op_expr {
                let rhs = compile_expr(&ctx, rhs, VarMode::Owned)?;
                quote! { { #rhs } }
            } else {
                quote! { true }
            };

            let false_rhs = match op_expr {
                Some(MatchesOpExpr { op_token, .. }) => match op_token {
                    MatchesOpToken::Implies(..) => quote! { true },
                    MatchesOpToken::AndAnd(..) => quote! { false },
                    MatchesOpToken::BigAnd => quote! { false },
                },
                None => quote! { false },
            };

            let owned = quote! {
                match #lhs {
                    #pat => #true_rhs,
                    _ => #false_rhs,
                }
            };

            match mode {
                VarMode::Ref => quote! { #owned.get_ref() },
                VarMode::Owned => owned,
            }
        }

        // TODOs:
        // Expr::Let(expr_let) => todo!(),
        // Expr::Is(expr_is) => todo!(),
        // Expr::IsNot(expr_is_not) => todo!(),

        // Maybe TODOs:
        // Expr::Verbatim(token_stream) => todo!(),
        // Expr::Has(expr_has) => todo!(),
        // Expr::HasNot(expr_has_not) => todo!(),
        // Expr::GetField(expr_get_field) => todo!(),

        // No plan to support:
        // Expr::Array(expr_array) => todo!(),
        // Expr::Assign(expr_assign) => todo!(),
        // Expr::Async(expr_async) => todo!(),
        // Expr::Await(expr_await) => todo!(),
        // Expr::Break(expr_break) => todo!(),
        // Expr::Closure(expr_closure) => todo!(),
        // Expr::Const(expr_const) => todo!(),
        // Expr::Continue(expr_continue) => todo!(),
        // Expr::ForLoop(expr_for_loop) => todo!(),
        // Expr::Group(expr_group) => todo!(),
        // Expr::Infer(expr_infer) => todo!(),
        // Expr::Loop(expr_loop) => todo!(),
        // Expr::Range(expr_range) => todo!(),
        // Expr::RawAddr(expr_raw_addr) => todo!(),
        // Expr::Reference(expr_reference) => todo!(),
        // Expr::Repeat(expr_repeat) => todo!(),
        // Expr::Return(expr_return) => todo!(),
        // Expr::Try(expr_try) => todo!(),
        // Expr::TryBlock(expr_try_block) => todo!(),
        // Expr::Unsafe(expr_unsafe) => todo!(),
        // Expr::While(expr_while) => todo!(),
        // Expr::Yield(expr_yield) => todo!(),
        // Expr::Assume(assume) => todo!(),
        // Expr::Assert(assert) => todo!(),
        // Expr::AssertForall(assert_forall) => todo!(),
        // Expr::RevealHide(reveal_hide) => todo!(),
        _ => return Err(Error::new_spanned(expr, "unsupported expression")),
    };

    // Wrap another token tree group
    // so that the outer layer won't override
    // the span of what's inside the group.
    // And also helps with clarifying associativity
    let expr_span = expr.span();
    let expr_ts = quote_spanned! { expr_span => (#expr_ts) };

    Ok(expr_ts)
}

/// Compiles a block.
///
/// TODO: to avoid issues of `temporary value dropped while borrowed`
/// the return value of a block has the owned type instead of the ref type
/// This might incur some performance overhead.
fn compile_block(ctx: &LocalCtx, block: &Block) -> Result<TokenStream2, Error> {
    let mut ts = Vec::new();
    let mut ctx = ctx.clone();

    for stmt in &block.stmts {
        match stmt {
            // A local binding
            Stmt::Local(binding) => {
                let (var, typ) = get_simple_pat(&binding.pat)?;

                if typ.is_some() {
                    return Err(Error::new_spanned(binding, "typed local variables not supported"));
                }

                let Some(local_init) = &binding.init else {
                    return Err(Error::new_spanned(
                        stmt,
                        "unsupported let statement without initializer",
                    ));
                };

                let expr = compile_expr(&ctx, &local_init.expr, VarMode::Owned)?;

                ctx.add(var.clone(), VarMode::Owned);
                ts.push(quote! { let #var = #expr; });
            }

            // NOTE: this is expected to be the last expression
            Stmt::Expr(expr, ..) => {
                let expr = compile_expr(&ctx, expr, VarMode::Owned)?;
                ts.push(quote! { #expr });
            }

            _ => return Err(Error::new_spanned(stmt, "unsupported statement")),
        }
    }

    Ok(quote! { { #(#ts)* } })
}

/// Recursively sets the span of all tokens in a token stream to the given one.
fn respan(input: TokenStream2, span: Span) -> TokenStream2 {
    input
        .into_iter()
        .map(|mut tt| {
            if let TokenTree::Group(g) = tt {
                let mut new_g = Group::new(g.delimiter(), respan(g.stream(), span));
                new_g.set_span(span);
                TokenTree::Group(new_g)
            } else {
                tt.set_span(span);
                tt
            }
        })
        .collect()
}

/// Compiles a spec function into an exec function.
fn compile_spec_fn(item_fn: &ItemFn) -> Result<TokenStream2, Error> {
    if let FnMode::Spec(..) = &item_fn.sig.mode {
    } else {
        return Err(Error::new_spanned(item_fn, "#[exec_spec] only supports spec functions"));
    }

    let mut ctx = LocalCtx::new(&item_fn.sig.ident);

    let sig = compile_sig(&mut ctx, item_fn)?;
    let body = compile_block(&ctx, &item_fn.block)?;

    // Generate all promised trigger functions
    let trigger_fns = ctx
        .trigger_fns
        .borrow()
        .iter()
        .map(|(name, typ)| {
            Ok(quote! {
                uninterp spec fn #name(x: #typ);
            })
        })
        .collect::<Result<Vec<_>, Error>>()?;

    let span = item_fn.span();
    Ok(quote_spanned! { span =>
        #item_fn

        #(#trigger_fns)*

        #[allow(unused_parens)]
        #[allow(non_shorthand_field_patterns)]
        #[verifier::loop_isolation(false)]
        #sig #body
    })
}

/// Compiles a fn/struct/enum item.
fn compile_item(item: Item) -> Result<TokenStream2, Error> {
    match item {
        Item::Fn(item_fn) => compile_spec_fn(&item_fn),
        Item::Struct(item_struct) => compile_struct(&item_struct),
        Item::Enum(item_enum) => compile_enum(&item_enum),
        _ => Err(Error::new_spanned(item, "unsupported item")),
    }
}

/// Parses and compiles a list of items.
pub fn exec_spec(input: TokenStream) -> TokenStream {
    let items = parse_macro_input!(input as Items);
    let res = items
        .0
        .into_iter()
        .map(|item| match compile_item(item) {
            Ok(ts) => Ok(ts),
            Err(err) => Err(err.to_compile_error().into()),
        })
        .collect::<Result<Vec<_>, _>>();

    match res {
        Ok(ts) => quote_vstd! { vstd =>
            #vstd::prelude::verus! { #(#ts)* }
        }
        .into(),
        Err(err) => err,
    }
}
