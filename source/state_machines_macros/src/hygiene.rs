//! Hygiene of the code that `verified_tokenized_state_machine!` generates.
//!
//! The generated items of a transition mix user tokens (the transition
//! parameters, and the expressions and binders of the transition body, which
//! resolve at the call site) with binders of their own: the fragment
//! parameters `owned` and `h` of the raw operations, the frame `z` and the
//! outputs `new` of their specifications, the token parameters `token` and
//! `shared`, the return value `out`, locals such as `outputs` and `empty`, and
//! so on. No user name may collide with or capture these, nor be captured by
//! them, so that every name is available to transition parameters and binders.
//!
//! Two rules achieve this (`binder`):
//!
//! * Every binder the macro introduces has the mixed-site span: like a local
//!   variable of a `macro_rules!` expansion, only identifiers of the same
//!   expansion resolve to it. A user binder of the same name (a `let` or a
//!   pattern of the body, which the generated code may wrap or be wrapped by)
//!   is then a different variable.
//! * Its name also differs from the name of every parameter of the transition:
//!   `owned`, unless the transition has a parameter `owned`, and then `owned_`
//!   (or `owned__`, ...). Hygiene alone does not suffice next to parameters:
//!   `verus!` rejects a return binder that has the name of a parameter (its
//!   check compares names), and VIR requires the parameters of a function to
//!   have distinct names.
//!
//! The names are a function of the transition's parameters only, so every
//! emitter derives the same identifier for the same binder. Without such a
//! parameter, the generated items read exactly as before, and the
//! documentation's `owned` and `h` are the parameters' names.
//!
//! Binders that user tokens do name keep the call-site span: `pre` and `post`
//! (reserved in every state machine, see `ident_visitor::validate_ident`) and
//! the user's own parameters and binders.
use crate::ast::TransitionParam;
use proc_macro2::{Ident, Span};

/// The internal binder `name` of the generated items of a transition with the
/// parameters `params` (see the module documentation).
pub(crate) fn binder(name: &str, params: &[TransitionParam]) -> Ident {
    named_apart(name, params.iter().map(|p| &p.name))
}

/// `binder` for several names.
pub(crate) fn binders<const N: usize>(names: [&str; N], params: &[TransitionParam]) -> [Ident; N] {
    names.map(|name| binder(name, params))
}

/// The binders of a transition's raw operations and their specifications
/// (`verified_general`, `verified_operations`): the fragments `owned` and `h`,
/// the frame `z`, the output `new`, the tokens `token` and `shared`, the
/// storage `deposit` and `withdrawn`, the return values `out` and `result`, ...
pub(crate) struct Binders {
    pub(crate) owned: Ident,
    pub(crate) h: Ident,
    pub(crate) z: Ident,
    pub(crate) new: Ident,
    pub(crate) f: Ident,
    pub(crate) s: Ident,
    pub(crate) token: Ident,
    pub(crate) shared: Ident,
    pub(crate) base: Ident,
    pub(crate) empty: Ident,
    pub(crate) outputs: Ident,
    pub(crate) out: Ident,
    pub(crate) result: Ident,
    pub(crate) deposit: Ident,
    pub(crate) withdrawn: Ident,
    pub(crate) physical_deposit: Ident,
    pub(crate) pair: Ident,
    pub(crate) key: Ident,
    pub(crate) guard_key: Ident,
    pub(crate) post_fragment: Ident,
}

impl Binders {
    pub(crate) fn new(params: &[TransitionParam]) -> Binders {
        let b = |name| binder(name, params);
        Binders {
            owned: b("owned"),
            h: b("h"),
            z: b("z"),
            new: b("new"),
            f: b("f"),
            s: b("s"),
            token: b("token"),
            shared: b("shared"),
            base: b("base"),
            empty: b("empty"),
            outputs: b("outputs"),
            out: b("out"),
            result: b("result"),
            deposit: b("deposit"),
            withdrawn: b("withdrawn"),
            physical_deposit: b("physical_deposit"),
            pair: b("__tsm_storage_exchange_pair"),
            key: b("__tsm_key"),
            guard_key: b("__tsm_guard_key"),
            post_fragment: b("__tsm_post_fragment"),
        }
    }
}

/// `binder` for a transition with the parameters named `params`.
pub(crate) fn binder_among(name: &str, params: &[&Ident]) -> Ident {
    named_apart(name, params.iter().copied())
}

fn named_apart<'a>(name: &str, params: impl Iterator<Item = &'a Ident> + Clone) -> Ident {
    let taken: Vec<String> =
        params.map(|p| p.to_string().trim_start_matches("r#").to_string()).collect();
    let mut candidate = name.to_string();
    while taken.contains(&candidate) {
        candidate.push('_');
    }
    Ident::new(&candidate, Span::mixed_site())
}
