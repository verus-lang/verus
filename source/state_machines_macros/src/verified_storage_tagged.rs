//! The tagged storage layout. A machine's stored resources are one
//! `IMap<__StorageKey, __StorageValue>`, the storage of vstd's storage protocol
//! (`StorageResource<K, V, P>`), with two generated enums: per storage field
//! `f`, a key variant (`__StorageKey::f(K)` for a `storage_map`/`storage_imap`
//! field with keys `K`, `__StorageKey::f` for a `storage_option` field) and a
//! value variant holding its payload (`__StorageValue::f(V)`). Every machine with
//! storage fields uses this layout, also one with a single storage field or with
//! storage fields of one payload type.
//!
//! The state's storage (`State::__storage`) is the union of its fields' tagged
//! parts (`__tag_f(s.f)`, `__tag_f(s.f.to_imap())` for a `storage_map`). It is
//! written as that union for a machine with one storage field or only
//! `storage_option` fields; otherwise it is defined per key by two named spec
//! functions of `State` (`__storage_dom`/`__storage_val`), equal to the union
//! extensionally.
//!
//! Per storage field `f` the layout also generates, as functions of the
//! machine's module (generic over the type parameters the storage types
//! mention), the tagging of the field's own value (`__tag_f`, `__untag_f`) and
//! tracked conversions between the field's value and its tagged part
//! (`__pack_f`, `__unpack_f`, `__borrow_f`, and `__unwrap_f` for one storage
//! value). Raw-interface clients use them to build deposits and take apart
//! withdrawals. The tracked conversions of a map field build or take apart a
//! tagged map key by key, so they need a finite domain: a general (whole-map)
//! operand of a `storage_imap` field must have a finite domain where the
//! generated code converts it.
use crate::ast::{Field, MonoidElt, SM, ShardableType, SplitKind, SubIdx, TransitionStmt};
use crate::parse_token_stream::SMBundle;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use std::collections::HashSet;
use verus_syn::{Error, Ident};

/// The union (`union_prefer_right`) of `parts` as a balanced tree. It equals
/// the left-to-right chain (the union is associative), but a solver reaches
/// every part in O(log n) unfoldings instead of O(n): with dozens of storage
/// fields the chain exceeds the instantiation depth the solver explores.
/// Up to 8 parts it is the plain chain.
pub fn balanced_union(parts: &[TokenStream]) -> TokenStream {
    match parts.len() {
        0 => quote! {::vstd::imap::IMap::empty()},
        n if n <= 8 => {
            let (first, rest) = (&parts[0], &parts[1..]);
            rest.iter().fold(first.clone(), |acc, p| quote! {(#acc).union_prefer_right(#p)})
        }
        n => {
            let (a, b) = parts.split_at(n / 2);
            let (a, b) = (balanced_union(a), balanced_union(b));
            quote! {(#a).union_prefer_right(#b)}
        }
    }
}

/// Whether `ts` mentions the identifier `id`.
fn mentions(ts: &TokenStream, id: &Ident) -> bool {
    ts.clone().into_iter().any(|t| match t {
        proc_macro2::TokenTree::Ident(i) => i == *id,
        proc_macro2::TokenTree::Group(g) => mentions(&g.stream(), id),
        _ => false,
    })
}

/// Every identifier in `tokens`, into `names`.
fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
    for token in tokens {
        match token {
            proc_macro2::TokenTree::Ident(id) => {
                names.insert(id.to_string());
            }
            proc_macro2::TokenTree::Group(group) => reserve(group.stream(), names),
            _ => {}
        }
    }
}

/// `stem`, extended by underscores until no name in `names` is it.
fn fresh(names: &mut HashSet<String>, stem: &str) -> Ident {
    let mut name = stem.to_string();
    while names.contains(&name) {
        name.push('_');
    }
    names.insert(name.clone());
    Ident::new(&name, Span::call_site())
}

/// Every identifier of a transition body, into `names`.
fn reserve_stmt(stmt: &TransitionStmt, names: &mut HashSet<String>) {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                reserve_stmt(child, names);
            }
        }
        TransitionStmt::Require(_, expr)
        | TransitionStmt::Update(_, _, expr)
        | TransitionStmt::Initialize(_, _, expr)
        | TransitionStmt::PostCondition(_, expr) => reserve(quote! {#expr}, names),
        TransitionStmt::Assert(_, expr, proof) => {
            let block = proof.proof.as_ref().map(|block| &**block);
            reserve(quote! {#expr #block}, names);
        }
        TransitionStmt::SubUpdate(_, _, indices, expr) => {
            reserve(quote! {#expr}, names);
            for index in indices {
                if let SubIdx::Idx(expr) = index {
                    reserve(quote! {#expr}, names);
                }
            }
        }
        TransitionStmt::Split(_, kind, children) => {
            match &**kind {
                SplitKind::If(expr) => reserve(quote! {#expr}, names),
                SplitKind::Match(expr, arms) => {
                    reserve(quote! {#expr}, names);
                    for arm in arms {
                        let pat = &arm.pat;
                        let guard = arm.guard.as_ref().map(|(_, expr)| expr);
                        reserve(quote! {#pat #guard}, names);
                    }
                }
                SplitKind::Let(pat, ty, _, expr) => reserve(quote! {#pat #ty #expr}, names),
                SplitKind::Special(_, op, proof, pat) => {
                    let block = proof.proof.as_ref().map(|block| &**block);
                    reserve(quote! {#pat #block}, names);
                    match &op.elt {
                        MonoidElt::General(expr)
                        | MonoidElt::SingletonMultiset(expr)
                        | MonoidElt::SingletonSet(expr) => reserve(quote! {#expr}, names),
                        MonoidElt::OptionSome(expr) => reserve(quote! {#expr}, names),
                        MonoidElt::SingletonKV(key, value) => reserve(quote! {#key #value}, names),
                        MonoidElt::True => {}
                    }
                }
            }
            for child in children {
                reserve_stmt(child, names);
            }
        }
    }
}

/// The machine's type parameters that some tokens mention, with their bounds,
/// and the where-clause predicates over them.
struct Params {
    used: Vec<Ident>,
    /// The parameters, with their bounds, comma-separated.
    list: TokenStream,
    /// The generic parameters (`<T: Bound, ..>`, or nothing) and the where clause.
    decl: TokenStream,
    wc: TokenStream,
    /// Recursion annotations of the parameters (`#[verifier::accept_recursive_types(T)]`).
    attrs: Vec<TokenStream>,
}

impl Params {
    fn new(sm: &SM, tokens: &TokenStream) -> Params {
        let mut params = vec![];
        let mut attrs = vec![];
        for gp in sm.generics.iter().flat_map(|g| g.params.iter()) {
            if let verus_syn::GenericParam::Type(t) = gp {
                if mentions(tokens, &t.ident) {
                    let mut t = t.clone();
                    let name = t.ident.clone();
                    t.attrs.retain(|a| {
                        let Some(last) = a.meta.path().segments.last() else { return true };
                        let keep = !matches!(
                            last.ident.to_string().as_str(),
                            "accept_recursive_types"
                                | "reject_recursive_types"
                                | "reject_recursive_types_in_ground_variants"
                        );
                        if !keep {
                            let annotation = &last.ident;
                            attrs.push(quote! {#[verifier::#annotation(#name)]});
                        }
                        keep
                    });
                    params.push(t);
                }
            }
        }
        let used: Vec<Ident> = params.iter().map(|t| t.ident.clone()).collect();
        // Where-clause predicates that mention only the used parameters.
        let unused: Vec<Ident> = sm
            .generics
            .iter()
            .flat_map(|g| g.params.iter())
            .filter_map(|gp| match gp {
                verus_syn::GenericParam::Type(t) if !used.contains(&t.ident) => {
                    Some(t.ident.clone())
                }
                _ => None,
            })
            .collect();
        let preds: Vec<TokenStream> = sm
            .generics
            .iter()
            .filter_map(|g| g.where_clause.as_ref())
            .flat_map(|w| w.predicates.iter())
            .map(|p| quote! {#p})
            .filter(|p| !unused.iter().any(|u| mentions(p, u)))
            .collect();
        let list = quote! {#(#params),*};
        let decl = if used.is_empty() {
            quote! {}
        } else {
            quote! {<#list>}
        };
        let wc = if preds.is_empty() {
            quote! {}
        } else {
            quote! {where #(#preds),*}
        };
        Params { used, list, decl, wc, attrs }
    }
}

/// One of the generated enums, over the machine's type parameters that its
/// variants mention (an enum may not have unused parameters).
struct Enum {
    name: Ident,
    /// The type (`name<..>`).
    ty: TokenStream,
    /// The same in expression and pattern position (`name::<..>`).
    path: TokenStream,
    params: Params,
}

impl Enum {
    fn new(sm: &SM, name: Ident, variants: &TokenStream) -> Enum {
        let params = Params::new(sm, variants);
        let used = &params.used;
        let (ty, path) = if used.is_empty() {
            (quote! {#name}, quote! {#name})
        } else {
            (quote! {#name<#(#used),*>}, quote! {#name::<#(#used),*>})
        };
        Enum { name, ty, path, params }
    }
}

/// A machine's storage layout (see the module documentation).
pub struct Tagged {
    pub fields: Vec<Field>,
    key: Enum,
    value: Enum,
    /// The parameters of the storage helpers (those of both enums).
    helpers: Params,
    /// The named per-key functions of the state's storage (`__storage_dom`/`__storage_val`).
    dom_fn: Ident,
    val_fn: Ident,
    /// Every storage field is a `storage_option`.
    options_only: bool,
    /// The state's storage is written as the union of its fields' tagged
    /// parts (one storage field, or only `storage_option` fields), rather than
    /// by `dom_fn`/`val_fn`.
    by_tags: bool,
}

/// The prefixes of the per-field storage helpers (`<prefix><field>`).
const HELPERS: [&str; 9] = [
    "__tag_",
    "__untag_",
    "__untag_tag_",
    "__tag_finite_",
    "__tag_shape_",
    "__pack_",
    "__unpack_",
    "__borrow_",
    "__unwrap_",
];

/// The value variant's field accessor (`->f_0`).
fn accessor(field: &Ident) -> Ident {
    format_ident!("{}_0", field)
}

impl Tagged {
    /// The layout of the machine's storage fields; `None` without storage fields.
    ///
    /// The enums and the storage functions are named `__StorageKey`,
    /// `__StorageValue`, `__storage_dom` and `__storage_val`, extended by
    /// underscores where the machine's own items or parameters use one of these
    /// names.
    pub fn build(bundle: &SMBundle) -> Result<Option<Tagged>, Error> {
        let sm = &bundle.sm;
        let fields: Vec<Field> =
            sm.fields.iter().filter(|f| f.stype.is_storage()).cloned().collect();
        if fields.is_empty() {
            return Ok(None);
        }
        let mut names = HashSet::new();
        let normal = &bundle.normal_fns;
        let invariants = bundle.extras.invariants.iter().map(|i| &i.func);
        let lemmas = bundle.extras.lemmas.iter().map(|l| &l.func);
        reserve(quote! {#(#normal)* #(#invariants)* #(#lemmas)*}, &mut names);
        let field_ast = &sm.fields_named_ast;
        let generics_ast = &sm.generics;
        reserve(quote! {#field_ast #generics_ast}, &mut names);
        for tr in &sm.transitions {
            names.insert(tr.name.to_string());
            reserve_stmt(&tr.body, &mut names);
            for param in &tr.params {
                let ty = &param.ty;
                reserve(quote! {#ty}, &mut names);
            }
        }
        let mut key_variants = vec![];
        let mut value_variants = vec![];
        for f in &fields {
            let n = &f.name;
            match &f.stype {
                ShardableType::StorageOption(v) => {
                    key_variants.push(quote! {#n,});
                    value_variants.push(quote! {#n(#v),});
                }
                ShardableType::StorageMap(k, v) | ShardableType::StorageIMap(k, v) => {
                    key_variants.push(quote! {#n(#k),});
                    value_variants.push(quote! {#n(#v),});
                }
                _ => return Err(Error::new(f.type_span, "unsupported storage strategy")),
            }
        }
        // The storage helpers are items of the machine's module; a machine
        // whose own items or identifiers use one of their names is rejected.
        for field in &fields {
            for prefix in HELPERS {
                let helper = format!("{prefix}{}", field.name);
                if names.contains(&helper) {
                    return Err(Error::new(
                        field.name.span(),
                        format!(
                            "`{helper}` conflicts with a generated storage helper of field `{}`",
                            field.name
                        ),
                    ));
                }
            }
        }
        let key = Enum::new(sm, fresh(&mut names, "__StorageKey"), &quote! {#(#key_variants)*});
        let value =
            Enum::new(sm, fresh(&mut names, "__StorageValue"), &quote! {#(#value_variants)*});
        let helpers = Params::new(sm, &quote! {#(#key_variants)* #(#value_variants)*});
        let dom_fn = fresh(&mut names, "__storage_dom");
        let val_fn = fresh(&mut names, "__storage_val");
        let options_only =
            fields.iter().all(|f| matches!(f.stype, ShardableType::StorageOption(_)));
        let by_tags = options_only || fields.len() == 1;
        Ok(Some(Tagged { fields, key, value, helpers, dom_fn, val_fn, options_only, by_tags }))
    }

    /// The key type (`__StorageKey<..>`).
    pub fn key_ty(&self) -> TokenStream {
        self.key.ty.clone()
    }

    /// The value type (`__StorageValue<..>`).
    pub fn value_ty(&self) -> TokenStream {
        self.value.ty.clone()
    }

    /// The storage type, `IMap<__StorageKey<..>, __StorageValue<..>>`.
    pub fn ty(&self) -> TokenStream {
        let (k, v) = (&self.key.ty, &self.value.ty);
        quote! {::vstd::imap::IMap<#k, #v>}
    }

    fn path(&self) -> TokenStream {
        let (k, v) = (&self.key.ty, &self.value.ty);
        quote! {::vstd::imap::IMap::<#k, #v>}
    }

    /// The empty storage.
    pub fn unit(&self) -> TokenStream {
        let p = self.path();
        quote! {#p::empty()}
    }

    pub fn tracked_unit(&self) -> TokenStream {
        let p = self.path();
        quote! {#p::tracked_empty()}
    }

    /// The storage key of field `f` at `k` (`None` for a `storage_option` field).
    pub fn key_of(&self, f: &Ident, k: Option<&TokenStream>) -> TokenStream {
        let kp = &self.key.path;
        match k {
            Some(k) => quote! {#kp::#f(#k)},
            None => quote! {#kp::#f},
        }
    }

    /// The storage value holding payload `v` of field `f`.
    pub fn wrap(&self, f: &Ident, v: TokenStream) -> TokenStream {
        let vp = &self.value.path;
        quote! {#vp::#f(#v)}
    }

    /// The payload of field `f` in the storage value `v`.
    pub fn payload(&self, f: &Ident, v: TokenStream) -> TokenStream {
        let a = accessor(f);
        quote! {(#v)->#a}
    }

    /// Statements turning the tracked storage value `name` of field `f` into
    /// its payload (rebinding `name`).
    pub fn unwrap(&self, f: &Ident, name: &Ident) -> TokenStream {
        let vp = &self.value.path;
        let other = self.other_value_arm(quote! {None});
        quote! {
            let tracked #name = match #name {#vp::#f(__tsm_x) => Some(__tsm_x), #other};
            let tracked #name = ::vstd::std_specs::option::OptionAdditionalFns::tracked_unwrap(#name);
        }
    }

    /// A catch-all match arm on keys (none when the key enum has one variant).
    fn other_key_arm(&self, value: TokenStream) -> TokenStream {
        if self.fields.len() > 1 {
            quote! {_ => #value,}
        } else {
            quote! {}
        }
    }

    /// A catch-all match arm on values (none when the value enum has one variant).
    fn other_value_arm(&self, value: TokenStream) -> TokenStream {
        self.other_key_arm(value)
    }

    /// The path of the storage helper `<prefix><f>` of field `f` (e.g.
    /// `__pack_f::<T>`), with the parameters it is generic over.
    pub fn helper(&self, prefix: &str, f: &Ident) -> TokenStream {
        let name = format_ident!("{}{}", prefix, f);
        let used = &self.helpers.used;
        if used.is_empty() {
            quote! {#name}
        } else {
            quote! {#name::<#(#used),*>}
        }
    }

    /// The tagged part of the general operand `e` of field `f` (`__tag_f`).
    pub fn tagged(&self, f: &Field, e: &TokenStream) -> TokenStream {
        let tag = self.helper("__tag_", &f.name);
        match &f.stype {
            ShardableType::StorageMap(..) => quote! {#tag((#e).to_imap())},
            _ => quote! {#tag(#e)},
        }
    }

    /// The deposit (or guarded storage) of one storage statement of field
    /// `field` with operand `elt`.
    pub fn singleton(&self, field: &Ident, elt: &MonoidElt) -> Result<TokenStream, Error> {
        let unit = self.unit();
        match elt {
            MonoidElt::OptionSome(Some(v)) => {
                let (k, v) = (self.key_of(field, None), self.wrap(field, quote! {#v}));
                Ok(quote! {#unit.insert(#k, #v)})
            }
            MonoidElt::SingletonKV(k, Some(v)) => {
                let (k, v) =
                    (self.key_of(field, Some(&quote! {#k})), self.wrap(field, quote! {#v}));
                Ok(quote! {#unit.insert(#k, #v)})
            }
            MonoidElt::General(v) => {
                let f = self
                    .fields
                    .iter()
                    .find(|f| f.name == *field)
                    .ok_or_else(|| Error::new(field.span(), "unknown storage field"))?;
                Ok(self.tagged(f, &quote! {#v}))
            }
            _ => Err(Error::new(
                field.span(),
                "verified deposit requires an explicit optional or map value",
            )),
        }
    }

    /// The union of the tagged parts of the storage fields of state `s`.
    fn tags(&self, s: &TokenStream) -> TokenStream {
        let tags: Vec<_> = self
            .fields
            .iter()
            .map(|f| {
                let tag = self.helper("__tag_", &f.name);
                let n = &f.name;
                match f.stype {
                    ShardableType::StorageMap(..) => quote! {#tag(#s.#n.to_imap())},
                    _ => quote! {#tag(#s.#n)},
                }
            })
            .collect();
        balanced_union(&tags)
    }

    /// The storage of state `s` (of type `State<..>`).
    pub fn projection(&self, s: TokenStream) -> TokenStream {
        if self.by_tags {
            // One tagged part, or finite unions of singleton maps (solvers
            // reason about these more reliably than about a closure-defined
            // domain).
            self.tags(&s)
        } else {
            // The per-key case split is a named function: instantiating the
            // map's closures then costs a call, not a copy of the case split
            // over every storage field.
            let (kt, dom, val) = (&self.key.ty, &self.dom_fn, &self.val_fn);
            quote! {::vstd::imap::IMap::new(|__tsm_key: #kt| State::#dom(#s, __tsm_key),
            |__tsm_key: #kt| State::#val(#s, __tsm_key))}
        }
    }

    /// The declarations of the enums and the storage helpers, emitted once in
    /// the machine's module, and the per-key functions of the state's storage
    /// (in `impl State`; `decl`/`wc` are the machine's generic parameters and
    /// where clause, `st` the state type).
    pub fn decl(&self, decl: &TokenStream, wc: &TokenStream, st: &TokenStream) -> TokenStream {
        let (kn, vn) = (&self.key.name, &self.value.name);
        let (kd, vd) = (&self.key.params.decl, &self.value.params.decl);
        let (kw, vw) = (&self.key.params.wc, &self.value.params.wc);
        let (ka, va) = (&self.key.params.attrs, &self.value.params.attrs);
        let (kt, vt) = (&self.key.ty, &self.value.ty);
        let (kp, vp) = (&self.key.path, &self.value.path);
        let map = self.ty();
        let mp = self.path();
        // The helpers' generic parameters (with a lifetime for the borrows).
        let (hd, hw) = (&self.helpers.decl, &self.helpers.wc);
        let list = &self.helpers.list;
        let bd = if self.helpers.used.is_empty() {
            quote! {<'a>}
        } else {
            quote! {<'a, #list>}
        };
        let mut key_variants = vec![];
        let mut value_variants = vec![];
        let mut domains = vec![];
        let mut values = vec![];
        let mut helpers = vec![];
        let groups = quote! {broadcast use {::vstd::map::group_map_lemmas, ::vstd::imap::group_imap_lemmas,
        ::vstd::set::group_set_lemmas, ::vstd::iset::group_iset_lemmas};};
        for f in &self.fields {
            let n = &f.name;
            let acc = accessor(n);
            let tag = format_ident!("__tag_{}", n);
            let untag = format_ident!("__untag_{}", n);
            let pack = format_ident!("__pack_{}", n);
            let unpack = format_ident!("__unpack_{}", n);
            let borrow = format_ident!("__borrow_{}", n);
            // The helpers' paths (with the parameters: a field's types need
            // not determine them, e.g. through an associated type).
            let (tag_c, untag_c, pack_c, unpack_c) = (
                self.helper("__tag_", n),
                self.helper("__untag_", n),
                self.helper("__pack_", n),
                self.helper("__unpack_", n),
            );
            let tag_finite_c = self.helper("__tag_finite_", n);
            let unwrap = format_ident!("__unwrap_{}", n);
            let payload = match &f.stype {
                ShardableType::StorageOption(v)
                | ShardableType::StorageMap(_, v)
                | ShardableType::StorageIMap(_, v) => v,
                _ => unreachable!(),
            };
            let none = self.other_value_arm(quote! {None});
            helpers.push(quote! {
                /// The payload of a storage value of the storage field.
                pub proof fn #unwrap #hd (tracked value: #vt) -> (tracked out: #payload) #hw
                    requires value is #n,
                    ensures value == #vp::#n(out),
                {
                    let tracked out = match value { #vp::#n(out) => Some(out), #none };
                    ::vstd::std_specs::option::OptionAdditionalFns::tracked_unwrap(out)
                }
            });
            match &f.stype {
                ShardableType::StorageOption(v) => {
                    key_variants.push(quote! {#n,});
                    value_variants.push(quote! {#n(#v),});
                    domains.push(quote! {#kp::#n => s.#n is Some,});
                    values.push(quote! {#kp::#n => #vp::#n(s.#n->Some_0),});
                    let untag_tag = format_ident!("__untag_tag_{}", n);
                    let other = self.other_value_arm(quote! {None});
                    helpers.push(quote! {
                        /// The tagged part holding the value of the storage field.
                        pub open spec fn #tag #hd (input: Option<#v>) -> #map #hw {
                            match input {
                                Some(value) => #mp::empty().insert(#kp::#n, #vp::#n(value)),
                                None => #mp::empty(),
                            }
                        }
                        /// The value of the storage field in a tagged map.
                        pub open spec fn #untag #hd (input: #map) -> Option<#v> #hw {
                            if input.contains_key(#kp::#n) && input[#kp::#n] is #n {
                                Some(input[#kp::#n]->#acc)
                            } else {
                                None
                            }
                        }
                        pub proof fn #untag_tag #hd (input: Option<#v>) #hw
                            ensures #untag_c(#tag_c(input)) == input,
                        {
                        }
                        pub proof fn #pack #hd (tracked input: Option<#v>) -> (tracked output: #map) #hw
                            ensures output == #tag_c(input),
                        {
                            match input {
                                Some(value) => {
                                    let tracked mut output = #mp::tracked_empty();
                                    output.tracked_insert(#kp::#n, #vp::#n(value));
                                    output
                                }
                                None => #mp::tracked_empty(),
                            }
                        }
                        pub proof fn #unpack #hd (tracked input: #map) -> (tracked output: Option<#v>) #hw
                            requires input == #tag_c(#untag_c(input)),
                            ensures output == #untag_c(input),
                        {
                            if input.contains_key(#kp::#n) {
                                let tracked mut input = input;
                                let tracked value = input.tracked_remove(#kp::#n);
                                match value { #vp::#n(value) => Some(value), #other }
                            } else {
                                None
                            }
                        }
                        pub proof fn #borrow #bd (tracked input: &'a #map) -> (tracked output: Option<&'a #v>) #hw
                            requires input.contains_key(#kp::#n), input[#kp::#n] is #n,
                            ensures output is Some, *output->Some_0 == input[#kp::#n]->#acc,
                        {
                            let tracked value = input.tracked_borrow(#kp::#n);
                            match value { #vp::#n(value) => Some(value), #other }
                        }
                    });
                }
                ShardableType::StorageMap(k, v) | ShardableType::StorageIMap(k, v) => {
                    key_variants.push(quote! {#n(#k),});
                    value_variants.push(quote! {#n(#v),});
                    let local = if matches!(f.stype, ShardableType::StorageMap(..)) {
                        quote! {s.#n.to_imap()}
                    } else {
                        quote! {s.#n}
                    };
                    domains.push(quote! {#kp::#n(key) => (#local).contains_key(key),});
                    values.push(quote! {#kp::#n(key) => #vp::#n((#local)[key]),});
                    let tag_finite = format_ident!("__tag_finite_{}", n);
                    let tag_shape = format_ident!("__tag_shape_{}", n);
                    let no_key = self.other_key_arm(quote! {false});
                    let no_value = self.other_key_arm(quote! {::vstd::prelude::arbitrary()});
                    let other_key = self.other_key_arm(quote! {::vstd::prelude::arbitrary()});
                    let other = self.other_value_arm(quote! {None});
                    helpers.push(quote! {
                        /// The tagged part holding the map of the storage field.
                        pub open spec fn #tag #hd (input: ::vstd::imap::IMap<#k, #v>) -> #map #hw {
                            ::vstd::imap::IMap::new(
                                |key: #kt| match key { #kp::#n(local) => input.contains_key(local), #no_key },
                                |key: #kt| match key { #kp::#n(local) => #vp::#n(input[local]), #no_value },
                            )
                        }
                        /// The map of the storage field in a tagged map.
                        pub open spec fn #untag #hd (input: #map) -> ::vstd::imap::IMap<#k, #v> #hw {
                            ::vstd::imap::IMap::new(
                                |key: #k| input.contains_key(#kp::#n(key)) && input[#kp::#n(key)] is #n,
                                |key: #k| input[#kp::#n(key)]->#acc,
                            )
                        }
                        /// Tagging a finite map gives a finite map, and untagging undoes it.
                        pub proof fn #tag_shape #hd (input: ::vstd::imap::IMap<#k, #v>) #hw
                            requires input.dom().finite(),
                            ensures #tag_c(input).dom().finite(), #untag_c(#tag_c(input)) == input,
                        {
                            let inject = |key: #k| #kp::#n(key);
                            input.dom().lemma_map_finite(inject);
                            assert(::vstd::prelude::ext_equal(#tag_c(input).dom(), input.dom().map(inject)));
                            assert(::vstd::prelude::ext_equal(#untag_c(#tag_c(input)), input));
                        }
                        pub proof fn #tag_finite #hd (input: ::vstd::map::Map<#k, #v>) #hw
                            ensures #tag_c(input.to_imap()).dom().finite(),
                            decreases input.len(),
                        {
                            #groups
                            ::vstd::set_lib::lemma_set_empty_equivalency_len(input.dom());
                            if input.len() == 0 {
                                assert(::vstd::prelude::ext_equal(#tag_c(input.to_imap()).dom(), ::vstd::iset::ISet::<#kt>::empty()));
                            } else {
                                let key = choose|key: #k| input.dom().contains(key);
                                ::vstd::set::lemma_set_remove_len(input.dom(), key);
                                #tag_finite_c(input.remove(key));
                                assert(::vstd::prelude::ext_equal(#tag_c(input.to_imap()).dom(),
                                    #tag_c(input.remove(key).to_imap()).dom().insert(#kp::#n(key))));
                            }
                        }
                        /// The tagged part of a finite map of the storage field.
                        pub proof fn #pack #hd (tracked input: ::vstd::map::Map<#k, #v>) -> (tracked output: #map) #hw
                            ensures output == #tag_c(input.to_imap()), output.dom().finite(), output.dom().len() == input.len(),
                            decreases input.len(),
                        {
                            #groups
                            let ghost original = input;
                            ::vstd::set_lib::lemma_set_empty_equivalency_len(input.dom());
                            if input.len() == 0 {
                                let tracked output = #mp::tracked_empty();
                                assert(::vstd::prelude::ext_equal(output, #tag_c(original.to_imap())));
                                output
                            } else {
                                let key = choose|key: #k| input.dom().contains(key);
                                ::vstd::set::lemma_set_remove_len(input.dom(), key);
                                let tracked mut input = input;
                                let tracked value = input.tracked_remove(key);
                                let tracked mut output = #pack_c(input);
                                output.tracked_insert(#kp::#n(key), #vp::#n(value));
                                assert(::vstd::prelude::ext_equal(output, #tag_c(original.to_imap())));
                                output
                            }
                        }
                        /// The finite map of the storage field in a finite tagged part.
                        pub proof fn #unpack #hd (tracked input: #map) -> (tracked output: ::vstd::map::Map<#k, #v>) #hw
                            requires input.dom().finite(), input == #tag_c(#untag_c(input)),
                            ensures output.to_imap() == #untag_c(input),
                            decreases input.dom().len(),
                        {
                            #groups
                            let ghost original = input;
                            ::vstd::iset_lib::lemma_iset_empty_equivalency_len(input.dom());
                            if input.dom().len() == 0 {
                                let tracked output = ::vstd::map::Map::tracked_empty();
                                assert(::vstd::prelude::ext_equal(output.to_imap(), #untag_c(original)));
                                output
                            } else {
                                let key = input.dom().choose();
                                ::vstd::iset::lemma_iset_choose_len(input.dom());
                                let native_key = match key { #kp::#n(key) => key, #other_key };
                                assert(key == #kp::#n(native_key));
                                ::vstd::iset::lemma_iset_remove_len(input.dom(), key);
                                let tracked mut input = input;
                                let tracked value = input.tracked_remove(key);
                                let tracked value = match value { #vp::#n(value) => Some(value), #other };
                                assert(value is Some);
                                let tracked value = ::vstd::std_specs::option::OptionAdditionalFns::tracked_unwrap(value);
                                assert(::vstd::prelude::ext_equal(input, #tag_c(#untag_c(input))));
                                let tracked mut output = #unpack_c(input);
                                // The removed key is the only difference.
                                let ghost expected = #untag_c(input).insert(native_key, value);
                                assert(::vstd::prelude::ext_equal(#untag_c(original), expected)) by {
                                    assert forall|other: #k| #untag_c(original).contains_key(other) == #[trigger] expected.contains_key(other) by {
                                        if other != native_key {
                                            assert(#kp::#n(other) != key);
                                        }
                                    }
                                    assert forall|other: #k| #[trigger] expected.contains_key(other)
                                        implies #untag_c(original)[other] == expected[other] by {
                                        if other != native_key {
                                            assert(#kp::#n(other) != key);
                                        }
                                    }
                                }
                                output.tracked_insert(native_key, value);
                                assert(::vstd::prelude::ext_equal(output.to_imap(), #untag_c(original)));
                                output
                            }
                        }
                        pub proof fn #borrow #bd (tracked input: &'a #map, key: #k) -> (tracked output: Option<&'a #v>) #hw
                            requires input.contains_key(#kp::#n(key)), input[#kp::#n(key)] is #n,
                            ensures output is Some, *output->Some_0 == input[#kp::#n(key)]->#acc,
                        {
                            let tracked value = input.tracked_borrow(#kp::#n(key));
                            match value { #vp::#n(value) => Some(value), #other }
                        }
                    });
                }
                _ => unreachable!(),
            }
        }
        let storage_fns = if self.by_tags {
            quote! {}
        } else {
            let (dom, val) = (&self.dom_fn, &self.val_fn);
            quote! {
                /// Whether the storage of `s` holds `key`.
                pub open spec fn #dom(s: #st, key: #kt) -> bool { match key { #(#domains)* } }
                /// The storage of `s` at `key`.
                pub open spec fn #val(s: #st, key: #kt) -> #vt { match key { #(#values)* } }
            }
        };
        quote! {
            /// The keys of the machine's storage: one variant per storage field.
            #[allow(non_camel_case_types)]
            #(#ka)* pub enum #kn #kd #kw { #(#key_variants)* }
            /// The values of the machine's storage: one variant per storage field, holding its payload.
            #[allow(non_camel_case_types)]
            #(#va)* pub tracked enum #vn #vd #vw { #(#value_variants)* }
            impl #decl #st #wc {
                #storage_fns
            }
            #(#helpers)*
        }
    }

    pub fn op(&self, a: TokenStream, b: TokenStream) -> TokenStream {
        quote! {(#a).union_prefer_right(#b)}
    }

    pub fn disjoint(&self, a: TokenStream, b: TokenStream) -> TokenStream {
        quote! {(#a).dom().disjoint((#b).dom())}
    }

    /// `a` without the keys of `b`.
    pub fn minus(&self, a: TokenStream, b: TokenStream) -> TokenStream {
        quote! {(#a).remove_keys((#b).dom())}
    }

    pub fn le(&self, a: TokenStream, b: TokenStream) -> TokenStream {
        quote! {(#a).submap_of(#b)}
    }

    pub fn agrees(&self, a: TokenStream, b: TokenStream) -> TokenStream {
        quote! {(#a).agrees(#b)}
    }

    /// A proof of `goal` (about the key `index`) by a case split on the key's
    /// storage field.
    pub fn cases(&self, index: &Ident, goal: &TokenStream) -> TokenStream {
        self.cases_by_steps(index, &[goal.clone()])
    }

    /// A case split on the storage field of the key `index`, asserting the
    /// `steps` in order in each case.
    fn cases_by_steps(&self, index: &Ident, steps: &[TokenStream]) -> TokenStream {
        let kp = &self.key.path;
        let arms: Vec<_> = self
            .fields
            .iter()
            .map(|f| {
                let n = &f.name;
                if matches!(f.stype, ShardableType::StorageOption(_)) {
                    quote! {#kp::#n => {#(assert(#steps);)*},}
                } else {
                    quote! {#kp::#n(..) => {#(assert(#steps);)*},}
                }
            })
            .collect();
        quote! {match #index {#(#arms)*}}
    }

    /// The per-key hint of the pointwise proofs below: the storage of a
    /// machine with only `storage_option` fields (a union of singleton maps)
    /// needs the case split on the key's field.
    fn hint(&self, index: &Ident, goal: TokenStream) -> TokenStream {
        if self.options_only {
            self.cases(index, &goal)
        } else {
            quote! {}
        }
    }

    /// `a == b`, pointwise.
    pub fn prove_eq(&self, idx: &Ident, a: TokenStream, b: TokenStream) -> TokenStream {
        let dom = self.hint(idx, quote! {(#a).contains_key(#idx) == (#b).contains_key(#idx)});
        quote! {
            assert(::vstd::prelude::ext_equal(#a, #b)) by {
                assert forall|#idx| (#a).contains_key(#idx) == (#b).contains_key(#idx) by {#dom};
                assert forall|#idx| (#a).contains_key(#idx) implies (#a)[#idx] == (#b)[#idx] by {};
            }
        }
    }

    /// `agrees(a, b)`, pointwise.
    pub fn prove_agrees(&self, idx: &Ident, a: TokenStream, b: TokenStream) -> TokenStream {
        self.prove_agrees_at(idx, a, b, None)
    }

    /// `prove_agrees`; with `replace`, the pointwise goal is checked at a deposit that may
    /// replace a stored value, with the hint of `assert_storage_no_replace`.
    pub fn prove_agrees_at(
        &self,
        idx: &Ident,
        a: TokenStream,
        b: TokenStream,
        replace: Option<Span>,
    ) -> TokenStream {
        let goal = quote! {(#a)[#idx] == (#b)[#idx]};
        let mut hint = self.hint(idx, goal.clone());
        if let Some(span) = replace {
            let check = no_replace_check(span, goal);
            hint = quote! {#hint #check};
        }
        quote! {
            assert((#a).agrees(#b)) by {
                assert forall|#idx| (#a).contains_key(#idx) && (#b).contains_key(#idx) implies (#a)[#idx] == (#b)[#idx] by {#hint};
            }
        }
    }

    /// `le(a, b)`, pointwise.
    pub fn prove_le(&self, idx: &Ident, a: TokenStream, b: TokenStream) -> TokenStream {
        self.prove_le_with(idx, a, b, false)
    }

    /// `le(a, b)`, pointwise, by a case split on each key's storage field.
    pub fn prove_le_by_cases(&self, idx: &Ident, a: TokenStream, b: TokenStream) -> TokenStream {
        self.prove_le_with(idx, a, b, true)
    }

    fn prove_le_with(
        &self,
        idx: &Ident,
        a: TokenStream,
        b: TokenStream,
        by_cases: bool,
    ) -> TokenStream {
        let goal = quote! {(#b).contains_key(#idx) && (#a)[#idx] == (#b)[#idx]};
        // In each case, the key's presence first: the value equality then
        // follows from the same field's facts.
        let hint = if by_cases {
            self.cases_by_steps(idx, &[quote! {(#b).contains_key(#idx)}, goal.clone()])
        } else {
            quote! {}
        };
        quote! {
            assert((#a).submap_of(#b)) by {
                assert forall|#idx| (#a).contains_key(#idx) implies #goal by {#hint};
            }
        }
    }

    /// `disjoint(a, b)`, pointwise.
    pub fn prove_disjoint(&self, idx: &Ident, a: TokenStream, b: TokenStream) -> TokenStream {
        self.prove_disjoint_at(idx, a, b, None)
    }

    /// `prove_disjoint`; with `replace`, as in `prove_agrees_at`.
    pub fn prove_disjoint_at(
        &self,
        idx: &Ident,
        a: TokenStream,
        b: TokenStream,
        replace: Option<Span>,
    ) -> TokenStream {
        let hint = match replace {
            Some(span) => no_replace_check(span, quote! {!(#b).contains_key(#idx)}),
            None => quote! {},
        };
        quote! {
            assert((#a).dom().disjoint((#b).dom())) by {
                assert forall|#idx| (#a).contains_key(#idx) implies !(#b).contains_key(#idx) by {#hint};
            }
        }
    }
}

/// The check of `goal` at a deposit (`span`) that may be at a location withdrawn earlier in the
/// same transition: it fails with the hint to split the transition.
fn no_replace_check(span: Span, goal: TokenStream) -> TokenStream {
    quote::quote_spanned! {span=> ::vstd::state_machine_internal::assert_storage_no_replace(#goal);}
}
