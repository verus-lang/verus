//! Nominal physical owners. Descriptor resources carry identity and immutable
//! metadata only; every operation consumes a genuine checked storage owner.
use crate::ast::*;
use crate::field_access_visitor::visit_field_accesses;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

struct Generics {
    decl: TokenStream,
    wc: TokenStream,
    attrs: Vec<verus_syn::Attribute>,
    types: TokenStream,
    expr: TokenStream,
}

fn generics(sm: &SM) -> Generics {
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    Generics {
        decl,
        wc,
        attrs,
        types: args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default(),
        expr: args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default(),
    }
}

fn fresh(sm: &SM, tr: &Transition, label: &str) -> Ident {
    let mut unavailable: HashSet<_> = sm.fields.iter().map(|f| f.name.to_string()).collect();
    unavailable.extend(tr.params.iter().map(|p| p.name.to_string()));
    fn bindings(stmt: &TransitionStmt, out: &mut HashSet<String>) {
        struct Names<'a>(&'a mut HashSet<String>);
        impl<'ast> verus_syn::visit::Visit<'ast> for Names<'_> {
            fn visit_ident(&mut self, ident: &'ast Ident) {
                self.0.insert(ident.to_string());
            }
        }
        use verus_syn::visit::Visit;
        match stmt {
            TransitionStmt::Block(_, children) => {
                for child in children {
                    bindings(child, out);
                }
            }
            TransitionStmt::Split(_, split, children) => {
                match &**split {
                    SplitKind::Let(pat, ..) => Names(out).visit_pat(pat),
                    SplitKind::Special(_, _, _, Some(pat)) => Names(out).visit_pat(pat),
                    SplitKind::Match(_, arms) => {
                        for arm in arms {
                            Names(out).visit_pat(&arm.pat);
                        }
                    }
                    _ => {}
                }
                for child in children {
                    bindings(child, out);
                }
            }
            _ => {}
        }
    }
    bindings(&tr.body, &mut unavailable);
    let mut candidate = format!("__tsm_storage_{label}");
    while unavailable.contains(&candidate) {
        candidate.push('_');
    }
    Ident::new(&candidate, Span::mixed_site())
}

fn initial(
    stmt: &TransitionStmt,
    values: &mut HashMap<String, Expr>,
    requirements: &mut Vec<Expr>,
) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                initial(child, values, requirements)?;
            }
        }
        TransitionStmt::Initialize(_, name, value) => {
            values.insert(name.to_string(), value.clone());
        }
        TransitionStmt::Require(_, value) => requirements.push(value.clone()),
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "physical field initializer requires straight-line initialization",
            ))
        }
    }
    Ok(())
}

#[derive(Default)]
struct Operation {
    updates: HashMap<String, Expr>,
    requirements: Vec<Expr>,
    assertions: Vec<Expr>,
    physical: Option<(SpecialOp, Option<Box<verus_syn::Pat>>)>,
    hidden: Option<(Box<verus_syn::Pat>, Expr)>,
}

fn operation(stmt: &TransitionStmt, out: &mut Operation) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            for child in children {
                operation(child, out)?;
            }
        }
        TransitionStmt::Update(_, name, value) => {
            if out
                .updates
                .insert(name.to_string(), value.clone())
                .is_some()
            {
                return Err(Error::new(
                    name.span(),
                    "physical field facade requires one write per field",
                ));
            }
        }
        TransitionStmt::Require(_, value) => out.requirements.push(value.clone()),
        TransitionStmt::Assert(_, value, _) => out.assertions.push(value.clone()),
        TransitionStmt::Split(_, split, children) => {
            if let SplitKind::Let(pattern, _, LetKind::BirdsEye, value) = &**split {
                if out
                    .hidden
                    .replace((pattern.clone(), value.clone()))
                    .is_some()
                {
                    return Err(Error::new(
                        *stmt.get_span(),
                        "grouped physical facade currently supports one selected physical binding",
                    ));
                }
                for child in children {
                    operation(child, out)?;
                }
                return Ok(());
            }
            let SplitKind::Special(_, op, _, pattern) = &**split else {
                return Err(Error::new(
                    *stmt.get_span(),
                    "physical field facade currently requires straight-line operations",
                ));
            };
            if !matches!(op.stmt, MonoidStmtType::Deposit | MonoidStmtType::Withdraw)
                || out
                    .physical
                    .replace((op.clone(), pattern.clone()))
                    .is_some()
            {
                return Err(Error::new(
                    *stmt.get_span(),
                    "physical field facade currently supports one deposit or withdrawal",
                ));
            }
            for child in children {
                operation(child, out)?;
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "unsupported physical field operation",
            ))
        }
    }
    Ok(())
}

fn native(
    input: &Expr,
    fields: &HashMap<String, Field>,
    arguments: &HashMap<String, Ident>,
    before: Option<&TokenStream>,
    old: bool,
    mutable: Option<&HashSet<String>>,
) -> Result<TokenStream, Error> {
    let mut expression = input.clone();
    let mut errors = Vec::new();
    visit_field_accesses(
        &mut expression,
        |errors, field, node| {
            let getter = format_ident!("value_{}", field.name);
            *node = Expr::Verbatim(if let Some(before) = before {
                quote! {#before.#getter()}
            } else if matches!(field.stype, ShardableType::Constant(_)) {
                let n = &field.name;
                quote! {self.#n()}
            } else if let Some(argument) = arguments.get(&field.name.to_string()) {
                if old
                    && mutable
                        .map(|names| names.contains(&field.name.to_string()))
                        .unwrap_or(true)
                {
                    quote! {old(#argument).value()}
                } else {
                    quote! {#argument.value()}
                }
            } else {
                errors.push(Error::new(
                    field.name.span(),
                    "physical expressions require an actually supplied ordinary field",
                ));
                quote! {false}
            });
        },
        &mut errors,
        fields,
    );
    if let Some(error) = errors.into_iter().next() {
        return Err(error);
    }
    Ok(quote! {#expression})
}

fn footprint(
    expression: &Expr,
    fields: &HashMap<String, Field>,
    used: &mut HashSet<String>,
) -> Result<(), Error> {
    let mut expression = expression.clone();
    let mut errors = Vec::new();
    visit_field_accesses(
        &mut expression,
        |_, field, _| {
            used.insert(field.name.to_string());
        },
        &mut errors,
        fields,
    );
    if let Some(error) = errors.into_iter().next() {
        return Err(error);
    }
    Ok(())
}

fn sum(parts: &[TokenStream], expr: &TokenStream) -> TokenStream {
    parts.iter().fold(
        quote! {Fragment #expr::empty()},
        |sum, part| quote! {Fragment #expr::op(#sum,#part)},
    )
}

fn validate(sm: &SM) -> Result<(), Error> {
    let mut names: HashSet<String> = [
        "Instance",
        "Protocol",
        "State",
        "Fragment",
        "Token",
        "TransitionObservation",
        "__StorageMetadata",
    ]
    .iter()
    .map(|name| name.to_string())
    .collect();
    for field in &sm.fields {
        if !names.insert(field.name.to_string()) {
            return Err(Error::new(
                field.name.span(),
                "physical field type conflicts with a generated type",
            ));
        }
    }
    let mut methods: HashSet<String> = ["id", "clone", "invariant", "__read_included_transitive"]
        .iter()
        .map(|name| name.to_string())
        .collect();
    for field in &sm.fields {
        if matches!(field.stype, ShardableType::Constant(_))
            && !methods.insert(field.name.to_string())
        {
            return Err(Error::new(
                field.name.span(),
                "constant conflicts with a physical instance method",
            ));
        }
    }
    for transition in &sm.transitions {
        if !methods.insert(transition.name.to_string()) {
            return Err(Error::new(
                transition.name.span(),
                "transition conflicts with a physical instance method",
            ));
        }
    }
    for transition in &sm.transitions {
        if transition.kind != TransitionKind::Init
            && !methods.insert(format!("__physical_raw_{}", transition.name))
        {
            return Err(Error::new(
                transition.name.span(),
                "transition conflicts with a physical instance helper",
            ));
        }
    }
    Ok(())
}

/// Grouping consumes only actual owners. Read-only inputs are independently
/// included in one actual borrowed upper, then projected and lawfully weakened.
pub fn output(sm: &SM, selected: &HashSet<String>) -> Result<TokenStream, Error> {
    validate(sm)?;
    let Some(first_transition) = sm.transitions.first() else {
        return Err(Error::new(
            sm.name.span(),
            "physical field facade requires checked initialization",
        ));
    };
    let location_field = fresh(sm, first_transition, "protocol_loc");
    let marker_field = fresh(sm, first_transition, "types");
    let Generics {
        decl,
        wc,
        attrs,
        types,
        expr,
    } = generics(sm);
    let token = quote! {Token #types};
    let constants: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(_)))
        .collect();
    let variables: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Variable(_)))
        .collect();
    let storage: Vec<_> = sm.fields.iter().filter(|f| f.stype.is_storage()).collect();
    if variables.is_empty()
        || storage.len() != 1
        || sm.fields.iter().any(|f| {
            !matches!(
                f.stype,
                ShardableType::Variable(_)
                    | ShardableType::Constant(_)
                    | ShardableType::StorageOption(_)
            )
        })
    {
        return Err(Error::new(
            sm.name.span(),
            "grouped physical facade requires variables, constants and one optional store",
        ));
    }
    let ShardableType::StorageOption(permission_ty) = &storage[0].stype else {
        unreachable!()
    };
    let storage_name = &storage[0].name;
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
    let ct: Vec<_> = constants.iter().map(|f| f.get_type()).collect();
    let setters: Vec<_> = cn.iter().map(|n| format_ident!("with_{n}")).collect();
    let cget: Vec<_> = cn.iter().map(|n| format_ident!("value_{n}")).collect();
    let metadata = quote! {__StorageMetadata #types};
    let descriptor = quote! {::vstd::resource::tsm_context::Descriptor<#metadata>};
    let generic_args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let marker = generic_args
        .as_ref()
        .map(|args| quote! {ghost #marker_field:core::marker::PhantomData<(#args,)>,});
    let marker_value = generic_args
        .as_ref()
        .map(|_| quote! {#marker_field:core::marker::PhantomData,});
    let mut wrappers = Vec::new();
    for field in &variables {
        let n = &field.name;
        let ty = field.get_type();
        let factory = format_ident!("field_{n}");
        let getter = format_ident!("value_{n}");
        let owns = format_ident!("owns_{n}");
        wrappers.push(quote!{
            #(#attrs)*#[allow(non_camel_case_types)]
            pub tracked struct #n #decl #wc {raw:Tracked<Option<#token>>,metadata:#descriptor}
            impl #decl #n #types #wc {
                #[verifier::type_invariant]
                spec fn invariant(self)->bool {
                    self.raw@ is Some
                    &&self.raw@->Some_0.loc()==self.metadata.value().#location_field
                    &&self.raw@->Some_0.fragment().#owns()
                    &&self.raw@->Some_0.fragment()==Fragment #expr::#factory(self.value())
                        #(.#setters(self.metadata.value().#cn))*
                }
                pub closed spec fn instance_id(&self)->::vstd::resource::Loc{self.metadata.id()}
                pub closed spec fn value(&self)->#ty{self.raw@->Some_0.fragment().#getter()}
                pub closed spec fn resource_location(&self)->::vstd::resource::Loc{self.raw@->Some_0.loc()}
                pub closed spec fn raw_fragment(&self)->Fragment #types{self.raw@->Some_0.fragment()}
                pub proof fn borrow_token(tracked &self)->(tracked out:&#token)
                    ensures out.loc()==self.resource_location(),out.fragment()==self.raw_fragment(),
                        out.fragment().#owns(),out.fragment().#getter()==self.value(),
                {::vstd::prelude::use_type_invariant(self);self.raw.borrow().tracked_borrow()}
                proof fn __from_token(tracked raw:#token,tracked metadata:#descriptor)->(tracked out:Self)
                    requires raw.loc()==metadata.value().#location_field,raw.fragment().#owns(),
                        raw.fragment()==Fragment #expr::#factory(raw.fragment().#getter())
                            #(.#setters(metadata.value().#cn))*,
                    ensures out.instance_id()==metadata.id(),out.value()==raw.fragment().#getter(),
                {Self{raw:Tracked(Some(raw)),metadata}}
            }
        });
    }
    let mut methods = Vec::new();
    for tr in &sm.transitions {
        let n = &tr.name;
        let params: Vec<_> = tr
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let ty = &p.ty;
                quote! {#n:#ty}
            })
            .collect();
        let args: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
        if tr.kind == TransitionKind::Init {
            let mut values = HashMap::new();
            let mut requirements = Vec::new();
            initial(&tr.body, &mut values, &mut requirements)?;
            let cnv: Vec<_> = cn.iter().map(|n| &values[&n.to_string()]).collect();
            let names: Vec<_> = variables.iter().map(|f| &f.name).collect();
            let valuesv: Vec<_> = names.iter().map(|n| &values[&n.to_string()]).collect();
            let storage_value = &values[&storage_name.to_string()];
            let actual = fresh(sm, tr, "initial_permission");
            let deposited = fresh(sm, tr, "initial_deposit");
            let remaining = fresh(sm, tr, "remaining");
            let md = fresh(sm, tr, "metadata");
            let raw_names: Vec<_> = names
                .iter()
                .map(|n| fresh(sm, tr, &format!("owner_{n}")))
                .collect();
            let indexes: Vec<_> = (1..=names.len()).map(verus_syn::Index::from).collect();
            let selected_part = fresh(sm, tr, "selected_part");
            let selected_rest = fresh(sm, tr, "selected_rest");
            let mut splits = Vec::new();
            for (field, raw) in variables.iter().zip(&raw_names) {
                let select = format_ident!("select_{}", field.name);
                let without = format_ident!("without_{}", field.name);
                splits.push(quote! {
                    let #selected_part=#remaining.fragment().#select()#(.#setters(#cnv))*;
                    let #selected_rest=#remaining.fragment().#without();
                    assert(Fragment #expr::op(#selected_part,#selected_rest)==#remaining.fragment());
                    let tracked (#raw,#remaining)=#remaining.split(#selected_part,#selected_rest);
                });
            }
            methods.push(quote!{
                pub proof fn #n(#(#params,)*tracked #actual:Option<#permission_ty>)
                    ->(tracked out:(Tracked<Self>,#(Tracked<#names #types>),*))
                    requires #(#requirements,)*#actual==#storage_value,
                    ensures #(out.#indexes@.instance_id()==out.0@.id(),out.#indexes@.value()==#valuesv,)*
                        #(out.0@.#cn()==#cnv,)*
                {
                    let tracked #deposited=match #actual{
                        Some(permission)=>::vstd::resource::tsm_helpers::singleton_map(0int,permission),
                        None=>IMap::<int,#permission_ty>::tracked_empty(),
                    };
                    let tracked #remaining=Protocol #expr::#n(#deposited,#(#args),*);
                    let tracked #md=::vstd::resource::tsm_context::Descriptor::alloc(__StorageMetadata #expr {
                        #location_field:#remaining.loc(),#(#cn:#cnv,)*#marker_value
                    });
                    #(#splits)*
                    #(let tracked #raw_names=<#names #types>::__from_token(#raw_names,#md.clone());)*
                    (Tracked(Self{metadata:#md,context:Tracked(Some(#remaining))}),
                        #(Tracked(#raw_names)),*)
                }
            });
            continue;
        }
        if tr.kind != TransitionKind::Transition || !selected.contains(&n.to_string()) {
            return Err(Error::new(
                n.span(),
                "grouped physical facade requires selected checked mutating readiness",
            ));
        }
        let mut op = Operation::default();
        operation(&tr.body, &mut op)?;
        if let Some((pattern, value)) = &op.hidden {
            let verus_syn::Pat::Ident(bound) = &**pattern else {
                return Err(Error::new(
                    n.span(),
                    "physical selected binding must be one identifier",
                ));
            };
            let expected = quote! {pre.#storage_name->0}.to_string();
            if value.to_token_stream().to_string() != expected {
                return Err(Error::new(
                    n.span(),
                    "physical selected binding must select the optional store value",
                ));
            }
            let Some((
                SpecialOp {
                    stmt: MonoidStmtType::Withdraw,
                    elt: MonoidElt::OptionSome(Some(operand)),
                },
                None,
            )) = &op.physical
            else {
                return Err(Error::new(
                    n.span(),
                    "physical selected binding requires its singleton withdrawal",
                ));
            };
            if operand.to_token_stream().to_string() != bound.ident.to_string() {
                return Err(Error::new(
                    n.span(),
                    "physical selected withdrawal must consume the selected value",
                ));
            }
        }
        let mut used: HashSet<_> = op.updates.keys().cloned().collect();
        for e in op
            .updates
            .values()
            .chain(op.requirements.iter())
            .chain(op.assertions.iter())
        {
            footprint(e, &fields, &mut used)?;
        }
        if let Some((
            SpecialOp {
                elt: MonoidElt::OptionSome(Some(value)),
                ..
            },
            _,
        )) = &op.physical
        {
            footprint(value, &fields, &mut used)?;
        }
        let supplied: Vec<_> = variables
            .iter()
            .filter(|f| used.contains(&f.name.to_string()))
            .copied()
            .collect();
        if supplied.is_empty() {
            return Err(Error::new(
                n.span(),
                "grouped physical transition requires an actual variable owner",
            ));
        }
        let bindings: HashMap<_, _> = supplied
            .iter()
            .map(|f| {
                let name = if tr.params.iter().any(|p| p.name == f.name) {
                    fresh(sm, tr, &format!("field_{}", f.name))
                } else {
                    f.name.clone()
                };
                (f.name.to_string(), name)
            })
            .collect();
        let mutable_names: HashSet<_> = op.updates.keys().cloned().collect();
        let readonly: Vec<_> = supplied
            .iter()
            .filter(|f| !mutable_names.contains(&f.name.to_string()))
            .copied()
            .collect();
        let all_names: Vec<_> = supplied
            .iter()
            .map(|f| &bindings[&f.name.to_string()])
            .collect();
        let readonly_names: Vec<_> = readonly
            .iter()
            .map(|f| &bindings[&f.name.to_string()])
            .collect();
        let readonly_types: Vec<_> = readonly.iter().map(|f| &f.name).collect();
        let supplied: Vec<_> = supplied
            .into_iter()
            .filter(|f| mutable_names.contains(&f.name.to_string()))
            .collect();
        if supplied.is_empty() {
            return Err(Error::new(
                n.span(),
                "grouped physical transition requires mutable actual field ownership",
            ));
        }
        let public_names: Vec<_> = supplied
            .iter()
            .map(|f| &bindings[&f.name.to_string()])
            .collect();
        let typesv: Vec<_> = supplied.iter().map(|f| &f.name).collect();
        let slots: Vec<_> = supplied
            .iter()
            .map(|f| fresh(sm, tr, &format!("slot_{}", f.name)))
            .collect();
        let owners: Vec<_> = supplied
            .iter()
            .map(|f| fresh(sm, tr, &format!("owned_{}", f.name)))
            .collect();
        let restored: Vec<_> = supplied
            .iter()
            .map(|f| fresh(sm, tr, &format!("restored_{}", f.name)))
            .collect();
        let getter: Vec<_> = supplied
            .iter()
            .map(|f| format_ident!("value_{}", f.name))
            .collect();
        let initial_fragments: Vec<_> = slots
            .iter()
            .map(|s| quote! {old(#s)@->Some_0.fragment()})
            .collect();
        let oldsum = sum(&initial_fragments, &expr);
        let observation = fresh(sm, tr, "observation");
        let readonly_frame = if readonly.is_empty() {
            quote! {Fragment #expr::empty()}
        } else {
            quote! {#observation.fragment()}
        };
        let pre_expr = quote! {Fragment #expr::op(#oldsum,#readonly_frame)};
        let shapes:Vec<_>=supplied.iter().zip(&slots).map(|(field,slot)|{
            let factory=format_ident!("field_{}",field.name);
            let getter=format_ident!("value_{}",field.name);
            let owns=format_ident!("owns_{}",field.name);
            quote!{old(#slot)@->Some_0.fragment().#owns()
                &&old(#slot)@->Some_0.fragment()==Fragment #expr::#factory(old(#slot)@->Some_0.fragment().#getter())
                    #(.#setters((#pre_expr).#cget()))*}
        }).collect();
        let initial = fresh(sm, tr, "initial");
        let remaining = fresh(sm, tr, "remaining");
        let before = fresh(sm, tr, "before");
        let after = fresh(sm, tr, "after");
        let withdrawn = fresh(sm, tr, "withdrawn");
        let actual = fresh(sm, tr, "actual");
        let deposited = fresh(sm, tr, "deposited");
        let result = fresh(sm, tr, "result");
        let split_part = fresh(sm, tr, "split_part");
        let split_rest = fresh(sm, tr, "split_rest");
        let raw = format_ident!("__physical_raw_{n}");
        let local = format_ident!("{n}_local_requires");
        let observed = format_ident!("{n}_observed");
        let ready = format_ident!("{n}_local_ready");
        let frame = format_ident!("{n}_frame");
        let outputs = format_ident!("{n}_outputs");
        let witness = format_ident!("{n}_witness");
        let mut public_updates = Vec::new();
        let mut raw_updates = Vec::new();
        let mut split_steps = Vec::new();
        for (((field, slot), out), get) in supplied.iter().zip(&slots).zip(&restored).zip(&getter) {
            let arg = &bindings[&field.name.to_string()];
            let select = format_ident!("select_{}", field.name);
            let without = format_ident!("without_{}", field.name);
            let set = format_ident!("with_{}", field.name);
            let update = op.updates.get(&field.name.to_string());
            let public_value = if let Some(e) = update {
                native(e, &fields, &bindings, None, true, Some(&mutable_names))?
            } else {
                quote! {old(#arg).value()}
            };
            let raw_value = if let Some(e) = update {
                native(e, &fields, &bindings, Some(&pre_expr), false, None)?
            } else {
                quote! {old(#slot)@->Some_0.fragment().#get()}
            };
            public_updates.push(quote! {final(#arg).value()==#public_value});
            raw_updates.push(quote!{final(#slot)@->Some_0.fragment()==old(#slot)@->Some_0.fragment().#set(#raw_value)});
            split_steps.push(quote! {
                let #split_part=#remaining.fragment().#select()#(.#setters(#initial.#cget()))*;
                let #split_rest=#remaining.fragment().#without();
                assert(Fragment #expr::op(#split_part,#split_rest)==#remaining.fragment());
                let tracked (#out,#remaining)=#remaining.split(#split_part,#split_rest);
                *#slot=Tracked(Some(#out));
            });
        }
        let requirements: Vec<_> = op
            .requirements
            .iter()
            .map(|e| native(e, &fields, &bindings, None, false, None))
            .collect::<Result<_, _>>()?;
        let binding = op
            .physical
            .as_ref()
            .and_then(|(_, binding)| binding.as_ref())
            .or(op.hidden.as_ref().map(|(pattern, _)| pattern));
        let mut public_assertions = Vec::new();
        let mut raw_assertions = Vec::new();
        for e in &op.assertions {
            let public = native(e, &fields, &bindings, None, true, Some(&mutable_names))?;
            let raw = native(e, &fields, &bindings, Some(&pre_expr), false, None)?;
            if let Some(binding) = binding {
                public_assertions.push(quote! {{let #binding=#result;#public}});
                raw_assertions.push(quote! {{let #binding=#result;#raw}});
            } else {
                public_assertions.push(public);
                raw_assertions.push(raw);
            }
        }
        let withdrawing = op
            .physical
            .as_ref()
            .is_some_and(|(op, _)| matches!(op.stmt, MonoidStmtType::Withdraw));
        let (physical_params, physical_arg, deposit_value, pack, extra_public, extra_raw) =
            match &op.physical {
                Some((
                    SpecialOp {
                        stmt: MonoidStmtType::Deposit,
                        elt: MonoidElt::OptionSome(Some(value)),
                    },
                    _,
                )) => {
                    let pubvalue = native(value, &fields, &bindings, None, false, None)?;
                    let rawvalue = native(value, &fields, &bindings, Some(&pre_expr), false, None)?;
                    (
                        quote! {tracked #actual:#permission_ty,},
                        quote! {#deposited,},
                        quote! {IMap::empty().insert(0int,#actual)},
                        quote! {let tracked #deposited=::vstd::resource::tsm_helpers::singleton_map(0int,#actual);},
                        quote! {#actual==#pubvalue,},
                        quote! {#actual==#rawvalue,},
                    )
                }
                Some((
                    SpecialOp {
                        stmt: MonoidStmtType::Withdraw,
                        elt: MonoidElt::OptionSome(_),
                    },
                    _,
                )) if binding.is_some() => (
                    quote! {},
                    quote! {},
                    quote! {IMap::empty()},
                    quote! {},
                    quote! {},
                    quote! {},
                ),
                None => (
                    quote! {},
                    quote! {},
                    quote! {IMap::empty()},
                    quote! {},
                    quote! {},
                    quote! {},
                ),
                _ => {
                    return Err(Error::new(
                        n.span(),
                        "grouped physical facade requires singleton transfers",
                    ))
                }
            };
        let return_clause = if withdrawing {
            quote! {->(tracked #result:#permission_ty)}
        } else {
            quote! {}
        };
        let unpack = if withdrawing {
            quote! {
                assert(#before.#storage_name is Some);
                assert(#after.#storage_name is None);
                assert(#withdrawn==IMap::empty().insert(0int,#before.#storage_name->Some_0));
                let tracked #result=::vstd::resource::tsm_helpers::take_singleton(#withdrawn,0int);
            }
        } else {
            quote! {}
        };
        let return_value = if withdrawing {
            quote! {#result}
        } else {
            quote! {}
        };
        let slots0 = &slots[0];
        let owners0 = &owners[0];
        let joins: Vec<_> = owners
            .iter()
            .skip(1)
            .map(|o| quote! {let tracked #remaining=#remaining.join(#o);})
            .collect();
        let rawcallactual = if op
            .physical
            .as_ref()
            .is_some_and(|(op, _)| matches!(op.stmt, MonoidStmtType::Deposit))
        {
            quote! {#actual,}
        } else {
            quote! {}
        };
        let observation_param = if readonly.is_empty() {
            quote! {}
        } else {
            quote! {tracked #observation:&::vstd::resource::tsm_storage::StorageObservation<Protocol #types>,}
        };
        let observation_argument = if readonly.is_empty() {
            quote! {}
        } else {
            quote! {&#observation,}
        };
        let observation_requires = if readonly.is_empty() {
            quote! {}
        } else {
            quote! {#observation.loc()==old(#slots0)@->Some_0.loc(),}
        };
        let execute = if readonly.is_empty() {
            quote! {
                let tracked TransitionObservation #expr {
                    token:#remaining,withdrawn:#withdrawn,before:#before,after:#after,..
                }=Protocol #expr::#observed(#remaining,#physical_arg#(#args),*);
            }
        } else {
            let make_empty = if op
                .physical
                .as_ref()
                .is_some_and(|(op, _)| matches!(op.stmt, MonoidStmtType::Deposit))
            {
                quote! {}
            } else {
                quote! {let tracked #deposited=IMap::<int,#permission_ty>::tracked_empty();}
            };
            let h = fresh(sm, tr, "shared_fragment");
            let dep = fresh(sm, tr, "deposited_fragment");
            let choices = fresh(sm, tr, "output_choices");
            let pair = fresh(sm, tr, "output_pair");
            quote! {
                #make_empty
                let #h=#observation.fragment();
                let #dep=#deposited;
                Protocol #expr::#ready(#initial,#h,#dep,#(#args),*);
                Protocol #expr::#frame(#initial,#h,#dep,#(#args),*);
                let #choices=ISet::new(|#pair:(Fragment #types,IMap<int,#permission_ty>)|
                    Protocol #expr::#outputs(#initial,#h,#pair.0,#dep,#pair.1,#(#args),*));
                let tracked (#remaining,#withdrawn)=#remaining.exchange_nondeterministic_with_observation(
                    #observation,#deposited,#choices);
                let (#before,#after,_)=Protocol #expr::#witness(#initial,#h,#remaining.fragment(),#dep,#withdrawn,#(#args),*);
            }
        };
        let observation_setup = if readonly.is_empty() {
            quote! {}
        } else {
            let rawobs: Vec<_> = readonly
                .iter()
                .map(|f| fresh(sm, tr, &format!("read_{}", f.name)))
                .collect();
            let lowerframes: Vec<_> = readonly
                .iter()
                .map(|f| fresh(sm, tr, &format!("read_frame_{}", f.name)))
                .collect();
            let upper = fresh(sm, tr, "upper");
            let whole = fresh(sm, tr, "whole");
            let outer = fresh(sm, tr, "outer");
            let target = fresh(sm, tr, "target");
            let rest = fresh(sm, tr, "read_remainder");
            let lower_frame = fresh(sm, tr, "lower_frame");
            let readgetters: Vec<_> = readonly
                .iter()
                .map(|f| format_ident!("value_{}", f.name))
                .collect();
            let readowns: Vec<_> = readonly
                .iter()
                .map(|f| format_ident!("owns_{}", f.name))
                .collect();
            let readsetters: Vec<_> = readonly
                .iter()
                .map(|f| format_ident!("with_{}", f.name))
                .collect();
            let readwithout: Vec<_> = readonly
                .iter()
                .map(|f| format_ident!("without_{}", f.name))
                .collect();
            let names: Vec<_> = readonly.iter().map(|f| &f.name).collect();
            let first = &rawobs[0];
            let initial_upper = if rawobs.len() == 1 {
                let first_name = readonly_names[0];
                quote! {
                    let tracked #upper=#first;
                    #first_name.raw@->Some_0.fragment().op_unit();
                    assert(Fragment #expr::op(#first_name.raw@->Some_0.fragment(),Fragment #expr::empty())==#upper.fragment());
                    assert(exists|#lower_frame:Fragment #types|Fragment #expr::op(#first_name.raw@->Some_0.fragment(),#lower_frame)==#upper.fragment());
                }
            } else {
                let second = &rawobs[1];
                quote! {let tracked #upper=#first.join(&#second);}
            };
            let previous = fresh(sm, tr, "previous_upper");
            let merges: Vec<_> = rawobs.iter().enumerate().skip(2).map(|(index,o)| {
                let prefix=&readonly_names[..index];
                quote! {
                    let #previous=#upper.fragment();
                    let tracked #upper=#upper.join(&#o);
                    #(Self::__read_included_transitive(#prefix.raw@->Some_0.fragment(),#previous,#upper.fragment());)*
                }
            }).collect();
            quote! {
                #(let tracked #rawobs=#readonly_names.borrow_token().observe();)*
                #initial_upper
                #(#merges)*
                #upper.validate();
                let (#whole,#outer)=choose|whole:State #types,outer:Fragment #types|
                    whole.invariant()&&Fragment #expr::op(#upper.fragment(),outer)==Protocol #expr::embed(whole);
                #(
                    let #lowerframes=choose|#lower_frame:Fragment #types|
                        Fragment #expr::op(#readonly_names.raw@->Some_0.fragment(),#lower_frame)==#upper.fragment();
                    Fragment #expr::associative(#readonly_names.raw@->Some_0.fragment(),#lowerframes,#outer);
                    assert(Fragment #expr::op(#readonly_names.raw@->Some_0.fragment(),
                        Fragment #expr::op(#lowerframes,#outer))==Protocol #expr::embed(#whole));
                    assert(#whole.#names==#readonly_names.value());
                    assert(#upper.fragment().#readowns());
                    assert(#upper.fragment().#readgetters()==#readonly_names.value());
                )*
                #(assert(#upper.fragment().#cget()==self.#cn());)*
                let #target=Fragment #expr::empty()#(.#setters(self.#cn()))*
                    #(.#readsetters(#readonly_names.value()))*;
                let #rest=#upper.fragment()#(.#readwithout())*;
                assert(Fragment #expr::op(#target,#rest)==#upper.fragment());
                let tracked #observation=#upper.weaken(#target);
            }
        };
        methods.push(quote!{
            proof fn #raw(#(#params,)*#(tracked #slots:&mut Tracked<Option<#token>>,)*#observation_param#physical_params)#return_clause
                requires #(old(#slots)@ is Some,)*
                    #(old(#slots)@->Some_0.loc()==old(#slots0)@->Some_0.loc(),)*
                    #(#shapes,)*#observation_requires
                    Protocol #expr::#local(#oldsum,#readonly_frame,#deposit_value,#(#args),*),
                    #extra_raw
                ensures #(final(#slots)@ is Some,
                    final(#slots)@->Some_0.loc()==old(#slots)@->Some_0.loc(),)*
                    #(#raw_updates,)*#(#raw_assertions,)*
            {
                #(let tracked #owners=#slots.borrow_mut().tracked_take();)*
                let tracked #remaining=#owners0;
                #(#joins)*
                let #initial=#remaining.fragment();
                #pack
                #execute
                #unpack
                #(#split_steps)*
                #return_value
            }
            pub proof fn #n(tracked &self,#(#params,)*#(tracked #public_names:&mut #typesv #types,)*#(tracked #readonly_names:&#readonly_types #types,)*#physical_params)#return_clause
                requires #(#all_names.instance_id()==self.id(),)*#(#requirements,)*#extra_public
                ensures #(final(#public_names).instance_id()==self.id(),)*#(#public_updates,)*#(#public_assertions,)*
            {
                #(::vstd::prelude::use_type_invariant(&*#all_names);
                    self.metadata.agrees(&#all_names.metadata);)*
                #observation_setup
                Self::#raw(#(#args,)*#(&mut #public_names.raw,)*#observation_argument#rawcallactual)
            }
        });
    }
    Ok(quote! {
        #(#attrs)*struct __StorageMetadata #decl #wc{
            ghost #location_field: ::vstd::resource::Loc,#(ghost #cn:#ct,)*#marker
        }
        #(#wrappers)*
        #(#attrs)*pub tracked struct Instance #decl #wc {metadata:#descriptor,context:Tracked<Option<#token>>}
        impl #decl Instance #types #wc{
            #[verifier::type_invariant]
            spec fn invariant(self)->bool{
                ::vstd::prelude::imply(self.context@ is Some,{
                    self.context@->Some_0.loc()==self.metadata.value().#location_field
                    &&self.context@->Some_0.fragment()==Fragment #expr::empty()
                        #(.#setters(self.metadata.value().#cn))*
                })
            }
            pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}
            #(pub closed spec fn #cn(&self)->#ct{self.metadata.value().#cn})*
            proof fn __read_included_transitive(source:Fragment #types,middle:Fragment #types,target:Fragment #types)
                requires ::vstd::resource::tsm::fragment_included::<Protocol #types>(source,middle),
                    ::vstd::resource::tsm::fragment_included::<Protocol #types>(middle,target),
                ensures ::vstd::resource::tsm::fragment_included::<Protocol #types>(source,target),
            {
                let left=choose|left:Fragment #types|Fragment #expr::op(source,left)==middle;
                let right=choose|right:Fragment #types|Fragment #expr::op(middle,right)==target;
                Fragment #expr::associative(source,left,right);
                assert(Fragment #expr::op(source,Fragment #expr::op(left,right))==target);
            }
            pub proof fn clone(tracked &self)->(tracked out:Self)
                ensures out.id()==self.id(),#(out.#cn()==self.#cn(),)*
            {Self{metadata:self.metadata.clone(),context:Tracked(None)}}
            #(#methods)*
        }
    })
}
