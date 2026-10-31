use super::prelude::*;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(Options)]
#[verifier::reject_recursive_types(ArgModes)]
#[verifier::reject_recursive_types(OutMode)]
#[verifier::reject_recursive_types(Args)]
#[verifier::accept_recursive_types(Output)]
pub struct ExFnProof<'a, Options, ArgModes, OutMode, Args, Output>(
    FnProof<'a, Options, ArgModes, OutMode, Args, Output>,
);

#[doc(hidden)]
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(USAGE)]
#[verifier::reject_recursive_types(ReqEns)]
#[verifier::reject_recursive_types(COPY)]
#[verifier::reject_recursive_types(SEND)]
#[verifier::reject_recursive_types(SYNC)]
#[verifier::reject_recursive_types(OPENS)]
pub struct ExFnProofOptions<
    const USAGE: u8,
    ReqEns,
    const COPY: u8,
    const SEND: u8,
    const SYNC: u8,
    const OPENS: u8,
>(FOpts<USAGE, ReqEns, COPY, SEND, SYNC, OPENS>);

#[verifier::external_trait_specification]
pub trait ExProofFnSpecification<Args, Output> {
    type ExternalTraitSpecificationFor: ProofFnReqEnsDef<Args, Output>;

    spec fn req(_args: Args) -> bool;

    spec fn ens(_args: Args, _output: Output) -> bool;
}

#[doc(hidden)]
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
pub struct ExFnProofOptionReqEns<R>(RqEn<R>);

#[doc(hidden)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFnProofOptionTracked(Trk);

#[verifier::external_trait_specification]
pub trait ExProofFnNoOpens {
    type ExternalTraitSpecificationFor: ProofFnNoOpens;
}

#[verifier::external_trait_specification]
pub trait ExProofFnOnceOpens {
    type ExternalTraitSpecificationFor: ProofFnOnceOpens;
}

#[verifier::external_trait_specification]
pub trait ExProofFnMutOpens: ProofFnOnceOpens {
    type ExternalTraitSpecificationFor: ProofFnMutOpens;
}

#[verifier::external_trait_specification]
pub trait ExProofFnOpens: ProofFnMutOpens {
    type ExternalTraitSpecificationFor: ProofFnOpens;
}

#[verifier::external_trait_specification]
pub trait ExProofFnOnce: ProofFnOnceOpens + ProofFnNoOpens {
    type ExternalTraitSpecificationFor: ProofFnOnce;
}

#[verifier::external_trait_specification]
pub trait ExProofFnMut: ProofFnOnce + ProofFnMutOpens + ProofFnNoOpens {
    type ExternalTraitSpecificationFor: ProofFnMut;
}

#[verifier::external_trait_specification]
pub trait ExProofFn: ProofFnMut + ProofFnOpens + ProofFnNoOpens {
    type ExternalTraitSpecificationFor: ProofFn;
}

#[verifier::external_trait_specification]
pub trait ExProofFnReqEnsAssoc {
    type ExternalTraitSpecificationFor: ProofFnReqEnsAssoc;

    type ReqEns;
}

#[verifier::external_trait_specification]
pub trait ExProofFnReqEns<R>: ProofFnReqEnsAssoc<ReqEns = R> {
    type ExternalTraitSpecificationFor: ProofFnReqEns<R>;
}

#[doc(hidden)]
pub broadcast axiom fn axiom_proof_fn_requires<
    F,
    ArgModes,
    OutMode,
    Args: core::marker::Tuple,
    Output,
>(f: FnProof<F, ArgModes, OutMode, Args, Output>, args: Args) where
    F: ProofFnOnceOpens,
    F: ProofFnReqEnsAssoc,
    <F as ProofFnReqEnsAssoc>::ReqEns: ProofFnReqEnsDef<Args, Output>,

    ensures
        #[trigger] f.requires(args) <==> <F as ProofFnReqEnsAssoc>::ReqEns::req(args),
;

#[doc(hidden)]
pub broadcast axiom fn axiom_proof_fn_ensures<
    F,
    ArgModes,
    OutMode,
    Args: core::marker::Tuple,
    Output,
>(f: FnProof<F, ArgModes, OutMode, Args, Output>, args: Args, output: Output) where
    F: ProofFnOnceOpens,
    F: ProofFnReqEnsAssoc,
    <F as ProofFnReqEnsAssoc>::ReqEns: ProofFnReqEnsDef<Args, Output>,

    ensures
        #[trigger] f.ensures(args, output) <==> <F as ProofFnReqEnsAssoc>::ReqEns::ens(
            args,
            output,
        ),
;

#[doc(hidden)]
pub broadcast axiom fn axiom_proof_fn_no_opens_invariants<
    F,
    ArgModes,
    OutMode,
    Args: core::marker::Tuple,
    Output,
>(f: FnProof<F, ArgModes, OutMode, Args, Output>, args: Args) where
    F: ProofFnOnceOpens,
    F: ProofFnNoOpens,

    ensures
        #[trigger] call_opens_invariants::<_, _, ISet<int>>(f, args) == ISet::empty(),
;

/// Retype a proof_fn, introducing `ReqEns<R>`
pub axiom fn proof_fn_as_req_ens<
    R: ProofFnReqEnsDef<Args, Output>,
    const USAGE: u8,
    ReqEns,
    const COPY: u8,
    const SEND: u8,
    const SYNC: u8,
    const OPENS: u8,
    ArgModes,
    OutMode,
    Args: core::marker::Tuple,
    Output,
>(
    tracked f: FnProof<
        FOpts<USAGE, ReqEns, COPY, SEND, SYNC, OPENS>,
        ArgModes,
        OutMode,
        Args,
        Output,
    >,
) -> tracked FnProof<
    FOpts<USAGE, RqEn<R>, COPY, SEND, SYNC, OPENS>,
    ArgModes,
    OutMode,
    Args,
    Output,
>
    requires
        forall|args: Args| #[trigger] R::req(args) ==> f.requires(args),
        forall|args: Args, output: Output|
            f.ensures(args, output) ==> #[trigger] R::ens(args, output),
;

pub broadcast axiom fn axiom_fn_mut_call_requires<Args: core::marker::Tuple, F: FnMut<Args>>(
    f: &mut F,
    args: Args,
)
    requires
        call_requires::<Args, F>(mut_ref_current(f), args),
    ensures
        #[trigger] call_requires::<Args, &mut F>(f, args),
;

// The output contract concerns the callable's current value. The reference may
// outlive the call and be used to replace the callable, so its future is unconstrained.
pub broadcast axiom fn axiom_fn_mut_call_ensures<Args: core::marker::Tuple, F: FnMut<Args>>(
    f: &mut F,
    args: Args,
    output: F::Output,
)
    requires
        #[trigger] call_ensures::<Args, &mut F>(f, args, output),
    ensures
        call_ensures::<Args, F>(mut_ref_current(f), args, output),
;

pub broadcast axiom fn axiom_fn_mut_call_opens_invariants<
    Args: core::marker::Tuple,
    F: FnMut<Args>,
    I,
>(f: &mut F, args: Args)
    ensures
        #[trigger] call_opens_invariants::<Args, &mut F, I>(f, args) == call_opens_invariants::<
            Args,
            F,
            I,
        >(mut_ref_current(f), args),
;

pub broadcast group group_function_axioms {
    axiom_proof_fn_requires,
    axiom_proof_fn_ensures,
    axiom_proof_fn_no_opens_invariants,
    axiom_fn_mut_call_requires,
    axiom_fn_mut_call_ensures,
    axiom_fn_mut_call_opens_invariants,
}

} // verus!
