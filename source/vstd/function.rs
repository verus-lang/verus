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
pub struct ExFnProofOptions<
    const USAGE: u8,
    ReqEns,
    const COPY: u8,
    const SEND: u8,
    const SYNC: u8,
>(FOpts<USAGE, ReqEns, COPY, SEND, SYNC>);

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
pub trait ExProofFnOnce {
    type ExternalTraitSpecificationFor: ProofFnOnce;
}

#[verifier::external_trait_specification]
pub trait ExProofFnMut: ProofFnOnce {
    type ExternalTraitSpecificationFor: ProofFnMut;
}

#[verifier::external_trait_specification]
pub trait ExProofFn: ProofFnMut {
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
    F: ProofFnOnce,
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
    F: ProofFnOnce,
    F: ProofFnReqEnsAssoc,
    <F as ProofFnReqEnsAssoc>::ReqEns: ProofFnReqEnsDef<Args, Output>,

    ensures
        #[trigger] f.ensures(args, output) <==> <F as ProofFnReqEnsAssoc>::ReqEns::ens(
            args,
            output,
        ),
;

/// Retype a proof_fn, introducing `ReqEns<R>`
pub axiom fn proof_fn_as_req_ens<
    R: ProofFnReqEnsDef<Args, Output>,
    const USAGE: u8,
    ReqEns,
    const COPY: u8,
    const SEND: u8,
    const SYNC: u8,
    ArgModes,
    OutMode,
    Args: core::marker::Tuple,
    Output,
>(
    tracked f: FnProof<FOpts<USAGE, ReqEns, COPY, SEND, SYNC>, ArgModes, OutMode, Args, Output>,
) -> tracked FnProof<FOpts<USAGE, RqEn<R>, COPY, SEND, SYNC>, ArgModes, OutMode, Args, Output>
    requires
        forall|args: Args| #[trigger] R::req(args) ==> f.requires(args),
        forall|args: Args, output: Output|
            f.ensures(args, output) ==> #[trigger] R::ens(args, output),
;

pub broadcast group group_function_axioms {
    axiom_proof_fn_requires,
    axiom_proof_fn_ensures,
}

} // verus!
