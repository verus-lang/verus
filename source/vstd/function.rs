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
#[verifier::reject_recursive_types(Usage)]
#[verifier::reject_recursive_types(ReqEns)]
#[verifier::reject_recursive_types(Cpy)]
#[verifier::reject_recursive_types(Snd)]
#[verifier::reject_recursive_types(Syn)]
pub struct ExFnProofOptions<Usage, ReqEns, Cpy, Snd, Syn>(
    FnProofOptions<Usage, ReqEns, Cpy, Snd, Syn>,
);

#[verifier::external_trait_specification]
pub trait ExProofFnSpecification<Args, Output> {
    type ExternalTraitSpecificationFor: ProofFnReqEnsDef<Args, Output>;

    spec fn req(_args: Args) -> bool;

    spec fn ens(_args: Args, _output: Output) -> bool;
}

#[doc(hidden)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFnProofOptionOnce(FN_Once);

#[doc(hidden)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFnProofOptionMut(FN_Mut);

#[doc(hidden)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFnProofOption(FN_Fn);

#[doc(hidden)]
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
pub struct ExFnProofOptionReqEns<R>(FN_RE<R>);

#[doc(hidden)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFnProofOptionCopy(FN_Cpy);

#[doc(hidden)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFnProofOptionSend(FN_Snd);

#[doc(hidden)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFnProofOptionSync(FN_Syn);

#[doc(hidden)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFnProofOptionTracked(FN_T);

#[doc(hidden)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFnProofOptionNot(FN_);

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

#[verifier::external_trait_specification]
pub trait ExProofFnCopy {
    type ExternalTraitSpecificationFor: ProofFnCopy;
}

#[verifier::external_trait_specification]
pub trait ExProofFnSend {
    type ExternalTraitSpecificationFor: ProofFnSend;
}

#[verifier::external_trait_specification]
pub trait ExProofFnSync {
    type ExternalTraitSpecificationFor: ProofFnSync;
}

#[doc(hidden)]
pub broadcast proof fn axiom_proof_fn_requires<
    F,
    ArgModes,
    OutMode,
    Args: std::marker::Tuple,
    Output,
>(f: FnProof<F, ArgModes, OutMode, Args, Output>, args: Args) where
    F: ProofFnOnce,
    F: ProofFnReqEnsAssoc,
    <F as ProofFnReqEnsAssoc>::ReqEns: ProofFnReqEnsDef<Args, Output>,

    ensures
        #[trigger] f.requires(args) <==> <F as ProofFnReqEnsAssoc>::ReqEns::req(args),
{
    admit()
}

#[doc(hidden)]
pub broadcast proof fn axiom_proof_fn_ensures<
    F,
    ArgModes,
    OutMode,
    Args: std::marker::Tuple,
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
{
    admit()
}

/// Retype a proof_fn, introducing ReqEns<R>
pub proof fn proof_fn_as_req_ens<
    R: ProofFnReqEnsDef<Args, Output>,
    Usage,
    ReqEns,
    Cpy,
    Snd,
    Syn,
    ArgModes,
    OutMode,
    Args: std::marker::Tuple,
    Output,
>(
    tracked f: FnProof<
        FnProofOptions<Usage, ReqEns, Cpy, Snd, Syn>,
        ArgModes,
        OutMode,
        Args,
        Output,
    >,
) -> tracked FnProof<
    FnProofOptions<Usage, FN_RE<R>, Cpy, Snd, Syn>,
    ArgModes,
    OutMode,
    Args,
    Output,
>
    requires
        forall|args: Args| #[trigger] R::req(args) ==> f.requires(args),
        forall|args: Args, output: Output|
            f.ensures(args, output) ==> #[trigger] R::ens(args, output),
{
    admit();
    proof_from_false()
}

pub broadcast group group_seq_axioms {
    axiom_proof_fn_requires,
    axiom_proof_fn_ensures,
}

} // verus!
