use super::prelude::*;

pub mod frac;
mod lib;
pub mod map;
pub mod pcm;
pub mod seq;
pub mod set;
pub mod storage_protocol;

pub use lib::*;

verus! {

/** Interface for PCM / Resource Algebra ghost state.

RA-based ghost state is a well-established theory that is especially
useful for verifying concurrent code. An introduction to the concept
can be found in
[Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning](https://iris-project.org/pdfs/2015-popl-iris1-final.pdf)
or
[Iris from the ground up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf).

To embed the concept into Verus, we:
 * Use a trait, [`PCM`](pcm::PCM), to embed the well-formedness laws of a resource algebra
 * use a "tracked ghost" object, `Resource<P>` (this page) to represent ownership of a resource.

Most operations are fairly standard, just "translated" from the usual CSL presentation into Verus.

 * [`alloc`](Self::alloc) to allocate a resource.
 * [`join`](Self::join) to combine two resources via `P::op`, and [`split`](Self::split), its inverse.
 * [`validate`](Self::validate) to assert the validity of any held resource.
 * [`update`](Self::update) or [`update_nondeterministic`](Self::update_nondeterministic) to perform a frame-preserving update.

The interface also includes a nontrivial extension for working with _shared references_ to resources.
Shared resources do not compose in a "separating" way via `P::op`, but rather, in a "potentially overlapping" way ([`join_shared`](Self::join_shared)). Shared resources can also be used to "help" perform frame-preserving updates, as long as they themselves do not change ([`update_with_shared`](Self::update_with_shared)).

### Examples

See:
 * Any of the examples in [this directory](https://github.com/verus-lang/verus/tree/main/examples/pcm)
 * The source code for the [fractional resource library](super::tokens::frac::FracGhost)

### See also

The ["storage protocol"](super::storage_protocol::StorageResource) formalism
is an even more significant
extension with additional capabilities for interacting with shared resources.

[VerusSync](https://verus-lang.github.io/verus/state_machines/intro.html) provides a higher-level
"swiss army knife" for building useful ghost resources.
*/
#[verifier::external_body]
#[verifier::accept_recursive_types(P)]
pub tracked struct Resource<P> {
    p: core::marker::PhantomData<P>,
}

pub type Loc = int;

} // verus!
