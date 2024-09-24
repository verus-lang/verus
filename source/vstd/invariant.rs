#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;

// TODO:
//  * utility for conveniently creating unique namespaces

// An invariant storing objects of type V needs to be able to have some kind of configurable
// predicate `V -> bool`. However, doing this naively with a fully configurable
// predicate function would result in V being reject_recursive_types,
// which is too limiting and prevents important use cases with recursive types.

//
// Instead, we allow the user to specify a predicate which is fixed *at the type level*
// which we do through this trait, InvariantPredicate. However, the predicate still
// needs to be "dynamically configurable" upon the call to the invariant constructor.
// To support this, we add another type parameter K, a constant is fixed for a given
// Invariant object.
//
// So each Invariant object has 3 type parameters:
//  * K - A "constant" which is specified at constructor time
//  * V - Type of the stored 'tracked' object
//  * Pred: InvariantPredicate - provides the predicate (K, V) -> bool
//
// With this setup, we can now declare both K and V without reject_recursive_types.
// To be sure, note that the following, based on our trait formalism,
// is well-formed CIC (Coq), without any type polarity issues:
//
// ```
//    Inductive InvariantPredicate K V :=
//        | inv_pred : (K -> V -> bool) -> InvariantPredicate K V.
//
//    Inductive Inv (K V: Type) (x: InvariantPredicate K V) :=
//      | inv : K -> Inv K V x.
//
//    Definition some_predicate (V: Type) : InvariantPredicate nat V :=
//      inv_pred nat V (fun k v => false). (* an arbitrary predicate *)
//
//    (* example recursive type *)
//    Inductive T :=
//      | A : (Inv nat T (some_predicate T)) -> T.
// ```
//
// Note that the user can always just set K to be `V -> bool` in order to make the
// Invariant's predicate maximally configurable without having to restrict it at the
// type level. By doing so, the user opts in to the negative usage of V in exchange
// for the flexibility.

verus! {

/// Trait used to specify an _invariant predicate_ for
/// [`LocalInvariant`] and [`AtomicInvariant`].
pub trait InvariantPredicate<K, V> {
    spec fn inv(k: K, v: V) -> bool;
}

} // verus!
// LocalInvariant is NEVER `Sync`.
//
// Furthermore, for either type:
//
//  * If an Invariant<T> is Sync, then T must be Send
//      * We could put the T in an Invariant, sync the invariant to another thread,
//        and then extract the T, having effectively send it to the other thread.
//  * If Invariant<T> is Send, then T must be Send
//      * We could put the T in an Invariant, send the invariant to another thread,
//        and then take the T out.
//
// So the Sync/Send-ness of the Invariant depends on the Send-ness of T;
// however, the Sync-ness of T is unimportant (the invariant doesn't give you an extra
// ability to share a reference to a T across threads).
//
// In conclusion, we should have:
//
//    T                   AtomicInvariant<T>  LocalInvariant<T>
//
//    {}          ==>     {}                  {}
//    Send        ==>     Send+Sync           Send
//    Sync        ==>     {}                  {}
//    Sync+Send   ==>     Send+Sync           Send
/// An `AtomicInvariant` is a ghost object that provides "interior mutability"
/// for ghost objects, specifically, for `tracked` ghost objects.
/// A reference `&AtomicInvariant` may be shared between clients.
/// A client holding such a reference may _open_ the invariant
/// to obtain ghost ownership of `v1: V`, and then _close_ the invariant by returning
/// ghost ownership of a (potentially) different object `v2: V`.
///
/// An `AtomicInvariant` implements [`Sync`](https://doc.rust-lang.org/std/sync/)
/// and may be shared between threads.
/// However, this means that an `AtomicInvariant` can be only opened for
/// the duration of a single _sequentially consistent atomic_ operation.
/// Such operations are provided by our [`PAtomic`](crate::atomic) library.
/// For an invariant object without this atomicity restriction,
/// see [`LocalInvariant`], which gives up thread safety in exchange.
///
/// An `AtomicInvariant` consists of:
///
///  * A _predicate_ specified via the `InvariantPredicate` type bound, that determines
///    what values `V` may be saved inside the invariant.
///  * A _constant_ `K`, specified at construction type. The predicate function takes
///    this constant as a parameter, so the constant allows users to dynamically configure
///    the predicate function in a way that can't be done at the type level.
///  * A _namespace_. This is a bit of a technicality, and you can often just declare
///    it as an arbitrary integer with no issues. See the [`open_local_invariant!`]
///    documentation for more details.
///
/// The constant and namespace are specified at construction time ([`AtomicInvariant::new`]).
/// These values are fixed for the lifetime of the `AtomicInvariant` object.
/// To open the invariant and access the stored object `V`,
/// use the macro [`open_atomic_invariant!`].
///
/// The `AtomicInvariant` API is an instance of the ["invariant" method in Verus's general philosophy on interior mutability](https://verus-lang.github.io/verus/guide/interior_mutability.html).
///
/// **Note:** Rather than using `AtomicInvariant` directly, we generally recommend
/// using the [`atomic_ghost` APIs](crate::atomic_ghost).
#[cfg_attr(verus_keep_ghost, verifier::proof)]
#[cfg_attr(verus_keep_ghost, verifier::external_body)] /* vattr */
#[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(K))]
#[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(V))]
#[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(Pred))]
pub struct AtomicInvariant<K, V, Pred> {
    dummy: super::prelude::SyncSendIfSend<V>,
    dummy1: super::prelude::AlwaysSyncSend<(K, Pred, *mut V)>,
}

/// A `LocalInvariant` is a ghost object that provides "interior mutability"
/// for ghost objects, specifically, for `tracked` ghost objects.
/// A reference `&LocalInvariant` may be shared between clients.
/// A client holding such a reference may _open_ the invariant
/// to obtain ghost ownership of `v1: V`, and then _close_ the invariant by returning
/// ghost ownership of a (potentially) different object `v2: V`.
///
/// A `LocalInvariant` cannot be shared between threads
/// (that is, it does not implement [`Sync`](https://doc.rust-lang.org/std/sync/)).
/// However, this means that a `LocalInvariant` can be opened for an indefinite length
/// of time, since there is no risk of a race with another thread.
/// For an invariant object with the opposite properties, see [`AtomicInvariant`].
///
/// A `LocalInvariant` consists of:
///
///  * A _predicate_ specified via the `InvariantPredicate` type bound, that determines
///    what values `V` may be saved inside the invariant.
///  * A _constant_ `K`, specified at construction type. The predicate function takes
///    this constant as a parameter, so the constant allows users to dynamically configure
///    the predicate function in a way that can't be done at the type level.
///  * A _namespace_. This is a bit of a technicality, and you can often just declare
///    it as an arbitrary integer with no issues. See the [`open_local_invariant!`]
///    documentation for more details.
///
/// The constant and namespace are specified at construction time ([`LocalInvariant::new`]).
/// These values are fixed for the lifetime of the `LocalInvariant` object.
/// To open the invariant and access the stored object `V`,
/// use the macro [`open_local_invariant!`].
///
/// The `LocalInvariant` API is an instance of the ["invariant" method in Verus's general philosophy on interior mutability](https://verus-lang.github.io/verus/guide/interior_mutability.html).

#[cfg_attr(verus_keep_ghost, verifier::proof)]
#[cfg_attr(verus_keep_ghost, verifier::external_body)] /* vattr */
#[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(K))]
#[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(V))]
#[cfg_attr(verus_keep_ghost, verifier::accept_recursive_types(Pred))]
pub struct LocalInvariant<K, V, Pred> {
    dummy: super::prelude::SendIfSend<V>,
    dummy1: super::prelude::AlwaysSyncSend<(K, Pred, *mut V)>,
}

macro_rules! declare_invariant_impl {
    ($invariant:ident) => {
        // note the path names of `inv` and `namespace` are harcoded into the VIR crate.

        verus!{

        impl<K, V, Pred: InvariantPredicate<K, V>> $invariant<K, V, Pred> {
            /// The constant specified upon the initialization of this `
            #[doc = stringify!($invariant)]
            ///`.
            pub spec fn constant(&self) -> K;

            /// Namespace the invariant was declared in.
            #[rustc_diagnostic_item = concat!("verus::vstd::invariant::", stringify!($invariant), "::namespace")]
            pub spec fn namespace(&self) -> int;

            /// Returns `true` if it is possible to store the value `v` into the `
            #[doc = stringify!($invariant)]
            ///`.
            ///
            /// This is equivalent to `Pred::inv(self.constant(), v)`.

            #[rustc_diagnostic_item = concat!("verus::vstd::invariant::", stringify!($invariant), "::inv")]
            pub open spec fn inv(&self, v: V) -> bool {
                Pred::inv(self.constant(), v)
            }

            /// Initialize a new `
            #[doc = stringify!($invariant)]
            ///` with constant `k`. initial stored (tracked) value `v`,
            /// and in the namespace `ns`.

            #[verifier::external_body]
            pub proof fn new(k: K, tracked v: V, ns: int) -> (tracked i: $invariant<K, V, Pred>)
                requires
                    Pred::inv(k, v),
                ensures
                    i.constant() == k,
                    i.namespace() == ns,
            {
                unimplemented!();
            }

            /// Destroys the `
            #[doc = stringify!($invariant)]
            ///`, returning the tracked value contained within.

            #[verifier::external_body]
            pub proof fn into_inner(#[verifier::proof] self) -> (tracked v: V)
                ensures self.inv(v),
                opens_invariants [ self.namespace() ]
            {
                unimplemented!();
            }
        }

        }
    };
}

declare_invariant_impl!(AtomicInvariant);
declare_invariant_impl!(LocalInvariant);

#[doc(hidden)]
#[cfg_attr(verus_keep_ghost, verifier::proof)]
pub struct InvariantBlockGuard;

// In the "Logical Paradoxes" section of the Iris 4.1 Reference
// (`https://plv.mpi-sws.org/iris/appendix-4.1.pdf`), they show that
// opening invariants carries the risk of unsoundness.
//
// The paradox is similar to "Landin's knot", a short program that implements
// an infinite loop by combining two features: higher-order closures
// and mutable state:
//
//    let r := new_ref();
//    r := () -> {
//        let f = !r;
//        f();
//    };
//    let f = !r;
//    f();
//
// Invariants effectively serve as "mutable state"
// Therefore, in order to implement certain higher-order features
// like "proof closures" or "dyn", we need to make sure we have an
// answer to this paradox.
//
// One solution to
// this, described in the paper "Later Credits: Resourceful Reasoning
// for the Later Modality" by Spies et al. (available at
// `https://plv.mpi-sws.org/later-credits/paper-later-credits.pdf`) is
// to use "later credits". That is, require the expenditure of a later
// credit, only obtainable in exec mode, when opening an invariant. So
// we require the relinquishment of a tracked
// `OpenInvariantCredit` to open an invariant, and we provide an
// exec-mode function `create_open_invariant_credit` to obtain one.

verus! {

#[doc(hidden)]
#[cfg_attr(verus_keep_ghost, verifier::proof)]
#[verifier::external_body]
pub struct OpenInvariantCredit {}

// It's intentional that `create_open_invariant_credit` uses `exec` mode. This prevents
// creation of an infinite number of credits to open invariants infinitely often.
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::invariant::create_open_invariant_credit"]
#[verifier::external_body]
#[inline(always)]
pub fn create_open_invariant_credit() -> Tracked<OpenInvariantCredit>
    opens_invariants none
    no_unwind
{
    Tracked::<OpenInvariantCredit>::assume_new()
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::invariant::spend_open_invariant_credit_in_proof"]
#[doc(hidden)]
#[inline(always)]
pub proof fn spend_open_invariant_credit_in_proof(tracked credit: OpenInvariantCredit) {
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::invariant::spend_open_invariant_credit"]
#[doc(hidden)]
#[inline(always)]
pub fn spend_open_invariant_credit(credit: Tracked<OpenInvariantCredit>)
    opens_invariants none
    no_unwind
{
    proof {
        spend_open_invariant_credit_in_proof(credit.get());
    }
}

} // verus!
// NOTE: These 3 methods are removed in the conversion to VIR; they are only used
// for encoding and borrow-checking.
// In the VIR these are all replaced by the OpenInvariant block.
// This means that the bodies, preconditions, and even their modes are not important.
//
// An example usage of the macro is like
//
//   i: AtomicInvariant<X>
//
//   open_invariant!(&i => inner => {
//      { modify `inner` here }
//   });
//
//  where `inner` will have type `X`.
#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::invariant::open_atomic_invariant_begin"]
#[doc(hidden)]
#[verifier::external] /* vattr */
pub fn open_atomic_invariant_begin<'a, K, V, Pred: InvariantPredicate<K, V>>(
    _inv: &'a AtomicInvariant<K, V, Pred>,
) -> (InvariantBlockGuard, V) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::invariant::open_local_invariant_begin"]
#[doc(hidden)]
#[verifier::external] /* vattr */
pub fn open_local_invariant_begin<'a, K, V, Pred: InvariantPredicate<K, V>>(
    _inv: &'a LocalInvariant<K, V, Pred>,
) -> (InvariantBlockGuard, V) {
    unimplemented!();
}

#[cfg(verus_keep_ghost)]
#[rustc_diagnostic_item = "verus::vstd::invariant::open_invariant_end"]
#[doc(hidden)]
#[verifier::external] /* vattr */
pub fn open_invariant_end<V>(_guard: InvariantBlockGuard, _v: V) {
    unimplemented!();
}

/// Macro used to temporarily "open" an [`AtomicInvariant`] object, obtaining the stored
/// value within.
///
/// ### Usage
///
/// The form of the macro looks like,
///
/// ```rust
/// open_atomic_invariant($inv => $id => {
///     // Inner scope
/// });
/// ```
///
/// This operation is very similar to [`open_local_invariant!`], so we refer to its
/// documentation for the basics. There is only one difference, besides
/// the fact that `$inv` should be an [`&AtomicInvariant`](AtomicInvariant)
/// rather than a [`&LocalInvariant`](LocalInvariant).
/// The difference is that `open_atomic_invariant!` has an additional _atomicity constraint_:
///
///  * **Atomicity constraint**: The code body of an `open_atomic_invariant!` block
///    cannot contain any `exec`-mode code with the exception of a _single_ atomic operation.
///
/// (Of course, the code block can still contain an arbitrary amount of ghost code.)
///
/// The atomicity constraint is needed because an `AtomicInvariant` must be thread-safe;
/// that is, it can be shared across threads. In order for the ghost state to be shared
/// safely, it must be restored after each atomic operation.
///
/// The atomic operations may be found in the [`PAtomic`](crate::atomic) library.
/// The user can also mark their own functions as "atomic operations" using
/// `#[verifier::atomic)]`; however, this is not useful for very much other than defining
/// wrappers around the existing atomic operations from [`PAtomic`](crate::atomic).
/// Note that reading and writing through a [`PCell`](crate::cell::PCell)
/// or a [`PPtr`](crate::simple_pptr::PPtr) are _not_ atomic operations.
///
/// **Note:** Rather than using `open_atomic_invariant!` directly, we generally recommend
/// using the [`atomic_ghost` APIs](crate::atomic_ghost).
///
/// It's not legal to use `open_atomic_invariant!` in proof mode. In proof mode, you need
/// to use `open_atomic_invariant_in_proof!` instead. This takes one extra parameter,
/// an open-invariant credit, which you can get by calling
/// `create_open_invariant_credit()` before you enter proof mode.

/// ### Example
///
/// TODO fill this in

// TODO the `$eexpr` argument here should be macro'ed in ghost context, not exec

#[macro_export]
macro_rules! open_atomic_invariant {
    [$($tail:tt)*] => {
        #[cfg(verus_keep_ghost_body)]
        let credit = $crate::vstd::invariant::create_open_invariant_credit();
        ::builtin_macros::verus_exec_inv_macro_exprs!(
            $crate::vstd::invariant::open_atomic_invariant_internal!(credit => $($tail)*)
        )
    };
}

#[macro_export]
macro_rules! open_atomic_invariant_in_proof {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_ghost_inv_macro_exprs!($crate::vstd::invariant::open_atomic_invariant_in_proof_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! open_atomic_invariant_internal {
    ($credit_expr:expr => $eexpr:expr => $iident:ident => $bblock:block) => {
        #[cfg_attr(verus_keep_ghost, verifier::invariant_block)] /* vattr */ {
            #[cfg(verus_keep_ghost_body)]
            $crate::vstd::invariant::spend_open_invariant_credit($credit_expr);
            #[cfg(verus_keep_ghost_body)]
            #[allow(unused_mut)] let (guard, mut $iident) =
                $crate::vstd::invariant::open_atomic_invariant_begin($eexpr);
            $bblock
            #[cfg(verus_keep_ghost_body)]
            $crate::vstd::invariant::open_invariant_end(guard, $iident);
        }
    }
}

#[macro_export]
macro_rules! open_atomic_invariant_in_proof_internal {
    ($credit_expr:expr => $eexpr:expr => $iident:ident => $bblock:block) => {
        #[cfg_attr(verus_keep_ghost, verifier::invariant_block)] /* vattr */ {
            #[cfg(verus_keep_ghost_body)]
            $crate::vstd::invariant::spend_open_invariant_credit_in_proof($credit_expr);
            #[cfg(verus_keep_ghost_body)]
            #[allow(unused_mut)] let (guard, mut $iident) =
                $crate::vstd::invariant::open_atomic_invariant_begin($eexpr);
            $bblock
            #[cfg(verus_keep_ghost_body)]
            $crate::vstd::invariant::open_invariant_end(guard, $iident);
        }
    }
}

pub use open_atomic_invariant;
pub use open_atomic_invariant_in_proof;
#[doc(hidden)]
pub use open_atomic_invariant_in_proof_internal;
#[doc(hidden)]
pub use open_atomic_invariant_internal;

/// Macro used to temporarily "open" a [`LocalInvariant`] object, obtaining the stored
/// value within.
///
/// ### Usage
///
/// The form of the macro looks like,
///
/// ```rust
/// open_local_invariant($inv => $id => {
///     // Inner scope
/// });
/// ```
///
/// The operation of opening an invariant is a ghost one; however, the inner code block
/// may contain arbitrary `exec`-mode code. The invariant remains "open" for the duration
/// of the inner code block, and it is closed again of the end of the block.
///
/// The `$inv` parameter should be an expression of type `&LocalInvariant<K, V, Pred>`,
/// the invariant object to be opened. The `$id` is an identifier which is bound within
/// the code block as a `mut` variable of type `V`. This gives the user ownership over
/// the `V` value, which they may manipulate freely within the code block. At the end
/// of the code block, the variable `$id` is consumed.
///
/// The obtained object `v: V`, will satisfy the `LocalInvariant`'s invariant predicate
/// [`$inv.inv(v)`](LocalInvariant::inv). Furthermore, the user must prove that this
/// invariant still holds at the end. In other words, the macro usage is
/// roughly equivalent to the following:
///
/// ```rust
/// {
///     let $id: V = /* an arbitrary value */;
///     assume($inv.inv($id));
///     /* user code block here */
///     assert($inv.inv($id));
///     consume($id);
/// }
/// ```
///
/// ### Avoiding Reentrancy
///
/// Verus adds additional checks to ensure that an invariant is never opened
/// more than once at the same time. For example, suppose that you attempt to nest
/// the use of `open_invariant`, supplying the same argument `inv` to each:
///
/// ```rust
/// open_local_invariant(inv => id1 => {
///     open_local_invariant(inv => id2 => {
///     });
/// });
/// ```
///
/// In this situation, Verus would produce an error:
///
/// ```
/// error: possible invariant collision
///   |
///   |   open_atomic_invariant!(&inv => id1 => {
///   |                           ^ this invariant
///   |       open_atomic_invariant!(&inv => id2 => {
///   |                               ^ might be the same as this invariant
///   ...
///   |       }
///   |   }
/// ```
///
/// When generating these conditions, Verus compares invariants via their
/// [`namespace()`](LocalInvariant::namespace) values.
/// An invariant's namespace (represented simply as an integer)
/// is specified upon the call to [`LocalInvariant::new`].
/// If you have the need to open multiple invariants at once, make sure to given
/// them different namespaces.
///
/// So that Verus can ensure that there are no nested invariant accesses across function
/// boundaries, every `proof` and `exec` function has, as part of its specification,
/// the set of invariant namespaces that it might open.
///
/// The invariant set of a function can be specified via the [`opens_invariants` clause](https://verus-lang.github.io/verus/guide/reference-opens-invariants.html).
/// The default for an `exec`-mode function is to open any, while the default
/// for a `proof`-mode function is to open none.
///
/// It's not legal to use `open_local_invariant!` in proof mode. In proof mode, you need
/// to use `open_local_invariant_in_proof!` instead. This takes one extra parameter,
/// an open-invariant credit, which you can get by calling
/// `create_open_invariant_credit()` before you enter proof mode.
///
/// ### Example
///
/// TODO fill this in
///
/// ### More Examples
///
/// TODO fill this in

#[macro_export]
macro_rules! open_local_invariant {
    [$($tail:tt)*] => {
        #[cfg(verus_keep_ghost_body)]
        let credit = $crate::vstd::invariant::create_open_invariant_credit();
        ::builtin_macros::verus_exec_inv_macro_exprs!(
            $crate::vstd::invariant::open_local_invariant_internal!(credit => $($tail)*))
    };
}

#[macro_export]
macro_rules! open_local_invariant_in_proof {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_ghost_inv_macro_exprs!($crate::vstd::invariant::open_local_invariant_in_proof_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! open_local_invariant_internal {
    ($credit_expr:expr => $eexpr:expr => $iident:ident => $bblock:block) => {
        #[cfg_attr(verus_keep_ghost, verifier::invariant_block)] /* vattr */ {
            #[cfg(verus_keep_ghost_body)]
            $crate::vstd::invariant::spend_open_invariant_credit($credit_expr);
            #[cfg(verus_keep_ghost_body)]
            #[allow(unused_mut)] let (guard, mut $iident) = $crate::vstd::invariant::open_local_invariant_begin($eexpr);
            $bblock
            #[cfg(verus_keep_ghost_body)]
            $crate::vstd::invariant::open_invariant_end(guard, $iident);
        }
    }
}

#[macro_export]
macro_rules! open_local_invariant_in_proof_internal {
    ($credit_expr:expr => $eexpr:expr => $iident:ident => $bblock:block) => {
        #[cfg_attr(verus_keep_ghost, verifier::invariant_block)] /* vattr */ {
            #[cfg(verus_keep_ghost_body)]
            $crate::vstd::invariant::spend_open_invariant_credit_in_proof($credit_expr);
            #[cfg(verus_keep_ghost_body)]
            #[allow(unused_mut)] let (guard, mut $iident) = $crate::vstd::invariant::open_local_invariant_begin($eexpr);
            $bblock
            #[cfg(verus_keep_ghost_body)]
            $crate::vstd::invariant::open_invariant_end(guard, $iident);
        }
    }
}

pub use open_local_invariant;
pub use open_local_invariant_in_proof;
#[doc(hidden)]
pub use open_local_invariant_in_proof_internal;
#[doc(hidden)]
pub use open_local_invariant_internal;
