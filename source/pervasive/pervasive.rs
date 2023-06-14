#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[cfg(feature = "non_std")]
macro_rules! println {
    ($($arg:tt)*) => {
    };
}

verus! {

// TODO: remove this
pub proof fn assume(b: bool)
    ensures b
{
    admit();
}

// TODO: remove this
#[verifier(custom_req_err("assertion failure"))]
pub proof fn assert(b: bool)
    requires b
    ensures b
{
}

pub proof fn affirm(b: bool)
    requires b
{
}

// Non-statically-determined function calls are translated *internally* (at the VIR level)
// to this function call. This should not actually be called directly by the user.
// That is, Verus treats `f(x, y)` as `exec_nonstatic_call(f, (x, y))`.
// (Note that this function wouldn't even satisfy the borrow-checker if you tried to
// use it with a `&F` or `&mut F`, but this doesn't matter since it's only used at VIR.)

#[verifier(custom_req_err("Call to non-static function fails to satisfy `callee.requires(args)`"))]
#[doc(hidden)]
#[verifier(external_body)]
fn exec_nonstatic_call<Args: std::marker::Tuple, Output, F>(f: F, args: Args) -> (output: Output)
    where F: FnOnce<Args, Output=Output>
    requires f.requires(args)
    ensures f.ensures(args, output)
{
    unimplemented!();
}

/// A tool to check one's reasoning while writing complex spec functions.
/// Not intended to be used as a mechanism for instantiating quantifiers, `spec_affirm` should
/// be removed from spec functions once they are complete.
///
/// ## Example
///
/// ```rust
/// #[spec(checked)] fn some_predicate(a: nat) -> bool {
///     recommends(a < 100);
///     if (a >= 50) {
///         let _ = spec_affirm(50 <= a && a < 100);
///         a >= 75
///     } else {
///         let _ = spec_affirm(a < 50);
///         // let _ = spec_affirm(a < 40); would raise a recommends note here
///         a < 25
///     }
/// }
/// ```
pub closed spec fn spec_affirm(b: bool) -> bool
    recommends b
{
    b
}

/// In spec, all types are inhabited
#[verifier(external_body)] /* vattr */
#[allow(dead_code)]
pub closed spec fn arbitrary<A>() -> A {
    unimplemented!()
}

#[verifier(external_body)] /* vattr */
#[allow(dead_code)]
pub proof fn proof_from_false<A>() -> (tracked a: A) {
    requires(false);

    unimplemented!()
}

#[verifier(external_body)] /* vattr */
#[allow(dead_code)]
pub fn unreached<A>() -> A
    requires false
{
    panic!("unreached_external")
}

#[verifier(external_body)] /* vattr */
pub fn print_u64(i: u64) {
    println!("{}", i);
}

/// deprecated, use core::mem::swap or std::mem::swap directly instead (TODO remove this)
#[verifier(external_body)]
pub fn swap<A>(x: &mut A, y: &mut A)
    ensures
        *x == *old(y),
        *y == *old(x),
{
    core::mem::swap(x, y)
}

} // verus!

/// Allows you to prove a boolean predicate by assuming its negation and proving
/// a contradiction.
///
/// `assert_by_contradiction!(b, { /* proof */ });`
/// Equivalent to writing `if !b { /* proof */; assert(false); }`
/// but is more concise and documents intent.
///
/// ```rust
/// assert_by_contradiction!(b, {
///     // assume !b here
///     // prove `false`
/// });
/// ```

#[macro_export]
macro_rules! assert_by_contradiction {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!($crate::assert_by_contradiction_internal!($($a)*))
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! assert_by_contradiction_internal {
    ($predicate:expr, $bblock:block) => {
        ::builtin::assert_by($predicate, {
            if !$predicate {
                $bblock
                ::builtin::assert_(false);
            }
        });
    }
}

/// Macro to help set up boilerplate for specifying invariants when using
/// invariant-based datatypes.
///
/// This currently supports the `AtomicInvariant` and `LocalInvariant`
/// types, as well as all the `atomic_ghost` types (e.g., `AtomicU64`, `AtomicBool`, and so on).
/// It is important to first understand how these types work.
/// In particular, `LocalInvariant` (for example) takes three type parameters,
/// `K`, `V`, and `Pred: InvariantPredicate`.
/// The `InvariantPredicate` trait lets the user specify an invariant at the static type
/// level, while `K` allows the user to configure the invariant upon construction.
/// `AtomicInvariant` uses the same system, and the `atomic_ghost` types are similar
/// but use a different trait (`AtomicInvariantPredicate`).
///
/// However, setting all this up in a typical application tends to involve a bit
/// of boilerplate. That's where this macro comes in.
///
/// # Usage
///
/// The `struct_with_invariants!` macro is used at the item level, and it should contains
/// a single struct declaration followed by a single declaration of a `spec` function
/// returning `bool`. However, this spec function should not contain a boolean predicate
/// as usual, but instead a series of _invariant declarations_.
/// Each invariant declaration applies to a single field of the struct.
///
/// ```rust
/// struct_with_invariants!{
///     (pub)? struct $struct_name (<...>)? (where ...)? {
///         ( (pub)? $field_name: $type, )*
///     }
/// 
///     (pub)? (open|closed)? spec fn(&self (, ...)?) $fn_name {
///         ( InvariantDecl | BoolPredicateDecl )*
///     }
/// }
/// ```
///
/// A field of the struct, if it uses a supported type, may leave the type _incomplete_ by
/// omitting some of its type parameters.
/// The following are valid incomplete types:
///
///  * `LocalInvariant<_, V, _>`
///  * `AtomicInvariant<_, V, _>`
///  * `AtomicBool<_, G, _>`
///  * `AtomicU64<_, G, _>`
///    * ... and so on for the other `atomic_ghost` types.
///
/// There must be exactly one invariant declaration for each incomplete type used in the
/// struct declaration. The macro uses invariant declarations to fill in the type parameters.
///
/// The user can also provide boolean predicate declarations, which are copied verbatim
/// into the `$fn_name` definition. This is a convenience, since it is common to want
/// to add extra conditions, and it is fairly straightforward.
/// The complex part of the macro expansion in the invariant declarations.
///
/// ```rust
/// BoolPredicateDecl  :=  predicate { $bool_expr }
/// 
/// InvariantDecl  :=
///     invariant on $field_name
///         ( with ($dependencies) )?
///         ( forall | ($ident: $type, )* | )?
///         ( where ($where_expr) )?
///         ( specifically ($specifically_expr) )?
///         is ($params) {
///             $bool_expr
///         }
/// ```
///
/// In the `InvariantDecl`, the user always needs to provide the following data:
///
///  * The `$field_name` is the field that this invariant applies to
///     (which must have an incomplete type as described above)
///  * The `$params` are the values constrained by the invariant.
///      * For a `LocalInvariant<V>` or `AtomicInvariant<V>`, this should be a single
///        parameter of type `V`.
///      * For an `atomic_ghost` type, this should consist of two parameters,
///        first the primitive type stored by the atomic, and secondly one of the ghost type, `G`.
///        (For example, the type `AtomicBool<_, G, _>` should have two parameters
///        here, `b: bool, g: G`.)
///  * Finally, the `$bool_expr` is the invariant predicate, which may reference any of
///     the fields declared in `$dependencies`, or any of the params.
///
/// The other input clauses handle additional complexities that often comes up.
/// For example, it is often necessary for the invariant to refer to the values of other fields
/// in the struct.
///
///  * The `with` input gives the list of field names (other fields
///     from the struct definition) that may be referenced from
///     the body of this invariant.
///     The graph of dependencies across all fields must be acyclic.
///
/// Finally, when the field is a _container_ type, e.g., `vec: Vec<AtomicU64<_, G, _>>` or
/// `opt: Option<AtomicU64<_, G, _>>`, there are some additional complexities.
/// We might need the invariant to be conditional (e.g., for an optional, the invariant would only
/// exist if `opt.is_Some()`).
/// We might need to quantify over a variable (e.g., in a vector, we want to specify an invariant
/// for each element, element `i` where `0 <= i < vec.len()`).
/// Finally, we need to indicate the value actually getting the invariant (e.g., `self.vec[i]`).
///
/// * The `forall` lets you specify additional bound variables. Everything after the `forall`---the
///   `where`, the `specifically`, and finally the `$bool_expr$`---can all reference these bound variables.
/// * The `where` lets you specify an additional hypothesis that the invariant is dependent on.
/// * The `specifically` lets you indicate the value getting the invariant.
///
/// This all roughly means, "forall instantiations of the quantified variables, if the condition `$where_expr` holds,
/// then the value given by `$specifically_expr` has the invariant given by `$bool_expr`.
/// See the detailed information on the macro-expansion below for more details.
///
/// Given all the information from the `InvariantDecl`, the macro fills in the `_` placeholders as follows:
///
///  * The macro fills in the `K` type as the types of the fields marked as dependencies and
///    the quantified variables in the forall (packing all these types into a tuple if necessary).
///  * The macro fills in the `Pred` type by creating a new type and implementing the appropriate
///    trait with the user-provided predicate.
///
/// # Example (TODO)
///
/// # Example using a container type (TODO)
///
/// # Macro Expansion (TODO)

pub use builtin_macros::struct_with_invariants;
