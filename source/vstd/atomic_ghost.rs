//! Provides sequentially-consistent atomic memory locations with associated ghost state.
//! See the [`atomic_with_ghost!`] documentation for more information.
#![allow(unused_imports)]

use super::atomic::*;
use super::invariant::*;
use super::modes::*;
use super::prelude::*;

verus! {

pub trait AtomicInvariantPredicate<K, V, G> {
    spec fn atomic_inv(k: K, v: V, g: G) -> bool;
}

} // verus!
macro_rules! declare_atomic_type {
    ($at_ident:ident, $patomic_ty:ident, $perm_ty:ty, $value_ty: ty, $atomic_pred_ty: ident) => {
        verus!{

        pub struct $atomic_pred_ty<Pred> { p: Pred }

        impl<K, G, Pred> InvariantPredicate<(K, int), ($perm_ty, G)> for $atomic_pred_ty<Pred>
            where Pred: AtomicInvariantPredicate<K, $value_ty, G>
        {
            open spec fn inv(k_loc: (K, int), perm_g: ($perm_ty, G)) -> bool {
                let (k, loc) = k_loc;
                let (perm, g) = perm_g;

                perm.view().patomic == loc
                  && Pred::atomic_inv(k, perm.view().value, g)
            }
        }

        #[doc = concat!(
            "Sequentially-consistent atomic memory location storing a `",
            stringify!($value_ty),
            "` and associated ghost state."
        )]
        ///
        /// See the [`atomic_with_ghost!`] documentation for usage information.

        pub struct $at_ident<K, G, Pred>
            //where Pred: AtomicInvariantPredicate<K, $value_ty, G>
        {
            #[doc(hidden)]
            pub patomic: $patomic_ty,

            #[doc(hidden)]
            pub atomic_inv: Tracked<AtomicInvariant<(K, int), ($perm_ty, G), $atomic_pred_ty<Pred>>>,
        }

        impl<K, G, Pred> $at_ident<K, G, Pred>
            where Pred: AtomicInvariantPredicate<K, $value_ty, G>
        {
            pub open spec fn well_formed(&self) -> bool {
                self.atomic_inv@.constant().1 == self.patomic.id()
            }

            pub open spec fn constant(&self) -> K {
                self.atomic_inv@.constant().0
            }

            #[inline(always)]
            pub const fn new(Ghost(k): Ghost<K>, u: $value_ty, Tracked(g): Tracked<G>) -> (t: Self)
                requires Pred::atomic_inv(k, u, g),
                ensures t.well_formed() && t.constant() == k,
            {

                let (patomic, Tracked(perm)) = $patomic_ty::new(u);

                let tracked pair = (perm, g);
                let tracked atomic_inv = AtomicInvariant::new(
                    (k, patomic.id()), pair, 0);

                $at_ident {
                    patomic,
                    atomic_inv: Tracked(atomic_inv),
                }
            }

            #[inline(always)]
            pub fn load(&self) -> $value_ty
                requires self.well_formed(),
            {
                atomic_with_ghost!(self => load(); g => { })
            }

            #[inline(always)]
            pub fn into_inner(self) -> (res: ($value_ty, Tracked<G>))
                requires self.well_formed(),
                ensures Pred::atomic_inv(self.constant(), res.0, res.1@),
            {
                let Self { patomic, atomic_inv: Tracked(atomic_inv) } = self;
                let tracked (perm, g) = atomic_inv.into_inner();
                let v = patomic.into_inner(Tracked(perm));
                (v, Tracked(g))
            }
        }

        }
    };
}
macro_rules! declare_atomic_type_generic {
    ($at_ident:ident, $patomic_ty:ident, $perm_ty:ty, $value_ty: ty, $atomic_pred_ty: ident) => {
        verus!{

        pub struct $atomic_pred_ty<T, Pred> { t: T, p: Pred }

        impl<T, K, G, Pred> InvariantPredicate<(K, int), ($perm_ty, G)> for $atomic_pred_ty<T, Pred>
            where Pred: AtomicInvariantPredicate<K, $value_ty, G>
        {
            open spec fn inv(k_loc: (K, int), perm_g: ($perm_ty, G)) -> bool {
                let (k, loc) = k_loc;
                let (perm, g) = perm_g;

                perm.view().patomic == loc
                  && Pred::atomic_inv(k, perm.view().value, g)
            }
        }

        #[doc = concat!(
            "Sequentially-consistent atomic memory location storing a `",
            stringify!($value_ty),
            "` and associated ghost state."
        )]
        ///
        /// See the [`atomic_with_ghost!`] documentation for usage information.

        pub struct $at_ident<T, K, G, Pred>
            //where Pred: AtomicInvariantPredicate<K, $value_ty, G>
        {
            #[doc(hidden)]
            pub patomic: $patomic_ty<T>,

            #[doc(hidden)]
            pub atomic_inv: Tracked<AtomicInvariant<(K, int), ($perm_ty, G), $atomic_pred_ty<T, Pred>>>,
        }

        impl<T, K, G, Pred> $at_ident<T, K, G, Pred>
            where Pred: AtomicInvariantPredicate<K, $value_ty, G>
        {
            pub open spec fn well_formed(&self) -> bool {
                self.atomic_inv@.constant().1 == self.patomic.id()
            }

            pub open spec fn constant(&self) -> K {
                self.atomic_inv@.constant().0
            }

            #[inline(always)]
            pub const fn new(Ghost(k): Ghost<K>, u: $value_ty, Tracked(g): Tracked<G>) -> (t: Self)
                requires Pred::atomic_inv(k, u, g),
                ensures t.well_formed() && t.constant() == k,
            {

                let (patomic, Tracked(perm)) = $patomic_ty::<T>::new(u);

                let tracked pair = (perm, g);
                let tracked atomic_inv = AtomicInvariant::new(
                    (k, patomic.id()), pair, 0);

                $at_ident {
                    patomic,
                    atomic_inv: Tracked(atomic_inv),
                }
            }

            #[inline(always)]
            pub fn load(&self) -> $value_ty
                requires self.well_formed(),
            {
                atomic_with_ghost!(self => load(); g => { })
            }

            #[inline(always)]
            pub fn into_inner(self) -> (res: ($value_ty, Tracked<G>))
                requires self.well_formed(),
                ensures Pred::atomic_inv(self.constant(), res.0, res.1@),
            {
                let Self { patomic, atomic_inv: Tracked(atomic_inv) } = self;
                let tracked (perm, g) = atomic_inv.into_inner();
                let v = patomic.into_inner(Tracked(perm));
                (v, Tracked(g))
            }
        }

        }
    };
}

declare_atomic_type!(AtomicU64, PAtomicU64, PermissionU64, u64, AtomicPredU64);
declare_atomic_type!(AtomicU32, PAtomicU32, PermissionU32, u32, AtomicPredU32);
declare_atomic_type!(AtomicU16, PAtomicU16, PermissionU16, u16, AtomicPredU16);
declare_atomic_type!(AtomicU8, PAtomicU8, PermissionU8, u8, AtomicPredU8);
declare_atomic_type!(AtomicUsize, PAtomicUsize, PermissionUsize, usize, AtomicPredUsize);

declare_atomic_type!(AtomicI64, PAtomicI64, PermissionI64, i64, AtomicPredI64);
declare_atomic_type!(AtomicI32, PAtomicI32, PermissionI32, i32, AtomicPredI32);
declare_atomic_type!(AtomicI16, PAtomicI16, PermissionI16, i16, AtomicPredI16);
declare_atomic_type!(AtomicI8, PAtomicI8, PermissionI8, i8, AtomicPredI8);
declare_atomic_type!(AtomicIsize, PAtomicIsize, PermissionIsize, isize, AtomicPredIsize);

declare_atomic_type!(AtomicBool, PAtomicBool, PermissionBool, bool, AtomicPredBool);

declare_atomic_type_generic!(AtomicPtr, PAtomicPtr, PermissionPtr<T>, *mut T, AtomicPredPtr);

/// Performs a given atomic operation on a given atomic
/// while providing access to its ghost state.
///
/// `atomic_with_ghost!` supports the types
/// [`AtomicU64`] [`AtomicU32`], [`AtomicU16`], [`AtomicU8`],
/// [`AtomicI64`], [`AtomicI32`], [`AtomicI16`], [`AtomicI8`], and [`AtomicBool`].
///
/// For each type, it supports all applicable atomic operations among
/// `load`, `store`, `swap`, `compare_exchange`, `compare_exchange_weak`,
/// `fetch_add`, `fetch_add_wrapping`, `fetch_sub`, `fetch_sub_wrapping`,
/// `fetch_or`, `fetch_and`, `fetch_xor`, `fetch_nand`, `fetch_max`, and `fetch_min`.
///
/// Naturally, `AtomicBool` does not support the arithmetic-specific operations.
///
/// In general, the syntax is:
///
///     let result = atomic_with_ghost!(
///         $atomic => $operation_name($operands...);
///         update $prev -> $next;         // `update` line is optional
///         returning $ret;                // `returning` line is optional
///         ghost $g => {
///             /* Proof code with access to `tracked` variable `g: G` */
///         }
///     );
///
/// Here, the `$operation_name` is one of `load`, `store`, etc. Meanwhile,
/// `$prev`, `$next`, and `$ret` are all identifiers which
/// will be available as spec variable inside the block to describe the
/// atomic action which is performed.
///
/// For example, suppose the user performs `fetch_add(1)`. The atomic
/// operation might load the value 5, add 1, store the value 6,
/// and return the original value, 5. In that case, we would have
/// `prev == 5`, `next == 6`, and `ret == 5`.
///
/// The specification for a given operation is given as a relation between
/// `prev`, `next`, and `ret`; that is, at the beginning of the proof block,
/// the user may assume the given specification holds:
///
/// | operation                     | specification                                                                                                              |
/// |-------------------------------|----------------------------------------------------------------------------------------------------------------------------|
/// | `load()`                      | `next == prev && rev == prev`                                                                                              |
/// | `store(x)`                    | `next == x && ret == ()`                                                                                                   |
/// | `swap(x)`                     | `next == x && ret == prev`                                                                                                 |
/// | `compare_exchange(x, y)`      | `prev == x && next == y && ret == Ok(prev)` ("success") OR<br> `prev != x && next == prev && ret == Err(prev)` ("failure") |
/// | `compare_exchange_weak(x, y)` | `prev == x && next == y && ret == Ok(prev)` ("success") OR<br> `next == prev && ret == Err(prev)` ("failure")              |
/// | `fetch_add(x)` (*)            | `next == prev + x && ret == prev`                                                                                          |
/// | `fetch_add_wrapping(x)`       | `next == wrapping_add(prev, x) && ret == prev`                                                                             |
/// | `fetch_sub(x)` (*)            | `next == prev - x && ret == prev`                                                                                          |
/// | `fetch_sub_wrapping(x)`       | `next == wrapping_sub(prev, x) && ret == prev`                                                                             |
/// | `fetch_or(x)`                 | <code>next == prev \| x && ret == prev</code>                                                                              |
/// | `fetch_and(x)`                | `next == prev & x && ret == prev`                                                                                          |
/// | `fetch_xor(x)`                | `next == prev ^ x && ret == prev`                                                                                          |
/// | `fetch_nand(x)`               | `next == !(prev & x) && ret == prev`                                                                                       |
/// | `fetch_max(x)`                | `next == max(prev, x) && ret == prev`                                                                                      |
/// | `fetch_min(x)`                | `next == max(prev, x) && ret == prev`                                                                                      |
/// | `no_op()` (**)                | `next == prev && ret == ()`                                                                                                |
///
/// (*) Note that `fetch_add` and `fetch_sub` do not specify
/// wrapping-on-overflow; instead, they require the user to
/// prove that overflow _does not occur_, i.e., the user must show
/// that `next` is in bounds for the integer type in question.
/// Furthermore, for `fetch_add` and `fetch_sub`, the spec values of
/// `prev`, `next`, and `ret` are all given with type `int`, so the
/// user may reason about boundedness within the proof block.
///
/// (As executable code, `fetch_add` is equivalent to `fetch_add_wrapping`,
/// and likewise for `fetch_sub` and `fetch_sub_wrapping`.
/// We have both because it's frequently the case that the user needs to verify
/// lack-of-overflow _anyway_, and having it as an explicit precondition by default
/// then makes verification errors easier to diagnose. Furthermore, when overflow is
/// intended, the wrapping operations document that intent.)
///
/// (**) `no_op` is entirely a ghost operation and doesn't emit any actual instruction.
/// This allows the user to access the ghost state and the stored value (as `spec` data)
/// without actually performing a load.
///
/// ---
///
/// At the beginning of the proof block, the user may assume, in addition
/// to the specified relation between `prev`, `next`, and `ret`, that
/// `atomic.inv(prev, g)` holds. The user is required to update `g` such that
/// `atomic.inv(next, g)` holds at the end of the block.
/// In other words, the ghost block has the implicit pre- and post-conditions:
///
///     let result = atomic_with_ghost!(
///         $atomic => $operation_name($operands...);
///         update $prev -> $next;
///         returning $ret;
///         ghost $g => {
///             assume(specified relation on (prev, next, ret));
///             assume(atomic.inv(prev, g));
///
///             // User code here; may update variable `g` with full
///             // access to variables in the outer context.
///
///             assert(atomic.inv(next, g));
///         }
///     );
///
/// Note that the necessary action on ghost state might depend
/// on the result of the operation; for example, if the user performs a
/// compare-and-swap, then the ghost action that they then need to do
/// will probably depend on whether the operation succeeded or not.
///
/// The value returned by the `atomic_with_ghost!(...)` expression will be equal
/// to `ret`, although the return value is an `exec` value (the actual result of
/// the operation) while `ret` is a `spec` value.
///
/// ### Example (TODO)

#[macro_export]
macro_rules! atomic_with_ghost {
    ($($tokens:tt)*) => {
        // The helper is used to parse things using Verus syntax
        // The helper then calls atomic_with_ghost_inner, below:
        ::builtin_macros::atomic_with_ghost_helper!(
            $crate::vstd::atomic_ghost::atomic_with_ghost_inner,
            $($tokens)*)
    }
}

pub use atomic_with_ghost;

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_inner {
    (load, $e:expr, (), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_load!($e, $prev, $next, $ret, $g, $b)
    };
    (store, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_store!(
            $e, $operand, $prev, $next, $ret, $g, $b
        )
    };
    (swap, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
            swap, $e, $operand, $prev, $next, $ret, $g, $b
        )
    };

    (fetch_or, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
            fetch_or, $e, $operand, $prev, $next, $ret, $g, $b
        )
    };
    (fetch_and, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
            fetch_and, $e, $operand, $prev, $next, $ret, $g, $b
        )
    };
    (fetch_xor, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
            fetch_xor, $e, $operand, $prev, $next, $ret, $g, $b
        )
    };
    (fetch_nand, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
            fetch_nand, $e, $operand, $prev, $next, $ret, $g, $b
        )
    };
    (fetch_max, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
            fetch_max, $e, $operand, $prev, $next, $ret, $g, $b
        )
    };
    (fetch_min, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
            fetch_min, $e, $operand, $prev, $next, $ret, $g, $b
        )
    };
    (fetch_add_wrapping, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
            fetch_add_wrapping,
            $e,
            $operand,
            $prev,
            $next,
            $ret,
            $g,
            $b
        )
    };
    (fetch_sub_wrapping, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_with_1_operand!(
            fetch_sub_wrapping,
            $e,
            $operand,
            $prev,
            $next,
            $ret,
            $g,
            $b
        )
    };

    (fetch_add, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_fetch_add!(
            $e, $operand, $prev, $next, $ret, $g, $b
        )
    };
    (fetch_sub, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_fetch_sub!(
            $e, $operand, $prev, $next, $ret, $g, $b
        )
    };

    (compare_exchange, $e:expr, ($operand1:expr, $operand2:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_with_2_operand!(
            compare_exchange,
            $e,
            $operand1,
            $operand2,
            $prev,
            $next,
            $ret,
            $g,
            $b
        )
    };
    (compare_exchange_weak, $e:expr, ($operand1:expr, $operand2:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_update_with_2_operand!(
            compare_exchange_weak,
            $e,
            $operand1,
            $operand2,
            $prev,
            $next,
            $ret,
            $g,
            $b
        )
    };
    (no_op, $e:expr, (), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        $crate::vstd::atomic_ghost::atomic_with_ghost_no_op!($e, $prev, $next, $ret, $g, $b)
    };
}

pub use atomic_with_ghost_inner;

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_store {
    ($e:expr, $operand:expr, $prev:pat, $next:pat, $res:pat, $g:ident, $b:block) => {
        ::builtin_macros::verus_exec_expr! { {
            let atomic = &($e);
            $crate::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (mut perm, mut $g) = pair;
                let ghost $prev = perm.view().value;
                atomic.patomic.store(Tracked(&mut perm), $operand);
                let ghost $next = perm.view().value;
                let ghost $res = ();

                proof { $b }

                proof { pair = (perm, $g); }
            });
        } }
    };
}
pub use atomic_with_ghost_store;

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_load {
    ($e:expr, $prev:pat, $next: pat, $res: pat, $g:ident, $b:block) => {
        ::builtin_macros::verus_exec_expr! { {
            let result;
            let atomic = &($e);
            $crate::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (perm, mut $g) = pair;
                result = atomic.patomic.load(Tracked(&perm));
                let ghost $res = result;
                let ghost $prev = result;
                let ghost $next = result;

                proof { $b }

                proof { pair = (perm, $g); }
            });
            result
        } }
    };
}

pub use atomic_with_ghost_load;

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_no_op {
    ($e:expr, $prev:pat, $next: pat, $res: pat, $g:ident, $b:block) => {
        ::builtin_macros::verus_exec_expr! { {
            let atomic = &($e);
            $crate::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (perm, mut $g) = pair;
                let ghost result = perm.view().value;
                let ghost $res = result;
                let ghost $prev = result;
                let ghost $next = result;

                proof { $b }

                proof { pair = (perm, $g); }
            });
        } }
    };
}

pub use atomic_with_ghost_no_op;

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_update_with_1_operand {
    ($name:ident, $e:expr, $operand:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        ::builtin_macros::verus_exec_expr! { {
            let result;
            let atomic = &($e);
            let operand = $operand;
            $crate::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (mut perm, mut $g) = pair;
                let ghost $prev = perm.view().value;
                result = atomic.patomic.$name(Tracked(&mut perm), operand);
                let ghost $res = result;
                let ghost $next = perm.view().value;

                proof { $b }

                proof { pair = (perm, $g); }
            });
            result
        } }
    };
}

pub use atomic_with_ghost_update_with_1_operand;

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_update_with_2_operand {
    ($name:ident, $e:expr, $operand1:expr, $operand2:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        ::builtin_macros::verus_exec_expr! { {
            let result;
            let atomic = &($e);
            let operand1 = $operand1;
            let operand2 = $operand2;
            $crate::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (mut perm, mut $g) = pair;
                let ghost $prev = perm.view().value;
                result = atomic.patomic.$name(Tracked(&mut perm), operand1, operand2);
                let ghost $res = result;
                let ghost $next = perm.view().value;

                proof { $b }

                proof { pair = (perm, $g); }
            });
            result
        } }
    };
}

pub use atomic_with_ghost_update_with_2_operand;

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_update_fetch_add {
    ($e:expr, $operand:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        (::builtin_macros::verus_exec_expr!( {
            let result;
            let atomic = &($e);
            let operand = $operand;
            $crate::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (mut perm, mut $g) = pair;

                proof {
                    let $prev = perm.view().value as int;
                    let $res = perm.view().value as int;
                    let $next = perm.view().value as int + (operand as int);

                    { $b }
                }

                result = atomic.patomic.fetch_add(Tracked(&mut perm), operand);

                proof { pair = (perm, $g); }
            });
            result
        } ))
    }
}

pub use atomic_with_ghost_update_fetch_add;

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_update_fetch_sub {
    ($e:expr, $operand:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        ::builtin_macros::verus_exec_expr! { {
            let result;
            let atomic = &($e);
            let operand = $operand;
            $crate::vstd::invariant::open_atomic_invariant!(atomic.atomic_inv.borrow() => pair => {
                #[allow(unused_mut)]
                let tracked (mut perm, mut $g) = pair;

                proof {
                    let $prev = perm.view().value as int;
                    let $res = perm.view().value as int;
                    let $next = perm.view().value as int - (operand as int);

                    { $b }
                }

                result = atomic.patomic.fetch_sub(Tracked(&mut perm), operand);

                proof { pair = (perm, $g); }
            });
            result
        } }
    };
}

pub use atomic_with_ghost_update_fetch_sub;
