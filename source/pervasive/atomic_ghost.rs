#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
use crate::pervasive::invariant::*;
use crate::pervasive::atomic::*;
use crate::pervasive::modes::*;

macro_rules! declare_atomic_type {
    ($at_ident:ident, $patomic_ty:ident, $perm_ty:ty, $value_ty: ty) => {
        pub struct $at_ident<#[verus::verifier(maybe_negative)] G> {
            pub patomic: $patomic_ty,
            #[proof] pub atomic_inv: AtomicInvariant<($perm_ty, G)>,
        }

        impl<G> $at_ident<G> {
            #[spec] #[verus::verifier(publish)]
            pub fn has_inv<F: Fn($value_ty, G) -> bool>(&self, f: F) -> bool {
                forall(|p| #[trigger] self.atomic_inv.inv(p) == (
                    self.patomic.id() == p.0.patomic
                        && f(p.0.value, p.1)
                ))
            }

            #[spec] #[verus::verifier(publish)]
            pub fn has_inv_fn<F: Fn($value_ty) -> G>(&self, f: F) -> bool {
                self.has_inv(|v: $value_ty, g: G| equal(g, f(v)))
            }

            #[inline(always)]
            pub fn new<F: Fn($value_ty, G) -> bool>(u: $value_ty, #[proof] g: G, #[spec] f: F) -> Self {
                requires(f(u, g));
                ensures(|t: Self| t.has_inv(f));

                let (patomic, Proof(perm)) = $patomic_ty::new(u);
                #[proof] let pair = (perm, g);
                #[proof] let atomic_inv = AtomicInvariant::new(pair,
                    |p| patomic.id() == p.0.patomic && f(p.0.value, p.1),
                    spec_literal_int("0"));

                $at_ident {
                    patomic,
                    atomic_inv,
                }
            }

            // TODO into_inner

            /*
            #[inline(always)]
            pub fn into_inner(self) -> ($value_ty, G) {
                ensures(

                let { patomic, atomic_inv } = self;
                let (perm, g) = atomic_inv.into_inner();
                let v = patomic.into_inner(perm);
                (v, g)
            }
            */
        }
    }
}

declare_atomic_type!(AtomicU64, PAtomicU64, PermissionU64, u64);
declare_atomic_type!(AtomicU32, PAtomicU32, PermissionU32, u32);
declare_atomic_type!(AtomicU16, PAtomicU16, PermissionU16, u16);
declare_atomic_type!(AtomicU8, PAtomicU8, PermissionU8, u8);

declare_atomic_type!(AtomicI64, PAtomicI64, PermissionI64, i64);
declare_atomic_type!(AtomicI32, PAtomicI32, PermissionI32, i32);
declare_atomic_type!(AtomicI16, PAtomicI16, PermissionI16, i16);
declare_atomic_type!(AtomicI8, PAtomicI8, PermissionI8, i8);

declare_atomic_type!(AtomicBool, PAtomicBool, PermissionBool, bool);

/// Macro to perform a given atomic operation on a given atomic
/// while providing access to its ghost state.
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
    ($atomic:expr => $operation_name:ident ($($operands:tt)*);
        update $prev:ident -> $next:ident;
        returning $ret:ident;
        ghost $g:ident => $b:block
    ) => {
        atomic_with_ghost_inner!($operation_name, $atomic, ($($operands)*), $prev, $next, $ret, $g, $b)
    };
    ($atomic:expr => $operation_name:ident ($($operands:tt)*);
        update $prev:ident -> $next:ident;
        ghost $g:ident => $b:block
    ) => {
        atomic_with_ghost_inner!($operation_name, $atomic, ($($operands)*), $prev, $next, _, $g, $b)
    };
    ($atomic:expr => $operation_name:ident ($($operands:tt)*);
        returning $ret:ident;
        ghost $g:ident => $b:block
    ) => {
        atomic_with_ghost_inner!($operation_name, $atomic, ($($operands)*), _, _, $ret, $g, $b)
    };
    ($atomic:expr => $operation_name:ident ($($operands:tt)*);
        ghost $g:ident => $b:block
    ) => {
        atomic_with_ghost_inner!($operation_name, $atomic, ($($operands)*), _, _, _, $g, $b)
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_inner {
    (load, $e:expr, (), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_load!($e, $prev, $next, $ret, $g, $b)
    };
    (store, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_store!($e, $operand, $prev, $next, $ret, $g, $b)
    };
    (swap, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_with_1_operand!(
            swap, $e, $operand, $prev, $next, $ret, $g, $b)
    };

    (fetch_or, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_with_1_operand!(
            fetch_or, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_and, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_with_1_operand!(
            fetch_and, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_xor, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_with_1_operand!(
            fetch_xor, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_nand, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_with_1_operand!(
            fetch_nand, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_max, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_with_1_operand!(
            fetch_max, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_min, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_with_1_operand!(
            fetch_min, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_add_wrapping, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_with_1_operand!(
            fetch_add_wrapping, $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_sub_wrapping, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_with_1_operand!(
            fetch_sub_wrapping, $e, $operand, $prev, $next, $ret, $g, $b)
    };

    (fetch_add, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_fetch_add!(
            $e, $operand, $prev, $next, $ret, $g, $b)
    };
    (fetch_sub, $e:expr, ($operand:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_fetch_sub!(
            $e, $operand, $prev, $next, $ret, $g, $b)
    };

    (compare_exchange, $e:expr, ($operand1:expr, $operand2:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_with_2_operand!(
            compare_exchange, $e, $operand1, $operand2, $prev, $next, $ret, $g, $b)
    };
    (compare_exchange_weak, $e:expr, ($operand1:expr, $operand2:expr), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_update_with_2_operand!(
            compare_exchange_weak, $e, $operand1, $operand2, $prev, $next, $ret, $g, $b)
    };
    (no_op, $e:expr, (), $prev:pat, $next:pat, $ret:pat, $g:ident, $b:block) => {
        atomic_with_ghost_no_op!($e, $prev, $next, $ret, $g, $b)
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_store {
    ($e:expr, $operand:expr, $prev:pat, $next:pat, $res:pat, $g:ident, $b:block) => {
        {
            let atomic = &$e;
            crate::open_atomic_invariant!(&atomic.atomic_inv => pair => {
                #[allow(unused_mut)]
                #[proof] let (mut perm, mut $g) = pair;
                #[spec] let $prev = perm.value;
                atomic.patomic.store(&mut perm, $operand);
                #[spec] let $next = perm.value;
                #[spec] let $res = ();

                { $b }

                pair = (perm, $g);
            });
        }
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_load {
    ($e:expr, $prev:pat, $next: pat, $res: pat, $g:ident, $b:block) => {
        {
            let result;
            let atomic = &$e;
            crate::open_atomic_invariant!(&atomic.atomic_inv => pair => {
                #[allow(unused_mut)]
                #[proof] let (perm, mut $g) = pair;
                result = atomic.patomic.load(&perm);
                #[spec] let $res = result;
                #[spec] let $prev = result;
                #[spec] let $next = result;

                { $b }

                pair = (perm, $g);
            });
            result
        }
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_no_op {
    ($e:expr, $prev:pat, $next: pat, $res: pat, $g:ident, $b:block) => {
        {
            let atomic = &$e;
            crate::open_atomic_invariant!(&atomic.atomic_inv => pair => {
                #[allow(unused_mut)]
                #[proof] let (perm, mut $g) = pair;
                #[spec] let $res = result;
                #[spec] let $prev = result;
                #[spec] let $next = result;

                { $b }

                pair = (perm, $g);
            });
        }
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_update_with_1_operand {
    ($name:ident, $e:expr, $operand:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        {
            let result;
            let atomic = &$e;
            crate::open_atomic_invariant!(&atomic.atomic_inv => pair => {
                #[allow(unused_mut)]
                #[proof] let (mut perm, mut $g) = pair;
                #[spec] let $prev = perm.value;
                result = atomic.patomic.$name(&mut perm, $operand);
                #[spec] let $res = result;
                #[spec] let $next = perm.value;

                { $b }

                pair = (perm, $g);
            });
            result
        }
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_update_with_2_operand {
    ($name:ident, $e:expr, $operand1:expr, $operand2:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        {
            let result;
            let atomic = &$e;
            crate::open_atomic_invariant!(&atomic.atomic_inv => pair => {
                #[allow(unused_mut)]
                #[proof] let (mut perm, mut $g) = pair;
                #[spec] let $prev = perm.value;
                result = atomic.patomic.$name(&mut perm, $operand1, $operand2);
                #[spec] let $res = result;
                #[spec] let $next = perm.value;

                { $b }

                pair = (perm, $g);
            });
            result
        }
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_update_fetch_add {
    ($e:expr, $operand:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        {
            let result;
            let atomic = &$e;
            crate::open_atomic_invariant!(&atomic.atomic_inv => pair => {
                #[allow(unused_mut)]
                #[proof] let (mut perm, mut $g) = pair;
                #[spec] let $prev = perm.value as int;
                let op = $operand;
                #[spec] let computed = perm.value + (op as int);
                #[spec] let $res = computed;
                #[spec] let $next = computed;

                { $b }

                result = atomic.patomic.fetch_add(&mut perm, op);

                pair = (perm, $g);
            });
            result
        }
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! atomic_with_ghost_update_fetch_sub {
    ($e:expr, $operand:expr, $prev:pat, $next:pat, $res: pat, $g:ident, $b:block) => {
        {
            let result;
            let atomic = &$e;
            crate::open_atomic_invariant!(&atomic.atomic_inv => pair => {
                #[allow(unused_mut)]
                #[proof] let (mut perm, mut $g) = pair;
                #[spec] let $prev = perm.value as int;
                let op = $operand;
                #[spec] let computed = perm.value - (op as int);
                #[spec] let $res = computed;
                #[spec] let $next = computed;

                { $b }

                result = atomic.patomic.fetch_sub(&mut perm, op);

                pair = (perm, $g);
            });
            result
        }
    }
}

