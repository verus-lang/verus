//! Checked convenience operations over existing linear ownership.
use super::super::prelude::*;
use super::algebra::ResourceAlgebra;
use super::tsm::{Machine, Token};
use super::tsm_storage::{StorageMachine, StorageToken, frame_guard};

verus! {
broadcast use {super::super::imap::group_imap_lemmas, super::super::iset::group_iset_lemmas};
/// Select a part of the current owned fragment. The remainder is chosen only
/// from an exact local decomposition, never from a compatible machine state.
pub proof fn split_off<M: Machine>(tracked token: Token<M>, part: M::Fragment)
    -> (tracked out: (Token<M>, Token<M>))
    requires exists|remainder: M::Fragment|
        token.fragment() == M::Fragment::op(part, remainder),
    ensures out.0.loc() == token.loc(), out.1.loc() == token.loc(),
        out.0.fragment() == part,
        M::Fragment::op(out.0.fragment(), out.1.fragment()) == token.fragment(),
{
    let remainder = choose|remainder: M::Fragment|
        token.fragment() == M::Fragment::op(part, remainder);
    token.split(part, remainder)
}

/// `split_off` for storage tokens.
pub proof fn split_off_storage<M: StorageMachine>(tracked token: StorageToken<M>, part: M::Fragment)
    -> (tracked out: (StorageToken<M>, StorageToken<M>))
    requires exists|remainder: M::Fragment|
        token.fragment() == M::Fragment::op(part, remainder),
    ensures out.0.loc() == token.loc(), out.1.loc() == token.loc(),
        out.0.fragment() == part,
        M::Fragment::op(out.0.fragment(), out.1.fragment()) == token.fragment(),
{
    let remainder = choose|remainder: M::Fragment|
        token.fragment() == M::Fragment::op(part, remainder);
    token.split(part, remainder)
}

/// Pack an actual tracked value for a singleton physical deposit.
pub proof fn singleton_map<K, V>(key: K, tracked value: V) -> (tracked out: IMap<K, V>)
    ensures out == IMap::<K,V>::empty().insert(key, value),
{
    let tracked mut out = IMap::<K,V>::tracked_empty();
    out.tracked_insert(key, value);
    out
}

/// Recover a value from an actual singleton withdrawal.
pub proof fn take_singleton<K, V>(tracked map: IMap<K, V>, key: K) -> (tracked out: V)
    requires map.dom() == ISet::<K>::empty().insert(key),
    ensures out == map[key],
{
    let tracked mut map = map;
    map.tracked_remove(key)
}

/// Borrow the actual stored value directly; its lifetime follows the token.
pub proof fn guard_value<M: StorageMachine>(tracked token: &StorageToken<M>, key: M::Key, value: M::Value)
    -> (tracked out: &M::Value)
    requires frame_guard::<M>(token.fragment(), IMap::empty().insert(key, value)),
    ensures *out == value,
{
    let tracked guarded = token.guard(IMap::empty().insert(key, value));
    guarded.tracked_borrow(key)
}
}
