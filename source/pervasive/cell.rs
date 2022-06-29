use core::cell::UnsafeCell;
use core::mem::MaybeUninit;

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;

verus!{

// TODO implement: borrow_mut; figure out Drop, see if we can avoid leaking?

/// `PCell<V>` (which stands for "permissioned call") is the primitive Verus `Cell` type.
///
/// Technically, it is a wrapper around
/// `core::cell::UnsafeCell<core::mem::MaybeUninit<V>>`, and thus has the same runtime
/// properties: there are no runtime checks (as there would be for Rust's traditional
/// [`core::cell::RefCell`](https://doc.rust-lang.org/core/cell/struct.RefCell.html)).
/// Its data may be uninitialized.
///
/// Furthermore (and unlike both
/// [`core::cell::Cell`](https://doc.rust-lang.org/core/cell/struct.Cell.html) and
/// [`core::cell::RefCell`](https://doc.rust-lang.org/core/cell/struct.RefCell.html)),
/// a `PCell<V>` may be `Sync` (depending on `V`).
/// Thanks to verification, Verus ensures that access to the cell is data-race-free.
///
/// `PCell` uses a _ghost permission token_ similar to [`ptr::PPtr`] -- see the [`ptr::PPtr`]
/// documentation for the basics.
/// For `PCell`, the associated type of the permission token is [`cell::PermissionOpt`].
///
/// ### Differences from `PPtr`.
///
/// The key difference is that, whereas [`ptr::PPtr`] represents a fixed address in memory,
/// a `PCell` has _no_ fixed address because a `PCell` might be moved.
/// As such, the [`pcell.id()`](PCell::id) does not correspond to a memory address; rather,
/// it is a unique identifier that is fixed for a given cell, even when it is moved.
///
/// The arbitrary ID given by [`pcell.id()`](PCell::id) is of type [`CellId`].
/// Despite the fact that it is, in some ways, "like a pointer", note that
/// `CellId` does not support any meangingful arithmetic,
/// has no concept of a "null ID",
/// and has no runtime representation.
///
/// Also note that the `PCell` might be dropped before the `PermissionOpt` token is dropped,
/// although in that case it will no longer be possible to use the `PermissionOpt` in `exec` code
/// to extract data from the cell.
///
/// ### Example (TODO)

#[verifier(external_body)]
pub struct PCell<#[verifier(strictly_positive)] V> {
    ucell: UnsafeCell<MaybeUninit<V>>,
}

// PCell is always safe to Send/Sync. It's the PermissionOpt object where Send/Sync matters.
// (It doesn't matter if you move the bytes to another thread if you can't access them.)

#[verifier(external)]
unsafe impl<T> Sync for PCell<T> {}

#[verifier(external)]
unsafe impl<T> Send for PCell<T> {}

// PermissionOpt<V>, on the other hand, needs to inherit both Send and Sync from the V,
// which it does by default in the given definition.
// (Note: this depends on the current behavior that #[spec] fields are still counted for marker traits)

#[verifier(external_body)]
pub tracked struct PermissionOpt<#[verifier(strictly_positive)] V> {
    phantom: core::marker::PhantomData<V>,
}

pub ghost struct PermissionOptData<V> {
    pub pcell: CellId,
    pub value: option::Option<V>,
}

#[doc(hidden)]
#[macro_export]
macro_rules! pcell_opt_internal {
    [$pcell:expr => $val:expr] => {
        $crate::pervasive::cell::PermissionOptData {
            pcell: $pcell,
            value: $val,
        }
    };
}

#[macro_export]
macro_rules! pcell_opt {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!(
            $crate::pervasive::cell::pcell_opt_internal!($($tail)*)
        )
    }
}

pub use pcell_opt_internal;
pub use pcell_opt;

#[verifier(external_body)]
pub struct CellId {
    id: int,
}

impl<V> PermissionOpt<V> {
    pub spec fn view(self) -> PermissionOptData<V>;
}

impl<V> PCell<V> {
    /// A unique ID for the cell.

    pub spec fn id(&self) -> CellId;

    /// Return an empty ("uninitialized") cell.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn empty() -> (pt: (PCell<V>, Tracked<PermissionOpt<V>>))
        ensures pt.1@@ ===
            pcell_opt![ pt.0.id() => option::Option::None ],
    {
        let p = PCell { ucell: UnsafeCell::new(MaybeUninit::uninit()) };
        (p, Tracked::assume_new())
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn put(&self, perm: &mut Tracked<PermissionOpt<V>>, v: V)
        requires
            old(perm)@@ ===
              pcell_opt![ self.id() => option::Option::None ],
        ensures
            perm@@ ===
              pcell_opt![ self.id() => option::Option::Some(v) ],
    {
        opens_invariants_none();

        unsafe {
            *(self.ucell.get()) = MaybeUninit::new(v);
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn take(&self, perm: &mut Tracked<PermissionOpt<V>>) -> (v: V)
        requires
            self.id() === old(perm)@@.pcell,
            old(perm)@@.value.is_Some(),
        ensures
            perm@@.pcell === old(perm)@@.pcell,
            perm@@.value === option::Option::None,
            v === old(perm)@@.value.get_Some_0(),
    {
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::uninit();
            core::mem::swap(&mut m, &mut *self.ucell.get());
            m.assume_init()
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn replace(&self, perm: &mut Tracked<PermissionOpt<V>>, in_v: V) -> (out_v: V)
        requires
            self.id() === old(perm)@@.pcell,
            old(perm)@@.value.is_Some(),
        ensures
            perm@@.pcell === old(perm)@@.pcell,
            perm@@.value === option::Option::Some(in_v),
            out_v === old(perm)@@.value.get_Some_0(),
    {
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::new(in_v);
            core::mem::swap(&mut m, &mut *self.ucell.get());
            m.assume_init()
        }
    }

    // The reason for the the lifetime parameter 'a is
    // that `self` actually contains the data in its interior, so it needs
    // to outlive the returned borrow.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn borrow<'a>(&'a self, perm: &'a Tracked<PermissionOpt<V>>) -> (v: &'a V)
        requires
            self.id() === perm@@.pcell,
            perm@@.value.is_Some(),
        ensures
            *v === perm@@.value.get_Some_0(),
    {
        opens_invariants_none();

        unsafe {
            (*self.ucell.get()).assume_init_ref()
        }
    }

    //////////////////////////////////
    // Untrusted functions below here

    #[inline(always)]
    pub fn into_inner(self, perm: Tracked<PermissionOpt<V>>) -> (v: V)
        requires
            self.id() === perm@@.pcell,
            perm@@.value.is_Some(),
        ensures
            v === perm@@.value.get_Some_0(),
    {
        opens_invariants_none();

        let mut perm = perm;
        self.take(&mut perm)
    }

    #[inline(always)]
    pub fn new(v: V) -> (pt: (PCell<V>, Tracked<PermissionOpt<V>>))
        ensures (pt.1@@ === PermissionOptData{ pcell: pt.0.id(), value: option::Option::Some(v) }),
    {
        let (p, mut t) = Self::empty();
        p.put(&mut t, v);
        (p, t)
    }
}

}
