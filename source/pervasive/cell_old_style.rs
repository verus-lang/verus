use core::cell::UnsafeCell;
use core::{mem, mem::MaybeUninit};
use core::marker;

#[allow(unused_imports)] use builtin::*;
#[allow(unused_imports)] use builtin_macros::*;
#[allow(unused_imports)] use crate::pervasive::*;
#[allow(unused_imports)] use crate::pervasive::modes::*;
#[allow(unused_imports)] use crate::pervasive::invariant::*;
#[allow(unused_imports)] use crate::pervasive::set::*;

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
/// For `PCell`, the associated type of the permission token is [`cell::PermData`].
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
/// Also note that the `PCell` might be dropped before the `PermData` token is dropped,
/// although in that case it will no longer be possible to use the `PermData` in `exec` code
/// to extract data from the cell.
///
/// ### Example (TODO)

#[verifier(external_body)]
pub struct PCell<#[verifier(strictly_positive)] V> {
    ucell: UnsafeCell<MaybeUninit<V>>,
}

// PCell is always safe to Send/Sync. It's the PermData object where Send/Sync matters.
// (It doesn't matter if you move the bytes to another thread if you can't access them.)

#[verifier(external)]
unsafe impl<T> Sync for PCell<T> {}

#[verifier(external)]
unsafe impl<T> Send for PCell<T> {}

// PermData<V>, on the other hand, needs to inherit both Send and Sync from the V,
// which it does by default in the given definition.
// (Note: this depends on the current behavior that #[verus::spec] fields are still counted for marker traits)

#[verifier(external_body)]
pub tracked struct PermData<#[verifier(strictly_positive)] V> {
    phantom: marker::PhantomData<V>,
    no_copy: NoCopy,
}

pub ghost struct PermDataData<V> {
    pub pcell: CellId,
    pub value: option::Option<V>,
}

#[doc(hidden)]
#[macro_export]
macro_rules! old_style_pcell_opt_internal {
    [$pcell:expr => $val:expr] => {
        $crate::pervasive::cell_old_style::PermDataData {
            pcell: $pcell,
            value: $val,
        }
    };
}

#[macro_export]
macro_rules! old_style_pcell_opt {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!(
            $crate::pervasive::cell_old_style::pcell_opt_internal!($($tail)*)
        )
    }
}

pub use old_style_pcell_opt_internal as pcell_opt_internal;
pub use old_style_pcell_opt as pcell_opt;

#[verifier(external_body)]
pub struct CellId {
    id: int,
}

impl<V> PermData<V> {
    pub spec fn view(self) -> PermDataData<V>;
}

}

impl<V> PCell<V> {
    verus!{

    /// A unique ID for the cell.

    pub spec fn id(&self) -> CellId;

    /// Return an empty ("uninitialized") cell.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn empty() -> (pt: (PCell<V>, Trk<PermData<V>>))
        ensures pt.1.0@ ===
            pcell_opt![ pt.0.id() => option::Option::None ],
    {
        let p = PCell { ucell: UnsafeCell::new(MaybeUninit::uninit()) };
        (p, Trk(proof_from_false()))
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn put(&self, #[verus::proof] perm: &mut PermData<V>, v: V)
        requires
            old(perm)@ ===
              pcell_opt![ self.id() => option::Option::None ],
        ensures
            perm@ ===
              pcell_opt![ self.id() => option::Option::Some(v) ],
    {
        opens_invariants_none();

        unsafe {
            *(self.ucell.get()) = MaybeUninit::new(v);
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn take(&self, #[verus::proof] perm: &mut PermData<V>) -> (v: V)
        requires
            self.id() === old(perm)@.pcell,
            old(perm)@.value.is_Some(),
        ensures
            perm@.pcell === old(perm)@.pcell,
            perm@.value === option::Option::None,
            v === old(perm)@.value.get_Some_0(),
    {
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::uninit();
            mem::swap(&mut m, &mut *self.ucell.get());
            m.assume_init()
        }
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub fn replace(&self, #[verus::proof] perm: &mut PermData<V>, in_v: V) -> (out_v: V)
        requires
            self.id() === old(perm)@.pcell,
            old(perm)@.value.is_Some(),
        ensures
            perm@.pcell === old(perm)@.pcell,
            perm@.value === option::Option::Some(in_v),
            out_v === old(perm)@.value.get_Some_0(),
    {
        opens_invariants_none();

        unsafe {
            let mut m = MaybeUninit::new(in_v);
            mem::swap(&mut m, &mut *self.ucell.get());
            m.assume_init()
        }
    }

    // The reason for the the lifetime parameter 'a is
    // that `self` actually contains the data in its interior, so it needs
    // to outlive the returned borrow.

    #[inline(always)]
    #[verifier(external_body)]
    pub fn borrow<'a>(&'a self, #[verus::proof] perm: &'a PermData<V>) -> (v: &'a V)
        requires
            self.id() === perm@.pcell,
            perm@.value.is_Some(),
        ensures
            *v === perm@.value.get_Some_0(),
    {
        opens_invariants_none();

        unsafe {
            (*self.ucell.get()).assume_init_ref()
        }
    }

    }

    //////////////////////////////////
    // Untrusted functions below here

    #[inline(always)]
    pub fn into_inner(self, #[verus::proof] perm: PermData<V>) -> V
    {
        requires([
            equal(self.id(), perm.view().pcell),
            perm.view().value.is_Some(),
        ]);
        ensures(|v: V| [
            equal(v, perm.view().value.get_Some_0()),
        ]);
        opens_invariants_none();

        #[verus::proof] let mut perm = perm;
        self.take(&mut perm)
    }

    verus!{

    #[inline(always)]
    pub fn new(v: V) -> (pt: (PCell<V>, Trk<PermData<V>>))
        ensures (pt.1.0@ === PermDataData{ pcell: pt.0.id(), value: option::Option::Some(v) }),
    {
        let (p, Trk(mut t)) = Self::empty();
        p.put(&mut t, v);
        (p, Trk(t))
    }

    }
}

struct_with_invariants!{
    pub struct InvCell<#[verifier(maybe_negative)] T> {
        #[verus::spec] possible_values: Set<T>,
        pcell: PCell<T>,
        #[verus::proof] perm_inv: LocalInvariant<_, PermData<T>, _>,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant on perm_inv with (possible_values, pcell) is (perm: PermData<T>) {
            perm.view().value.is_Some()
            && possible_values.contains(perm.view().value.get_Some_0())
            && equal(pcell.id(), perm.view().pcell)
        }
    }
}

impl<T> InvCell<T> {
    #[verus::spec]
    pub fn inv(&self, val: T) -> bool {
        self.possible_values.contains(val)
    }

    pub fn new(val: T, #[verus::spec] f: FnSpec<(T,), bool>) -> Self
    {
        requires(f(val));
        ensures(|cell: Self| cell.wf() && forall(|v| f(v) == cell.inv(v)));

        let (pcell, Trk(perm)) = PCell::new(val);
        #[verus::spec] let possible_values = Set::new(f);
        #[verus::proof] let perm_inv = LocalInvariant::new(
            (possible_values, pcell),
            perm,
            verus_proof_expr!(0));
        InvCell {
            possible_values,
            pcell,
            perm_inv,
        }
    }

    pub fn replace(&self, val: T) -> T
    {
        requires(self.wf() && self.inv(val));
        ensures(|old_val| self.inv(old_val));

        let r;
        crate::open_local_invariant!(&self.perm_inv => perm => {
            r = self.pcell.replace(&mut perm, val);
        });
        r
    }
}

impl<T: Copy> InvCell<T> {
    pub fn get(&self) -> T
    {
        requires(self.wf());
        ensures(|val| self.inv(val));

        let r;
        crate::open_local_invariant!(&self.perm_inv => perm => {
            r = *self.pcell.borrow(&perm);
        });
        r
    }
}
