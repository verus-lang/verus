use super::prelude::*;

verus! {

/// Types used in executable code can implement View to provide a mathematical abstraction
/// of the type.
/// For example, Vec implements a view method that returns a Seq.
/// For base types like bool and u8, the view V of the type is the type itself.
/// Types only used in ghost code, such as int, nat, and Seq, do not need to implement View.
pub trait View {
    type V;

    spec fn view(&self) -> Self::V;
}

pub trait DeepView {
    type V;

    spec fn deep_view(&self) -> Self::V;
}

impl<A: View + ?Sized> View for &A {
    type V = A::V;

    #[verifier::inline]
    open spec fn view(&self) -> A::V {
        (**self).view()
    }
}

impl<A: DeepView + ?Sized> DeepView for &A {
    type V = A::V;

    #[verifier::inline]
    open spec fn deep_view(&self) -> A::V {
        (**self).deep_view()
    }
}

#[cfg(feature = "alloc")]
impl<A: View + ?Sized> View for alloc::boxed::Box<A> {
    type V = A::V;

    #[verifier::inline]
    open spec fn view(&self) -> A::V {
        (**self).view()
    }
}

#[cfg(feature = "alloc")]
impl<A: DeepView + ?Sized> DeepView for alloc::boxed::Box<A> {
    type V = A::V;

    #[verifier::inline]
    open spec fn deep_view(&self) -> A::V {
        (**self).deep_view()
    }
}

#[cfg(feature = "alloc")]
impl<A: View> View for alloc::rc::Rc<A> {
    type V = A::V;

    #[verifier::inline]
    open spec fn view(&self) -> A::V {
        (**self).view()
    }
}

#[cfg(feature = "alloc")]
impl<A: DeepView> DeepView for alloc::rc::Rc<A> {
    type V = A::V;

    #[verifier::inline]
    open spec fn deep_view(&self) -> A::V {
        (**self).deep_view()
    }
}

#[cfg(feature = "alloc")]
impl<A: View> View for alloc::sync::Arc<A> {
    type V = A::V;

    #[verifier::inline]
    open spec fn view(&self) -> A::V {
        (**self).view()
    }
}

#[cfg(feature = "alloc")]
impl<A: DeepView> DeepView for alloc::sync::Arc<A> {
    type V = A::V;

    #[verifier::inline]
    open spec fn deep_view(&self) -> A::V {
        (**self).deep_view()
    }
}

// Note: the view for Vec is declared here, not in std_specs/vec.rs,
// because "pub mod std_specs" is marked #[cfg(verus_keep_ghost)]
// and we want to keep the View impl regardless of verus_keep_ghost.
#[cfg(all(feature = "alloc", any(verus_keep_ghost, feature = "allocator")))]
impl<T, A: core::alloc::Allocator> View for alloc::vec::Vec<T, A> {
    type V = Seq<T>;

    uninterp spec fn view(&self) -> Seq<T>;
}

#[cfg(all(feature = "alloc", any(verus_keep_ghost, feature = "allocator")))]
impl<T: DeepView, A: core::alloc::Allocator> DeepView for alloc::vec::Vec<T, A> {
    type V = Seq<T::V>;

    open spec fn deep_view(&self) -> Seq<T::V> {
        let v = self.view();
        Seq::new(v.len(), |i: int| v[i].deep_view())
    }
}

#[cfg(all(feature = "alloc", not(verus_keep_ghost), not(feature = "allocator")))]
impl<T> View for alloc::vec::Vec<T> {
    type V = Seq<T>;

    uninterp spec fn view(&self) -> Seq<T>;
}

#[cfg(all(feature = "alloc", not(verus_keep_ghost), not(feature = "allocator")))]
impl<T: DeepView> DeepView for alloc::vec::Vec<T> {
    type V = Seq<T::V>;

    open spec fn deep_view(&self) -> Seq<T::V> {
        let v = self.view();
        Seq::new(v.len(), |i: int| v[i].deep_view())
    }
}

macro_rules! declare_identity_view {
    ($t:ty) => {
        #[cfg_attr(verus_keep_ghost, verifier::verify)]
        impl View for $t {
            type V = $t;

            #[cfg(verus_keep_ghost)]
            #[verus::internal(spec)]
            #[verus::internal(open)]
            #[verifier::inline]
            fn view(&self) -> $t {
                *self
            }
        }

        #[cfg_attr(verus_keep_ghost, verifier::verify)]
        impl DeepView for $t {
            type V = $t;

            #[cfg(verus_keep_ghost)]
            #[verus::internal(spec)]
            #[verus::internal(open)]
            #[verifier::inline]
            fn deep_view(&self) -> $t {
                *self
            }
        }
    }
}

declare_identity_view!(());

declare_identity_view!(bool);

declare_identity_view!(u8);

declare_identity_view!(u16);

declare_identity_view!(u32);

declare_identity_view!(u64);

declare_identity_view!(u128);

declare_identity_view!(usize);

declare_identity_view!(i8);

declare_identity_view!(i16);

declare_identity_view!(i32);

declare_identity_view!(i64);

declare_identity_view!(i128);

declare_identity_view!(isize);

declare_identity_view!(char);

macro_rules! declare_tuple_view {
    ([$($n:tt)*], [$($a:ident)*]) => {
        #[cfg_attr(verus_keep_ghost, verifier::verify)]
        impl<$($a: View, )*> View for ($($a, )*) {
            type V = ($($a::V, )*);
            #[cfg(verus_keep_ghost)]
            #[verus::internal(spec)]
            #[verus::internal(open)]
            fn view(&self) -> ($($a::V, )*) {
                ($(self.$n.view(), )*)
            }
        }

        #[cfg_attr(verus_keep_ghost, verifier::verify)]
        impl<$($a: DeepView, )*> DeepView for ($($a, )*) {
            type V = ($($a::V, )*);
            #[cfg(verus_keep_ghost)]
            #[verus::internal(spec)]
            #[verus::internal(open)]
            fn deep_view(&self) -> ($($a::V, )*) {
                ($(self.$n.deep_view(), )*)
            }
        }
    }
}

// REVIEW: we can declare more, but let's check the vstd size and overhead first
declare_tuple_view!([0], [A0]);

declare_tuple_view!([0 1], [A0 A1]);

declare_tuple_view!([0 1 2], [A0 A1 A2]);

declare_tuple_view!([0 1 2 3], [A0 A1 A2 A3]);

} // verus!
