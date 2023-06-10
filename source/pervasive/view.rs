#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

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

impl<A: View> View for &A {
    type V = A::V;
    #[verifier::external_body]
    spec fn view(&self) -> A::V {
        (**self).view()
    }
}

impl<A: View> View for Box<A> {
    type V = A::V;
    #[verifier::external_body]
    spec fn view(&self) -> A::V {
        (**self).view()
    }
}

impl<A: View> View for std::rc::Rc<A> {
    type V = A::V;
    #[verifier::external_body]
    spec fn view(&self) -> A::V {
        (**self).view()
    }
}

impl<A: View> View for std::sync::Arc<A> {
    type V = A::V;
    #[verifier::external_body]
    spec fn view(&self) -> A::V {
        (**self).view()
    }
}

macro_rules! declare_identify_view {
    ($t:ty) => {
        impl View for $t {
            type V = $t;
            #[verifier::spec]
            fn view(&self) -> $t {
                *self
            }
        }
    }
}

// TODO: declare_identify_view!(());
declare_identify_view!(bool);
declare_identify_view!(u8);
declare_identify_view!(u16);
declare_identify_view!(u32);
declare_identify_view!(u64);
declare_identify_view!(u128);
declare_identify_view!(usize);
declare_identify_view!(i8);
declare_identify_view!(i16);
declare_identify_view!(i32);
declare_identify_view!(i64);
declare_identify_view!(i128);
declare_identify_view!(isize);

macro_rules! declare_tuple_view {
    ([$($n:tt)*], [$($a:ident)*]) => {
        impl<$($a: View, )*> View for ($($a, )*) {
            type V = ($($a::V, )*);
            #[verifier::spec]
            fn view(&self) -> ($($a::V, )*) {
                ($(self.$n.view(), )*)
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
