#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const COMMON: &str = code_str! {
    use vstd::*;
    use vstd::resource::algebra::ResourceAlgebra;
    use vstd::resource::pcm::{PCM, Resource};
    use vstd::resource::storage_protocol::{Protocol, StorageResource, CopyableStorageResource};

    fn require_sync<T: Sync>(t: T) { }
    fn require_send<T: Send>(t: T) { }

    ::verus_builtin_macros::verus!{
        struct Pred<A, B> { a: A, b: B }
        impl<A, B> vstd::invariant::InvariantPredicate<A, B> for Pred<A, B> {
            open spec fn inv(k: A, v: B) -> bool { true }
        }

        struct Pred2;
        impl<'a> vstd::invariant::InvariantPredicate<(), &'a u8> for Pred2 {
            open spec fn inv(k: (), v: &'a u8) -> bool { true }
        }

        // PCM
        #[derive(Copy, Clone)]
        pub enum Excl {
            Unit,
            Excl(int),
            Fail,
        }

        impl ResourceAlgebra for Excl {
            open spec fn valid(self) -> bool { self != Excl::Fail }
            open spec fn op(a: Self, b: Self) -> Self {
                if a == Excl::Unit {
                    b
                } else if b == Excl::Unit {
                    a
                } else {
                    Excl::Fail
                }
            }
            proof fn associative(a: Self, b: Self, c: Self) { }
            proof fn commutative(a: Self, b: Self) { }
            proof fn valid_op(a: Self, b: Self) { }
        }

        impl PCM for Excl {
            open spec fn unit() -> Self { Excl::Unit }
            proof fn op_unit(self) { }
            proof fn unit_valid() { }
        }
    }
};

#[macro_export]
macro_rules! check_not_copy {
    ($name:ident, $name2:ident, $tparams:expr, $t:expr) => {
        test_verify_one_file! {
            #[test] $name COMMON.to_string() + &"
                fn test1<X>(x: X) { }
                fn test2$tparams(t: $t) {
                    test1(t);
                    test1(t);
                }
                ".replace("$tparams", $tparams)
                .replace("$t", $t)
            => Err(e) => assert_rust_error_msg(e, "use of moved value")
        }

        test_verify_one_file! {
            #[test] $name2 COMMON.to_string() + &"
                ::verus_builtin_macros::verus!{
                proof fn test1<X>(tracked x: X) { }
                proof fn test2$tparams(tracked t: $t) {
                    test1(t);
                    test1(t);
                }
                }
                ".replace("$tparams", $tparams)
                .replace("$t", $t)
            => Err(e) => assert_rust_error_msg(e, "use of moved value")
        }
    };
}

#[macro_export]
macro_rules! check_copy {
    ($name:ident, $tparams:expr, $t:expr) => {
        test_verify_one_file! {
            #[test] $name COMMON.to_string() + &"
                fn test1<X>(x: X) { }
                fn test2$tparams(t: $t) {
                    test1(t);
                    test1(t);
                }
                ".replace("$tparams", $tparams)
                .replace("$t", $t)
            => Ok(())
        }
    };
}

#[macro_export]
macro_rules! check_send_sync {
    ($name:ident, $tparams:expr, $t:expr) => {
        test_verify_one_file! {
            #[test] $name COMMON.to_string() + &"
                fn test1$tparams(t: $t) {
                    require_sync(t);
                }
                fn test2$tparams(t: $t) {
                    require_send(t);
                }
                ".replace("$tparams", $tparams)
                .replace("$t", $t)
            => Ok(())
        }
    };
}

#[macro_export]
macro_rules! check_send {
    ($name:ident, $name2:ident, $tparams:expr, $t:expr) => {
        test_verify_one_file! {
            #[test] $name COMMON.to_string() + &"
                fn test2$tparams(t: $t) {
                    require_send(t);
                }
                ".replace("$tparams", $tparams)
                .replace("$t", $t)
            => Ok(())
        }
        test_verify_one_file! {
            #[test] $name2 COMMON.to_string() + &"
                fn test2$tparams(t: $t) {
                    require_sync(t);
                }
                ".replace("$tparams", $tparams)
                .replace("$t", $t)
            => Err(e) => assert_rust_error_msg_all(e, "between threads safely")
        }
    };
}

#[macro_export]
macro_rules! check_sync {
    ($name:ident, $name2:ident, $tparams:expr, $t:expr) => {
        test_verify_one_file! {
            #[test] $name COMMON.to_string() + &"
                fn test2$tparams(t: $t) {
                    require_sync(t);
                }
                ".replace("$tparams", $tparams)
                .replace("$t", $t)
            => Ok(())
        }
        test_verify_one_file! {
            #[test] $name2 COMMON.to_string() + &"
                fn test2$tparams(t: $t) {
                    require_send(t);
                }
                ".replace("$tparams", $tparams)
                .replace("$t", $t)
            => Err(e) => assert_rust_error_msg_all(e, "between threads safely")
        }
    };
}

#[macro_export]
macro_rules! check_none {
    ($name:ident, $name2:ident, $tparams:expr, $t:expr) => {
        test_verify_one_file! {
            #[test] $name COMMON.to_string() + &"
                fn test2$tparams(t: $t) {
                    require_send(t);
                }
                ".replace("$tparams", $tparams)
                .replace("$t", $t)
            => Err(e) => assert_rust_error_msg_all(e, "between threads safely")
        }
        test_verify_one_file! {
            #[test] $name2 COMMON.to_string() + &"
                fn test2$tparams(t: $t) {
                    require_sync(t);
                }
                ".replace("$tparams", $tparams)
                .replace("$t", $t)
            => Err(e) => assert_rust_error_msg_all(e, "between threads safely")
        }
    };
}

#[macro_export]
macro_rules! check_covariant {
    ($name:ident, $name2: ident, $tparams:expr, $t:expr) => {
        test_verify_one_file! {
            #[test] $name COMMON.to_string() + &"
            struct J { }
            impl<'a> J {
                fn check_covariance$tparams(x: $WITH_STATIC) -> $WITH_A {
                    x
                }
            }
            ".replace("$tparams", $tparams)
            .replace("$WITH_STATIC", &($t).replace("$P", "&'static u8"))
            .replace("$WITH_A", &($t).replace("$P", "&'a u8"))
            => Ok(())
        }
        test_verify_one_file! {
            #[test] $name2 COMMON.to_string() + &"
            struct J { }
            impl<'a> J {
                fn check_contravariance$tparams(x: $WITH_A) -> $WITH_STATIC {
                    x
                }
            }
            ".replace("$tparams", $tparams)
            .replace("$WITH_STATIC", &($t).replace("$P", "&'static u8"))
            .replace("$WITH_A", &($t).replace("$P", "&'a u8"))
            => Err(err) => assert_vir_error_msg(err, "lifetime may not live long enough")
        }
    };
}

#[macro_export]
macro_rules! check_invariant {
    ($name:ident, $name2: ident, $tparams:expr, $t:expr) => {
        test_verify_one_file! {
            #[test] $name COMMON.to_string() + &"
            struct J { }
            impl<'a> J {
                fn check_covariance$tparams(x: $WITH_STATIC) -> $WITH_A {
                    x
                }
            }
            ".replace("$tparams", $tparams)
            .replace("$WITH_STATIC", &($t).replace("$P", "&'static u8"))
            .replace("$WITH_A", &($t).replace("$P", "&'a u8"))
            => Err(err) => assert_vir_error_msg(err, "lifetime may not live long enough")
        }
        test_verify_one_file! {
            #[test] $name2 COMMON.to_string() + &"
            struct J { }
            impl<'a> J {
                fn check_contravariance$tparams(x: $WITH_A) -> $WITH_STATIC {
                    x
                }
            }
            ".replace("$tparams", $tparams)
            .replace("$WITH_STATIC", &($t).replace("$P", "&'static u8"))
            .replace("$WITH_A", &($t).replace("$P", "&'a u8"))
            => Err(err) => assert_vir_error_msg(err, "lifetime may not live long enough")
        }
    };
}

// raw ptrs

check_send_sync!(raw_ptr_points_to_send_sync, "<T: Send + Sync>", "vstd::raw_ptr::PointsTo<T>");
check_send!(
    raw_ptr_points_to_send,
    raw_ptr_points_to_send2,
    "<T: Send>",
    "vstd::raw_ptr::PointsTo<T>"
);
check_sync!(
    raw_ptr_points_to_sync,
    raw_ptr_points_to_sync2,
    "<T: Sync>",
    "vstd::raw_ptr::PointsTo<T>"
);
check_none!(raw_ptr_points_none, raw_ptr_points_none2, "<T>", "vstd::raw_ptr::PointsTo<T>");

check_covariant!(
    raw_ptr_points_to_covariant,
    raw_ptr_points_to_covariant2,
    "",
    "vstd::raw_ptr::PointsTo<$P>"
);

check_not_copy!(
    raw_ptr_points_copy,
    raw_ptr_points_copy2,
    "<T: Copy>",
    "vstd::raw_ptr::PointsTo<T>"
);

// cells

check_send_sync!(cell_points_to_send_sync, "<T: Send + Sync>", "vstd::cell::PointsTo<T>");
check_send!(cell_points_to_send, cell_points_to_send2, "<T: Send>", "vstd::cell::PointsTo<T>");
check_sync!(cell_points_to_sync, cell_points_to_sync2, "<T: Sync>", "vstd::cell::PointsTo<T>");
check_none!(cell_points_none, cell_points_none2, "<T>", "vstd::cell::PointsTo<T>");

check_send_sync!(pcell, "<T: Send + Sync>", "vstd::cell::pcell::PCell<T>");

check_covariant!(
    cell_points_to_covariant,
    cell_ptr_points_to_covariant2,
    "",
    "vstd::cell::PointsTo<$P>"
);

check_not_copy!(pcell_points_copy, pcell_points_copy2, "<T: Copy>", "vstd::cell::PointsTo<T>");

// LocalInvariant

check_send!(
    local_send_sync,
    local_send_sync2,
    "<T: Send + Sync>",
    "vstd::invariant::LocalInvariant<(), T, Pred<(), T>>"
);
check_send!(
    local_send,
    local_send2,
    "<T: Send>",
    "vstd::invariant::LocalInvariant<(), T, Pred<(), T>>"
);
check_none!(
    local_sync,
    local_sync2,
    "<T: Sync>",
    "vstd::invariant::LocalInvariant<(), T, Pred<(), T>>"
);
check_none!(local_none, local_none2, "<T>", "vstd::invariant::LocalInvariant<(), T, Pred<(), T>>");

check_invariant!(
    local_invariant,
    local_invariant2,
    "",
    "vstd::invariant::LocalInvariant<(), $P, Pred2>"
);

// I think it might be ok to have
// impl<T: Copy> Copy for LocalInvariant<_, T, _>
// But I need to think about it
check_not_copy!(
    local_points_copy,
    local_points_copy2,
    "<T: Copy>",
    "vstd::invariant::LocalInvariant<(), T, Pred<(), T>>"
);

// AtomicInvariant

check_send_sync!(
    atomic_send_sync,
    "<T: Send + Sync>",
    "vstd::invariant::AtomicInvariant<(), T, Pred<(), T>>"
);
check_send_sync!(atomic_send, "<T: Send>", "vstd::invariant::AtomicInvariant<(), T, Pred<(), T>>");
check_none!(
    atomic_sync,
    atomic_sync2,
    "<T: Sync>",
    "vstd::invariant::AtomicInvariant<(), T, Pred<(), T>>"
);
check_none!(
    atomic_none,
    atomic_none2,
    "<T>",
    "vstd::invariant::AtomicInvariant<(), T, Pred<(), T>>"
);

check_invariant!(
    atomic_invariant,
    atomic_invariant2,
    "",
    "vstd::invariant::AtomicInvariant<(), $P, Pred2>"
);

check_not_copy!(
    atomic_points_copy,
    atomic_points_copy2,
    "<T: Copy>",
    "vstd::invariant::AtomicInvariant<(), T, Pred<(), T>>"
);

// AtomicUpdate

check_send_sync!(
    au_send_sync_of_send_sync,
    "<X: Send + Sync, Y: Send + Sync, P>",
    "vstd::atomic::AtomicUpdate<X, Y, P>"
);
check_send_sync!(
    au_send_sync_of_send,
    "<X: Send, Y: Send, P>",
    "vstd::atomic::AtomicUpdate<X, Y, P>"
);
check_sync!(
    au_sync_of_sync,
    au_not_send_of_sync,
    "<X: Sync, Y: Sync, P>",
    "vstd::atomic::AtomicUpdate<X, Y, P>"
);
check_sync!(
    au_sync_of_none,
    au_not_send_of_none,
    "<X, Y, P>",
    "vstd::atomic::AtomicUpdate<X, Y, P>"
);
check_not_copy!(
    au_not_copy,
    au_still_not_copy,
    "<X: Copy, Y: Copy, P: Copy>",
    "vstd::atomic::AtomicUpdate<X, Y, P>"
);

// Ghost and Tracked

check_send_sync!(trk_send_sync, "<T: Send + Sync>", "vstd::prelude::Tracked<T>");
check_send!(trk_send, trk_send2, "<T: Send>", "vstd::prelude::Tracked<T>");
check_sync!(trk_sync, trk_sync2, "<T: Sync>", "vstd::prelude::Tracked<T>");
check_none!(trk_none, trk_none2, "<T>", "vstd::prelude::Tracked<T>");
check_not_copy!(trk_not_copy, trk_not_copy_2, "<T>", "vstd::prelude::Tracked<T>");

check_send_sync!(gho, "<T>", "vstd::prelude::Ghost<T>");

check_covariant!(trk_covariant, trk_covariant2, "", "vstd::prelude::Tracked<$P>");

check_covariant!(gho_covariant, gho_covariant2, "", "vstd::prelude::Ghost<$P>");

// PCM resources
check_not_copy!(res_not_copy1, res_not_copy2, "", "vstd::resource::pcm::Resource<Excl>");
check_send_sync!(res_send_sync, "", "vstd::resource::pcm::Resource<Excl>");

check_copy!(cres_copy1, "", "vstd::resource::pcm::CopyableResource<Excl>");
check_send_sync!(cres_send_sync, "", "vstd::resource::pcm::CopyableResource<Excl>");

// Storage resources
// note: bounds on K, P should be unnecessary; V is what matters
check_not_copy!(
    sp_not_copy1,
    sp_not_copy2,
    "<K: Copy, V: Copy, P: Protocol<K, V> + Copy>",
    "vstd::resource::storage_protocol::StorageResource<K, V, P>"
);
check_send_sync!(
    sp_send_sync,
    "<K:Send+Sync, V: Send+Sync, P: Protocol<K, V> + Send + Sync>",
    "vstd::resource::storage_protocol::StorageResource<K, V, P>"
);
check_none!(
    sp_none1,
    sp_none2,
    "<K:Send+Sync, V: Sync, P: Protocol<K, V> + Send + Sync>",
    "vstd::resource::storage_protocol::StorageResource<K, V, P>"
);
check_none!(
    sp_none3,
    sp_none4,
    "<K:Send+Sync, V: Send, P: Protocol<K, V> + Send + Sync>",
    "vstd::resource::storage_protocol::StorageResource<K, V, P>"
);

check_copy!(
    csp_copy1,
    "<K, V, P>",
    "vstd::resource::storage_protocol::CopyableStorageResource<K, V, P>"
);
check_send_sync!(
    csp_send_sync,
    "<K:Send+Sync, V: Send+Sync, P: Protocol<K, V> + Send + Sync>",
    "vstd::resource::storage_protocol::CopyableStorageResource<K, V, P>"
);
check_none!(
    csp_none1,
    csp_none2,
    "<K:Send+Sync, V: Sync, P: Protocol<K, V> + Send + Sync>",
    "vstd::resource::storage_protocol::CopyableStorageResource<K, V, P>"
);
check_none!(
    csp_none3,
    csp_none4,
    "<K:Send+Sync, V: Send, P: Protocol<K, V> + Send + Sync>",
    "vstd::resource::storage_protocol::CopyableStorageResource<K, V, P>"
);
