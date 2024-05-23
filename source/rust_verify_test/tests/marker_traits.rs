#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const COMMON: &str = code_str! {
    use vstd::*;
    fn require_sync<T: Sync>(t: T) { }
    fn require_send<T: Send>(t: T) { }

    ::builtin_macros::verus!{
        struct Pred<A, B> { a: A, b: B }
        impl<A, B> vstd::invariant::InvariantPredicate<A, B> for Pred<A, B> {
            open spec fn inv(k: A, v: B) -> bool { true }
        }

        struct Pred2;
        impl<'a> vstd::invariant::InvariantPredicate<(), &'a u8> for Pred2 {
            open spec fn inv(k: (), v: &'a u8) -> bool { true }
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
                ::builtin_macros::verus!{
                proof fn test1<X>(tracked x: X) { }
                proof fn test2$tparams(tracked t: $t) {
                    test1(t);
                    test1(t);
                }
                }
                ".replace("$tparams", $tparams)
                .replace("$t", $t)
            => Err(e) => assert_vir_error_msg(e, "use of moved value")
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
    }
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
    }
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

// PPtr

check_send_sync!(ptr_points_to_send_sync, "<T: Send + Sync>", "vstd::ptr::PointsTo<T>");
check_send!(ptr_points_to_send, ptr_points_to_send2, "<T: Send>", "vstd::ptr::PointsTo<T>");
check_sync!(ptr_points_to_sync, ptr_points_to_sync2, "<T: Sync>", "vstd::ptr::PointsTo<T>");
check_none!(ptr_points_none, ptr_points_none2, "<T>", "vstd::ptr::PointsTo<T>");

check_covariant!(ptr_points_to_covariant, ptr_points_to_covariant2, "", "vstd::ptr::PointsTo<$P>");

check_send_sync!(points_to_raw_send_sync, "", "vstd::ptr::PointsToRaw");

// cells

check_send_sync!(cell_points_to_send_sync, "<T: Send + Sync>", "vstd::cell::PointsTo<T>");
check_send!(cell_points_to_send, cell_points_to_send2, "<T: Send>", "vstd::cell::PointsTo<T>");
check_sync!(cell_points_to_sync, cell_points_to_sync2, "<T: Sync>", "vstd::cell::PointsTo<T>");
check_none!(cell_points_none, cell_points_none2, "<T>", "vstd::cell::PointsTo<T>");

check_send_sync!(pcell, "<T: Send + Sync>", "vstd::cell::PCell<T>");

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
