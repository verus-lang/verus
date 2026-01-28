#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

use vstd::atomic::*;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::simple_pptr::*;

verus! {

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

pub fn increment_bad(var: &PAtomicU64, Tracked(perm): Tracked<&mut PermissionU64>)
    requires
        old(perm)@.patomic == var.id(),
    ensures
        perm@.patomic == old(perm)@.patomic,
        perm@.value == old(perm)@.value.wrapping_add(1),
{
    let val = var.load(Tracked(&*perm));
    var.store(Tracked(perm), val.wrapping_add(1));
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

fn call_increment_bad() {
    let (var, Tracked(perm)) = PAtomicU64::new(6);
    increment_bad(&var, Tracked(&mut perm));
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

pub fn increment_good(var: &PAtomicU64)
    atomically (atomic_update) {
        (perm: PermissionU64) -> (res: Result<PermissionU64, (PermissionU64, OpenInvariantCredit)>),
        requires
            perm@.patomic == var.id(),
        ensures match res {
            Err((p, _)) => p == perm,
            Ok(p) => {
                &&& p@.patomic == perm@.patomic
                &&& p@.value == perm@.value.wrapping_add(1)
            }
        },
        outer_mask any,
    },
{
    let Tracked(credit) = vstd::invariant::create_open_invariant_credit();
    let tracked mut au = atomic_update;

    let mut curr;
    let wrapped_au = try_open_atomic_update!(au, perm => {
        curr = var.load(Tracked(&perm));
        Tracked(Err((perm, credit)))
    });

    proof { au = wrapped_au.get().tracked_unwrap_err() };

    loop invariant au == atomic_update {
        let Tracked(credit) = vstd::invariant::create_open_invariant_credit();
        let next = curr.wrapping_add(1);

        let res;
        let maybe_au = try_open_atomic_update!(au, mut perm => {
            let ghost prev = perm;

            res = var.compare_exchange_weak(Tracked(&mut perm), curr, next);

            Tracked(match res {
                Ok(_) => Ok(perm),
                Err(_) => Err((perm, credit)),
            })
        });

        match res {
            Ok(_) => {
                assert(atomic_update.resolves());
                break;
            }

            Err(new) => {
                proof { au = maybe_au.get().tracked_unwrap_err() };
                curr = new;
            },
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

pub struct UserInv;
pub open spec const USER_INV: int = 12345;
impl InvariantPredicate<int, PermissionU64> for UserInv {
    open spec fn inv(id: int, perm: PermissionU64) -> bool {
        &&& perm.id() == id
    }
}

fn call_increment_good() {
    let (var, Tracked(perm)) = PAtomicU64::new(6);
    let tracked inv = AtomicInvariant::<_, _, UserInv>::new(perm.id(), perm, USER_INV);
    let Tracked(mut credit) = vstd::invariant::create_open_invariant_credit();

    increment_good(&var) atomically |update| {
        let tracked mut spare = None;
        open_atomic_invariant!(credit => &inv => perm => {
            let tracked res = update(perm);
            match res {
                Ok(p) => perm = p,
                Err((p, c)) => {
                    perm = p;
                    spare = Some(c);
                }
            }
        });

        match spare {
            None => break,
            Some(c) => {
                credit = c;
                continue;
            },
        }
    };

    let tracked perm = inv.into_inner();
    assert(perm@.patomic == var.id());
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

} // verus!
