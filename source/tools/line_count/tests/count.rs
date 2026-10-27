mod common;
use common::*;

// run line_count on a file in line_count/test_cases
fn line_count_file(filename: &str) -> String {
    assert!(filename.ends_with(".rs"));
    let file_path = test_cases_path().join(filename);
    run_line_count(&file_path).expect(&format!("line_count failed on {:?}", file_path))
}

// run line_count with --print-all on a file in line_count/test_cases, to capture the per-line
// classification (printed to stderr) followed by the summary table (printed to stdout);
// trailing whitespace is trimmed from each line so the snapshot is robust to editors that strip it
fn line_count_file_print_all(filename: &str) -> String {
    assert!(filename.ends_with(".rs"));
    let file_path = test_cases_path().join(filename);
    let (stdout, stderr) = run_line_count_with_args(&file_path, &["--print-all"])
        .expect(&format!("line_count failed on {:?}", file_path));
    format!("{stderr}{stdout}").lines().map(str::trim_end).collect::<Vec<_>>().join("\n")
}

#[test]
fn test_line_count_full() {
    insta::assert_snapshot!(line_count_file("full.rs"), @r"
    | file    | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted | Definitions |
    |---------|---------|------|-------|------|------------|---------|--------|-------------|-------------|
    | full.rs |       1 |   35 |    14 |   38 |          0 |       7 |      0 |          33 | 1           |
    |---------|---------|------|-------|------|------------|---------|--------|-------------|-------------|
    | total   |       1 |   35 |    14 |   38 |          0 |       7 |      0 |          33 | 1           |
    ");
}

#[test]
fn test_line_count_spec_fn() {
    insta::assert_snapshot!(line_count_file("spec_fn.rs"), @r"
    | file       | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |------------|---------|------|-------|------|------------|---------|--------|-------------|
    | spec_fn.rs |       0 |    7 |     0 | 0    | 0          | 0       | 0      | 6           |
    |------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total      |       0 |    7 |     0 | 0    | 0          | 0       | 0      | 6           |
    ");
}

#[test]
fn test_line_count_no_verus() {
    insta::assert_snapshot!(line_count_file("no_verus.rs"), @r"
    | file        | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |-------------|---------|------|-------|------|------------|---------|--------|-------------|
    | no_verus.rs |       0 |    0 | 0     | 0    | 0          | 0       | 0      | 3           |
    |-------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total       |       0 |    0 | 0     | 0    | 0          | 0       | 0      | 3           |
    ");
}

#[test]
fn test_line_verus_outside() {
    insta::assert_snapshot!(line_count_file("verus_outside.rs"), @r"
    | file             | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | verus_outside.rs |       4 |    3 |     0 |    0 | 0          | 0       | 0      | 11          |
    |------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total            |       4 |    3 |     0 |    0 | 0          | 0       | 0      | 11          |
    ");
}

#[test]
fn test_line_verus_verify() {
    insta::assert_snapshot!(line_count_file("verus_verify.rs"), @r"
    | file            | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |-----------------|---------|------|-------|------|------------|---------|--------|-------------|
    | verus_verify.rs |       0 |    0 |     0 | 3    | 0          | 0       | 0      | 5           |
    |-----------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total           |       0 |    0 |     0 | 3    | 0          | 0       | 0      | 5           |
    ");
}

#[test]
fn test_line_verus_verify_dual_spec() {
    insta::assert_snapshot!(line_count_file("verus_verify_dual_spec.rs"), @r"
    | file                      | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |---------------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | verus_verify_dual_spec.rs |       0 |    0 |     0 | 3    | 0          | 0       | 0      | 5           |
    |---------------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total                     |       0 |    0 |     0 | 3    | 0          | 0       | 0      | 5           |
    ");
}

#[test]
fn test_multiple_item_attributes() {
    insta::assert_snapshot!(line_count_file("multiple_item_attributes.rs"), @r"
    | file                        | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |-----------------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | multiple_item_attributes.rs |       3 |    1 |     0 |    0 | 0          | 0       | 0      | 6           |
    |-----------------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total                       |       3 |    1 |     0 |    0 | 0          | 0       | 0      | 6           |
    ");
}

#[test]
fn test_trusted() {
    insta::assert_snapshot!(line_count_file("trusted.rs"), @r"
    | file       | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |------------|---------|------|-------|------|------------|---------|--------|-------------|
    | trusted.rs |      11 |    0 |     2 |    0 | 0          | 0       | 0      | 13          |
    |------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total      |      11 |    0 |     2 |    0 | 0          | 0       | 0      | 13          |
    ");
}

#[test]
fn test_open_invariant() {
    insta::assert_snapshot!(line_count_file_print_all("open_invariant.rs"), @r"
    Category           | Detailed contents              |

    # open_invariant.rs
                       |                                | use vstd::prelude::*;
                       |                                | use vstd::atomic::*;
                       |                                | use vstd::invariant::*;
                       |                                | use vstd::cell::pcell_maybe_uninit::*;
                       |                                | use vstd::cell::CellId;
                       |                                | use vstd::simple_pptr::MemContents;
                       |                                |
                       |                                | verus! {
                       |                                |
    Spec               | DatatypeDecl                   | ghost struct EvenPredicate {}
                       |                                |
                       | Impl                           | impl InvariantPredicate<AtomicCellId, PermissionU32> for EvenPredicate {
    Spec               | Code(S Impl Signat Body(S      |     closed spec fn inv(id: AtomicCellId, perm: PermissionU32) -> bool {
    Spec               | Code(Spec Impl Body(Spec       |         perm.id() == id && perm.value() % 2 == 0
    Spec               | Code(Spec Impl Body(Spec       |     }
                       | Impl                           | }
                       |                                |
    Spec               | DatatypeDecl                   | ghost struct EvenCell {}
                       |                                |
                       | Impl                           | impl InvariantPredicate<CellId, PointsTo<u8>> for EvenCell {
    Spec               | Code(S Impl Signat Body(S      |     open spec fn inv(cell_id: CellId, points_to: PointsTo<u8>) -> bool {
    Spec               | Code(Spec Impl Body(Spec       |         points_to.id() == cell_id
    Spec               | Code(Spec Impl Body(Spec       |           && (match points_to.mem_contents() {
    Spec               | Code(Spec Impl Body(Spec       |               MemContents::Uninit => false,
    Spec               | Code(Spec Impl Body(Spec       |               MemContents::Init(x) => x % 2 == 0,
    Spec               | Code(Spec Impl Body(Spec       |           })
    Spec               | Code(Spec Impl Body(Spec       |     }
                       | Impl                           | }
                       |                                |
    Comment            | Comment                        | // open_atomic_invariant!
                       |                                |
    Proof Exec         | Signature(Exec)                | fn open_one(atomic: &PAtomicU32, i: Tracked<AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>>)
    Spec               | Signature(Exec FunctionSpec    |     requires
    Spec               | Signature(Exec FunctionSpec    |         i@.constant() == atomic.id(),
    Exec               | Code(Exec) Body(Exec)          | {
    Proof              | Code(E Body(E Atomic OpenIn    |     open_atomic_invariant!(i.borrow() => perm => {
    Proof Exec         | Code(E Body(E GhostT Atomic    |         let y: u32 = atomic.load(Tracked(&perm));
    Trusted            | Code(E Assump Body(E Atomic    |         assume(y < 1000);
    Proof              | Code(E Body(E GhostT Atomic    |         let ghost z: int = y as int * 2;
    Proof              | Code(E ProofB Body(E Atomic    |         proof {
    Proof              | Code(E ProofB Body(E Atomic    |             if y == 0 {
    Proof              | Code( Proof Proof Body( Atomi  |                 assert(z == 0);
    Proof              | Code(E ProofB Body(E Atomic    |             }
    Proof              | Code(E ProofB Body(E Atomic    |         }
    Proof              | Code(E ProofD Body(E Atomic    |         assert(y % 2 == 0);
    Proof              | Code(E Body(E Atomic OpenIn    |     });
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Exec               | Signature(Exec)                | fn open_nested(
    Exec               | Signature(Exec)                |     a: &PAtomicU32,
    Exec               | Signature(Exec)                |     b: &PAtomicU32,
    Proof Exec         | Signature(Exec)                |     i: Tracked<AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>>,
    Proof Exec         | Signature(Exec)                |     j: Tracked<AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>>,
    Exec               | Signature(Exec)                | )
    Spec               | Signature(Exec FunctionSpec    |     requires
    Spec               | Signature(Exec FunctionSpec    |         i@.constant() == a.id(),
    Spec               | Signature(Exec FunctionSpec    |         j@.constant() == b.id(),
    Spec               | Signature(Exec FunctionSpec    |         i@.namespace() != j@.namespace(),
    Exec               | Code(Exec) Body(Exec)          | {
    Proof              | Code(E Body(E Atomic OpenIn    |     open_atomic_invariant!(i.borrow() => perm_i => {
    Proof              | Code(E Body(E Atomic OpenIn    |         open_atomic_invariant!(j.borrow() => perm_j => {
    Exec               | Code(E Body(E GhostT Atomic    |             b.store(Tracked(&mut perm_j), 4);
    Proof              | Code(E ProofB Body(E Atomic    |             proof {
    Proof              | Code( Proof Body( Ghost Atomi  |                 let tracked tmp = perm_i;
    Proof              | Code(E ProofB Body(E Atomic    |                 perm_i = tmp;
    Proof              | Code(E ProofB Body(E Atomic    |             }
    Proof              | Code(E Body(E Atomic OpenIn    |         });
    Proof              | Code(E Body(E Atomic OpenIn    |     });
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Comment            | Comment                        | // open_local_invariant!
                       |                                |
    Proof Exec         | Signature(Exec)                | fn add_2(cell: &PCell<u8>, Tracked(inv): Tracked<&LocalInvariant<CellId, PointsTo<u8>, EvenCell>>)
    Spec               | Signature(Exec FunctionSpec    |     requires inv.constant() == cell.id(),
    Exec               | Code(Exec) Body(Exec)          | {
    Proof              | Code(Exec Body(Exec OpenInvar  |     open_local_invariant!(inv => points_to => {
    Proof              | Code(Exec ProofDire Body(Exec  |         assert(points_to.is_init());
    Proof              | Code(Exec ProofDire Body(Exec  |         assert(points_to.value() % 2 == 0);
    Layout             | Code(Exec) Body(Exec)          |
    Proof Exec         | Code(Exec Body(Exec GhostTrac  |         let x = cell.take(Tracked(&mut points_to));
    Proof              | Code(Exec ProofDire Body(Exec  |         assert(x % 2 == 0);
    Layout             | Code(Exec) Body(Exec)          |
    Comment            | Comment                        |         // Add 2 (wrap around if necessary)
    Exec               | Code(Exec) Body(Exec)          |         let x_plus_2 = if x == 254 { 0 } else { x + 2 };
    Layout             | Code(Exec) Body(Exec)          |
    Exec               | Code(Exec Body(Exec GhostTrac  |         cell.put(Tracked(&mut points_to), x_plus_2);
    Layout             | Code(Exec) Body(Exec)          |
    Proof              | Code(Exec ProofDire Body(Exec  |         assert(points_to.is_init());
    Proof              | Code(Exec ProofDire Body(Exec  |         assert(points_to.value() % 2 == 0);
    Proof              | Code(Exec Body(Exec OpenInvar  |     });
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
    Comment            | Comment                        | // open_atomic_invariant_in_proof!
                       |                                |
    Proof              | Signature(Proof)               | proof fn lemma_atomic_even(
    Proof              | Signature(Proof)               |     tracked credit: OpenInvariantCredit,
    Proof              | Signature(Proof)               |     tracked i: &AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>,
    Proof              | Signature(Proof)               | )
    Proof              | Signature(Proof)               |     opens_invariants any
    Proof              | Code(Proof) Body(Proof)        | {
    Proof              | Code(P Body(P Atomic OpenIn    |     open_atomic_invariant_in_proof!(credit => i => perm => {
    Proof              | Code(Proo Body(Proo Atomic     |         let v = perm.value();
    Proof              | Code(P Body(P GhostT Atomic    |         let tracked tmp = perm;
    Proof              | Code(Proo Body(Proo Atomic     |         perm = tmp;
    Proof              | Code(P ProofD Body(P Atomic    |         assert(v % 2 == 0);
    Proof              | Code(P Body(P Atomic OpenIn    |     });
    Proof              | Code(Proof) Body(Proof)        | }
                       |                                |
    Comment            | Comment                        | // open_local_invariant_in_proof!
                       |                                |
    Proof              | Signature(Proof)               | proof fn lemma_cell_even(
    Proof              | Signature(Proof)               |     tracked credit: OpenInvariantCredit,
    Proof              | Signature(Proof)               |     tracked inv: &LocalInvariant<CellId, PointsTo<u8>, EvenCell>,
    Proof              | Signature(Proof)               | )
    Proof              | Signature(Proof)               |     opens_invariants any
    Proof              | Code(Proof) Body(Proof)        | {
    Proof              | Code(Proo Body(Proo OpenInvar  |     open_local_invariant_in_proof!(credit => inv => points_to => {
    Proof              | Code(Proo ProofDire Body(Proo  |         assert(points_to.is_init());
    Proof              | Code(Proof) Body(Proof)        |         let v = points_to.value();
    Proof              | Code(Proo ProofDire Body(Proo  |         assert(v % 2 == 0);
    Proof              | Code(Proo Body(Proo OpenInvar  |     });
    Proof              | Code(Proof) Body(Proof)        | }
                       |                                |
    Exec               | Signature(Exec)                | fn use_credits(
    Proof Exec         | Signature(Exec)                |     i: Tracked<AtomicInvariant<AtomicCellId, PermissionU32, EvenPredicate>>,
    Proof Exec         | Signature(Exec)                |     Tracked(inv): Tracked<&LocalInvariant<CellId, PointsTo<u8>, EvenCell>>,
    Exec               | Code(Exec Signature Body(Exec  | ) {
    Exec               | Code(Exec) Body(Exec)          |     let credit1 = create_open_invariant_credit();
    Exec               | Code(Exec) Body(Exec)          |     let credit2 = create_open_invariant_credit();
    Proof              | Code(Exec ProofBloc Body(Exec  |     proof {
    Proof              | Code(Exec ProofBloc Body(Exec  |         lemma_atomic_even(credit1.get(), i.borrow());
    Proof              | Code(Exec ProofBloc Body(Exec  |         lemma_cell_even(credit2.get(), inv);
    Proof              | Code(Exec ProofBloc Body(Exec  |     }
    Exec               | Code(Exec) Body(Exec)          | }
                       |                                |
                       |                                | } // verus!

    | file              | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |-------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | open_invariant.rs |       1 |   19 |    53 |   18 |          8 |       5 |      4 |          28 |
    |-------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total             |       1 |   19 |    53 |   18 |          8 |       5 |      4 |          28 |
    ");
}
